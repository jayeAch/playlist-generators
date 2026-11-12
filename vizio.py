#!/usr/bin/env python3
"""
Standalone Vizio WatchFree+ extractor.
Writes an M3U playlist and XMLTV guide. No credentials required.

Usage:
    python vizio.py
    python vizio.py --out-dir playlists --m3u vizio.m3u --epg vizio.xml
    python vizio.py --hours 48
    python vizio.py --no-epg           # playlist only

Options:
    --out-dir DIR     Output directory, created if missing          (default: .)
    --m3u FILE        Playlist filename, relative to --out-dir      (default: vizio.m3u)
    --epg FILE        XMLTV filename, relative to --out-dir         (default: vizio.xml)
    --hours N         Hours of guide to fetch                       (default: 24)
    --no-epg          Write the playlist only
    -v, --verbose     Debug logging

Notes:
    - API host: watchfreeplus-epg-prod.smartcasttv.com (anonymous).
    - Channels with a tokenUrl (e.g. NFL Channel) need a Bearer JWT and are skipped.
    - Stream URL ad macros ({ADID}, {USPRIVACY}, ...) are filled with the same
      privacy-neutral defaults the WatchFree+ app uses, once, at generation time.
    - EPG is fetched in one bulk request, falling back to per-channel requests.

Deps: pip install requests
"""
import argparse
import logging
import os
import sys
import time
import urllib.parse
import xml.etree.ElementTree as ET
from collections import defaultdict
from datetime import datetime, timedelta, timezone

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

CHANNELS_URL     = "https://watchfreeplus-epg-prod.smartcasttv.com/api/channels"
AIRINGS_BASE_URL = "https://watchfreeplus-epg-prod.smartcasttv.com/api/airings/"

UA = "okhttp/4.12.0"
CHUNK_SIZE = 10  # channels per bulk airings request when backfilling

# Privacy-neutral ad macro defaults matching the app's anonymous WatchFree DI
DEFAULT_MACROS = {
    "ADID":          "00000000-0000-0000-0000-000000000000",
    "USPRIVACY":     "1---",
    "IFATYPE":       "aaid",
    "LMT":           "0",
    "TARGETOPT":     "False",
    "APP_NAME":      "VIZIO",
    "APP_BUNDLE":    "com.vizio.vue.launcher",
    "APP_STORE_URL": "https://play.google.com/store/apps/details?id=com.vizio.vue.launcher",
    "DOMAIN":        "https://www.vizio.com",
    "DNT":           "0",
    "COPPA":         "0",
    "DEVICE_MAKE":   "Google",
    "WIDTH":         "1080",
    "HEIGHT":        "1920",
    "DEVICE_MODEL":  "Pixel 7",
    "APP_VERSION":   "5.0.0",
    "DEVICE_TYPE":   "mobile",
    "SKIPPABLE":     "1",
}

log = logging.getLogger("vizio")


def expand_macros(url: str, macros: dict) -> str:
    """Decode the full URL, then substitute {KEY} with individually URL-encoded values."""
    decoded = urllib.parse.unquote(url)
    for key, value in macros.items():
        decoded = decoded.replace("{" + key + "}", urllib.parse.quote(value, safe=""))
    return decoded


def make_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({"User-Agent": UA, "Accept": "application/json"})
    retry = Retry(total=3, backoff_factor=5, status_forcelist=(429, 500, 502, 503, 504))
    s.mount("https://", HTTPAdapter(max_retries=retry))
    return s


# ── Channels ──────────────────────────────────────────────────────────────────

def fetch_channels(s: requests.Session) -> list[dict]:
    r = s.get(CHANNELS_URL, timeout=30)
    r.raise_for_status()
    out = []
    for ch in (r.json().get("channels") or []):
        ch_id = ch.get("channelId")
        name = (ch.get("channelName") or "").strip()
        if not ch_id or not name:
            continue
        if ch.get("tokenUrl"):
            log.debug("skipping token-gated channel %s (%s)", ch_id, name)
            continue
        urls = ch.get("channelUrls") or []
        if not urls or not isinstance(urls[0], str):
            log.debug("skipping %s: no channelUrl", name)
            continue
        stream = expand_macros(urls[0], DEFAULT_MACROS)
        if not stream.startswith("http"):
            log.debug("skipping %s: non-HTTP URL after macro expansion", name)
            continue
        ch["_id"] = str(ch_id)
        ch["_name"] = name
        ch["_stream"] = stream
        out.append(ch)
    return out


def q(v) -> str:
    return str(v).replace('"', "'")


def write_m3u(channels: list[dict], path: str, epg_name: str | None) -> None:
    header = "#EXTM3U"
    if epg_name:
        header += f' url-tvg="{epg_name}"'
    lines = [header]
    for ch in channels:
        attrs = [f'tvg-id="vizio.{ch["_id"]}"', f'tvg-name="{q(ch["_name"])}"']
        logo = ch.get("channelIcon") or ch.get("portraitIcon") or ch.get("bwIcon")
        if logo:
            attrs.append(f'tvg-logo="{logo}"')
        num = ch.get("channelNumber")
        if str(num or "").isdigit():
            attrs.append(f'tvg-chno="{num}"')
        tms = ch.get("tmsStationId")
        if tms and str(tms) != "-1":
            attrs.append(f'tvc-guide-stationid="{tms}"')
        attrs.append(f'group-title="{q(ch.get("category") or "Uncategorized")}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch["_name"]}')
        lines.append(ch["_stream"])
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    log.info("wrote %s (%d channels)", path, len(channels))


# ── EPG ───────────────────────────────────────────────────────────────────────

def parse_airings(airings: list[dict], station_map: dict[str, str]) -> list[dict]:
    progs = []
    for a in airings:
        # stationId matches the channel's airingsKey; channelId is a numeric CDN id
        cid = station_map.get(a.get("stationId") or "")
        if not cid:
            continue
        try:
            start = datetime.fromisoformat(a["timeStart"].replace("Z", "+00:00"))
            end = datetime.fromisoformat(a["timeEnd"].replace("Z", "+00:00"))
        except (KeyError, ValueError, AttributeError):
            continue

        raw_rating = a.get("rating")
        rating = (raw_rating.get("code") if isinstance(raw_rating, dict) else raw_rating) or None

        season = a.get("seasonNumber") or None
        episode = a.get("episodeNumber") or None

        series = (a.get("seriesTitle") or "").strip() or None
        sub = (a.get("subTitle") or "").strip() or None
        raw_title = (a.get("title") or "").strip() or "Unknown"

        # seriesTitle differing from title means an episode; subTitle is the episode title
        if series and series.lower() != raw_title.lower():
            title = series
            ep_title = sub if sub and sub.lower() != series.lower() else None
        else:
            title, ep_title = raw_title, None

        progs.append({
            "chl_id": cid,
            "title": title,
            "start": start,
            "end": end,
            "desc": (a.get("description") or "").strip() or None,
            "poster": a.get("airingIcon") or None,
            "rating": rating,
            "season": season,
            "episode": episode,
            "episode_title": ep_title,
        })
    return progs


def fetch_airings_bulk(s, channels, start, end, station_map) -> list[dict]:
    params = {"start": start, "end": end,
              "startChannel": channels[0]["_id"], "channelCount": len(channels)}
    try:
        r = s.get(AIRINGS_BASE_URL, params=params, timeout=60)
        r.raise_for_status()
        airings = r.json().get("airings") or []
        if airings:
            log.debug("bulk EPG returned %d airings", len(airings))
            return parse_airings(airings, station_map)
    except Exception as exc:
        log.warning("bulk EPG fetch failed: %s", exc)
    return []


def fetch_airings_per_channel(s, channels, start, end, station_map) -> list[dict]:
    log.info("per-channel EPG fetch for %d channels", len(channels))
    progs = []
    for i, ch in enumerate(channels, 1):
        params = {"start": start, "end": end, "startChannel": ch["_id"], "channelCount": 1}
        try:
            r = s.get(AIRINGS_BASE_URL, params=params, timeout=20)
            r.raise_for_status()
            progs.extend(parse_airings(r.json().get("airings") or [], station_map))
        except Exception as exc:
            log.warning("EPG fetch failed for %s: %s", ch["_id"], exc)
        if i % 50 == 0:
            log.info("EPG %d/%d channels", i, len(channels))
        time.sleep(0.5)
    return progs


def clean_programs(progs: list[dict]) -> list[dict]:
    """Drop duplicates, zero season/episode, and per-channel placeholder S/E values
    (every numbered programme on a channel sharing one identical season/episode)."""
    seen, out = set(), []
    for p in progs:
        key = (p["chl_id"], p["start"])
        if key in seen:
            continue
        seen.add(key)
        if p["season"] == 0:
            p["season"] = None
        if p["episode"] == 0:
            p["episode"] = None
        out.append(p)

    by_ch = defaultdict(list)
    for p in out:
        if p["season"] and p["episode"]:
            by_ch[p["chl_id"]].append(p)
    for plist in by_ch.values():
        if len(plist) >= 2 and len({(p["season"], p["episode"]) for p in plist}) == 1:
            for p in plist:
                p["season"] = p["episode"] = None
    return out


def fetch_epg(s, channels, hours: int) -> list[dict]:
    now = datetime.now(timezone.utc)
    start = now.strftime("%Y-%m-%dT%H:%M:%S.000Z")
    end = (now + timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%S.000Z")
    log.info("fetching EPG for %d channels (%s, +%dh)", len(channels), start, hours)

    station_map = {ch["airingsKey"]: ch["_id"] for ch in channels if ch.get("airingsKey")}
    progs = fetch_airings_bulk(s, channels, start, end, station_map)

    # The bulk call can succeed yet silently truncate (channels past a server-side
    # cap get nothing), so the per-channel fallback never fires. Backfill any
    # channel that came back empty, with chunked bulk requests first, then singly.
    def missing():
        have = {p["chl_id"] for p in progs}
        return [ch for ch in channels if ch["_id"] not in have]

    miss = missing()
    if miss and progs:
        log.info("bulk EPG left %d/%d channels empty; retrying in chunks of %d",
                 len(miss), len(channels), CHUNK_SIZE)
        for i in range(0, len(miss), CHUNK_SIZE):
            progs.extend(fetch_airings_bulk(s, miss[i:i + CHUNK_SIZE], start, end, station_map))
        miss = missing()
    if miss:
        log.info("%d channels still empty; fetching individually", len(miss))
        progs.extend(fetch_airings_per_channel(s, miss, start, end, station_map))
        miss = missing()
    if miss:
        log.warning("%d channels have no guide data upstream: %s", len(miss),
                    ", ".join(ch["_name"] for ch in miss[:10]))
    progs = clean_programs(progs)
    log.info("%d EPG entries", len(progs))
    return progs


def xmltv_time(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).strftime("%Y%m%d%H%M%S +0000")


def write_xmltv(channels: list[dict], progs: list[dict], path: str) -> None:
    tv = ET.Element("tv", {"generator-info-name": "vizio_extract"})
    for ch in channels:
        c = ET.SubElement(tv, "channel", {"id": f"vizio.{ch['_id']}"})
        ET.SubElement(c, "display-name").text = ch["_name"]
        logo = ch.get("channelIcon") or ch.get("portraitIcon") or ch.get("bwIcon")
        if logo:
            ET.SubElement(c, "icon", {"src": logo})

    for p in sorted(progs, key=lambda x: (x["chl_id"], x["start"])):
        e = ET.SubElement(tv, "programme", {
            "start": xmltv_time(p["start"]),
            "stop": xmltv_time(p["end"]),
            "channel": f"vizio.{p['chl_id']}",
        })
        ET.SubElement(e, "title", {"lang": "en"}).text = p["title"]
        if p["episode_title"]:
            ET.SubElement(e, "sub-title", {"lang": "en"}).text = p["episode_title"]
        if p["desc"]:
            ET.SubElement(e, "desc", {"lang": "en"}).text = p["desc"]
        if p["poster"]:
            ET.SubElement(e, "icon", {"src": p["poster"]})
        if p["season"] and p["episode"]:
            sn, ep = int(p["season"]), int(p["episode"])
            ET.SubElement(e, "episode-num", {"system": "onscreen"}).text = f"S{sn:02d}E{ep:02d}"
            ET.SubElement(e, "episode-num", {"system": "xmltv_ns"}).text = f"{sn - 1}.{ep - 1}."
        if p["rating"]:
            r = ET.SubElement(e, "rating")
            ET.SubElement(r, "value").text = str(p["rating"])

    ET.indent(tv)
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)
    log.info("wrote %s (%d programmes)", path, len(progs))


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Vizio WatchFree+ m3u + XMLTV extractor")
    ap.add_argument("--out-dir", default=".", help="output directory (created if missing)")
    ap.add_argument("--m3u", default="vizio.m3u", help="playlist filename (relative to --out-dir)")
    ap.add_argument("--epg", default="vizio.xml", help="XMLTV filename (relative to --out-dir)")
    ap.add_argument("--hours", type=int, default=24, help="hours of guide to fetch (default 24)")
    ap.add_argument("--no-epg", action="store_true", help="playlist only")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S")

    os.makedirs(args.out_dir, exist_ok=True)
    m3u_path = os.path.join(args.out_dir, args.m3u)
    epg_path = os.path.join(args.out_dir, args.epg)

    s = make_session()
    try:
        channels = fetch_channels(s)
    except Exception as exc:
        log.error("failed: %s", exc)
        return 1
    if not channels:
        log.error("no channels returned")
        return 1
    log.info("%d channels", len(channels))

    write_m3u(channels, m3u_path, None if args.no_epg else args.epg)

    if not args.no_epg:
        progs = fetch_epg(s, channels, args.hours)
        write_xmltv(channels, progs, epg_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
