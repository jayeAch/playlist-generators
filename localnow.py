#!/usr/bin/env python3
"""
Standalone Local Now extractor.
Writes an M3U playlist and XMLTV guide. No credentials required, but Local Now
is US-only: run from a US IP (or through a US proxy).

Usage:
    python localnow.py
    python localnow.py --city "Myrtle Beach"
    python localnow.py --dma 501 --market "nyNewYorkCity,pbs-wnet"
    python localnow.py --out-dir playlists --m3u localnow.m3u --epg localnow.xml
    python localnow.py --search "Conway"       # list matching cities and exit
    python localnow.py --no-epg                # playlist only

Options:
    --out-dir DIR      Output directory, created if missing         (default: .)
    --m3u FILE         Playlist filename, relative to --out-dir     (default: localnow.m3u)
    --epg FILE         XMLTV filename, relative to --out-dir        (default: localnow.xml)
    --city TEXT        City name; first match from Local Now's city search
                       supplies dma + market
    --dma ID           DMA override (e.g. 501)
    --market STR       Market override (e.g. ohColumbus,pbs-wosu)
    --search TEXT      Print matching cities (label, dma, market) and exit
    --best-variant     Write the highest-bandwidth variant URL instead of the
                       master playlist (default: master, so players can adapt)
    --workers N        Concurrent playback-URL lookups              (default: 8)
    --no-epg           Write the playlist only
    -v, --verbose      Debug logging

Notes:
    - Stream URLs are resolved at generation time (Local Now hands out a
      session m3u8 per request), so they are only as fresh as the last run.
      Re-run on a schedule (every few hours).
    - The API returns ~5 programmes per channel, so the guide is short
      (roughly 1-5 hours depending on channel). Run at least hourly if you
      need continuous guide data.
    - With no --city/--dma/--market, the market is auto-discovered from your
      IP; failing that it falls back to New York.
    - Subscription-locked channels are skipped.
    - Optional: drop category_utils.py next to this script to normalize
      group-title categories.

Deps: pip install requests
"""
import argparse
import base64
import json
import logging
import os
import re
import sys
import xml.etree.ElementTree as ET
import threading, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from urllib.parse import quote, urljoin

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:
    import category_utils as _cu
except Exception:  # optional
    _cu = None

HOME_URL = "https://localnow.com/"
CHANNELS_PAGE_URL = "https://localnow.com/channels"
EPG_URL_TMPL = "https://{host}/live/epg/US/website"
PLAY_URL_TMPL = "https://{host}/video/play/{video_id}/{width}/{height}"
CITY_SEARCH_URL = "https://prod.localnowapi.com/gis/api/v2/City/Search"
DEFAULT_DSP_HOST = "data-store-trans-cdn.api.cms.amdvids.com"
FALLBACK_DMA = "501"
FALLBACK_MARKET = "nyNewYorkCity,pbs-wnet,pbs-wedh,pbs-wliw,pbs-wnjt"

GEO_BLOCK_MESSAGE = (
    "Local Now is US-only and this IP appears to be outside the US (the "
    "homepage returned no runtime config). Use a US IP/VPN/proxy."
)

HEADERS = {
    "Accept": "application/json, text/plain, */*",
    "Origin": "https://localnow.com",
    "Referer": "https://localnow.com/",
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/145.0.0.0 Safari/537.36"
    ),
}

CALL_SIGN_RE = re.compile(r"^[WK][A-Z]{2,4}\b")
COMPOSITE_TITLE_RE = re.compile(
    r"^(?P<series>.+):\s+S(?P<season>\d+)\s+E(?P<episode>\d+)\s*-\s*(?P<ep_title>.+?)\s*$", re.I)
SE_RATING_RE = re.compile(
    r"^(?P<series>.+):\s+S(?P<season>\d+)\s+E(?P<episode>\d+)\s*\([^)]*\)\s*$", re.I)
EP_SUBTITLE_RE = re.compile(
    r"^(?P<series>.+?)\s[-–]\sEpisode\s(?P<episode>\d+)\s[-–]\s(?P<ep_title>.+?)\s*$", re.I)
EP_ONLY_RE = re.compile(
    r"^(?P<series>.+?)(?::\s*|,\s*|\s[-–]\s)Episode\s(?P<episode>\d+)\s*$", re.I)
INVALID_PROGRAM_IDS = {"epg-feed-not-available"}

log = logging.getLogger("localnow")

import threading, time

MIN_INTERVAL = 1.5  # seconds between playback-URL requests, across all workers
_throttle_lock = threading.Lock()
_last_call = [0.0]


def throttle():
    with _throttle_lock:
        wait = MIN_INTERVAL - (time.monotonic() - _last_call[0])
        if wait > 0:
            time.sleep(wait)
        _last_call[0] = time.monotonic()


class GeoBlocked(RuntimeError):
    pass


# ── helpers ───────────────────────────────────────────────────────────────────

def safe_int(v):
    try:
        return None if v in (None, "") else int(v)
    except (ValueError, TypeError):
        return None


def parse_title(raw, api_season, api_episode, api_ep_title):
    """Normalize Local Now composite titles -> (title, season, episode, ep_title)."""
    if not raw:
        return raw, api_season, api_episode, api_ep_title
    t = raw.strip()
    m = COMPOSITE_TITLE_RE.match(t)
    if m:
        return (m["series"].strip(), int(m["season"]), int(m["episode"]),
                (api_ep_title or m["ep_title"] or "").strip() or None)
    m = SE_RATING_RE.match(t)
    if m:
        return m["series"].strip(), int(m["season"]), int(m["episode"]), api_ep_title
    m = EP_SUBTITLE_RE.match(t)
    if m:
        ep = int(m["episode"])
        return (m["series"].strip(), api_season, api_episode or ep,
                (api_ep_title or m["ep_title"] or "").strip() or None)
    m = EP_ONLY_RE.match(t)
    if m:
        ep = int(m["episode"])
        return (m["series"].strip(), api_season, api_episode or ep,
                (api_ep_title or f"Episode {ep}").strip() or None)
    return t, api_season, api_episode, api_ep_title


def decode_jwt_exp(token):
    try:
        payload = token.split(".")[1]
        payload += "=" * (-len(payload) % 4)
        exp = json.loads(base64.urlsafe_b64decode(payload.encode()).decode()).get("exp")
        return datetime.fromtimestamp(int(exp), tz=timezone.utc) if exp else None
    except Exception:
        return None


def extract_next_data(html):
    m = re.search(r'<script id="__NEXT_DATA__" type="application/json">\s*(.*?)\s*</script>',
                  html, re.S)
    return json.loads(m.group(1)) if m else None


def extract_dma_id(value):
    if not value:
        return None
    if isinstance(value, dict):
        for k in ("dmaId", "dma_id", "dma"):
            if value.get(k):
                return str(value[k])
        return None
    s = str(value)
    m = re.search(r'"?dmaId"?\s*[:=]\s*"?(\d+)', s) or re.search(r"\b(\d{3,4})\b", s)
    return m.group(1) if m else None


def extract_market_slug(value):
    if not value:
        return None
    if isinstance(value, dict):
        for k in ("market", "slug", "citySlug", "marketSlug"):
            if value.get(k):
                return str(value[k])
        return None
    s = str(value)
    m = (re.search(r'"?(?:market|slug|citySlug|marketSlug)"?\s*[:=]\s*"?([A-Za-z0-9_-]+)', s)
         or re.search(r"\b([a-z]{2}[A-Z][A-Za-z0-9]+)\b", s))
    return m.group(1) if m else None


def discover_dma_market(next_data):
    props = (next_data.get("props") or {}).get("pageProps") or {}
    cookies = props.get("serverCookies") or {}
    my_market = cookies.get("_ln_myMarket")
    my_city = cookies.get("_ln_myCity")
    detected = cookies.get("_ln_myDetectedCity")

    dma = extract_dma_id(my_market) or extract_dma_id(detected) or extract_dma_id(my_city)
    parts = []
    slug = (extract_market_slug(my_market) or extract_market_slug(my_city)
            or extract_market_slug(detected))
    if slug:
        parts.append(slug)
    cfg = (props.get("config") or {}).get("localNow") or {}
    pbs = cfg.get("pbsMarkets") or cookies.get("_ln_pbsMarkets")
    if isinstance(pbs, str) and pbs.strip():
        parts.extend(x.strip() for x in pbs.split(",") if x.strip())
    market = ",".join(dict.fromkeys(parts)) or None
    return dma, market


def infer_category(ch, name):
    genres = ch.get("genres") or []
    iab = ch.get("iab_genres") or []
    slug = (ch.get("slug") or "").lower()
    if ("My City" in genres or "hyperlocal" in slug or slug.startswith("epg-local-now")
            or CALL_SIGN_RE.search(name)):
        return "Local News"
    cat = (iab[0] if iab else None) or (genres[0] if genres else None)
    if not cat and _cu:
        try:
            cat = _cu.infer_category_from_name(name)
        except Exception:
            cat = None
    return cat or "Other"


# ── client ────────────────────────────────────────────────────────────────────

class LocalNow:
    def __init__(self, dma="", market="", workers=8):
        self.dma_cfg = (dma or "").strip()
        self.market_cfg = (market or "").strip()
        self.s = requests.Session()
        self.s.trust_env = False
        self.s.headers.update(HEADERS)
        retry = Retry(total=3, backoff_factor=1, status_forcelist=(500, 502, 503, 504))
        self.s.mount("https://", HTTPAdapter(max_retries=retry, pool_connections=1,
                                             pool_maxsize=max(workers, 4)))
        self.host = DEFAULT_DSP_HOST
        self.api_key = None
        self.token = None
        self.token_exp = None
        self.dma = None
        self.market = None
        self.channels = []

    def bootstrap(self):
        now = datetime.now(timezone.utc)
        if self.token and self.token_exp and now < self.token_exp - timedelta(minutes=2):
            return
        log.info("bootstrapping runtime config from homepage")
        r = self.s.get(HOME_URL, timeout=20)
        if r.status_code in (403, 451):
            raise GeoBlocked(GEO_BLOCK_MESSAGE)
        r.raise_for_status()
        nd = extract_next_data(r.text)
        if nd is None:
            raise GeoBlocked(GEO_BLOCK_MESSAGE)
        rc = nd.get("runtimeConfig") or {}
        if not rc:
            raise RuntimeError("runtimeConfig missing from __NEXT_DATA__")

        self.host = rc.get("DSP_API_URL", self.host)
        self.api_key = rc.get("LN_API_KEY")
        raw = rc.get("DSP_TOKEN")
        if not raw:
            raise RuntimeError("DSP_TOKEN missing from runtime config")
        try:
            token = json.loads(raw).get("token")
        except json.JSONDecodeError as exc:
            raise RuntimeError(f"bad DSP_TOKEN JSON: {exc}") from exc
        if not token:
            raise RuntimeError("token missing inside DSP_TOKEN")
        self.token = token
        self.token_exp = decode_jwt_exp(token) or (now + timedelta(hours=12))
        self.s.headers["x-access-token"] = token

        if self.dma_cfg and self.market_cfg:
            self.dma, self.market = self.dma_cfg, self.market_cfg
        else:
            self.dma, self.market = discover_dma_market(nd)
            self.dma = self.dma_cfg or self.dma
            self.market = self.market_cfg or self.market
        self.dma = self.dma or FALLBACK_DMA
        self.market = self.market or FALLBACK_MARKET
        log.info("host=%s dma=%s market=%s token_exp=%s",
                 self.host, self.dma, self.market, self.token_exp.isoformat())

    def search_cities(self, query):
        self.bootstrap()
        if not self.api_key:
            log.warning("LN_API_KEY not available; city search unavailable")
            return []
        r = self.s.get(CITY_SEARCH_URL, params={"text": query},
                       headers={"x-api-key": self.api_key}, timeout=10)
        r.raise_for_status()
        data = r.json()
        out = []
        for c in (data if isinstance(data, list) else []):
            market = (c.get("market") or "").strip()
            pbs = (c.get("pbsMarkets") or "").strip()
            combined = ",".join(filter(None, [market, pbs]))
            if not combined:
                continue
            out.append({
                "label": c.get("cityStateName") or c.get("name") or "Unknown",
                "dma": str(c.get("dmaId") or c.get("zipDma") or ""),
                "market": combined,
            })
        return out

    def fetch_channels(self):
        self.bootstrap()
        r = self.s.get(EPG_URL_TMPL.format(host=self.host),
                       params={"dma": self.dma, "market": self.market}, timeout=30)
        r.raise_for_status()
        raw = r.json().get("channels") or []
        seen, locked, out = set(), [], []
        for ch in raw:
            cid = str(ch.get("video_id") or ch.get("_id") or "").strip()
            if not cid or cid in seen:
                continue
            seen.add(cid)
            sub = ch.get("subscription_access") or {}
            if isinstance(sub, dict) and sub.get("unlocked") is False:
                locked.append((ch.get("name") or cid).strip())
                continue
            name = (ch.get("name") or "").strip() or cid
            ch["_id_"] = cid
            ch["_name"] = name
            ch["_category"] = infer_category(ch, name)
            out.append(ch)
        if locked:
            log.debug("skipped %d subscription-locked channels: %s", len(locked), ", ".join(locked))
        log.info("%d channels (%d locked skipped)", len(out), len(locked))
        self.channels = out
        return out

    def resolve(self, ch, best_variant=False):
        """Return a playable URL for one channel, or None."""
        self.bootstrap()
        cid = ch["_id_"]
        slug = (ch.get("slug") or "").strip()
        page_url = f"{CHANNELS_PAGE_URL}/{slug}" if slug else CHANNELS_PAGE_URL
        params = {
            "page_url": quote(page_url, safe=""),
            "device_devicetype": "desktop_web",
            "app_version": "0.0.0",
            "app_bundle": "web.localnow",
            "ccpa_us_privacy": "1YNY",
        }
        r = self.s.get(PLAY_URL_TMPL.format(host=self.host, video_id=cid, width=1920, height=1080),
                       params=params, timeout=20)
        r.raise_for_status()
        pb = r.json()
        url = next((u for u in (pb.get("video_m3u8"), pb.get("session_m3u8")) if u), None)
        if not url:
            return None
        if best_variant:
            try:
                url = self._best_variant(url)
            except Exception as exc:
                log.warning("variant resolution failed for %s: %s", ch["_name"], exc)
        return url

    def _best_variant(self, url):
        r = self.s.get(url, timeout=15)
        r.raise_for_status()
        lines = [l.strip() for l in r.text.splitlines() if l.strip()]
        best = (0, url)
        for i, line in enumerate(lines):
            if not line.startswith("#EXT-X-STREAM-INF:"):
                continue
            m = re.search(r"BANDWIDTH=(\d+)", line)
            bw = int(m.group(1)) if m else 0
            j = i + 1
            while j < len(lines) and lines[j].startswith("#"):
                j += 1
            if j < len(lines) and bw >= best[0]:
                best = (bw, urljoin(url, lines[j]))
        return best[1]


# ── output ────────────────────────────────────────────────────────────────────

def q(v):
    return str(v).replace('"', "'")


def write_m3u(channels, urls, path, epg_name):
    header = "#EXTM3U"
    if epg_name:
        header += f' url-tvg="{epg_name}"'
    lines = [header]
    n = 0
    for ch in channels:
        url = urls.get(ch["_id_"])
        if not url:
            continue
        name = ch["_name"]
        attrs = [f'tvg-id="localnow.{ch["_id_"]}"', f'tvg-name="{q(name)}"']
        if ch.get("logo"):
            attrs.append(f'tvg-logo="{ch["logo"]}"')
        num = safe_int(ch.get("channel_number"))
        if num is not None:
            attrs.append(f'tvg-chno="{num}"')
        lang = (ch.get("language") or "en")
        lang = (lang if isinstance(lang, str) else "en").split("-")[0].lower() or "en"
        attrs.append(f'tvg-language="{lang}"')
        attrs.append(f'group-title="{q(ch["_category"])}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{name}')
        lines.append(url)
        n += 1
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    log.info("wrote %s (%d channels)", path, n)
    return n


def build_programs(channels):
    progs = []
    for ch in channels:
        cid = ch["_id_"]
        for item in ch.get("program") or []:
            st, et = item.get("starts_at"), item.get("ends_at")
            if st is None or et is None:
                continue
            try:
                start = datetime.fromtimestamp(int(st), tz=timezone.utc)
                end = datetime.fromtimestamp(int(et), tz=timezone.utc)
            except (ValueError, OSError, TypeError):
                continue
            raw_title = (item.get("program_title") or ch["_name"] or "Unknown").strip()
            title, season, episode, ep_title = parse_title(
                raw_title, safe_int(item.get("season")), safe_int(item.get("episode")),
                (item.get("episode_title") or "").strip() or None)
            pid = (item.get("program_id") or "").strip()
            if pid.lower() in INVALID_PROGRAM_IDS:
                pid = ""
            genres = ch.get("iab_genres") or ch.get("genres") or [None]
            progs.append({
                "chl_id": cid,
                "title": title or "Unknown",
                "start": start,
                "end": end,
                "desc": (item.get("program_description") or ch.get("description") or "").strip() or None,
                "poster": item.get("image") or ch.get("poster") or None,
                "category": genres[0],
                "rating": ch.get("rating") or None,
                "episode_title": ep_title,
                "season": season,
                "episode": episode,
                "pid": pid or None,
            })
    return progs


def xmltv_time(dt):
    return dt.strftime("%Y%m%d%H%M%S +0000")


def write_xmltv(channels, progs, path, with_streams):
    tv = ET.Element("tv", {"generator-info-name": "localnow_extract"})
    for ch in channels:
        if ch["_id_"] not in with_streams:
            continue
        c = ET.SubElement(tv, "channel", {"id": f"localnow.{ch['_id_']}"})
        ET.SubElement(c, "display-name").text = ch["_name"]
        if ch.get("logo"):
            ET.SubElement(c, "icon", {"src": ch["logo"]})

    n = 0
    for p in sorted(progs, key=lambda x: (x["chl_id"], x["start"])):
        if p["chl_id"] not in with_streams:
            continue
        e = ET.SubElement(tv, "programme", {
            "start": xmltv_time(p["start"]),
            "stop": xmltv_time(p["end"]),
            "channel": f"localnow.{p['chl_id']}",
        })
        ET.SubElement(e, "title", {"lang": "en"}).text = p["title"]
        if p.get("episode_title"):
            ET.SubElement(e, "sub-title", {"lang": "en"}).text = p["episode_title"]
        if p.get("desc"):
            ET.SubElement(e, "desc", {"lang": "en"}).text = p["desc"]
        if p.get("category"):
            ET.SubElement(e, "category", {"lang": "en"}).text = str(p["category"])
        if p.get("poster"):
            ET.SubElement(e, "icon", {"src": p["poster"]})
        if p.get("season") and p.get("episode"):
            s_, ep = p["season"], p["episode"]
            ET.SubElement(e, "episode-num", {"system": "onscreen"}).text = f"S{s_:02d}E{ep:02d}"
            ET.SubElement(e, "episode-num", {"system": "xmltv_ns"}).text = f"{s_ - 1}.{ep - 1}."
        elif p.get("pid"):
            ET.SubElement(e, "episode-num", {"system": "dd_progid"}).text = p["pid"]
        if p.get("rating"):
            r = ET.SubElement(e, "rating")
            ET.SubElement(r, "value").text = str(p["rating"])
        n += 1

    ET.indent(tv)
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)
    log.info("wrote %s (%d programmes)", path, n)


def dedupe_episode_ids(progs):
    """Drop a program id that is reused across different airings on one channel
    (some channels return one id for every block)."""
    by = {}
    for p in progs:
        if p.get("pid"):
            by.setdefault((p["chl_id"], p["pid"]), []).append(p)
    for group in by.values():
        if len(group) > 1 and len({p["title"] for p in group}) > 1:
            for p in group:
                p["pid"] = None


# ── main ──────────────────────────────────────────────────────────────────────

def main():
    ap = argparse.ArgumentParser(description="Local Now m3u + XMLTV extractor")
    ap.add_argument("--out-dir", default=".", help="output directory (created if missing)")
    ap.add_argument("--m3u", default="localnow.m3u", help="playlist filename (relative to --out-dir)")
    ap.add_argument("--epg", default="localnow.xml", help="XMLTV filename (relative to --out-dir)")
    ap.add_argument("--city", default="", help="city name; first search match supplies dma + market")
    ap.add_argument("--dma", default="", help="DMA override, e.g. 501")
    ap.add_argument("--market", default="", help="market override, e.g. ohColumbus,pbs-wosu")
    ap.add_argument("--search", default="", help="list matching cities and exit")
    ap.add_argument("--best-variant", action="store_true",
                    help="write highest-bandwidth variant URL instead of the master playlist")
    ap.add_argument("--workers", type=int, default=8, help="concurrent playback lookups (default 8)")
    ap.add_argument("--no-epg", action="store_true", help="playlist only")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S")

    ln = LocalNow(args.dma, args.market, args.workers)
    try:
        if args.search:
            for c in ln.search_cities(args.search):
                print(f'{c["label"]}\tdma={c["dma"]}\tmarket={c["market"]}')
            return 0

        if args.city and not (args.dma and args.market):
            hits = ln.search_cities(args.city)
            if not hits:
                log.error("no city match for %r", args.city)
                return 1
            log.info("city %r -> %s (dma=%s)", args.city, hits[0]["label"], hits[0]["dma"])
            ln.dma_cfg = ln.dma_cfg or hits[0]["dma"]
            ln.market_cfg = ln.market_cfg or hits[0]["market"]
            ln.token = None  # force re-bootstrap so overrides apply
            ln.token_exp = None

        channels = ln.fetch_channels()
    except GeoBlocked as exc:
        log.error("%s", exc)
        return 1
    except Exception as exc:
        log.error("failed: %s", exc)
        return 1
    if not channels:
        log.error("no channels returned")
        return 1

    urls = {}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futs = {pool.submit(ln.resolve, ch, args.best_variant): ch for ch in channels}
        for fut in as_completed(futs):
            ch = futs[fut]
            try:
                url = fut.result()
            except Exception as exc:
                log.warning("playback failed for %s: %s", ch["_name"], exc)
                continue
            if url:
                urls[ch["_id_"]] = url
            else:
                log.warning("no playback URL for %s", ch["_name"])
    log.info("resolved %d/%d streams", len(urls), len(channels))
    if not urls:
        log.error("no streams resolved")
        return 1

    os.makedirs(args.out_dir, exist_ok=True)
    m3u_path = os.path.join(args.out_dir, args.m3u)
    epg_path = os.path.join(args.out_dir, args.epg)

    write_m3u(channels, urls, m3u_path, None if args.no_epg else args.epg)

    if not args.no_epg:
        progs = build_programs(channels)
        dedupe_episode_ids(progs)
        write_xmltv(channels, progs, epg_path, set(urls))
    return 0


if __name__ == "__main__":
    sys.exit(main())
