#!/usr/bin/env python3
"""
Standalone Whale TV+ (rlaxx/zeasn.tv) extractor.
Writes an M3U playlist and XMLTV guide. No credentials required.

Usage:
    python whale.py
    python whale.py --out-dir playlists --m3u whale.m3u --epg whale.xml
    python whale.py --detail-hours 8 --detail-rate 1 --detail-budget 1500
    python whale.py --no-detail        # faster: titles/times only
    python whale.py --no-epg           # playlist only

Options:
    --out-dir DIR         Output directory, created if missing        (default: .)
    --m3u FILE            Playlist filename, relative to --out-dir    (default: whale.m3u)
    --epg FILE            XMLTV filename, relative to --out-dir       (default: whale.xml)
    --days N              Days of guide to fetch                      (default: 7)
    --detail-hours N      Only enrich programs starting within N
                          hours with descriptions/posters/episode
                          info; later programs keep titles + times    (default: 12)
    --detail-workers N    Concurrent detail requests                  (default: 4)
    --detail-rate R       Max detail requests/sec across all workers;
                          backs off automatically on HTTP 429         (default: 2.0)
    --detail-budget SEC   Max seconds spent on enrichment, soonest
                          programs first; the rest are skipped        (default: 600)
    --no-detail           Skip enrichment entirely
    --no-epg              Write the playlist only
    -v, --verbose         Debug logging

Notes:
    - Stream URL ad macros (did/session_id/cachebuster) are filled once at
      generation time, so URLs are only as fresh as the last run.
    - The detail endpoint is rate limited. If you see 429s, lower --detail-rate.

Deps: pip install requests
"""
import argparse
import logging
import os
import re
import sys
import threading
import time
import uuid
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

API_TOKEN      = "4ef13b5f3d2744e3b0a569feb8dde298"
AUTH_URL       = "https://rlaxx.zeasn.tv/livetv/api/v1/auth/access"
CHANNELS_URL   = "https://rlaxx.zeasn.tv/livetv/api/device/browser/v1/category/channels"
EPG_URL        = "https://rlaxx.zeasn.tv/livetv/api/device/browser/v1/epg"
EPG_DETAIL_URL = "https://rlaxx.zeasn.tv/livetv/api/device/browser/v1/epg/detail"
LOGO_BASE      = "https://d3b6luslimvglo.cloudfront.net/images/79/rlaxximages/channels-rescaled/icon-white"

EPG_BATCH_SIZE     = 10
EPG_DETAIL_WORKERS = 4      # keep low; 429s from shared CI IPs otherwise
DETAIL_MAX_429     = 20     # consecutive 429s (after backoff) before giving up on enrichment

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/148.0.0.0 Safari/537.36"
    ),
    "Origin":  "https://watch.whaletvplus.com",
    "Referer": "https://watch.whaletvplus.com/",
    "Accept":  "application/json, text/plain, */*",
}

CATEGORY_MAP = {
    "Movies and Series": "Movies",
    "Documentary":       "Documentary",
    "Lifestyle":         "Lifestyle",
    "Music":             "Music",
    "Travel":            "Travel",
    "DIY":               "Home & DIY",
    "Food and Drink":    "Food",
    "Sports":            "Sports",
    "Motorsports":       "Sports",
    "News":              "News",
    "Slow TV":           "Ambiance",
}
SKIP_CATEGORIES = {"All", "Featured all other countries"}

DEVICE_ID = str(uuid.uuid4())
MACRO_RE  = re.compile(r"\[%?[^\]]+%?\]")

log = logging.getLogger("whale")


def fill_url_macros(url: str) -> str:
    """Fill Ottera/SSAI ad macros (did, session_id, cachebuster are required)."""
    url = (url
           .replace("[did]",              DEVICE_ID)
           .replace("[session_id]",       str(uuid.uuid4()))
           .replace("[cachebuster]",      str(int(time.time() * 1000)))
           .replace("[dnt]",              "0")
           .replace("[lmt]",              "0")
           .replace("[consent]",          "")
           .replace("[content_id]",       "")
           .replace("[content_language]", "en")
           .replace("[content_duration]", "")
           .replace("[content_season]",   "")
           .replace("[content_episode]",  ""))
    return MACRO_RE.sub("", url)


def make_session(workers: int = EPG_DETAIL_WORKERS) -> requests.Session:
    s = requests.Session()
    s.headers.update(HEADERS)
    retry = Retry(total=3, backoff_factor=1, status_forcelist=(500, 502, 503, 504))
    s.mount("https://", HTTPAdapter(max_retries=retry, pool_connections=1,
                                    pool_maxsize=max(workers, 4)))
    return s


def get_token(s: requests.Session) -> str:
    r = s.get(AUTH_URL, params={"uuid": "1", "apiToken": API_TOKEN, "langCode": "en"}, timeout=15)
    r.raise_for_status()
    payload = r.json()
    token = (payload.get("data") or payload).get("token", "")
    if not token:
        raise RuntimeError(f"auth returned no token: {payload}")
    return token


def fetch_channels(s: requests.Session, token: str) -> list[dict]:
    r = s.get(CHANNELS_URL, params={"langCode": "en", "countryCode": "US"},
              headers={"token": token}, timeout=20)
    r.raise_for_status()
    seen, out = set(), []
    for cat in (r.json().get("data") or []):
        cat_name = cat.get("ctgName", "")
        if cat_name in SKIP_CATEGORIES:
            continue
        for ch in (cat.get("channels") or []):
            cid = ch.get("chlId", "")
            name = (ch.get("chlName") or "").strip()
            if not cid or not name or not ch.get("chlUrl") or cid in seen:
                continue
            seen.add(cid)
            ch["_category"] = CATEGORY_MAP.get(cat_name, cat_name)
            out.append(ch)
    return out


# ── M3U ───────────────────────────────────────────────────────────────────────

def q(v: str) -> str:
    return str(v).replace('"', "'")


def write_m3u(channels: list[dict], path: str, epg_path: str | None) -> None:
    header = "#EXTM3U"
    if epg_path:
        header += f' url-tvg="{epg_path}"'
    lines = [header]
    for ch in channels:
        cid  = ch["chlId"]
        name = ch["chlName"].strip()
        img  = ch.get("imageIdentifier", "")
        logo = f"{LOGO_BASE}/{img}_white.png" if img else ""
        attrs = [f'tvg-id="whale.{cid}"', f'tvg-name="{q(name)}"']
        if logo:
            attrs.append(f'tvg-logo="{logo}"')
        if str(ch.get("chlNum") or "").isdigit():
            attrs.append(f'tvg-chno="{ch["chlNum"]}"')
        lang = (ch.get("chlLangCode") or "en").split("-")[0]
        attrs.append(f'tvg-language="{lang}"')
        attrs.append(f'group-title="{q(ch["_category"])}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{name}')
        lines.append(fill_url_macros(ch["chlUrl"]))
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    log.info("wrote %s (%d channels)", path, len(channels))


# ── EPG ───────────────────────────────────────────────────────────────────────

def fetch_epg(s: requests.Session, token: str, channels: list[dict], days: int) -> list[dict]:
    ids = [ch["chlId"] for ch in channels]
    now = datetime.now(timezone.utc).timestamp()
    start_ms, end_ms = int(now * 1000), int((now + days * 86400) * 1000)

    progs: list[dict] = []
    for i in range(0, len(ids), EPG_BATCH_SIZE):
        batch = ids[i:i + EPG_BATCH_SIZE]
        url = (f"{EPG_URL}?channelIds={','.join(batch)}"
               f"&startTime={start_ms}&endTime={end_ms}&langCode=en&countryCode=US")
        try:
            r = s.get(url, headers={"token": token}, timeout=30)
            r.raise_for_status()
        except Exception as exc:
            log.error("EPG batch %d failed: %s", i // EPG_BATCH_SIZE, exc)
            continue
        for row in (r.json().get("data") or []):
            cid = str(row.get("chlId", ""))
            for pt in (row.get("ptList") or []):
                stm, etm = pt.get("prgStm"), pt.get("prgEtm")
                if not stm or not etm:
                    continue
                try:
                    start = datetime.fromtimestamp(int(stm) / 1000, tz=timezone.utc)
                    end   = datetime.fromtimestamp(int(etm) / 1000, tz=timezone.utc)
                except (ValueError, OSError):
                    continue
                if end.timestamp() <= now:
                    continue
                progs.append({
                    "chl_id":   cid,
                    "prgch_id": str(pt.get("prgchId") or ""),
                    "title":    (pt.get("prgTitle") or "").strip() or "Unknown",
                    "start":    start,
                    "end":      end,
                })
        log.info("EPG %d/%d channels", min(i + EPG_BATCH_SIZE, len(ids)), len(ids))
    return progs


class RateLimiter:
    """Shared across workers. Spaces requests by `interval`; backs off on 429, recovers on success."""

    def __init__(self, rate: float):
        self.base = 1.0 / rate if rate > 0 else 0.0
        self.interval = self.base
        self.next_at = 0.0
        self.lock = threading.Lock()

    def wait(self) -> None:
        with self.lock:
            now = time.monotonic()
            at = max(now, self.next_at)
            self.next_at = at + self.interval
        if at > now:
            time.sleep(at - now)

    def penalize(self, pause: float) -> None:
        """429: double the spacing (max 5s) and hold all workers for `pause` seconds."""
        with self.lock:
            self.interval = min(max(self.interval * 2, 0.5), 5.0)
            self.next_at = max(self.next_at, time.monotonic() + pause)

    def success(self) -> None:
        with self.lock:
            if self.interval > self.base:
                self.interval = max(self.base, self.interval * 0.97)


def enrich(s: requests.Session, token: str, progs: list[dict], hours: int,
           workers: int = EPG_DETAIL_WORKERS, rate: float = 2.0,
           budget: float = 600.0) -> None:
    cutoff = datetime.now(timezone.utc).timestamp() + hours * 3600
    # soonest first, so a cut-off budget loses the least valuable (furthest-out) programs
    ordered = sorted((p for p in progs if p["prgch_id"] and p["start"].timestamp() < cutoff),
                     key=lambda p: p["start"])
    targets = {p["prgch_id"]: p for p in ordered}
    if not targets:
        return
    log.info("enriching %d programs: %d workers, %.1f req/s, %ds budget",
             len(targets), workers, rate, budget)

    limiter = RateLimiter(rate)
    deadline = time.monotonic() + budget
    abort = threading.Event()
    lock = threading.Lock()
    state = {"consec_429": 0, "total_429": 0}

    def one(pid: str):
        if abort.is_set() or time.monotonic() > deadline:
            abort.set()
            return pid, "skipped"
        for _ in range(3):
            limiter.wait()
            try:
                r = s.get(f"{EPG_DETAIL_URL}/{pid}", headers={"token": token}, timeout=15)
            except Exception:
                return pid, None
            if r.status_code == 200:
                limiter.success()
                with lock:
                    state["consec_429"] = 0
                try:
                    return pid, r.json().get("data") or {}
                except ValueError:
                    return pid, None
            if r.status_code == 429:
                try:
                    pause = float(r.headers.get("Retry-After", ""))
                except ValueError:
                    pause = 5.0
                pause = min(max(pause, 2.0), 30.0)
                limiter.penalize(pause)
                with lock:
                    state["total_429"] += 1
                    state["consec_429"] += 1
                    if state["consec_429"] >= DETAIL_MAX_429:
                        if not abort.is_set():
                            log.warning("too many consecutive 429s, skipping remaining detail requests")
                        abort.set()
                if abort.is_set():
                    return pid, "skipped"
                continue
            return pid, None
        return pid, None

    ok = err = skipped = 0
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for fut in as_completed([pool.submit(one, pid) for pid in targets]):
            pid, d = fut.result()
            if d == "skipped":
                skipped += 1
                continue
            if d is None:
                err += 1
                continue
            if not d:
                continue
            p = targets[pid]
            if (desc := (d.get("prgDesc") or "").strip()):
                p["desc"] = desc
            imgs = d.get("images") or []
            if imgs and (u := (imgs[0].get("pimgUrl") or "").strip()):
                p["poster"] = u
            if (rating := (d.get("prgRating") or "").strip()):
                p["rating"] = rating
            if (d.get("prgType") or "").upper() == "EPISODE":
                series = (d.get("seriesTitle") or "").strip()
                ep_title = (d.get("prgTitle") or "").strip()
                if series:
                    p["title"] = series
                    p["episode_title"] = ep_title or None
                try:
                    if d.get("seasonNumber"):
                        p["season"] = int(d["seasonNumber"])
                    if d.get("episodeNumber"):
                        p["episode"] = int(d["episodeNumber"])
                except (ValueError, TypeError):
                    pass
            ok += 1
    log.info("detail enriched %d/%d (%d errors, %d skipped, %d 429s, final interval %.2fs)",
             ok, len(targets), err, skipped, state["total_429"], limiter.interval)


def xmltv_time(dt: datetime) -> str:
    return dt.strftime("%Y%m%d%H%M%S +0000")


def write_xmltv(channels: list[dict], progs: list[dict], path: str) -> None:
    tv = ET.Element("tv", {"generator-info-name": "whale_extract"})
    for ch in channels:
        c = ET.SubElement(tv, "channel", {"id": f"whale.{ch['chlId']}"})
        ET.SubElement(c, "display-name").text = ch["chlName"].strip()
        img = ch.get("imageIdentifier", "")
        if img:
            ET.SubElement(c, "icon", {"src": f"{LOGO_BASE}/{img}_white.png"})

    for p in sorted(progs, key=lambda x: (x["chl_id"], x["start"])):
        e = ET.SubElement(tv, "programme", {
            "start":   xmltv_time(p["start"]),
            "stop":    xmltv_time(p["end"]),
            "channel": f"whale.{p['chl_id']}",
        })
        ET.SubElement(e, "title", {"lang": "en"}).text = p["title"]
        if p.get("episode_title"):
            ET.SubElement(e, "sub-title", {"lang": "en"}).text = p["episode_title"]
        if p.get("desc"):
            ET.SubElement(e, "desc", {"lang": "en"}).text = p["desc"]
        if p.get("poster"):
            ET.SubElement(e, "icon", {"src": p["poster"]})
        if p.get("season") and p.get("episode"):
            s_, ep = p["season"], p["episode"]
            ET.SubElement(e, "episode-num", {"system": "onscreen"}).text = f"S{s_:02d}E{ep:02d}"
            ET.SubElement(e, "episode-num", {"system": "xmltv_ns"}).text = f"{s_ - 1}.{ep - 1}."
        if p.get("rating"):
            r = ET.SubElement(e, "rating")
            ET.SubElement(r, "value").text = p["rating"]

    ET.indent(tv)
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)
    log.info("wrote %s (%d programmes)", path, len(progs))


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Whale TV+ m3u + XMLTV extractor")
    ap.add_argument("--out-dir", default=".", help="output directory (created if missing)")
    ap.add_argument("--m3u", default="whale.m3u", help="playlist filename (relative to --out-dir)")
    ap.add_argument("--epg", default="whale.xml", help="XMLTV filename (relative to --out-dir)")
    ap.add_argument("--days", type=int, default=7, help="days of guide to fetch (default 7)")
    ap.add_argument("--detail-hours", type=int, default=12,
                    help="enrich programs starting within N hours with descriptions/posters/episode info")
    ap.add_argument("--detail-workers", type=int, default=EPG_DETAIL_WORKERS,
                    help="concurrent detail requests (default %d)" % EPG_DETAIL_WORKERS)
    ap.add_argument("--detail-rate", type=float, default=2.0,
                    help="max detail requests/sec across all workers (default 2.0; adapts down on 429)")
    ap.add_argument("--detail-budget", type=float, default=600.0,
                    help="max seconds to spend on detail enrichment (default 600)")
    ap.add_argument("--no-detail", action="store_true", help="skip detail enrichment")
    ap.add_argument("--no-epg", action="store_true", help="playlist only")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S")

    os.makedirs(args.out_dir, exist_ok=True)
    m3u_path = os.path.join(args.out_dir, args.m3u)
    epg_path = os.path.join(args.out_dir, args.epg)

    s = make_session(args.detail_workers)
    try:
        token = get_token(s)
        channels = fetch_channels(s, token)
    except Exception as exc:
        log.error("failed: %s", exc)
        return 1
    if not channels:
        log.error("no channels returned")
        return 1
    log.info("%d channels", len(channels))

    write_m3u(channels, m3u_path, None if args.no_epg else args.epg)

    if not args.no_epg:
        progs = fetch_epg(s, token, channels, args.days)
        if not args.no_detail and args.detail_hours > 0:
            enrich(s, token, progs, args.detail_hours, args.detail_workers,
                   args.detail_rate, args.detail_budget)
        write_xmltv(channels, progs, epg_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
