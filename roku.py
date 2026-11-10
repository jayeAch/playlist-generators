#!/usr/bin/env python3
"""
Standalone The Roku Channel (US live TV) extractor.
Writes an M3U playlist and XMLTV guide. No credentials required.

Usage:
    python roku.py
    python roku.py --out-dir playlists --m3u roku.m3u --epg roku.xml
    python roku.py --workers 4 --max-epg-requests 300
    python roku.py --no-epg            # playlist only
    python roku.py -v                  # debug logging

Options:
    --out-dir DIR           Output directory, created if missing        (default: .)
    --m3u FILE              Playlist filename, relative to --out-dir    (default: roku.m3u)
    --epg FILE              XMLTV filename, relative to --out-dir       (default: roku.xml)
    --workers N             Concurrent playback / guide requests        (default: 4)
    --stream-rate R         Max playback requests/sec across workers    (default: 5.0)
    --min-guide-hours N     Re-fetch a channel's guide when its stored
                            guide covers less than N hours ahead        (default: 12)
    --max-epg-requests N    Cap on guide requests per run, least-covered
                            channels first; 0 = no cap                  (default: 0)
    --epg-budget SEC        Max seconds spent on guide requests         (default: 600)
    --include-dash          Keep channels whose playback URL is a DASH
                            (.mpd) manifest instead of HLS; these need
                            Widevine and are skipped by default
    --no-epg                Write the playlist only
    -v, --verbose           Debug logging

Notes:
    - Stream URLs come from the playback API and are signed (JWT + traceId). They
      stay valid for roughly 5-6 hours, so run this at least every 6 hours.
    - Only channels that resolve to a stream are written. Channels the playback API
      refuses (403, usually DRM-locked) are skipped.
    - If a playback call fails with 502/503/504, a URL is built from the channel's
      selector UUID plus the OSM session token of a channel that did resolve.
    - The guide is incremental: programmes from the previous --epg file are kept for
      channels that don't need a refresh this run, so a run that hits 403/429 or runs
      out of budget doesn't lose guide data. Delete the XML to force a full refetch.
    - A 403/429 on the guide stops further guide requests for the run.
    - Gracenote station ids are emitted as tvc-guide-stationid when Roku supplies one.

Deps: pip install requests
"""
import argparse
import base64
import logging
import os
import re
import sys
import threading
import time
import uuid
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from urllib.parse import parse_qs, quote, urlparse

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

BASE        = "https://therokuchannel.roku.com"
HOME        = f"{BASE}/"
CSRF_URL    = f"{BASE}/api/v1/csrf"
PLAYBACK    = f"{BASE}/api/v3/playback"
EPG_URL     = f"{BASE}/api/v2/epg"
EPG_SCHEDULE_TPL = f"{BASE}/api/v4/epg/{{sid}}"
BILLBOARD_URL = f"{BASE}/api/v1/billboard/landing/trc-us-live-ml-page-en-current"
CONTENT_TPL = "https://content.sr.roku.com/content/v1/roku-trc/{sid}"
PROXY_BASE  = f"{BASE}/api/v2/homescreen/content/"
OSM_BASE    = "https://osm.sr.roku.com"

EPG_SCHEDULE_INCLUDE = (
    "seasonNumber,episodeNumber,description,descriptions,title,"
    "imageMap.gridEpg,series.title,parentalRatings,contentRatingClass"
)

UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/145.0.0.0 Safari/537.36"
)

HOME_403_RETRIES   = 3     # CloudFront 403s are often edge-specific; retry on a fresh connection
CSRF_ATTEMPTS      = 5
MAX_BAD_STREAMS    = 40    # consecutive 401/403 playback responses before giving up on the rest
DEFAULT_WORKERS    = 4

OSM_STREAM_RE   = re.compile(r"/osm/v1/hls/master/([0-9a-f-]{36})/([0-9a-f]+)/index\.m3u8")
SELECTOR_UUID_RE = re.compile(r"/v1/([0-9a-f-]{36})$")

# Tags on the EPG station object -> category (checked in order)
TAG_CATEGORY_PRIORITY = [
    ("news",               "News"),
    ("spanish-language",   "Spanish"),
    ("music",              "Music"),
    ("kids_music",         "Kids"),
    ("kids_linear",        "Kids"),
    ("ages_1-3",           "Kids"),
    ("ages_4-6",           "Kids"),
    ("ages_7-9",           "Kids"),
    ("ages_10plus",        "Kids"),
    ("educational",        "Kids"),
    ("preschool_specials", "Kids"),
]

CAT_ID_MAP = {
    "cat-news": "News", "cat-national-news": "News", "cat-epg-news-opinion": "News",
    "cat-sports": "Sports", "cat-sports-general": "Sports",
    "cat-movies": "Movies", "cat-movie": "Movies",
    "cat-comedy": "Comedy", "cat-drama": "Drama",
    "cat-reality": "Reality TV", "cat-lifestyle": "Lifestyle",
    "cat-food": "Food", "cat-music": "Music",
    "cat-kids": "Kids", "cat-family": "Kids",
}

NAME_CATEGORY_HINTS = [
    ("news",     "News"),
    ("sport",    "Sports"),
    ("movie",    "Movies"),
    ("film",     "Movies"),
    ("cinema",   "Movies"),
    ("kids",     "Kids"),
    ("cartoon",  "Kids"),
    ("music",    "Music"),
    ("comedy",   "Comedy"),
    ("food",     "Food"),
    ("cook",     "Food"),
    ("reality",  "Reality TV"),
    ("crime",    "Crime"),
    ("western",  "Western"),
]

log = logging.getLogger("roku")


# ── Session ───────────────────────────────────────────────────────────────────

def make_session(workers: int = DEFAULT_WORKERS) -> requests.Session:
    s = requests.Session()
    s.headers.update({"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"})
    # No read retries: content-proxy timeouts don't recover on retry, they just burn time.
    retry = Retry(total=3, connect=3, read=0, status=2, backoff_factor=1.0,
                  status_forcelist=(429, 500, 502, 503, 504),
                  allowed_methods=None, raise_on_status=False)
    s.mount("https://", HTTPAdapter(max_retries=retry, pool_connections=1,
                                    pool_maxsize=max(workers, 4)))
    return s


class RateLimiter:
    """Shared across workers; spaces requests by 1/rate seconds."""

    def __init__(self, rate: float):
        self.interval = 1.0 / rate if rate > 0 else 0.0
        self.next_at = 0.0
        self.lock = threading.Lock()

    def wait(self) -> None:
        if not self.interval:
            return
        with self.lock:
            now = time.monotonic()
            at = max(now, self.next_at)
            self.next_at = at + self.interval
        if at > now:
            time.sleep(at - now)


class Roku:
    """Holds the browser-style session (cookies + csrf) and makes authenticated API calls."""

    def __init__(self, workers: int = DEFAULT_WORKERS):
        self.workers = workers
        self.s = make_session(workers)
        self.csrf = ""
        self.gen = 0
        self.lock = threading.Lock()
        self.tl = threading.local()

    @staticmethod
    def _home_headers() -> dict:
        return {
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8",
            "Cache-Control": "max-age=0",
            "Pragma": "no-cache",
            "Referer": HOME,
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "same-origin",
            "Sec-Fetch-User": "?1",
            "Upgrade-Insecure-Requests": "1",
        }

    def api_headers(self) -> dict:
        return {
            "csrf-token":                         self.csrf,
            "origin":                             BASE,
            "referer":                            HOME,
            "content-type":                       "application/json",
            "x-roku-reserved-amoeba-ids":         "",
            "x-roku-reserved-experiment-configs": "e30=",
            "x-roku-reserved-experiment-state":   "W10=",
            "x-roku-reserved-lat":                "0",
        }

    def bootstrap(self) -> bool:
        """Home page for anonymous cookies, then the csrf token."""
        try:
            self.s.cookies.clear()
            self.csrf = ""
            # /live-tv is intermittently blocked by CloudFront; the root page yields the
            # same anonymous cookies.
            for attempt in range(HOME_403_RETRIES + 1):
                r = self.s.get(HOME, headers=self._home_headers(), timeout=15)
                if r.status_code == 200:
                    break
                if r.status_code == 403 and attempt < HOME_403_RETRIES:
                    log.warning("home bootstrap 403 (cf_pop=%s), retrying on a fresh connection",
                                r.headers.get("x-amz-cf-pop"))
                    self.s.close()
                    time.sleep(2 ** attempt)
                    continue
                log.error("home bootstrap returned %d", r.status_code)
                return False

            csrf = None
            for attempt in range(CSRF_ATTEMPTS):
                r2 = self.s.get(CSRF_URL, timeout=10)
                if r2.status_code == 200:
                    csrf = r2.json().get("csrf")
                    break
                wait = 2 ** attempt
                log.warning("csrf attempt %d returned %d, retry in %ds", attempt + 1, r2.status_code, wait)
                time.sleep(wait)
            if not csrf:
                log.error("could not obtain csrf token")
                return False
            self.csrf = csrf
            self.gen += 1
            log.debug("session ready, csrf=%s...", csrf[:12])
            return True
        except Exception as exc:
            log.error("session bootstrap failed: %s", exc)
            return False

    def refresh(self, seen_gen: int) -> bool:
        """Re-bootstrap once even if several workers hit a 401 at the same time."""
        with self.lock:
            if self.gen != seen_gen:
                return True
            return self.bootstrap()

    def worker_session(self) -> requests.Session:
        sess = getattr(self.tl, "session", None)
        if sess is None:
            sess = make_session(self.workers)
            self.tl.session = sess
        sess.cookies.update(self.s.cookies.get_dict())
        return sess

    def call(self, method: str, url: str, *, json_body=None, params=None, timeout: int = 10):
        """Authenticated request; refreshes the session and retries once on 401."""
        for attempt in range(2):
            gen = self.gen
            sess = self.worker_session()
            r = sess.request(method, url, headers=self.api_headers(), json=json_body,
                             params=params, timeout=timeout)
            if r.status_code == 401 and attempt == 0:
                log.warning("401 from %s, refreshing session", urlparse(url).path)
                if self.refresh(gen):
                    continue
            return r
        return r  # pragma: no cover


# ── Channels ──────────────────────────────────────────────────────────────────

def infer_category_from_name(name: str) -> str | None:
    n = (name or "").lower()
    for hint, label in NAME_CATEGORY_HINTS:
        if hint in n:
            return label
    return None


def category_from_station(station: dict) -> str:
    if station.get("kidsDirected"):
        return "Kids"
    tags = set(station.get("tags") or [])
    for tag, label in TAG_CATEGORY_PRIORITY:
        if tag in tags:
            return label
    for tag in tags:
        tl = tag.lower()
        if "reality" in tl or "wedding" in tl:
            return "Reality TV"
        if "thriller" in tl or "movie" in tl or "film" in tl or "ifc" in tl:
            return "Movies"
        if "comedy" in tl:
            return "Comedy"
        if "drama" in tl or "stories" in tl:
            return "Drama"
    return infer_category_from_name(station.get("title") or "") or "Live TV"


def extract_selector_url(view_opts: list | None) -> str | None:
    media = (view_opts[0].get("media") or {}) if view_opts else {}
    for video in media.get("videos") or []:
        if (isinstance(video, dict) and str(video.get("videoType", "")).upper() == "HLS"
                and video.get("url")):
            return video["url"]
    return None


def first_image_path(image_map: dict, keys: tuple) -> str | None:
    for key in keys:
        img = image_map.get(key)
        if img and img.get("path"):
            return img["path"]
    return None


def channel_from_station(sid: str, station: dict) -> dict:
    view_opts = station.get("viewOptions") or []
    tags = station.get("tags") or []
    category = category_from_station(station)
    gn = station.get("gracenoteStationId") or station.get("stationId") or ""
    return {
        "id":       sid,
        "name":     (station.get("title") or station.get("shortName") or "Unknown").strip(),
        "number":   station.get("displayNumber"),
        "logo":     first_image_path(station.get("imageMap") or {},
                                     ("gridEpg", "epgLogo", "liveHudLogo", "epgLogoDark")),
        "category": category,
        "language": "es" if ("spanish-language" in tags or category == "Spanish") else "en",
        "gracenote": str(gn) if str(gn).isdigit() else "",
        "play_id":  view_opts[0].get("playId") if view_opts else None,
        "selector": extract_selector_url(view_opts),
    }


def channel_from_content(sid: str, item: dict) -> dict:
    view_opts = item.get("viewOptions") or [{}]
    cats = item.get("categories") or []
    gn = item.get("gracenoteStationId") or item.get("stationId") or ""
    title = (item.get("title") or "Unknown").strip()
    return {
        "id":       sid,
        "name":     title,
        "number":   None,
        "logo":     first_image_path(item.get("imageMap") or {},
                                     ("grid", "gridEpg", "detailBackground", "detailPoster")),
        "category": CAT_ID_MAP.get(cats[0], "Live TV") if cats else (infer_category_from_name(title) or "Live TV"),
        "language": "en",
        "gracenote": str(gn) if str(gn).isdigit() else "",
        "play_id":  view_opts[0].get("playId") if view_opts else None,
        "selector": extract_selector_url(view_opts),
    }


def fetch_channels(api: Roku) -> list[dict]:
    channels: list[dict] = []
    seen: set[str] = set()

    # Phase 1: /api/v2/epg lists every live channel under features.station
    try:
        r = api.call("GET", EPG_URL, timeout=20)
        if r.status_code == 200:
            for col in r.json().get("collections", []):
                station = (col.get("features") or {}).get("station")
                if not station:
                    continue
                sid = (station.get("meta") or {}).get("id")
                if not sid or sid in seen:
                    continue
                seen.add(sid)
                channels.append(channel_from_station(sid, station))
        else:
            log.warning("channel list returned %d", r.status_code)
    except Exception as exc:
        log.warning("channel list failed: %s", exc)

    # Phase 2: billboard (hero channels) fills any gaps
    try:
        r2 = api.call("GET", BILLBOARD_URL, timeout=10)
        if r2.status_code == 200:
            for item in r2.json():
                sid = (item.get("meta") or {}).get("id")
                if not sid or sid in seen:
                    continue
                seen.add(sid)
                channels.append(channel_from_content(sid, item))
        else:
            log.debug("billboard returned %d", r2.status_code)
    except Exception as exc:
        log.warning("billboard failed: %s", exc)

    return channels


# ── Stream URLs ───────────────────────────────────────────────────────────────

def media_format(play_id: str) -> str:
    """The playId's payload says whether Roku wants DASH or HLS for the channel."""
    try:
        payload = play_id.split(".", 1)[1].replace("-", "+").replace("_", "/")
        payload += "=" * (-len(payload) % 4)
        decoded = base64.b64decode(payload).decode(errors="ignore")
        return "mpeg-dash" if "dash" in decoded.lower() else "m3u"
    except Exception:
        return "m3u"


def synthetic_osm_url(selector_url: str, session_token: str, trace_id: str) -> str | None:
    m = SELECTOR_UUID_RE.search(urlparse(selector_url).path)
    if not m:
        return None
    url = f"{OSM_BASE}/osm/v1/hls/master/{m.group(1)}/{session_token}/index.m3u8"
    return f"{url}?traceId={trace_id}" if trace_id else url


def osm_session_from_url(stream_url: str) -> tuple[str, str] | None:
    m = OSM_STREAM_RE.search(stream_url)
    if not m:
        return None
    trace = (parse_qs(urlparse(stream_url).query).get("traceId") or [""])[0]
    return m.group(2), trace


def playback_body(sid: str, play_id: str, session_id: str, fmt: str) -> dict:
    return {
        "rokuId":      sid,
        "playId":      play_id,
        "mediaFormat": fmt,
        "drmType":     "widevine",
        "quality":     "fhd",
        "bifUrl":      None,
        "adPolicyId":  "",
        "providerId":  "rokuavod",
        "playbackContextParams": (
            f"sessionId={session_id}"
            "&pageId=trc-us-live-ml-page-en-current"
            "&isNewSession=0&idType=roku-trc"
        ),
    }


def lookup_play_id(api: Roku, sid: str) -> tuple[str | None, str | None]:
    """Content-proxy fallback for channels that came without a playId."""
    content_url = CONTENT_TPL.format(sid=sid) + "?featureInclude=linearSchedule"
    r = api.call("GET", PROXY_BASE + quote(content_url, safe=""), timeout=10)
    if r.status_code != 200:
        return None, None
    view_opts = r.json().get("viewOptions") or [{}]
    return (view_opts[0].get("playId") if view_opts else None), extract_selector_url(view_opts)


def resolve_streams(api: Roku, channels: list[dict], workers: int, rate: float,
                    include_dash: bool) -> list[dict]:
    """Fill ch['stream_url'] for each channel; return the channels that resolved."""
    limiter = RateLimiter(rate)
    lock = threading.Lock()
    abort = threading.Event()
    state = {"bad_run": 0, "osm": None}
    stats: Counter = Counter()
    session_id = api.s.cookies.get("_usn", "roku-scraper")

    def one(ch: dict) -> tuple[dict, str | None, str]:
        if abort.is_set():
            return ch, None, "skipped"
        sid = ch["id"]
        try:
            play_id, selector = ch.get("play_id"), ch.get("selector")
            if not play_id:
                limiter.wait()
                play_id, sel = lookup_play_id(api, sid)
                selector = selector or sel
                ch["play_id"], ch["selector"] = play_id, selector
            if not play_id:
                return ch, None, "no_play_id"
            fmt = media_format(play_id)
            limiter.wait()
            r = api.call("POST", PLAYBACK, json_body=playback_body(sid, play_id, session_id, fmt))
        except Exception as exc:
            log.debug("playback error for %s: %s", sid, exc)
            return ch, None, "error"

        code = r.status_code
        with lock:
            if code in (401, 403):
                state["bad_run"] += 1
                if state["bad_run"] >= MAX_BAD_STREAMS and not abort.is_set():
                    log.warning("%d consecutive %s playback responses, skipping the rest",
                                state["bad_run"], code)
                    abort.set()
            elif code == 200:
                state["bad_run"] = 0
        if code != 200:
            return ch, None, f"http_{code}"
        try:
            url = r.json().get("url", "")
        except ValueError:
            url = ""
        if not url:
            return ch, None, "no_url"
        if fmt != "m3u" or ".m3u8" not in urlparse(url).path:
            if not include_dash:
                return ch, None, "dash"
        else:
            sess = osm_session_from_url(url)
            if sess:
                with lock:
                    state["osm"] = sess
        return ch, url, "ok"

    resolved: list[dict] = []
    failed_5xx: list[dict] = []
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for fut in as_completed([pool.submit(one, ch) for ch in channels]):
            ch, url, status = fut.result()
            stats[status] += 1
            if url:
                ch["stream_url"] = url
                resolved.append(ch)
            elif status in ("http_502", "http_503", "http_504") and ch.get("selector"):
                failed_5xx.append(ch)

    # Playback 5xx: build the URL from the selector UUID and a session token that worked.
    if failed_5xx and state["osm"]:
        token, trace = state["osm"]
        for ch in failed_5xx:
            if media_format(ch.get("play_id") or "") != "m3u":
                continue
            url = synthetic_osm_url(ch["selector"], token, trace)
            if url:
                ch["stream_url"] = url
                resolved.append(ch)
                stats["synthetic"] += 1

    log.info("streams: %d/%d resolved (%s)", len(resolved), len(channels),
             ", ".join(f"{k}={v}" for k, v in sorted(stats.items())))
    return resolved


# ── M3U ───────────────────────────────────────────────────────────────────────

def q(v: str) -> str:
    return str(v).replace('"', "'")


def write_m3u(channels: list[dict], path: str, epg_path: str | None) -> None:
    def sort_key(ch):
        num = str(ch.get("number") or "")
        return (int(num) if num.isdigit() else 999999, ch["name"].lower())

    header = "#EXTM3U"
    if epg_path:
        header += f' url-tvg="{epg_path}"'
    lines = [header]
    for ch in sorted(channels, key=sort_key):
        attrs = [f'tvg-id="roku.{ch["id"]}"', f'tvg-name="{q(ch["name"])}"']
        if ch.get("logo"):
            attrs.append(f'tvg-logo="{ch["logo"]}"')
        if str(ch.get("number") or "").isdigit():
            attrs.append(f'tvg-chno="{ch["number"]}"')
        attrs.append(f'tvg-language="{ch.get("language") or "en"}"')
        if ch.get("gracenote"):
            attrs.append(f'tvc-guide-stationid="{ch["gracenote"]}"')
        attrs.append(f'group-title="{q(ch["category"])}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch["name"].replace(",", ";")}')
        lines.append(ch["stream_url"])
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    log.info("wrote %s (%d channels)", path, len(channels))


# ── EPG ───────────────────────────────────────────────────────────────────────

class EPGRateLimited(Exception):
    def __init__(self, status: int):
        self.status = status
        super().__init__(f"dated EPG returned HTTP {status}")


def parse_program(entry: dict) -> dict | None:
    try:
        start = datetime.fromtimestamp(int(entry["start"]), timezone.utc)
        end = datetime.fromtimestamp(int(entry["end"]), timezone.utc)
    except (KeyError, TypeError, ValueError, OverflowError, OSError):
        return None
    if end <= start:
        return None

    c = entry.get("content") or {}
    series_title = ((c.get("series") or {}).get("title") or "").strip()
    ep_title = (c.get("title") or "").strip()
    title = series_title or ep_title or "Unknown"

    # The dated guide wraps descriptions as {"text": ...}; other payloads use plain strings.
    descs = c.get("descriptions") or {}
    desc = None
    for size in ("250", "100", "60", "40"):
        v = descs.get(size)
        if isinstance(v, dict):
            v = v.get("text")
        if isinstance(v, str) and v.strip():
            desc = v.strip()
            break
    if not desc and isinstance(c.get("description"), str):
        desc = c["description"].strip() or None

    image_map = c.get("imageMap") or {}
    poster = first_image_path(image_map, ("gridEpg", "grid"))

    ratings = c.get("parentalRatings") or []
    rating = ratings[0].get("code") if ratings and isinstance(ratings[0], dict) else None

    try:
        season = int(c["seasonNumber"]) if c.get("seasonNumber") else None
        episode = int(c["episodeNumber"]) if c.get("episodeNumber") else None
    except (ValueError, TypeError):
        season = episode = None
    if not (season and episode):
        season = episode = None

    cats: list[str] = []
    for g in c.get("genres") or []:
        g = (g or "").strip() if isinstance(g, str) else ""
        if g:
            label = g[0].upper() + g[1:]
            if label not in cats:
                cats.append(label)

    return {
        "title":         title,
        "episode_title": ep_title if series_title and ep_title and ep_title != series_title else None,
        "desc":          desc,
        "poster":        poster,
        "categories":    cats,
        "rating":        rating,
        "season":        season,
        "episode":       episode,
        "start":         start,
        "end":           end,
    }


def fetch_station_epg(api: Roku, sid: str, now: datetime) -> list[dict]:
    r = api.call("GET", EPG_SCHEDULE_TPL.format(sid=sid), params={
        "tpl_date": now.strftime("%Y-%m-%d"),
        "tpl_hour": now.hour,
        "include":  EPG_SCHEDULE_INCLUDE,
        "expand":   "series",
    })
    if r.status_code in (403, 429):
        raise EPGRateLimited(r.status_code)
    if r.status_code != 200:
        raise RuntimeError(f"HTTP {r.status_code}")
    out = []
    for entry in r.json().get("view") or []:
        window = (entry.get("features") or {}).get("otaOptions") or {}
        prog = parse_program({"start": window.get("start"), "end": window.get("end"),
                              "content": entry.get("content") or {}})
        if prog:
            out.append(prog)
    return out


def xmltv_time(dt: datetime) -> str:
    return dt.strftime("%Y%m%d%H%M%S +0000")


def parse_xmltv_time(s: str) -> datetime | None:
    try:
        return datetime.strptime(s, "%Y%m%d%H%M%S %z").astimezone(timezone.utc)
    except (TypeError, ValueError):
        return None


def load_previous_epg(path: str) -> dict[str, list[dict]]:
    """Read last run's XMLTV back into {station_id: [programme dicts]}."""
    try:
        root = ET.parse(path).getroot()
    except (FileNotFoundError, ET.ParseError, OSError):
        return {}
    out: dict[str, list[dict]] = {}
    for e in root.findall("programme"):
        ch = e.get("channel") or ""
        sid = ch[len("roku."):] if ch.startswith("roku.") else ch
        start, end = parse_xmltv_time(e.get("start")), parse_xmltv_time(e.get("stop"))
        title = e.findtext("title")
        if not sid or not start or not end or not title:
            continue
        season = episode = None
        for en in e.findall("episode-num"):
            if en.get("system") == "onscreen":
                m = re.fullmatch(r"S(\d+)E(\d+)", (en.text or "").strip())
                if m:
                    season, episode = int(m.group(1)), int(m.group(2))
        icon = e.find("icon")
        out.setdefault(sid, []).append({
            "title":         title,
            "episode_title": e.findtext("sub-title"),
            "desc":          e.findtext("desc"),
            "poster":        icon.get("src") if icon is not None else None,
            "categories":    [c.text for c in e.findall("category") if c.text],
            "rating":        e.findtext("rating/value"),
            "season":        season,
            "episode":       episode,
            "start":         start,
            "end":           end,
        })
    return out


def plan_epg_requests(sids: list[str], prev: dict[str, list[dict]], now: datetime,
                      min_hours: float, cap: int) -> list[str]:
    """Channels whose stored guide runs out within min_hours, least-covered first."""
    need = []
    for sid in sids:
        ends = [p["end"] for p in prev.get(sid, []) if p["end"] > now]
        hours = (max(ends) - now).total_seconds() / 3600 if ends else -1.0
        if hours < min_hours:
            need.append((hours, sid))
    need.sort()
    ids = [sid for _, sid in need]
    return ids[:cap] if cap > 0 else ids


def fetch_epg(api: Roku, channels: list[dict], prev: dict[str, list[dict]], workers: int,
              min_hours: float, cap: int, budget: float) -> dict[str, list[dict]]:
    """Return {station_id: programmes} for every channel: fresh where fetched, else carried over."""
    now = datetime.now(timezone.utc)
    sids = [ch["id"] for ch in channels]
    targets = plan_epg_requests(sids, prev, now, min_hours, cap)
    log.info("guide: %d/%d channels need a refresh (<%.0fh stored)%s",
             len(targets), len(sids), min_hours,
             f", capped at {cap}" if cap > 0 and len(targets) == cap else "")

    fresh: dict[str, list[dict]] = {}
    deadline = time.monotonic() + budget
    stop = threading.Event()
    stats: Counter = Counter()

    def one(sid: str):
        if stop.is_set() or time.monotonic() > deadline:
            stop.set()
            return sid, None, "skipped"
        try:
            return sid, fetch_station_epg(api, sid, now), "ok"
        except EPGRateLimited as exc:
            stop.set()
            return sid, None, f"http_{exc.status}"
        except Exception as exc:
            log.debug("guide error for %s: %s", sid, exc)
            return sid, None, "error"

    with ThreadPoolExecutor(max_workers=workers) as pool:
        for fut in as_completed([pool.submit(one, sid) for sid in targets]):
            sid, progs, status = fut.result()
            stats[status] += 1
            if progs is not None:
                fresh[sid] = progs
    if stats:
        log.info("guide: %s", ", ".join(f"{k}={v}" for k, v in sorted(stats.items())))
    if stats.get("http_403") or stats.get("http_429"):
        log.warning("guide rate-limited; keeping previous data for the channels not fetched")
    elif stats.get("skipped"):
        log.warning("guide budget used up; %d channels keep previous data this run", stats["skipped"])

    merged: dict[str, list[dict]] = {}
    for sid in sids:
        progs = fresh[sid] if sid in fresh else prev.get(sid, [])
        merged[sid] = [p for p in progs if p["end"] > now]
    return merged


def write_xmltv(channels: list[dict], guide: dict[str, list[dict]], path: str) -> None:
    tv = ET.Element("tv", {"generator-info-name": "roku_extract"})
    for ch in channels:
        c = ET.SubElement(tv, "channel", {"id": f"roku.{ch['id']}"})
        ET.SubElement(c, "display-name").text = ch["name"]
        if ch.get("logo"):
            ET.SubElement(c, "icon", {"src": ch["logo"]})

    count = 0
    for ch in channels:
        sid = ch["id"]
        seen = set()
        for p in sorted(guide.get(sid, []), key=lambda x: x["start"]):
            if (p["start"], p["title"]) in seen:
                continue
            seen.add((p["start"], p["title"]))
            e = ET.SubElement(tv, "programme", {
                "start":   xmltv_time(p["start"]),
                "stop":    xmltv_time(p["end"]),
                "channel": f"roku.{sid}",
            })
            ET.SubElement(e, "title", {"lang": "en"}).text = p["title"]
            if p.get("episode_title"):
                ET.SubElement(e, "sub-title", {"lang": "en"}).text = p["episode_title"]
            if p.get("desc"):
                ET.SubElement(e, "desc", {"lang": "en"}).text = p["desc"]
            for cat in p.get("categories") or []:
                ET.SubElement(e, "category", {"lang": "en"}).text = cat
            if p.get("poster"):
                ET.SubElement(e, "icon", {"src": p["poster"]})
            if p.get("season") and p.get("episode"):
                s_, ep = p["season"], p["episode"]
                ET.SubElement(e, "episode-num", {"system": "onscreen"}).text = f"S{s_:02d}E{ep:02d}"
                ET.SubElement(e, "episode-num", {"system": "xmltv_ns"}).text = f"{s_ - 1}.{ep - 1}."
            if p.get("rating"):
                r = ET.SubElement(e, "rating")
                ET.SubElement(r, "value").text = p["rating"]
            count += 1

    ET.indent(tv)
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)
    log.info("wrote %s (%d programmes, %d/%d channels with guide)", path, count,
             sum(1 for ch in channels if guide.get(ch["id"])), len(channels))


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="The Roku Channel m3u + XMLTV extractor")
    ap.add_argument("--out-dir", default=".", help="output directory (created if missing)")
    ap.add_argument("--m3u", default="roku.m3u", help="playlist filename (relative to --out-dir)")
    ap.add_argument("--epg", default="roku.xml", help="XMLTV filename (relative to --out-dir)")
    ap.add_argument("--workers", type=int, default=DEFAULT_WORKERS,
                    help="concurrent playback / guide requests (default %d)" % DEFAULT_WORKERS)
    ap.add_argument("--stream-rate", type=float, default=5.0,
                    help="max playback requests/sec across all workers (default 5.0)")
    ap.add_argument("--min-guide-hours", type=float, default=12.0,
                    help="re-fetch a channel's guide when its stored guide covers less than N hours (default 12)")
    ap.add_argument("--max-epg-requests", type=int, default=0,
                    help="cap on guide requests per run, least-covered first; 0 = no cap (default 0)")
    ap.add_argument("--epg-budget", type=float, default=600.0,
                    help="max seconds spent on guide requests (default 600)")
    ap.add_argument("--include-dash", action="store_true",
                    help="keep channels whose playback URL is DASH instead of HLS")
    ap.add_argument("--no-epg", action="store_true", help="playlist only")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S")

    os.makedirs(args.out_dir, exist_ok=True)
    m3u_path = os.path.join(args.out_dir, args.m3u)
    epg_path = os.path.join(args.out_dir, args.epg)

    api = Roku(args.workers)
    if not api.bootstrap():
        log.error("could not establish a Roku session (403 or no data); often a regional/CDN block")
        return 1

    channels = fetch_channels(api)
    if not channels:
        log.error("no channels returned")
        return 1
    log.info("%d channels", len(channels))

    channels = resolve_streams(api, channels, args.workers, args.stream_rate, args.include_dash)
    if not channels:
        log.error("no channels resolved to a stream")
        return 1

    write_m3u(channels, m3u_path, None if args.no_epg else args.epg)

    if not args.no_epg:
        prev = load_previous_epg(epg_path)
        guide = fetch_epg(api, channels, prev, args.workers, args.min_guide_hours,
                          args.max_epg_requests, args.epg_budget)
        write_xmltv(channels, guide, epg_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
