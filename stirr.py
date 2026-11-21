#!/usr/bin/env python3
"""
Standalone STIRR playlist + EPG generator (ported from FastChannels' StirrScraper).

Outputs:
  <out-dir>/stirr.m3u   direct HLS master URLs, resolved at generation time
  <out-dir>/stirr.xml   XMLTV guide

Only dependency: requests
    pip install requests
    python stirr.py --out-dir playlists

No cache is needed. The original scraper's on-disk cache only fed channel
descriptions, which neither the m3u nor the XMLTV output uses, so that
code is dropped.

Stream URLs are resolved per channel at generation time (POST /playable), so
run it on a schedule (e.g. every 6 hours) rather than once.
"""
from __future__ import annotations

import argparse
import logging
import re
import secrets
import sys
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError, as_completed
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from html import unescape
from pathlib import Path
from typing import Any, Optional
from urllib.parse import urlparse

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

log = logging.getLogger("stirr")

CHANNELS_URL = (
    "https://stirr.com/api/videos/list/"
    "?categories=all_categories&content_type=4&no_limit=true"
)
PLAYABLE_URL = "https://stirr.com/api/v2/videos/{videoid}/playable"
EPG_FALLBACK_URL = "https://stirr.com/api/epg"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/145.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json, text/plain, */*",
    "Origin": "https://stirr.com",
    "Referer": "https://stirr.com/",
}

CATEGORY_MAP = {
    "News Flash Live": "News",
    "Sports Live": "Sports",
    "Entertainment Live": "Entertainment",
    "Music Live": "Music",
    "Food and Fitness Live": "Lifestyle",
    "Comedy Live": "Comedy",
    "Shopping Live": "Shopping",
    "Default Category": "General",
    "Crime Files": "Crime",
    "Documentary Series": "Documentary",
    "STIRR Kids": "Kids",
    "Finance and Business": "Business",
    "Paranormal Series": "Entertainment",
    "Science to Space, Amplified": "Science",
    "Pack your Bag Travel": "Travel",
}

_FILE_EXTS = frozenset(("xml", "json", "m3u8", "m3u", "csv", "txt", "zip"))


# ── Data ─────────────────────────────────────────────────────

@dataclass
class Channel:
    id: str
    name: str
    logo: Optional[str] = None
    category: Optional[str] = None
    number: Optional[int] = None
    epg_url: str = ""
    epg_channel_id: str = ""
    stream_url: Optional[str] = None


@dataclass
class Program:
    channel_id: str
    title: str
    start: datetime
    end: datetime
    description: Optional[str] = None
    poster: Optional[str] = None
    category: Optional[str] = None
    rating: Optional[str] = None
    episode_title: Optional[str] = None
    season: Optional[int] = None
    episode: Optional[int] = None


# ── HTTP ─────────────────────────────────────────────────────

def make_session(retries: int) -> requests.Session:
    s = requests.Session()
    s.headers.update(HEADERS)
    retry = Retry(
        total=retries, connect=retries, read=retries, status=retries,
        backoff_factor=1.0, status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=None, raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry, pool_maxsize=32)
    s.mount("https://", adapter)
    s.mount("http://", adapter)
    return s


def make_epg_session() -> requests.Session:
    """No retries: dead provider EPG hosts should fail fast."""
    s = requests.Session()
    s.headers.update(HEADERS)
    adapter = HTTPAdapter(max_retries=0, pool_maxsize=32)
    s.mount("https://", adapter)
    s.mount("http://", adapter)
    return s


# ── Small helpers ────────────────────────────────────────────

def coerce_int(val: Any) -> Optional[int]:
    try:
        return int(val)
    except (TypeError, ValueError):
        return None


def sanitize_url(url: str) -> str:
    """Strip whitespace, decode entities, add https:// if missing; '' if not a real http URL."""
    url = unescape((url or "").strip().rstrip("\u00a0").strip())
    if not url:
        return ""
    parsed = urlparse(url)
    if not parsed.scheme:
        url = "https://" + url
        parsed = urlparse(url)
    if parsed.scheme not in ("http", "https"):
        return ""
    netloc = parsed.netloc.lower().split(":")[0]
    if not netloc or "." not in netloc:
        return ""
    if netloc.rsplit(".", 1)[-1] in _FILE_EXTS:
        return ""
    return url


def normalize_local_news_name(name: str) -> str:
    """'FOX 9 - WTOV - (Steubenville, OH)' -> 'FOX 9 Steubenville OH'"""
    if " - (" not in name:
        return name
    m = re.search(r"\(([^)]+)\)\s*(?:#(\d+))?\s*$", name)
    if not m:
        return name
    location_raw, number_suffix = m.group(1), m.group(2)
    if "," not in location_raw and "&" not in location_raw \
            and not re.search(r"\b[A-Z]{2}$", location_raw):
        return name
    location = re.sub(r"\s+", " ", location_raw.replace(",", "")).strip()
    prefix = name[:m.start()].rstrip(" -").strip()
    parts = re.split(r"\s+-\s+", prefix)
    if len(parts) > 1 and re.fullmatch(r"[A-Z]{2,5}", parts[-1]):
        parts = parts[:-1]
    prefix = " - ".join(parts).strip()
    result = f"{prefix} {location}"
    if number_suffix:
        result += f" {number_suffix}"
    return result.strip()


def normalize_name(name: str) -> str:
    name = name.strip().strip("\t\u00a0")
    name = name.replace("*", "")
    name = re.sub(r"  +", " ", name)
    name = re.sub(r"\s*-\s*\(", " - (", name)
    name = re.sub(r"(\w)-\s{2,}", r"\1 - ", name)
    return normalize_local_news_name(name).strip()


def parse_dt(val: Any) -> Optional[datetime]:
    if not val:
        return None
    if isinstance(val, (int, float)):
        if val > 1e11:  # milliseconds
            val /= 1000
        try:
            return datetime.fromtimestamp(val, tz=timezone.utc)
        except (ValueError, OverflowError, OSError):
            return None
    if isinstance(val, str):
        try:
            dt = datetime.fromisoformat(val.replace("Z", "+00:00"))
            return dt.replace(tzinfo=timezone.utc) if not dt.tzinfo else dt.astimezone(timezone.utc)
        except ValueError:
            pass
    return None


def parse_xmltv_dt(val: Optional[str]) -> Optional[datetime]:
    if not val:
        return None
    s = val.strip()
    # Some providers put raw epoch seconds in start/stop.
    if s.isdigit() and 9 <= len(s) <= 10:
        try:
            dt = datetime.fromtimestamp(int(s), tz=timezone.utc)
        except (ValueError, OverflowError, OSError):
            return None
        if abs((dt - datetime.now(timezone.utc)).days) > 730:
            return None
        return dt
    if len(s) >= 14:
        try:
            return datetime.strptime(s[:14], "%Y%m%d%H%M%S").replace(tzinfo=timezone.utc)
        except ValueError:
            pass
    if len(s) >= 12:
        try:
            return datetime.strptime(s[:12], "%Y%m%d%H%M").replace(tzinfo=timezone.utc)
        except ValueError:
            return None
    return None


# ── Channels ─────────────────────────────────────────────────

def extract_channel_rows(payload: Any) -> list[dict]:
    rows: list[dict] = []

    def walk(obj: Any) -> None:
        if isinstance(obj, dict):
            if "videoid" in obj and "title" in obj:
                rows.append(obj)
                return
            for v in obj.values():
                walk(v)
        elif isinstance(obj, list):
            for item in obj:
                walk(item)

    walk(payload)
    seen: set[str] = set()
    out = []
    for row in rows:
        vid = str(row.get("videoid", ""))
        if vid and vid not in seen:
            seen.add(vid)
            out.append(row)
    return out


def pick_id(row: dict) -> Optional[str]:
    for key in ("videoid", "id", "channel_id"):
        val = row.get(key)
        if val:
            return str(val).strip()
    return None


def pick_logo(row: dict) -> Optional[str]:
    if str(row.get("logo", "")).startswith("http"):
        return row["logo"]
    for b in ("thumbs", "square_thumbs"):
        bucket = row.get(b)
        if isinstance(bucket, dict):
            for v in bucket.values():
                if str(v).startswith("http"):
                    return v
    return None


def pick_category(row: dict) -> Optional[str]:
    cats = row.get("categories")
    if isinstance(cats, list) and cats:
        first = cats[0]
        raw = (first.get("category_name") or first.get("name")) if isinstance(first, dict) else str(first)
    else:
        raw = row.get("category") or row.get("genre")
    return CATEGORY_MAP.get(raw, raw) if raw else None


def fetch_channels(session: requests.Session, timeout: int) -> list[Channel]:
    r = session.get(CHANNELS_URL, timeout=timeout)
    r.raise_for_status()
    rows = extract_channel_rows(r.json())
    channels: list[Channel] = []
    for row in rows:
        cid = pick_id(row)
        if not cid:
            continue
        name = normalize_name(
            row.get("title") or row.get("name") or row.get("channel_name") or f"STIRR {cid}"
        )
        channels.append(Channel(
            id=cid,
            name=name,
            logo=pick_logo(row),
            category=pick_category(row),
            number=coerce_int(row.get("channel_number")),
            epg_url=sanitize_url(row.get("epg_url") or ""),
            epg_channel_id=row.get("epg_channel_id") or "",
        ))
    log.info("%d channels fetched", len(channels))
    return channels


# ── Stream resolution ────────────────────────────────────────

def extract_media_url(payload: Any) -> Optional[str]:
    # data[0].media[0]
    if isinstance(payload, dict):
        data = payload.get("data")
        if isinstance(data, list) and data and isinstance(data[0], dict):
            media = data[0].get("media")
            if isinstance(media, list) and media:
                return media[0]
            if isinstance(media, str):
                return media
    return None


def resolve_channel(session: requests.Session, ch: Channel, timeout: int) -> tuple[Optional[str], str]:
    """Returns (url, status) where status is 'ok', 'dead' (404/410) or 'fail'."""
    try:
        r = session.post(PLAYABLE_URL.format(videoid=ch.id), timeout=timeout)
    except requests.RequestException as exc:
        log.debug("resolve network error for %s: %s", ch.id, exc)
        return None, "fail"
    if r.status_code in (404, 410):
        return None, "dead"
    if r.status_code != 200:
        log.debug("resolve %s -> HTTP %s", ch.id, r.status_code)
        return None, "fail"
    try:
        media = extract_media_url(r.json())
    except ValueError:
        return None, "fail"
    if not media or not media.startswith("http"):
        return None, "fail"
    # The playable URL carries a [vx_nonce] template; aniview rejects it unfilled.
    return media.replace("[vx_nonce]", secrets.token_hex(16)), "ok"


def resolve_all(channels: list[Channel], session: requests.Session, workers: int, timeout: int) -> list[Channel]:
    ok: list[Channel] = []
    dead = failed = 0
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(resolve_channel, session, ch, timeout): ch for ch in channels}
        for fut in as_completed(futures):
            ch = futures[fut]
            try:
                url, status = fut.result()
            except Exception as exc:  # noqa: BLE001
                log.debug("resolve worker error for %s: %s", ch.id, exc)
                url, status = None, "fail"
            if url:
                ch.stream_url = url
                ok.append(ch)
            elif status == "dead":
                dead += 1
            else:
                failed += 1
    log.info("resolved %d/%d streams (%d dead, %d failed)", len(ok), len(channels), dead, failed)
    return ok


# ── EPG parsing ──────────────────────────────────────────────

def programs_from_wurl(cid: str, payload: dict) -> list[Program]:
    movies = {str(m["id"]): m for m in (payload.get("movies") or []) if "id" in m}
    shorts = {str(s["id"]): s for s in (payload.get("shortFormVideos") or []) if "id" in s}
    specials = {str(t["id"]): t for t in (payload.get("tvSpecials") or []) if "id" in t}
    episodes: dict[str, dict] = {}
    for show in (payload.get("series") or []):
        for season in (show.get("seasons") or []):
            for ep in (season.get("episodes") or []):
                if "id" in ep:
                    episodes[str(ep["id"])] = ep

    def _title(item: dict) -> Optional[str]:
        t = item.get("title")
        if isinstance(t, dict):
            return t.get("value") or t.get("text")
        return t or item.get("name") or None

    out = []
    for sched in (payload.get("schedules") or []):
        sid = str(sched.get("id", ""))
        start = parse_dt(sched.get("startDateTime"))
        dur = sched.get("durSecs")
        if not sid or not start or not dur:
            continue
        item = movies.get(sid) or episodes.get(sid) or shorts.get(sid) or specials.get(sid)
        if item is None:
            continue
        title = _title(item)
        if not title:
            continue
        desc_raw = item.get("description")
        desc = (desc_raw.get("value") if isinstance(desc_raw, dict) else desc_raw) or None
        out.append(Program(
            channel_id=cid, title=title, start=start,
            end=start + timedelta(seconds=int(dur)),
            description=desc,
            poster=(item.get("thumbnails") or [{}])[0].get("url"),
            category=(item.get("genres") or [{}])[0].get("description"),
        ))
    return out


def programs_from_ctvcraft(cid: str, root: ET.Element) -> list[Program]:
    out = []
    for item in root.findall(".//item"):
        title = item.findtext("title")
        start_str = item.findtext("startTime")
        dur_str = item.findtext("duration")
        if not title or not start_str or not dur_str:
            continue
        start = parse_dt(start_str)
        try:
            dur = int(dur_str)
        except (ValueError, TypeError):
            continue
        if not start or dur <= 0:
            continue
        poster, best = None, -1
        for thumb in item.findall(".//thumbnail"):
            try:
                w = int(thumb.attrib.get("width", 0) or 0)
            except (ValueError, TypeError):
                w = 0
            if w > best:
                best, poster = w, thumb.attrib.get("url")
        out.append(Program(
            channel_id=cid, title=title, start=start,
            end=start + timedelta(seconds=dur),
            description=item.findtext("description"),
            poster=poster, category=item.findtext("genre"),
        ))
    return out


def programs_from_xmltv(cid: str, root: ET.Element, epg_id: str) -> list[Program]:
    programmes = root.findall(".//programme")
    if not programmes:
        return []
    targets = {cid.lower(), epg_id.lower()} if epg_id else {cid.lower()}
    matched = [p for p in programmes if p.attrib.get("channel", "").lower() in targets]
    if not matched and len(root.findall(".//channel")) <= 1:
        matched = programmes  # single-channel feed
    out = []
    for p in matched:
        start = parse_xmltv_dt(p.attrib.get("start"))
        stop = parse_xmltv_dt(p.attrib.get("stop"))
        title = p.find("title")
        if not start or not stop or title is None:
            continue
        desc, icon, cat = p.find("desc"), p.find("icon"), p.find("category")
        out.append(Program(
            channel_id=cid, title=title.text or "Unknown", start=start, end=stop,
            description=desc.text if desc is not None else None,
            poster=icon.attrib.get("src") if icon is not None else None,
            category=cat.text if cat is not None else None,
        ))
    return out


def generic_json_entries(payload: Any) -> list[dict]:
    rows: list[dict] = []

    def walk(obj: Any) -> None:
        if isinstance(obj, dict):
            if any(k in obj for k in ("start", "start_time", "starts_at")):
                rows.append(obj)
                return
            for v in obj.values():
                walk(v)
        elif isinstance(obj, list):
            for item in obj:
                walk(item)

    walk(payload)
    return rows


def entry_time(entry: dict, primary: str, numeric: str, fallback: str) -> Optional[datetime]:
    dt = parse_dt(entry.get(primary))
    if dt is not None and 2000 <= dt.year <= 2100:
        return dt
    # STIRR's /api/epg sometimes ships year-8387 strings next to a correct
    # compact YYYYMMDDHHMM(SS) integer; recover from that.
    raw = entry.get(numeric)
    if raw is not None:
        s = str(int(raw)) if isinstance(raw, (int, float)) else str(raw).strip()
        if s.isdigit() and len(s) in (12, 14):
            rec = parse_xmltv_dt(s)
            if rec is not None:
                return rec
        rec = parse_dt(raw)
        if rec is not None and 2000 <= rec.year <= 2100:
            return rec
    return dt if dt is not None else parse_dt(entry.get(fallback))


def program_from_entry(cid: str, entry: dict) -> Optional[Program]:
    title = entry.get("title") or entry.get("program_title") or entry.get("name")
    start = entry_time(entry, "start", "start_time", "airing_start_time")
    end = entry_time(entry, "end", "end_time", "airing_end_time")
    if not title or not start or not end:
        return None
    return Program(
        channel_id=cid, title=title, start=start, end=end,
        description=entry.get("description") or entry.get("summary"),
        poster=entry.get("poster") or entry.get("image"),
        category=entry.get("category") or entry.get("genre"),
        rating=entry.get("rating") if isinstance(entry.get("rating"), str) else None,
        episode_title=entry.get("episode_title") or entry.get("subtitle"),
        season=coerce_int(entry.get("season")),
        episode=coerce_int(entry.get("episode")),
    )


def fetch_epg_one(session: requests.Session, ch: Channel) -> list[Program]:
    result: list[Program] = []

    # 1. Provider EPG URL
    if ch.epg_url:
        try:
            r = session.get(ch.epg_url, timeout=8)
            r.raise_for_status()
            text = r.text.strip()
            if text.startswith("<"):
                try:
                    root = ET.fromstring(text)
                except ET.ParseError:
                    root = None
                if root is not None:
                    item = root.find(".//item")
                    if item is not None and item.find("startTime") is not None:
                        result.extend(programs_from_ctvcraft(ch.id, root))
                    else:
                        result.extend(programs_from_xmltv(ch.id, root, ch.epg_channel_id))
            else:
                payload = r.json()
                if isinstance(payload, dict) and "schedules" in payload:
                    result.extend(programs_from_wurl(ch.id, payload))
                else:
                    for entry in generic_json_entries(payload):
                        prog = program_from_entry(ch.id, entry)
                        if prog:
                            result.append(prog)
        except Exception as exc:  # noqa: BLE001
            log.debug("provider EPG failed for %s: %s", ch.id, exc)

    # 2. STIRR's own endpoint (400s are expected for unsupported ids)
    if not result:
        try:
            r = session.get(f"{EPG_FALLBACK_URL}?channel_id={ch.id}&tz=UTC", timeout=10)
            if r.status_code == 200:
                for entry in generic_json_entries(r.json()):
                    prog = program_from_entry(ch.id, entry)
                    if prog:
                        result.append(prog)
        except Exception as exc:  # noqa: BLE001
            log.debug("fallback EPG failed for %s: %s", ch.id, exc)

    return result


def fetch_epg(channels: list[Channel], workers: int, days: float) -> list[Program]:
    session = make_epg_session()
    programs: list[Program] = []
    pool = ThreadPoolExecutor(max_workers=workers)
    futures = {pool.submit(fetch_epg_one, session, ch): ch for ch in channels}
    try:
        for fut in as_completed(futures, timeout=300):
            try:
                programs.extend(fut.result())
            except Exception as exc:  # noqa: BLE001
                log.debug("EPG worker error for %s: %s", futures[fut].id, exc)
    except FuturesTimeoutError:
        log.warning("EPG fetch timed out after 300s; %d channel(s) incomplete",
                    sum(1 for f in futures if not f.done()))
    finally:
        pool.shutdown(wait=False, cancel_futures=True)

    # Keep only [now, now + days]; several upstream schedules are months stale.
    now = datetime.now(timezone.utc)
    horizon = now + timedelta(days=days)
    kept = []
    for p in programs:
        if p.start.tzinfo is None:
            p.start = p.start.replace(tzinfo=timezone.utc)
        if p.end.tzinfo is None:
            p.end = p.end.replace(tzinfo=timezone.utc)
        if p.end > now and p.start < horizon and p.end > p.start:
            kept.append(p)

    # Sort, dedupe on (channel, start), and trim overlaps.
    kept.sort(key=lambda p: (p.channel_id, p.start))
    out: list[Program] = []
    for p in kept:
        if out and out[-1].channel_id == p.channel_id:
            prev = out[-1]
            if prev.start == p.start:
                continue
            if prev.end > p.start:
                prev.end = p.start
        out.append(p)
    out = [p for p in out if p.end > p.start]
    log.info("%d programs kept (next %sd)", len(out), days)
    return out


# ── Writers ──────────────────────────────────────────────────

def _attr(s: str) -> str:
    return (s or "").replace('"', "'").replace("\n", " ").strip()


def write_m3u(channels: list[Channel], path: Path) -> None:
    lines = ["#EXTM3U"]
    for ch in channels:
        attrs = [f'tvg-id="{_attr(ch.id)}"', f'tvg-name="{_attr(ch.name)}"']
        if ch.logo:
            attrs.append(f'tvg-logo="{_attr(ch.logo)}"')
        if ch.number is not None:
            attrs.append(f'tvg-chno="{ch.number}"')
        attrs.append(f'group-title="{_attr(ch.category or "General")}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch.name}')
        lines.append(ch.stream_url or "")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _xt(dt: datetime) -> str:
    return dt.astimezone(timezone.utc).strftime("%Y%m%d%H%M%S +0000")


def write_xmltv(channels: list[Channel], programs: list[Program], path: Path) -> None:
    tv = ET.Element("tv", {"generator-info-name": "stirr.py"})
    for ch in channels:
        c = ET.SubElement(tv, "channel", {"id": ch.id})
        ET.SubElement(c, "display-name").text = ch.name
        if ch.logo:
            ET.SubElement(c, "icon", {"src": ch.logo})
    for p in programs:
        e = ET.SubElement(tv, "programme", {
            "start": _xt(p.start), "stop": _xt(p.end), "channel": p.channel_id,
        })
        ET.SubElement(e, "title").text = p.title
        if p.episode_title:
            ET.SubElement(e, "sub-title").text = p.episode_title
        if p.description:
            ET.SubElement(e, "desc").text = p.description
        if p.category:
            ET.SubElement(e, "category").text = p.category
        if p.poster:
            ET.SubElement(e, "icon", {"src": p.poster})
        if p.season and p.episode and p.season >= 1 and p.episode >= 1:
            ET.SubElement(e, "episode-num", {"system": "xmltv_ns"}).text = f"{p.season - 1}.{p.episode - 1}."
            ET.SubElement(e, "episode-num", {"system": "onscreen"}).text = f"S{p.season:02d}E{p.episode:02d}"
        if p.rating:
            ET.SubElement(ET.SubElement(e, "rating"), "value").text = p.rating
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)


# ── Main ─────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Standalone STIRR m3u + XMLTV generator")
    ap.add_argument("--out-dir", default="playlists", help="output directory (default: playlists)")
    ap.add_argument("--m3u-name", default="stirr.m3u")
    ap.add_argument("--xml-name", default="stirr.xml")
    ap.add_argument("--epg-days", type=float, default=2, help="days of guide to keep (default: 2)")
    ap.add_argument("--no-epg", action="store_true", help="skip the XMLTV guide")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=15, help="HTTP timeout in seconds")
    ap.add_argument("--retries", type=int, default=2)
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s [%(name)s] %(message)s",
    )

    session = make_session(args.retries)
    try:
        channels = fetch_channels(session, args.timeout)
    except (requests.RequestException, ValueError) as exc:
        log.error("channel list failed: %s", exc)
        return 1
    if not channels:
        log.error("no channels returned")
        return 1

    channels = resolve_all(channels, session, args.workers, args.timeout)
    if not channels:
        log.error("no streams resolved")
        return 1
    channels.sort(key=lambda c: (c.number is None, c.number or 0, c.name.lower()))

    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    write_m3u(channels, out / args.m3u_name)
    log.info("wrote %s (%d channels)", out / args.m3u_name, len(channels))

    if not args.no_epg:
        programs = fetch_epg(channels, args.workers, args.epg_days)
        write_xmltv(channels, programs, out / args.xml_name)
        log.info("wrote %s", out / args.xml_name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
