#!/usr/bin/env python3
"""
lgtv.py - standalone LG Channels (lgchannels.com) m3u + XMLTV generator.

Usage:
    python lgtv.py [--out-dir playlists] [--m3u lgtv.m3u] [--epg lgtv.xml] [--no-epg] [-v]
                   [--country US] [--delay 0] [--retries 3] [--backoff 2] [--timeout 60]

Outputs:
    <out-dir>/lgtv.m3u
    <out-dir>/lgtv.xml   (gzipped if --epg ends in .gz)

Needs: requests
Stream URLs have LG's macros ([DEVICE_ID], [NONCE], ...) expanded at generation
time, so run it on a schedule (e.g. every 6 hours) to keep them fresh.
"""
from __future__ import annotations

import argparse
import base64
import binascii
import gzip
import json
import logging
import re
import sys
import time
import uuid
import zlib
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import quote
from xml.etree import ElementTree as ET

import requests
from requests.utils import requote_uri

API_BASE = "https://api.lgchannels.com/api/v1.0"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)
PLAY_DEVICE_TYPE = "Personal Computer"
APP_NAME = "lgchannels_web"

log = logging.getLogger("lgtv")

_XML_BAD = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\ufffe\uffff]")


# ── HTTP ─────────────────────────────────────────────────────

def _redirect_target(resp):
    """Re-quote redirect Locations (LG sends unescaped chars)."""
    if not resp.is_redirect:
        return None
    location = resp.headers.get("location")
    if location is None:
        return None
    if isinstance(location, bytes):
        try:
            location = location.decode("utf-8")
        except UnicodeDecodeError:
            location = location.decode("latin-1")
    return requote_uri(location)


def make_session(country: str) -> requests.Session:
    s = requests.Session()
    s.get_redirect_target = _redirect_target
    s.headers.update({
        "User-Agent": USER_AGENT,
        "Accept": "application/json, text/plain, */*",
        "Origin": "https://lgchannels.com",
        "Referer": "https://lgchannels.com/",
        "x-device-country": country.upper(),
        "x-device-language": "en",
        "x-device-type": "WEB",
    })
    return s


def decode_payload(text: str) -> dict[str, Any] | None:
    """Fallback: base64(zlib(json)) body."""
    if not text:
        return None
    try:
        raw = zlib.decompress(base64.b64decode(text.strip(), validate=True))
        data = json.loads(raw.decode("utf-8"))
        return data if isinstance(data, dict) else None
    except (binascii.Error, UnicodeDecodeError, ValueError, zlib.error):
        return None


def fetch_schedulelist(session: requests.Session, retries: int = 3, backoff: float = 2.0,
                       timeout: float = 60.0) -> dict[str, Any] | None:
    for attempt in range(1, retries + 1):
        try:
            r = session.get(f"{API_BASE}/schedulelist", timeout=timeout)
            r.raise_for_status()
        except requests.RequestException as exc:
            log.warning("schedulelist attempt %d/%d failed: %s", attempt, retries, exc)
            if attempt < retries:
                time.sleep(backoff * attempt)
            continue
        try:
            payload = r.json()
        except ValueError:
            payload = decode_payload(r.text)
        if isinstance(payload, dict):
            return payload
        log.error("schedulelist payload unusable (status=%s bytes=%s preview=%r)",
                  r.status_code, len(r.content or b""), (r.text or "")[:80])
        return None
    return None


# ── Helpers ──────────────────────────────────────────────────

def clean(value: Any) -> str | None:
    if value is None:
        return None
    text = str(value).strip()
    return text or None


def parse_int(value: Any) -> int | None:
    try:
        return int(str(value).strip())
    except (TypeError, ValueError):
        return None


def parse_dt(value: Any) -> datetime | None:
    if not value or not isinstance(value, str):
        return None
    value = value.strip()
    try:
        if value.endswith("Z"):
            return datetime.fromisoformat(value[:-1] + "+00:00").astimezone(timezone.utc)
        dt = datetime.fromisoformat(value)
        return dt.astimezone(timezone.utc) if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def xml_text(s: str | None) -> str:
    return _XML_BAD.sub("", s or "")


def expand_macros(url: str, country: str) -> str:
    repl = {
        "[DEVICE_ID]": str(uuid.uuid4()),
        "[IFA]": "",
        "[IFA_TYPE]": "",
        "[LMT]": "0",
        "[DNS]": "0",
        "[UA]": quote(USER_AGENT, safe=""),
        "[IP]": "0.0.0.0",
        "[GDPR]": "",
        "[GDPR_CONSENT]": "",
        "[COUNTRY]": country.upper(),
        "[US_PRIVACY]": "",
        "[APP_STOREURL]": "",
        "[APP_BUNDLE]": "",
        "[APP_NAME]": APP_NAME,
        "[APP_VERSION]": "",
        "[DEVICE_TYPE]": quote(PLAY_DEVICE_TYPE, safe=""),
        "[DEVICE_MAKE]": "",
        "[DEVICE_MODEL]": "",
        "[TARGETAD_ALLOWED]": "",
        "[FCK]": "",
        "[PCS]": "",
        "[COPPA]": "0",
        "[VIEWSIZE]": "1920x1080",
        "[NONCE]": str(int(time.time())),
        "[HOTELTYPE]": "",
        "[HOTEL_TYPE]": "",
    }
    for k, v in repl.items():
        url = url.replace(k, v)
    return url


def strip_locale(prog_id: str | None) -> str | None:
    """'MV014035030000-US' -> 'MV014035030000'; leaves 'US-BBC-...' prefixes alone."""
    if not prog_id:
        return None
    if "-" in prog_id:
        prefix, _, suffix = prog_id.rpartition("-")
        if len(suffix) == 2 and suffix.isalpha() and suffix.isupper():
            return prefix
    return prog_id


def dedupe_dominant_ids(programs: list[dict]) -> None:
    """If one program id covers most of a channel's airings, it's a placeholder: drop it."""
    by_ch: dict[str, list[dict]] = {}
    for p in programs:
        by_ch.setdefault(p["channel"], []).append(p)
    for items in by_ch.values():
        ids = Counter(p["pid"] for p in items if p["pid"])
        if not ids:
            continue
        top, n = ids.most_common(1)[0]
        if n > 2 and n / len(items) > 0.5:
            for p in items:
                if p["pid"] == top:
                    p["pid"] = None


# ── Build ────────────────────────────────────────────────────

def build(payload: dict[str, Any], country: str) -> tuple[list[dict], list[dict]]:
    channels: list[dict] = []
    programs: list[dict] = []
    seen: set[str] = set()

    for cat in payload.get("categories", []):
        cat_name = clean(cat.get("categoryName"))
        for ch in cat.get("channels", []):
            cid = clean(ch.get("channelId"))
            name = clean(ch.get("channelName"))
            url = clean(ch.get("mediaStaticUrl"))
            if not cid or not name or not url or cid in seen:
                continue
            seen.add(cid)

            ch_genre = clean(ch.get("channelGenreName"))
            group = cat_name or ch_genre or clean(ch.get("providerId")) or ""
            channels.append({
                "id": cid,
                "name": name,
                "url": expand_macros(url, country),
                "logo": clean(ch.get("channelLogoUrl")) or "",
                "group": group,
                "number": parse_int(ch.get("channelNumber")),
            })

            for prog in ch.get("programs", []):
                title = clean(prog.get("programTitle"))
                start = parse_dt(prog.get("startDateTime"))
                end = parse_dt(prog.get("endDateTime"))
                if not title or not start or not end or end <= start:
                    continue

                primary = clean(prog.get("engGenreName"))
                secondary = clean(prog.get("engSecondGenreName"))
                base = primary or ch_genre or cat_name
                cats = [c for c in (base, secondary) if c]
                if len(cats) == 2 and cats[0] == cats[1]:
                    cats = cats[:1]

                programs.append({
                    "channel": cid,
                    "title": title,
                    "start": start,
                    "end": end,
                    "desc": clean(prog.get("description")),
                    "icon": (clean(prog.get("thumbnailUrl"))
                             or clean(prog.get("imageUrl"))
                             or clean(prog.get("previewImgUrl"))),
                    "cats": cats,
                    "rating": clean(prog.get("ratingCode")),
                    "pid": strip_locale(clean(prog.get("programId"))),
                })

    dedupe_dominant_ids(programs)
    return channels, programs


def write_m3u(path: Path, channels: list[dict]) -> None:
    def attr(s: str) -> str:
        return s.replace('"', "'")

    lines = ["#EXTM3U"]
    for ch in sorted(channels, key=lambda c: (c["number"] is None, c["number"] or 0, c["name"].lower())):
        num = f' tvg-chno="{ch["number"]}"' if ch["number"] is not None else ""
        lines.append(
            f'#EXTINF:-1 tvg-id="{attr(ch["id"])}" tvg-name="{attr(ch["name"])}"'
            f'{num} tvg-logo="{attr(ch["logo"])}" group-title="{attr(ch["group"])}",{ch["name"]}'
        )
        lines.append(ch["url"])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_xmltv(path: Path, channels: list[dict], programs: list[dict]) -> None:
    fmt = "%Y%m%d%H%M%S +0000"
    tv = ET.Element("tv", {"generator-info-name": "lgtv.py"})

    for ch in channels:
        c = ET.SubElement(tv, "channel", id=xml_text(ch["id"]))
        ET.SubElement(c, "display-name").text = xml_text(ch["name"])
        if ch["logo"]:
            ET.SubElement(c, "icon", src=xml_text(ch["logo"]))

    valid = {c["id"] for c in channels}
    for p in sorted(programs, key=lambda x: (x["channel"], x["start"])):
        if p["channel"] not in valid:
            continue
        e = ET.SubElement(tv, "programme", {
            "start": p["start"].strftime(fmt),
            "stop": p["end"].strftime(fmt),
            "channel": xml_text(p["channel"]),
        })
        ET.SubElement(e, "title", lang="en").text = xml_text(p["title"])
        if p["desc"]:
            ET.SubElement(e, "desc", lang="en").text = xml_text(p["desc"])
        for cat in p["cats"]:
            ET.SubElement(e, "category", lang="en").text = xml_text(cat)
        if p["icon"]:
            ET.SubElement(e, "icon", src=xml_text(p["icon"]))
        if p["pid"]:
            ET.SubElement(e, "episode-num", system="dd_progid").text = xml_text(p["pid"])
        if p["rating"]:
            r = ET.SubElement(e, "rating")
            ET.SubElement(r, "value").text = xml_text(p["rating"])

    ET.indent(tv)
    data = ET.tostring(tv, encoding="utf-8", xml_declaration=True)
    if path.suffix == ".gz":
        with gzip.open(path, "wb") as f:
            f.write(data)
    else:
        path.write_bytes(data)


def main() -> int:
    ap = argparse.ArgumentParser(description="LG Channels m3u + XMLTV generator")
    ap.add_argument("--out-dir", default="playlists", help="output directory (default: playlists)")
    ap.add_argument("--m3u", default="lgtv.m3u", help="m3u filename (default: lgtv.m3u)")
    ap.add_argument("--epg", default="lgtv.xml", help="XMLTV filename; .gz suffix gzips (default: lgtv.xml)")
    ap.add_argument("--no-epg", action="store_true", help="skip EPG output")
    ap.add_argument("-v", "--verbose", action="store_true", help="debug logging")
    ap.add_argument("--country", default="US", help="country code (default: US)")
    ap.add_argument("--delay", type=float, default=0.0, help="sleep N seconds before the request (default: 0)")
    ap.add_argument("--retries", type=int, default=3, help="request attempts (default: 3)")
    ap.add_argument("--backoff", type=float, default=2.0, help="retry wait = backoff * attempt seconds (default: 2)")
    ap.add_argument("--timeout", type=float, default=60.0, help="request timeout seconds (default: 60)")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO, format="%(asctime)s %(levelname)s %(message)s")

    session = make_session(args.country)
    if args.delay:
        time.sleep(args.delay)
    payload = fetch_schedulelist(session, args.retries, args.backoff, args.timeout)
    if not payload:
        log.error("no schedulelist data; aborting")
        return 1

    channels, programs = build(payload, args.country)
    if not channels:
        log.error("no channels parsed; aborting")
        return 1
    log.info("%d channels, %d programs", len(channels), len(programs))

    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    write_m3u(out / args.m3u, channels)
    log.info("wrote %s", out / args.m3u)
    if not args.no_epg:
        write_xmltv(out / args.epg, channels, programs)
        log.info("wrote %s", out / args.epg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
