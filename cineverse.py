#!/usr/bin/env python3
"""
Standalone Cineverse + RetroCrush + JoySauce M3U Playlist + EPG (XMLTV) Generator

Scrapes the Matchpoint (JunctionTV) metax API used by three English-oriented
Cineverse sites:
  - streaming.cineverse.com  (Screambox, Bob Ross, Dove, MidnightPulp, ...)
  - retrocrush.tv            (English-subtitled/dubbed anime)
  - joysauce.tv              (English Asian pop culture)

All three run on the same metax backend. The guide is fetched the way the
sites' own pages do it: GET <site>/api/get with the metax URL AES-encrypted
into an `mp-tag` header (passphrase from the sites' JS bundle) and a `cauth`
header (MD5 of the app tag). The response is metax JSON, AES-256-CTR encrypted
with another bundle key. The livefeed lists every channel with its HLS URL
and its schedule from a day back to a day ahead.

Usage:
    python cineverse_m3u_epg.py [--out-dir DIR] [--m3u NAME] [--epg NAME]
                                [--include-non-english] [--no-m3u] [--no-epg]
                                [-v]

If the sites change their bundle keys, decryption fails, no channels are
written, and the M3U/EPG are left at their previous contents.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import logging
import os
import re
import sys
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from datetime import UTC, datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit
from xml.dom import minidom

import requests

try:
    from Cryptodome.Cipher import AES
    from Cryptodome.Util.Padding import pad
except ImportError:  # pragma: no cover
    from Crypto.Cipher import AES  # type: ignore[no-redef]
    from Crypto.Util.Padding import pad  # type: ignore[no-redef]

logger = logging.getLogger("cineverse")


# ---------------------------------------------------------------------------
# Inline data classes + helpers (replaces `from ._common import ...`)
# ---------------------------------------------------------------------------

@dataclass
class NetChannel:
    id: str
    name: str
    stream_url: str
    logo: str | None = None
    category: str | None = None
    language: str | None = None


@dataclass
class ProgramData:
    source_channel_id: str
    title: str
    start_time: datetime
    end_time: datetime
    description: str | None = None
    poster_url: str | None = None
    category: str | None = None
    rating: str | None = None
    episode_title: str | None = None
    episode: int | None = None
    program_type: str | None = None


def from_epoch(ms: Any) -> datetime | None:
    if ms in (None, ""):
        return None
    try:
        return datetime.fromtimestamp(int(ms) / 1000, tz=UTC)
    except (ValueError, OSError, OverflowError):
        return None


def program(channel_id, title, start, end, **extra) -> ProgramData | None:
    if not title or not start or not end or end <= start:
        return None
    return ProgramData(
        source_channel_id=channel_id,
        title=title.strip(),
        start_time=start,
        end_time=end,
        description=extra.get("description"),
        poster_url=extra.get("poster_url"),
        category=extra.get("category"),
        rating=extra.get("rating"),
        episode_title=extra.get("episode_title"),
        episode=extra.get("episode"),
        program_type=extra.get("program_type"),
    )


class Session:
    """Thin requests wrapper with the JSON-or-None contract the scraper expects."""

    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update(
            {"User-Agent": "Mozilla/5.0 (compatible; cineverse-m3u-epg/1.0)"}
        )
        self._memo: dict[str, Any] = {}

    def get(self, url: str, **kwargs):
        kwargs.setdefault("timeout", 20)
        try:
            r = self.s.get(url, **kwargs)
            r.raise_for_status()
            return r
        except requests.RequestException as exc:
            logger.warning("[cineverse] GET %s failed: %s", url, exc)
            return None

    def memo(self, key: str, factory):
        if key not in self._memo:
            self._memo[key] = factory()
        return self._memo[key]


# ---------------------------------------------------------------------------
# Crypto + URL helpers (unchanged)
# ---------------------------------------------------------------------------

_URL_PASSPHRASE = b'd0e5a4cf1b791825734aadfe874b3ccf'
_RESPONSE_KEY = base64.b64encode(hashlib.sha256(b'e85c33e2d7333ad30dce716633d3b775').digest())[:32]
_CAUTH = hashlib.md5(b'Cinedigm-India-Cineverse').hexdigest()

_LIVEFEED = 'https://metax.api.matchpoint.tv/metax/6.0/c_{brand}/itemEpg/livefeed?isSchedule=true&jloc=us'
_SITES = (
    ('retrocrush', 'https://www.retrocrush.tv'),
    ('joysauce',   'https://www.joysauce.tv'),
    ('cineverse',  'https://streaming.cineverse.com'),
)
_ELSEWHERE = {'cmc california music channel', 'tastemade us', 'tastemade home',
              'tastemade travel', 'entrepreneurtv'}
_KEEP_QUERY = {'cnvslinear.telos.indicue.com'}

_CATEGORY = {
    'midnightpulp':       'Movies',
    'real madrid':        'Sports',
    'infamous tv':        'True Crime',
    'young hollywood':    'Entertainment',
    'entrepreneurtv':     'Lifestyle',
    'so... real':         'Reality TV',
    'latino alternative tv': 'Latino',
}

# Non-English channels, filterable via --include-non-english.
_NON_ENGLISH = {'latino alternative tv', 'real madrid'}


def _encrypt_url(url: str) -> str:
    salt = os.urandom(8)
    derived, block = b'', b''
    while len(derived) < 48:
        block = hashlib.md5(block + _URL_PASSPHRASE + salt).digest()
        derived += block
    cipher = AES.new(derived[:32], AES.MODE_CBC, derived[32:48])
    return base64.b64encode(b'Salted__' + salt + cipher.encrypt(pad(url.encode(), 16))).decode()


def _decrypt_response(data: list[int]) -> str:
    raw = bytes(data)
    cipher = AES.new(_RESPONSE_KEY, AES.MODE_CTR, nonce=b'', initial_value=raw[:16])
    return cipher.decrypt(raw[16:]).decode('utf-8')


def _slug(title: str) -> str:
    return re.sub(r'[^a-z0-9]+', '-', title.lower()).strip('-')


def _stream_url(url: str) -> str:
    return url if urlsplit(url).hostname in _KEEP_QUERY else url.split('?', 1)[0]


# ---------------------------------------------------------------------------
# Scraper
# ---------------------------------------------------------------------------

class CineverseScraper:
    def __init__(self, include_non_english: bool = False):
        self.include_non_english = include_non_english
        self.session = Session()

    def _livefeed(self, brand: str, site: str) -> list[dict]:
        r = self.session.get(site + '/api/get', headers={
            'cauth': _CAUTH,
            'mp-tag': _encrypt_url(_LIVEFEED.format(brand=brand)),
            'Origin': site,
            'Referer': site + '/livetv',
        })
        if not r:
            return []
        try:
            feed = json.loads(_decrypt_response(r.json()['data']['data']))
        except (ValueError, KeyError, TypeError, UnicodeDecodeError) as exc:
            logger.warning(
                "[cineverse] %s livefeed did not decrypt (%s) — the site bundle "
                "keys may have changed", brand, exc,
            )
            return []
        return feed.get('liveFeeds') or []

    def _feeds(self) -> dict[str, dict]:
        def fetch():
            out: dict[str, dict] = {}
            for brand, site in _SITES:
                for feed in self._livefeed(brand, site):
                    title = (feed.get('title') or '').strip()
                    url = (feed.get('content') or {}).get('hls_url')
                    if not title or not url:
                        continue
                    if title.lower() in _ELSEWHERE:
                        continue
                    out.setdefault(_slug(title), feed)
            return out
        return self.session.memo('cineverse_feeds', fetch)

    def fetch_channels(self) -> list[NetChannel]:
        channels: list[NetChannel] = []
        for slug, feed in self._feeds().items():
            title = feed['title'].strip()
            if not self.include_non_english and title.lower() in _NON_ENGLISH:
                continue
            channels.append(NetChannel(
                id=slug,
                name=title,
                stream_url=_stream_url(feed['content']['hls_url']),
                logo=feed.get('thumbnail') or None,
                category=_CATEGORY.get(title.lower()),
                language='es' if title.lower() == 'latino alternative tv' else 'en',
            ))
        logger.info("[cineverse] %d channels fetched", len(channels))
        return channels

    def fetch_epg(self, channels: list[NetChannel]) -> list[ProgramData]:
        feeds = self._feeds()
        since = (time.time() - 3600) * 1000
        out: list[ProgramData] = []
        by_id = {ch.id: ch for ch in channels}

        for ch in channels:
            feed = feeds.get(ch.id) or {}
            for row in (feed.get('content') or {}).get('schedule') or []:
                if row.get('type') == 'dummy':
                    continue
                if (row.get('schedule_end_timestamp') or 0) < since:
                    continue

                series = (row.get('series_title') or '').strip()
                episode = row.get('episode_no')
                rating_obj = row.get('rating')
                rating = rating_obj.get('value') if isinstance(rating_obj, dict) else None

                p = program(
                    ch.id,
                    series or row.get('title'),
                    from_epoch(row.get('schedule_timestamp')),
                    from_epoch(row.get('schedule_end_timestamp')),
                    episode_title=row.get('title') if series else None,
                    episode=(episode if series and isinstance(episode, int) and 0 < episode < 1000 else None),
                    description=(row.get('description')
                                 or row.get('description_large')
                                 or row.get('description_small')),
                    poster_url=row.get('thumbnail_land') or row.get('thumbnail_port') or None,
                    rating=rating or None,
                    category=by_id[ch.id].category,
                    program_type='movie' if row.get('type') in ('movie', 'vod') else None,
                )
                if p:
                    out.append(p)

        # Fill placeholder blocks for channels with no schedule rows at all.
        guided_ids = {p.source_channel_id for p in out}
        now = int(time.time())
        for ch in channels:
            if ch.id in guided_ids:
                continue
            for hour in range(24):
                start = datetime.fromtimestamp(now + hour * 3600, tz=UTC)
                out.append(ProgramData(
                    source_channel_id=ch.id,
                    title=ch.name,
                    start_time=start,
                    end_time=start + (datetime.fromtimestamp(now + (hour + 1) * 3600, tz=UTC)
                                      - start),
                    description="Live schedule not published for this channel by the source.",
                    category=ch.category,
                ))

        logger.info("[cineverse] %d EPG programs fetched across %d channels",
                    len(out), len(channels))
        return out


# ---------------------------------------------------------------------------
# M3U + XMLTV writers
# ---------------------------------------------------------------------------

def _esc(value: str) -> str:
    return value.replace('"', "'").replace("\n", " ")


def write_m3u(channels: list[NetChannel], path: Path) -> None:
    lines = ["#EXTM3U"]
    for ch in channels:
        attrs = [
            f'tvg-id="{_esc(ch.id)}"',
            f'tvg-name="{_esc(ch.name)}"',
            f'group-title="{_esc(ch.category or "General")}"',
        ]
        if ch.logo:
            attrs.append(f'tvg-logo="{_esc(ch.logo)}"')
        if ch.language:
            attrs.append(f'tvg-language="{ch.language}"')
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch.name}')
        lines.append(ch.stream_url)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    logger.info("Wrote %d channels to %s", len(channels), path)


def write_xmltv(channels: list[NetChannel], programs: list[ProgramData], path: Path) -> None:
    tv = ET.Element("tv", {
        "generator-info-name": "cineverse-m3u-epg",
        "generator-info-url": "https://streaming.cineverse.com/livetv",
        "source-info-name": "cineverse-m3u-epg",
    })
    for ch in channels:
        channel_el = ET.SubElement(tv, "channel", {"id": ch.id})
        ET.SubElement(channel_el, "display-name").text = ch.name
        if ch.logo:
            ET.SubElement(channel_el, "icon", {"src": ch.logo})

    fmt = "%Y%m%d%H%M%S %z"
    for prog in sorted(programs, key=lambda p: (p.source_channel_id, p.start_time)):
        prog_el = ET.SubElement(tv, "programme", {
            "start":  prog.start_time.astimezone(timezone.utc).strftime(fmt),
            "stop":   prog.end_time.astimezone(timezone.utc).strftime(fmt),
            "channel": prog.source_channel_id,
        })
        ET.SubElement(prog_el, "title", {"lang": "en"}).text = prog.title
        if prog.episode_title:
            ET.SubElement(prog_el, "sub-title", {"lang": "en"}).text = prog.episode_title
        if prog.description:
            ET.SubElement(prog_el, "desc", {"lang": "en"}).text = prog.description
        if prog.category:
            ET.SubElement(prog_el, "category", {"lang": "en"}).text = prog.category
        if prog.rating:
            rating_el = ET.SubElement(prog_el, "rating", {"system": "VCHIP"})
            ET.SubElement(rating_el, "value").text = prog.rating
        if prog.poster_url:
            ET.SubElement(prog_el, "icon", {"src": prog.poster_url})
        if prog.episode:
            ET.SubElement(prog_el, "episode-num",
                          {"system": "xmltv_ns"}).text = f"0.{prog.episode - 1}.0/1"

    raw = ET.tostring(tv, encoding="utf-8")
    pretty = minidom.parseString(raw).toprettyxml(indent="  ", encoding="utf-8")
    path.write_bytes(pretty)
    logger.info("Wrote %d programmes to %s", len(programs), path)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Generate Cineverse/RetroCrush/JoySauce M3U playlist + XMLTV EPG.",
    )
    p.add_argument("--out-dir", default=".", help="Output directory (default: .)")
    p.add_argument("--m3u", default="cineverse.m3u", help="Playlist filename")
    p.add_argument("--epg", default="cineverse.xml", help="EPG filename")
    p.add_argument("--no-m3u", action="store_true", help="Skip playlist generation")
    p.add_argument("--no-epg", action="store_true", help="Skip EPG generation")
    p.add_argument("--include-non-english", action="store_true",
                   help="Include Latino Alternative TV and Real Madrid TV")
    p.add_argument("-v", "--verbose", action="store_true", help="Verbose logging")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )

    out_dir = Path(args.out_dir).expanduser().resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    scraper = CineverseScraper(include_non_english=args.include_non_english)

    try:
        channels = scraper.fetch_channels()
    except Exception as exc:
        logger.error("Channel fetch failed: %s", exc)
        return 1
    if not channels:
        logger.error("No channels returned — bundle keys may have changed; "
                     "leaving existing outputs untouched.")
        return 2

    if not args.no_m3u:
        write_m3u(channels, out_dir / args.m3u)

    if not args.no_epg:
        try:
            programs = scraper.fetch_epg(channels)
        except Exception as exc:
            logger.error("EPG fetch failed: %s", exc)
            return 3
        write_xmltv(channels, programs, out_dir / args.epg)

    logger.info("Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
