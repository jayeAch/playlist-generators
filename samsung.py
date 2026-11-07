#!/usr/bin/env python3
"""
Standalone Samsung TV Plus M3U + XMLTV generator, with Widevine (DRM) channels.

Data source: Matt Huisman's public mirror (credit to @matthuisman)
    channels: https://i.mjh.nz/SamsungTVPlus/.channels.json.gz
    EPG:      https://i.mjh.nz/SamsungTVPlus/{region}.xml.gz
Streams:      https://jmp2.uk/stvp-{channel_id}   (redirects to the live CDN URL)

Channels whose metadata has a `license_url` are Widevine-protected. This script
keeps them and writes #KODIPROP lines with the license URL baked into the M3U,
same format as the Vidaa generator.

Changes vs the previous version (parity with FastChannels):
  * EPG: every programme gets a <category> (the channel's group) if it has none
  * M3U: adds channel-id and tvg-description
  * Multi-region: channel names get a " (US)" style suffix when more than one
    region is selected (M3U and EPG display-name), so duplicates are distinguishable
  * Multi-region: duplicate tvg-chno values are dropped (first one wins)

Usage:
    python samsung_m3u_epg.py [--regions us,ca] [--drm include|only|exclude]
      (regions: no spaces after commas unless you quote the whole value)
                              [--out-dir DIR] [--m3u NAME] [--epg NAME]
                              [--no-epg] [--inspect] [-v]

--inspect prints the raw metadata of the first few DRM channels and exits.

Requires: requests
"""

from __future__ import annotations

import argparse
import gzip
import json
import logging
import re
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.parse import quote
from xml.etree import ElementTree as ET

import requests

logger = logging.getLogger("samsung")

CHANNELS_URL = "https://i.mjh.nz/SamsungTVPlus/.channels.json.gz"
EPG_URL = "https://i.mjh.nz/SamsungTVPlus/{region}.xml.gz"
STREAM_URL = "https://jmp2.uk/stvp-{id}"
ALLOWED_REGIONS = ("us", "ca", "gb", "de", "fr", "es", "it", "kr", "in", "at", "ch")
UA = "okhttp/4.12.0"


def _esc(v: str) -> str:
    return str(v).replace('"', "'").replace("\n", " ")


def _gz(session: requests.Session, url: str) -> bytes:
    r = session.get(url, timeout=60, headers={"User-Agent": UA})
    r.raise_for_status()
    return gzip.decompress(r.content)


def _license_headers(ch: dict) -> dict[str, str]:
    """Pick up license request headers if the metadata carries any."""
    for key in ("license_headers", "license_request_headers", "headers"):
        h = ch.get(key)
        if isinstance(h, dict) and h:
            return {str(k): str(v) for k, v in h.items()}
    return {}


def sniff_manifest_type(session: requests.Session, url: str) -> str:
    """Return 'hls' or 'mpd' by looking at what the stream URL really serves.

    Non-2xx responses (rate limits, error pages) are retried once and never
    treated as DASH. Falls back to 'hls' if nothing conclusive comes back."""
    for _ in range(2):
        try:
            with session.get(url, stream=True, timeout=12, allow_redirects=True,
                             headers={"User-Agent": UA}) as r:
                if not r.ok:
                    continue
                head = next(r.iter_content(512), b"")[:512].lstrip().lower()
                ctype = (r.headers.get("Content-Type") or "").lower()
        except Exception as exc:
            logger.debug("manifest sniff failed for %s: %s", url, exc)
            continue
        if head.startswith(b"#extm3u") or "mpegurl" in ctype:
            return "hls"
        if head.startswith(b"<?xml") or head.startswith(b"<mpd") or "dash" in ctype:
            return "mpd"
    return "hls"


def fetch_channels(session: requests.Session, regions: list[str], drm_mode: str):
    data = json.loads(_gz(session, CHANNELS_URL))
    all_regions = data.get("regions", {})
    multi = len(regions) > 1
    channels: list[dict] = []
    seen: set[str] = set()
    used_chno: set[str] = set()
    for region in regions:
        rd = all_regions.get(region)
        if not rd:
            logger.warning("region %r not in source; available: %s", region, list(all_regions))
            continue
        n = 0
        for ch_id, ch in (rd.get("channels") or {}).items():
            if ch_id in seen:
                continue
            is_drm = bool(ch.get("license_url"))
            if (drm_mode == "exclude" and is_drm) or (drm_mode == "only" and not is_drm):
                continue
            seen.add(ch_id)
            name = ch.get("name") or ch_id
            display = f"{name} ({region.upper()})" if multi else name
            chno = ch.get("chno")
            chno_key = str(chno) if chno else None
            if chno_key and chno_key in used_chno:
                chno = None
            elif chno_key:
                used_chno.add(chno_key)
            channels.append({
                "id": ch_id,
                "region": region,
                "name": name,
                "display": display,
                "logo": ch.get("logo"),
                "group": ch.get("group") or "Live TV",
                "chno": chno,
                "description": (ch.get("description") or "").strip(),
                "license_url": ch.get("license_url") or None,
                "license_headers": _license_headers(ch),
                "raw": ch,
            })
            n += 1
        logger.info("%d channels (region=%s)", n, region)
    return channels


def write_m3u(channels: list[dict], path: Path, session: requests.Session) -> None:
    drm_chs = [c for c in channels if c["license_url"]]
    with ThreadPoolExecutor(max_workers=4) as pool:
        types = list(pool.map(lambda c: sniff_manifest_type(session, STREAM_URL.format(id=c["id"])), drm_chs))
    for c, t in zip(drm_chs, types):
        c["manifest_type"] = t
    logger.info("DRM manifest types: %d hls, %d mpd", types.count("hls"), types.count("mpd"))

    lines = ["#EXTM3U"]
    drm = 0
    for ch in channels:
        attrs = [f'channel-id="{_esc(ch["id"])}"',
                 f'tvg-id="{_esc(ch["id"])}"',
                 f'tvg-name="{_esc(ch["display"])}"',
                 f'group-title="{_esc(ch["group"])}"']
        if ch["logo"]:
            attrs.append(f'tvg-logo="{_esc(ch["logo"])}"')
        if ch["chno"]:
            attrs.append(f'tvg-chno="{_esc(ch["chno"])}"')
        if ch["description"]:
            attrs.append(f'tvg-description="{_esc(ch["description"])}"')
        is_drm = bool(ch["license_url"])
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch["display"]}{" [DRM]" if is_drm else ""}')
        if is_drm:
            drm += 1
            hdr = "&".join(f"{k}={quote(v, safe='=')}" for k, v in ch["license_headers"].items())
            lines += [
                "#KODIPROP:inputstream=inputstream.adaptive",
                f"#KODIPROP:inputstream.adaptive.manifest_type={ch['manifest_type']}",
                "#KODIPROP:inputstream.adaptive.license_type=com.widevine.alpha",
                f"#KODIPROP:inputstream.adaptive.license_key={ch['license_url']}|{hdr}|R{{SSM}}|",
            ]
        lines.append(STREAM_URL.format(id=ch["id"]))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    logger.info("Wrote %d channels (%d DRM) to %s", len(channels), drm, path)


def _fill_desc(prog: ET.Element, fallback: str) -> bool:
    """Add a <desc> from the channel description if the programme has none.

    XMLTV order is title, sub-title, desc, ... so the new element goes right after
    the last title/sub-title. Returns True if one was added."""
    if not fallback:
        return False
    existing = prog.find("desc")
    if existing is not None and (existing.text or "").strip():
        return False
    if existing is not None:
        prog.remove(existing)
    idx = 0
    for i, child in enumerate(list(prog)):
        if child.tag in ("title", "sub-title"):
            idx = i + 1
    desc = ET.Element("desc")
    desc.text = fallback
    prog.insert(idx, desc)
    return True


def _fill_category(prog: ET.Element, fallback: str) -> bool:
    """Add a <category> from the channel group if the programme has none.

    XMLTV order puts category after title, sub-title, desc, credits, date, so it
    goes after the last of those. Returns True if one was added."""
    if not fallback:
        return False
    for c in prog.findall("category"):
        if (c.text or "").strip():
            return False
    idx = 0
    for i, child in enumerate(list(prog)):
        if child.tag in ("title", "sub-title", "desc", "credits", "date", "category"):
            idx = i + 1
    cat = ET.Element("category", {"lang": "en"})
    cat.text = fallback
    prog.insert(idx, cat)
    return True


def write_epg(session: requests.Session, channels: list[dict], regions: list[str], path: Path) -> None:
    owned: dict[str, set[str]] = {}
    chan_desc: dict[str, str] = {}
    chan_group: dict[str, str] = {}
    for ch in channels:
        owned.setdefault(ch["region"], set()).add(ch["id"])
        chan_desc[ch["id"]] = ch["description"]
        chan_group[ch["id"]] = ch["group"]

    tv = ET.Element("tv", {"generator-info-name": "samsung-m3u-epg",
                           "source-info-name": "i.mjh.nz/SamsungTVPlus"})
    for ch in channels:
        el = ET.SubElement(tv, "channel", {"id": ch["id"]})
        ET.SubElement(el, "display-name").text = ch["display"]
        if ch["logo"]:
            ET.SubElement(el, "icon", {"src": ch["logo"]})

    total = 0
    for region in regions:
        ids = owned.get(region)
        if not ids:
            continue
        try:
            root = ET.fromstring(_gz(session, EPG_URL.format(region=region)))
        except Exception as exc:
            logger.warning("EPG fetch failed for region=%s: %s", region, exc)
            continue
        n = filled = cats = 0
        for prog in root.iter("programme"):
            cid = prog.get("channel")
            if cid in ids:
                if _fill_desc(prog, chan_desc.get(cid, "")):
                    filled += 1
                if _fill_category(prog, chan_group.get(cid, "")):
                    cats += 1
                tv.append(prog)
                n += 1
        total += n
        logger.info("%d programmes (region=%s), %d desc fallbacks, %d category fallbacks",
                    n, region, filled, cats)

    ET.indent(tv)
    ET.ElementTree(tv).write(path, encoding="utf-8", xml_declaration=True)
    logger.info("Wrote %d programmes to %s", total, path)


def _parse_args(argv=None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate Samsung TV Plus M3U + XMLTV, with DRM channels.")
    # NOTE: do NOT put unquoted spaces after commas (`--regions us, ca, gb`);
    # use `--regions us,ca,gb` or quote it: `--regions "us, ca, gb"`.
    p.add_argument("--regions", default="us",
                   help=f"Comma-separated regions, no spaces unless quoted (default: us). "
                        f"Options: {','.join(ALLOWED_REGIONS)}")
    p.add_argument("--drm", choices=("include", "only", "exclude"), default="include",
                   help="Widevine channels: include (default), only, or exclude")
    p.add_argument("--out-dir", default=".", help="Output directory (default: .)")
    p.add_argument("--m3u", default="samsung.m3u")
    p.add_argument("--epg", default="samsung.xml")
    p.add_argument("--no-epg", action="store_true")
    p.add_argument("--inspect", action="store_true",
                   help="Print raw metadata of the first DRM channels and exit")
    p.add_argument("-v", "--verbose", action="store_true")
    return p.parse_args(argv)


def main(argv=None) -> int:
    args = _parse_args(argv)
    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    regions = []
    for code in re.split(r"[,|/\s]+", args.regions.lower()):
        if code in ALLOWED_REGIONS and code not in regions:
            regions.append(code)
    if not regions:
        logger.error("No valid regions in %r", args.regions)
        return 1

    session = requests.Session()
    try:
        channels = fetch_channels(session, regions, "only" if args.inspect else args.drm)
    except Exception as exc:
        logger.error("Channel fetch failed: %s", exc)
        return 1
    if not channels:
        logger.error("No channels found; aborting.")
        return 1

    if args.inspect:
        for ch in channels[:3]:
            print(json.dumps({"id": ch["id"], "region": ch["region"], **ch["raw"]}, indent=2))
        print(f"\n{len(channels)} DRM channels total", file=sys.stderr)
        return 0

    out = Path(args.out_dir).expanduser().resolve()
    out.mkdir(parents=True, exist_ok=True)
    write_m3u(channels, out / args.m3u, session)
    if not args.no_epg:
        write_epg(session, channels, regions, out / args.epg)
    logger.info("Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
