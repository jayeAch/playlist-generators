#!/usr/bin/env python3
"""Normalize group-title categories in generated playlists using category_utils.

Run once after the generators, from one place, instead of editing each script:

    python normalize_playlists.py                       # playlists/*.m3u in place
    python normalize_playlists.py playlists/vizio.m3u   # specific files
    python normalize_playlists.py --epg                 # also fix XMLTV <category>
    python normalize_playlists.py --dry-run             # report only

The source name (used for source-specific rules such as Philo/HDHomeRun) is the
file stem: playlists/vizio.m3u -> "vizio". Channels whose category can't be
resolved keep their original group-title. Safe to re-run (idempotent).
"""
from __future__ import annotations

import argparse
import html
import re
import sys
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path

import category_utils as cu

# Final consolidation pass: canonical category -> broader player-facing group.
# Edit freely; anything not listed is left as category_utils resolved it.
# Idempotent: re-running maps the merged labels back to the same targets.
MERGE: dict[str, str] = {
    "Outdoors": "Sports",
    "Shopping": "Lifestyle",
    "Home & DIY": "Lifestyle",
    "Gaming": "Anime & Gaming",
    "Anime": "Anime & Gaming",
    "Science": "Documentary",
    "History": "Documentary",
    "Sci-Fi": "Sci-Fi & Horror",
    "Horror": "Sci-Fi & Horror",
    "Westerns": "Classic TV",
    "Food": "Food & Travel",
    "Travel": "Food & Travel",
    "Action & Adventure": "Drama",
    "Game Shows": "Reality TV",
}

GROUP_RE = re.compile(r'group-title="([^"]*)"')
TVG_ID_RE = re.compile(r'tvg-id="([^"]*)"')


def _split_extinf(line: str) -> tuple[str, str]:
    """Return (attribute part, display name). The name is after the last comma
    that is outside a quoted attribute value."""
    in_q = False
    last = -1
    for i, ch in enumerate(line):
        if ch == '"':
            in_q = not in_q
        elif ch == ',' and not in_q:
            last = i
    return (line[:last], line[last + 1:].strip()) if last >= 0 else (line, "")


def normalize_m3u(path: Path, dry_run: bool) -> tuple[dict[str, dict[str, str]], Counter]:
    """Rewrite group-title in one M3U. Returns ({tvg-id: {old: new}}, change counts)."""
    source = path.stem.lower()
    out: list[str] = []
    by_id: dict[str, dict[str, str]] = {}
    changes: Counter = Counter()

    for line in path.read_text(encoding="utf-8").splitlines():
        m = GROUP_RE.search(line) if line.startswith("#EXTINF") else None
        if not m:
            out.append(line)
            continue
        old = html.unescape(m.group(1))
        attrs, name = _split_extinf(line)
        new = cu.category_for_channel(name, old, source) or old
        new = MERGE.get(new, new)
        if new != old:
            changes[(old, new)] += 1
            line = GROUP_RE.sub(lambda _m: f'group-title="{new.replace(chr(34), "&quot;")}"', line, count=1)
        idm = TVG_ID_RE.search(attrs)
        if idm:
            by_id[idm.group(1)] = {"old": old, "new": new}
        out.append(line)

    if not dry_run:
        path.write_text("\n".join(out) + "\n", encoding="utf-8")
    return by_id, changes


def normalize_epg(path: Path, by_id: dict[str, dict[str, str]], dry_run: bool) -> int:
    """Rewrite programme <category> values that equal the channel's old group."""
    tree = ET.parse(path)
    n = 0
    for prog in tree.getroot().iter("programme"):
        info = by_id.get(prog.get("channel", ""))
        if not info or info["old"] == info["new"]:
            continue
        for cat in prog.findall("category"):
            if (cat.text or "").strip() == info["old"]:
                cat.text = info["new"]
                n += 1
    if n and not dry_run:
        tree.write(path, encoding="utf-8", xml_declaration=True)
    return n


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", type=Path, help="M3U files (default: playlists/*.m3u)")
    ap.add_argument("--epg", action="store_true", help="also rewrite matching <category> in the sibling .xml")
    ap.add_argument("--dry-run", action="store_true", help="report changes without writing")
    args = ap.parse_args()

    files = args.files or sorted(Path("playlists").glob("*.m3u"))
    if not files:
        print("no playlists found", file=sys.stderr)
        return 1

    for f in files:
        if not f.is_file():
            print(f"skip {f}: not found", file=sys.stderr)
            continue
        by_id, changes = normalize_m3u(f, args.dry_run)
        total = sum(changes.values())
        print(f"{f}: {total} group-title change(s)")
        for (old, new), c in changes.most_common(8):
            print(f"    {c:4d}  {old!r} -> {new!r}")
        xml = f.with_suffix(".xml")
        if args.epg and xml.is_file():
            print(f"{xml}: {normalize_epg(xml, by_id, args.dry_run)} <category> change(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
