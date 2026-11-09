#!/usr/bin/env python3
"""
Standalone Vidaa Free TV M3U Playlist + EPG (XMLTV) Generator, with DRM bridge.

Generate:
    python vidaa_m3u_epg.py [--out-dir DIR] [--license-base URL] ...
      -> vidaa.m3u (DRM tiles get Kodi/inputstream.adaptive Widevine props that
         point at the license proxy) and vidaa.xml

By default (like fc-lite with no base_url) the Widevine license URL and the
`playback-request` header are baked into the M3U, so no server is needed.
Optional proxy mode, if baked licenses stop working (stream ids expire):
    python vidaa_m3u_epg.py --serve [--port 8765]
    python vidaa_m3u_epg.py --license-base http://<host>:8765

The proxy receives the player's Widevine challenge at /license/<channel_id>,
re-resolves the per-tile license URL + stream id, adds the `playback-request`
header Vidaa's license server wants, and returns the license. Same approach as
FastChannels' /play/vidaa/license route.

Players: DRM tiles need a Widevine-capable player that honors #KODIPROP
(Kodi + inputstream.adaptive, TiviMate does not). HLS tiles play anywhere.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import io
import json
import logging
import socket
import sys
import threading
import time
import uuid
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import UTC, datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, parse_qsl, quote, unquote, urlencode, urljoin, urlparse, urlunparse
from xml.dom import minidom

import requests

logger = logging.getLogger("vidaa")


@dataclass
class ChannelData:
    source_channel_id: str
    name: str
    stream_url: str
    logo_url: str | None = None
    category: str | None = None
    language: str | None = None
    country: str | None = None
    stream_type: str | None = None
    gracenote_id: str | None = None


@dataclass
class ProgramData:
    source_channel_id: str
    title: str
    start_time: datetime
    end_time: datetime
    description: str | None = None
    poster_url: str | None = None


class ScrapeSkipError(RuntimeError):
    pass


def category_for_channel(name: str, column_title: str | None) -> str | None:
    if not column_title:
        return None
    if column_title in ("Movies", "Entertainment", "News & Opinion",
                        "Sports", "Kids", "Music"):
        return column_title
    return None


def infer_category_from_name(name: str) -> str | None:
    n = name.casefold()
    if any(k in n for k in ("news", "weather", "cnn", "fox news")):
        return "News"
    if any(k in n for k in ("sport", "nfl", "nba", "mlb", "nhl")):
        return "Sports"
    if any(k in n for k in ("kid", "cartoon", "nick", "disney", "junior")):
        return "Kids"
    if any(k in n for k in ("music", "mtv", "vh1", "vevo")):
        return "Music"
    return "General"


def infer_language_from_metadata(name: str) -> str:
    return "en"


def resolve_gracenote(source: str, lookup_key: str) -> str | None:
    return None


class BaseScraper:
    source_name = "base"

    def __init__(self, config: dict | None = None):
        self.config = config or {}
        self.session = requests.Session()
        self.cache: dict = {}


# ---------------------------------------------------------------------------
# Vidaa constants
# ---------------------------------------------------------------------------

_APP_KEY             = "1204099470"
_APP_SECRET          = "64nprh5fhk2syebs6qlkmmpt3l7s3ljg"
_OAUTH_CLIENT_SECRET = "28B3E8943D6FADFB28071C303EF3F26AAC634B4BA1F9937FFD725F0ED516CA1952237D39DC2460219C46E0B7170577AD"
_OAUTH_URL           = "https://partner.vidaahub.com/ns/account/oauth2.0/access_token"
_LAYOUT_UI           = "https://partner-layout-ui.vidaahub.com"
_DETAIL_UI           = "https://partner-detail-ui.vidaahub.com"

_LIVE_TYPE_CODE        = "600007"
_MEDIAS_BATCH_SIZE     = 5
_EPG_STEP_HOURS        = 12
_EPG_HORIZON_DAYS      = 5
_EPG_CIRCUIT_THRESHOLD = 5
_SPANISH_COLUMN_TITLE  = "In Spanish"
_DRM_PARAM_TTL         = 30 * 60
_DEFAULT_PORT          = 8765

_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
_DEVICE_ID = "002003059003001007000128pngito97hw8ktrcmhh4njsaof802ig"

_COMMON_PARAMS = {
    "appPackageName":      "net.vidaatv.hisense.android.tv",
    "appVersion":          "os_t.atvchannels.1.00.0.0.Q030800",
    "language":            "eng",
    "locale":              "USA",
    "country":             "USA",
    "brand":               "his",
    "capabilityCode":      "2026031101",
    "playerFamilyName":    "VDAndroid_TV",
    "playerFamilyVersion": "006110000",
    "deviceType":          "1",
    "appOwnership":        "oem",
    "personalizedRec":     "1",
    "localeLanguage":      "eng",
}


def _sign_query(params: dict[str, str]) -> str:
    keys = sorted(k for k, v in params.items() if v not in (None, ""))
    sign_data = "&".join(f"{k}={params[k]}" for k in keys)
    return base64.b64encode(hashlib.md5((sign_data + _APP_SECRET).encode()).digest()).decode()


def _sign_body(body: str) -> str:
    return base64.b64encode(hashlib.md5((body + _APP_SECRET).encode()).digest()).decode()


def _clean_stream_url(url: str) -> str:
    parsed = urlparse(url)
    params = parse_qsl(parsed.query, keep_blank_values=True)
    clean = [(k, v) for k, v in params
             if not ((v.startswith('[') and v.endswith(']'))
                     or (v.startswith('{') and v.endswith('}')))]
    return urlunparse(parsed._replace(query=urlencode(clean)))


def _parse_mini_player(url: str) -> dict | None:
    if not url or 'mini-player' not in url:
        return None
    q = parse_qs(urlparse(url).query)
    streaming_url = unquote((q.get('streaming_url') or [''])[0])
    drm_url       = unquote((q.get('drm_url') or [''])[0])
    stream_id     = (q.get('stream_id') or [''])[0]
    if not streaming_url or not drm_url or not stream_id:
        return None
    return {
        'streaming_url': _clean_stream_url(streaming_url),
        'drm_url':       drm_url,
        'stream_id':     stream_id,
    }


def _chunk(seq: list, size: int):
    for i in range(0, len(seq), size):
        yield seq[i:i + size]


def _playback_request_header(stream_id: str) -> str:
    return base64.b64encode(json.dumps({
        "assetId": stream_id,
        "clientMetadata": {
            "name": "vod",
            "version": "1.0.0",
            "os": {"name": "Linux", "version": "5.15.148"},
            "device": {"type": "vidaaOS"},
            "supportedDrms": [{"type": "widevine"}, {"type": "playready"}],
        },
    }, separators=(",", ":")).encode()).decode()


# ---------------------------------------------------------------------------
# Scraper
# ---------------------------------------------------------------------------

class VidaaScraper(BaseScraper):
    source_name = "vidaa"
    license_url = "https://drm-vss.vidaahub.com/multi-drm/vss/license"

    def __init__(self, config: dict | None = None):
        super().__init__(config)
        self.session.headers.update({"User-Agent": _UA})
        self._access_token: str | None = None
        self._token_expires_at: float = 0.0
        self._drm_param_cache: dict[str, dict] = {}
        self._lock = threading.Lock()
        self._load_drm_param_cache()

    # -- persisted DRM cache ------------------------------------------------

    def _cache_path(self) -> Path:
        out = self.config.get("cache_path")
        if out:
            return Path(out)
        return Path.home() / ".cache" / "vidaa_m3u_epg" / "drm_params.json"

    def _load_drm_param_cache(self) -> None:
        path = self._cache_path()
        if not path.exists():
            return
        try:
            raw = json.loads(path.read_text("utf-8"))
        except Exception as exc:
            logger.debug("[vidaa] ignoring unreadable DRM cache %s: %s", path, exc)
            return
        if not isinstance(raw, dict):
            return
        now = time.time()
        for cid, entry in raw.items():
            if not isinstance(entry, dict):
                continue
            cached_at = entry.get("cached_at")
            if not entry.get("params") or not isinstance(cached_at, (int, float)):
                continue
            if (now - float(cached_at)) >= _DRM_PARAM_TTL:
                continue
            self._drm_param_cache[cid] = entry

    def _persist_drm_param_cache(self) -> None:
        path = self._cache_path()
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(self._drm_param_cache), encoding="utf-8")
        except Exception:
            logger.debug("[vidaa] could not persist DRM cache", exc_info=True)

    # -- auth ---------------------------------------------------------------

    def _ensure_token(self) -> None:
        if self._access_token and time.monotonic() < self._token_expires_at:
            return
        r = self.session.get(_OAUTH_URL, params={
            "client_id": _APP_KEY,
            "client_secret": _OAUTH_CLIENT_SECRET,
            "grant_type": "client_credentials",
        }, timeout=20)
        r.raise_for_status()
        data = r.json()
        token = data.get("access_token")
        if not token:
            raise RuntimeError(f"Vidaa OAuth token missing in response: {data}")
        self._access_token = token
        expires_in = int(data.get("expires_in") or 3600)
        self._token_expires_at = time.monotonic() + max(expires_in - 120, 60)

    def _base_params(self, **extra: str) -> dict[str, str]:
        self._ensure_token()
        params = dict(_COMMON_PARAMS)
        params["deviceId"] = _DEVICE_ID
        params["accessToken"] = self._access_token
        params["commonRandomId"] = uuid.uuid4().hex
        params.update(extra)
        return params

    def _get(self, host: str, path: str, params: dict[str, str]) -> dict:
        signature = _sign_query(params)
        r = self.session.get(f"{host}{path}", params=params,
                             headers={"appKey": _APP_KEY, "x-sign-for": signature},
                             timeout=30)
        r.raise_for_status()
        return r.json()

    def _post(self, host: str, path: str, params: dict[str, str], body: dict) -> dict:
        body_str = json.dumps(body, separators=(",", ":"))
        signature = _sign_body(body_str)
        r = self.session.post(f"{host}{path}", params=params, data=body_str.encode(),
                              headers={
                                  "appKey": _APP_KEY,
                                  "x-sign-for": signature,
                                  "Content-Type": "application/json",
                              }, timeout=30)
        r.raise_for_status()
        return r.json()

    def _fetch_medias_info(self, channel_ids: list[int], related_date: int) -> dict:
        params = self._base_params(sceneCode="ottChannel", relatedDate=str(related_date))
        body = {"medias": [{"id": cid, "typeCode": _LIVE_TYPE_CODE} for cid in channel_ids]}
        return self._post(_DETAIL_UI, "/api/v1.0.0/detailApi/mediasInfo", params, body)

    # -- channels -----------------------------------------------------------

    def _discover_columns(self) -> list[dict]:
        params = self._base_params(scene="osPagingChannel", resourceType="1")
        data = self._get(_LAYOUT_UI, "/api/v1.0.0/layoutApi/activityResources", params)
        columns = data.get("columns") or []
        if not columns:
            raise RuntimeError(f"Vidaa category discovery returned no columns: {data}")
        return columns

    def _fetch_column_tiles(self, column_id) -> list[dict]:
        tiles_by_id: dict[int, dict] = {}
        page = 1
        while page <= 20:
            params = self._base_params(columnId=str(column_id), scene="osPagingChannel", ratio="16:9")
            if page > 1:
                params["metaInfo"] = f"page={page},oneMoreTile=1"
            data = self._get(_LAYOUT_UI, "/api/v1.0.0/layoutApi/columnData", params)
            tiles = (data.get("column") or {}).get("tiles") or []
            if not tiles:
                break
            for tile in tiles:
                if tile.get("typeCode") == _LIVE_TYPE_CODE and tile.get("id") is not None:
                    tiles_by_id[tile["id"]] = tile
            page += 1
        return list(tiles_by_id.values())

    def _build_channel(self, media: dict, column_title: str | None) -> ChannelData | None:
        cid = media.get("id")
        show = media.get("showInfo") or {}
        chan = media.get("channelInfo") or {}
        name = (show.get("title") or "").strip()
        stream_url = chan.get("streamingParam")
        if not cid or not name or not stream_url:
            return None
        drm = bool((chan.get("streamingDetailParam") or {}).get("encryption"))
        if drm:
            wrapped = _parse_mini_player(stream_url)
            if not wrapped:
                logger.warning("[vidaa] DRM tile %s (%s) has an unrecognized streamingParam shape — skipping",
                               cid, name)
                return None
            stream_url = wrapped['streaming_url']
            # Cache license params now so the proxy doesn't need a live lookup.
            self._drm_param_cache[str(cid)] = {"params": wrapped, "cached_at": time.time()}
        else:
            stream_url = _clean_stream_url(stream_url)
        is_spanish = column_title == _SPANISH_COLUMN_TITLE
        category = category_for_channel(name, column_title) or infer_category_from_name(name) or "Entertainment"
        language = "es" if is_spanish else infer_language_from_metadata(name)
        return ChannelData(
            source_channel_id = str(cid),
            name              = name,
            stream_url        = stream_url,
            logo_url          = show.get("frontPic") or show.get("appIcon") or None,
            category          = category,
            language          = language,
            country           = "US",
            stream_type       = "dash" if drm else "hls",
            gracenote_id      = resolve_gracenote('vidaa', lookup_key=str(cid)),
        )

    def fetch_channels(self) -> list[ChannelData]:
        columns = self._discover_columns()

        tile_ids_by_column: dict[int, list[int]] = {}
        column_title_by_channel_id: dict[int, str] = {}
        for col in columns:
            col_id = col.get("id")
            col_title = col.get("title") or ""
            if col_id is None:
                continue
            tiles = self._fetch_column_tiles(col_id)
            ids = [t["id"] for t in tiles]
            tile_ids_by_column[col_id] = ids
            for cid in ids:
                column_title_by_channel_id.setdefault(cid, col_title)
            logger.debug("[vidaa] %s: %d channels", col_title, len(ids))

        all_ids = list(column_title_by_channel_id.keys())
        if not all_ids:
            raise RuntimeError("Vidaa: no live channels discovered across any category")

        now_ts = int(time.time())
        channels: list[ChannelData] = []
        for batch in _chunk(all_ids, _MEDIAS_BATCH_SIZE):
            detail = self._fetch_medias_info(batch, now_ts)
            for media in detail.get("medias") or []:
                cid = media.get("id")
                if cid is None:
                    continue
                channel = self._build_channel(media, column_title_by_channel_id.get(cid))
                if channel:
                    channels.append(channel)

        self._persist_drm_param_cache()

        breakdown = ", ".join(
            f"{col.get('title') or ''}={len(tile_ids_by_column.get(col.get('id'), []))}"
            for col in columns
            if col.get("id") is not None
        )
        logger.info("[vidaa] %d channels fetched across %d categories (%s); %d DRM",
                    len(channels), len(columns), breakdown,
                    sum(1 for c in channels if c.stream_type == "dash"))
        return channels

    # -- EPG ----------------------------------------------------------------

    def fetch_epg(self, channels: list[ChannelData]) -> list[ProgramData]:
        if not channels:
            return []

        ids = [int(ch.source_channel_id) for ch in channels]
        now = int(time.time())
        steps = (_EPG_HORIZON_DAYS * 24) // _EPG_STEP_HOURS
        related_dates = [now + step * _EPG_STEP_HOURS * 3600 for step in range(steps)]
        batches = list(_chunk(ids, _MEDIAS_BATCH_SIZE))

        programs_by_key: dict[tuple[str, int], ProgramData] = {}
        seen_channel_ids: set[str] = set()
        consecutive_failures = 0
        circuit_open = False
        for related_date in related_dates:
            for batch in batches:
                if circuit_open:
                    continue
                try:
                    data = self._fetch_medias_info(batch, related_date)
                    consecutive_failures = 0
                except Exception as exc:
                    consecutive_failures += 1
                    logger.warning("[vidaa] EPG batch failed (relatedDate=%s, ids=%s): %s",
                                   related_date, batch, exc)
                    if consecutive_failures >= _EPG_CIRCUIT_THRESHOLD:
                        circuit_open = True
                        logger.error("[vidaa] %d consecutive EPG batch failures — "
                                     "aborting remaining requests", consecutive_failures)
                    continue

                for media in data.get("medias") or []:
                    cid = media.get("id")
                    if cid is None:
                        continue
                    seen_channel_ids.add(str(cid))
                    for sched in (media.get("channelInfo") or {}).get("scheduleList") or []:
                        title = (sched.get("scheduleName") or "").strip()
                        start_ms, end_ms = sched.get("startTime"), sched.get("endTime")
                        if not title or not start_ms or not end_ms:
                            continue
                        start_dt = datetime.fromtimestamp(start_ms / 1000, tz=UTC)
                        end_dt   = datetime.fromtimestamp(end_ms / 1000, tz=UTC)
                        if end_dt <= start_dt:
                            continue
                        key = (str(cid), sched.get("scheduleId") or start_ms)
                        programs_by_key[key] = ProgramData(
                            source_channel_id = str(cid),
                            title             = title,
                            start_time        = start_dt,
                            end_time          = end_dt,
                            description       = (sched.get("summary") or "").strip() or None,
                            poster_url        = sched.get("recommendPic"),
                        )

        if not programs_by_key and (circuit_open or consecutive_failures):
            raise ScrapeSkipError("Vidaa EPG unavailable: all attempted batches failed")

        covered_ids = {cid for cid, _ in programs_by_key}
        name_by_id = {ch.source_channel_id: ch.name for ch in channels}
        placeholder_channels = 0
        for source_channel_id in seen_channel_ids - covered_ids:
            name = name_by_id.get(source_channel_id)
            if not name:
                continue
            for step in range(_EPG_HORIZON_DAYS * 24):
                block_start = datetime.fromtimestamp(now + step * 3600, tz=UTC)
                block_end = block_start + timedelta(hours=1)
                programs_by_key[(source_channel_id, -1 - step)] = ProgramData(
                    source_channel_id = source_channel_id,
                    title             = name,
                    start_time        = block_start,
                    end_time          = block_end,
                    description       = "Live schedule not published for this channel by the source.",
                    poster_url        = None,
                )
            placeholder_channels += 1
        if placeholder_channels:
            logger.info("[vidaa] %d channel(s) had no published schedule — filled with placeholder blocks",
                        placeholder_channels)

        programs = list(programs_by_key.values())
        logger.info("[vidaa] %d EPG programs fetched across %d channels",
                    len(programs), len(channels))
        return programs

    # -- DRM license bridge -------------------------------------------------

    def _lookup_drm_params(self, channel_id: str) -> dict | None:
        cid = str(channel_id)
        with self._lock:
            cached = self._drm_param_cache.get(cid)
            if cached and (time.time() - cached["cached_at"]) < _DRM_PARAM_TTL:
                return cached["params"]
            try:
                detail = self._fetch_medias_info([int(channel_id)], int(time.time()))
            except Exception as exc:
                logger.warning("[vidaa] DRM param lookup failed for %s: %s", channel_id, exc)
                return None
            medias = detail.get("medias") or []
            if not medias:
                return None
            raw = (medias[0].get("channelInfo") or {}).get("streamingParam") or ""
            params = _parse_mini_player(raw)
            if params:
                self._drm_param_cache[cid] = {"params": params, "cached_at": time.time()}
                self._persist_drm_param_cache()
            return params

    def get_license_url(self, channel_id: str | None = None) -> str | None:
        if not channel_id:
            return None
        params = self._lookup_drm_params(channel_id)
        if not params:
            return None
        return f"{params['drm_url']}?streamId={params['stream_id']}&reqFrom=v_tvch_m"

    def prepare_license_request(
        self, challenge: bytes, channel_id: str | None = None, **kwargs
    ) -> tuple[bytes, dict]:
        params = self._lookup_drm_params(channel_id) if channel_id else None
        stream_id = params['stream_id'] if params else (channel_id or "")
        return challenge, {"playback-request": _playback_request_header(stream_id)}


# ---------------------------------------------------------------------------
# DASH manifest filter (drops video renditions above a bitrate / height cap)
# ---------------------------------------------------------------------------

def filter_mpd(data: bytes, base_url: str, max_bps: int | None, max_height: int | None) -> bytes:
    for _, (prefix, uri) in ET.iterparse(io.BytesIO(data), events=("start-ns",)):
        try:
            ET.register_namespace(prefix, uri)
        except ValueError:
            pass
    root = ET.fromstring(data)
    mpd_ns = root.tag.split("}")[0] + "}" if root.tag.startswith("{") else ""

    def ok(rep) -> bool:
        bw, h = int(rep.get("bandwidth") or 0), int(rep.get("height") or 0)
        return (not max_bps or not bw or bw <= max_bps) and (not max_height or not h or h <= max_height)

    removed = 0
    for aset in root.iter(f"{mpd_ns}AdaptationSet"):
        reps = aset.findall(f"{mpd_ns}Representation")
        is_video = (aset.get("contentType") == "video"
                    or "video" in (aset.get("mimeType") or "")
                    or any("video" in (r.get("mimeType") or "") for r in reps))
        if not is_video or not reps:
            continue
        keep = [r for r in reps if ok(r)] or [min(reps, key=lambda r: int(r.get("bandwidth") or 0))]
        for r in reps:
            if r not in keep:
                aset.remove(r)
                removed += 1

    # Segment URLs resolve against the manifest's location; since we serve it from the
    # proxy, make the MPD-level BaseURL absolute.
    bases = root.findall(f"{mpd_ns}BaseURL")
    if bases:
        for b in bases:
            b.text = urljoin(base_url, (b.text or "").strip())
    else:
        el = ET.Element(f"{mpd_ns}BaseURL")
        el.text = urljoin(base_url, ".")
        period = root.find(f"{mpd_ns}Period")
        root.insert(list(root).index(period) if period is not None else 0, el)
    logger.debug("[vidaa] manifest filter removed %d renditions", removed)
    return ET.tostring(root, encoding="utf-8", xml_declaration=True)


# ---------------------------------------------------------------------------
# License / manifest proxy server (stdlib only)
# ---------------------------------------------------------------------------

def _make_handler(scraper: VidaaScraper):
    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *args):
            logger.debug("[proxy] " + fmt, *args)

        def _reply(self, code: int, body: bytes = b"", ctype: str = "application/octet-stream"):
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Headers", "*")
            self.end_headers()
            if body:
                self.wfile.write(body)

        def do_OPTIONS(self):
            self._reply(204)

        def do_GET(self):
            u = urlparse(self.path)
            if u.path.rstrip("/") in ("", "/health"):
                return self._reply(200, b"vidaa proxy ok\n", "text/plain")
            parts = [p for p in u.path.split("/") if p]
            if len(parts) == 2 and parts[0] == "manifest" and parts[1].endswith(".mpd"):
                cid = parts[1][:-4]
                q = parse_qs(u.query)
                try:
                    max_bps = int(float((q.get("max_mbps") or ["0"])[0]) * 1_000_000) or None
                    max_h = int((q.get("max_height") or ["0"])[0]) or None
                except ValueError:
                    return self._reply(400)
                params = cid.isdigit() and scraper._lookup_drm_params(cid)
                if not params:
                    return self._reply(502)
                try:
                    r = scraper.session.get(params["streaming_url"], timeout=15)
                    r.raise_for_status()
                    out = filter_mpd(r.content, r.url, max_bps, max_h)
                except Exception as exc:
                    logger.warning("[proxy] manifest %s failed: %s", cid, exc)
                    return self._reply(502)
                return self._reply(200, out, "application/dash+xml")
            self._reply(404)

        def do_POST(self):
            parts = [p for p in urlparse(self.path).path.split("/") if p]
            if len(parts) != 2 or parts[0] != "license" or not parts[1].isdigit():
                return self._reply(404)
            cid = parts[1]
            try:
                length = int(self.headers.get("Content-Length") or 0)
            except ValueError:
                length = 0
            if not 0 < length <= 65536:
                return self._reply(400 if length <= 0 else 413)
            challenge = self.rfile.read(length)

            license_url = scraper.get_license_url(cid)
            if not license_url:
                logger.warning("[proxy] no license params for channel %s", cid)
                return self._reply(502)
            body, headers = scraper.prepare_license_request(challenge, cid)
            headers["Content-Type"] = "application/octet-stream"
            try:
                r = requests.post(license_url, data=body, headers=headers, timeout=15)
            except Exception as exc:
                logger.warning("[proxy] license request failed for %s: %s", cid, exc)
                return self._reply(502)
            if r.status_code >= 400:
                logger.warning("[proxy] channel %s upstream HTTP %s: %s",
                               cid, r.status_code, r.content[:300])
                # stale stream_id? drop cache so the next attempt re-resolves
                scraper._drm_param_cache.pop(cid, None)
            else:
                logger.info("[proxy] channel %s license OK (%d bytes)", cid, len(r.content))
            self._reply(r.status_code, r.content)

    return Handler


def serve(scraper: VidaaScraper, host: str, port: int) -> None:
    server = ThreadingHTTPServer((host, port), _make_handler(scraper))
    logger.info("License proxy listening on http://%s:%d (POST /license/<channel_id>)", host, port)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


def _lan_ip() -> str:
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        s.close()


# ---------------------------------------------------------------------------
# M3U + XMLTV writers
# ---------------------------------------------------------------------------

_RES_TO_BPS = {"360p": 1_000_000, "480p": 1_800_000, "540p": 2_500_000,
               "720p": 4_500_000, "1080p": 9_000_000}


def write_m3u(channels: list[ChannelData], path: Path, scraper: VidaaScraper,
              license_base: str | None, max_res: str | None = None,
              manifest_qs: str | None = None, manifest_base: str | None = None) -> None:
    lines = ["#EXTM3U"]
    drm_count = 0
    for ch in channels:
        group = ch.category or "General"
        attrs = [
            f'tvg-id="{_esc(ch.source_channel_id)}"',
            f'tvg-name="{_esc(ch.name)}"',
            f'group-title="{_esc(group)}"',
        ]
        if ch.logo_url:
            attrs.append(f'tvg-logo="{_esc(ch.logo_url)}"')
        if ch.language:
            attrs.append(f'tvg-language="{ch.language}"')
        is_drm = ch.stream_type == "dash"
        suffix = " [DRM]" if is_drm else ""
        lines.append(f'#EXTINF:-1 {" ".join(attrs)},{ch.name}{suffix}')
        key = None
        if is_drm:
            if license_base:
                key = f"{license_base}/license/{ch.source_channel_id}||R{{SSM}}|"
            else:
                # Baked mode (fc-lite default): license URL + playback-request header
                # go straight into the M3U; no proxy needed.
                lic = scraper.get_license_url(ch.source_channel_id)
                if lic:
                    _, hdrs = scraper.prepare_license_request(b"", ch.source_channel_id)
                    hdr = "&".join(f"{k}={quote(v, safe='=')}" for k, v in hdrs.items())  # literal '=' padding, as OTT Navigator needs
                    key = f"{lic}|{hdr}|R{{SSM}}|"
                else:
                    logger.warning("[vidaa] no license params for %s (%s)", ch.source_channel_id, ch.name)
        if key:
            drm_count += 1
            lines += [
                "#KODIPROP:inputstream=inputstream.adaptive",
                "#KODIPROP:inputstream.adaptive.manifest_type=mpd",
                "#KODIPROP:inputstream.adaptive.license_type=com.widevine.alpha",
                f"#KODIPROP:inputstream.adaptive.license_key={key}",
            ]
            if max_res:
                # Honored by Kodi inputstream.adaptive; ExoPlayer apps (OTT Navigator,
                # TiviMate) ignore these and use their own quality setting.
                lines += [
                    f"#KODIPROP:inputstream.adaptive.chooser_resolution_max={max_res}",
                    f"#KODIPROP:inputstream.adaptive.chooser_resolution_secure_max={max_res}",
                    f"#KODIPROP:inputstream.adaptive.max_bandwidth={_RES_TO_BPS[max_res]}",
                ]
        url = ch.stream_url
        if is_drm and key and manifest_base:
            url = f"{manifest_base}/manifest/{ch.source_channel_id}.mpd?{manifest_qs}"
        lines.append(url)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    logger.info("Wrote %d channels (%d DRM, %s) to %s", len(channels), drm_count,
                f"proxy {license_base}" if license_base else "license baked in", path)


def write_xmltv(channels: list[ChannelData], programs: list[
