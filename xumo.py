# -*- coding: utf-8 -*-
"""
Standalone Xumo Play extractor (US, list 10006). Writes an M3U playlist and XMLTV guide.
No credentials required. DRM channels are skipped.

Usage:
    python xumo.py
    python xumo.py --out-dir playlists --m3u xumo.m3u --epg xumo.xml
    python xumo.py --epg xumo_epg.xml.gz       # gzipped XMLTV if the name ends in .gz
    python xumo.py --no-epg                    # playlist only
    python xumo.py -v                          # debug logging

Options:
    --out-dir DIR   Output directory, created if missing       (default: playlists)
    --m3u FILE      Playlist filename, relative to --out-dir   (default: xumo_playlist.m3u)
    --epg FILE      XMLTV filename, relative to --out-dir      (default: xumo_epg.xml.gz)
    --no-epg        Write the playlist only
    -v, --verbose   Debug logging

Notes:
    - Stream URLs are resolved at generation time and go stale when a program changes,
      so re-run on a schedule.
    - Program titles are cached in <out-dir>/xumo_asset_titles.json; commit it so the
      cache survives between runs.

Deps: pip install requests
"""
import argparse
import requests
import json
import os
import gzip
from datetime import datetime, timedelta, timezone
import xml.etree.ElementTree as ET
import logging
import time
import re
import uuid
import sys
import concurrent.futures
from collections import Counter
from urllib.parse import urlparse, parse_qsl, urlencode, urlunparse

# --- Configuration ---
ANDROID_TV_ENDPOINT = "https://android-tv-mds.xumo.com/v2"
VALENCIA_API_ENDPOINT = "https://valencia-app-mds.xumo.com/v2"
# Valencia web geoId. "2f08a9b3" is what the FastChannels scraper (xumo.py) sends; the older
# value here was "us". If the lineup looks different or shrinks, set this back to "us".
GEO_ID = "2f08a9b3"
# Stable per-run identifiers, reused in the channel list request and in stream macros
# so every request in one run looks like the same device.
DEVICE_ID = str(uuid.uuid4())
IFA_ID = str(uuid.uuid4())

PRIMARY_LIST_ID = "10006"
ASSET_LOOKUP_ENDPOINT = ANDROID_TV_ENDPOINT

PRIMARY_CHANNEL_LIST_URL = (
    f"{VALENCIA_API_ENDPOINT}/proxy/channels/list/{PRIMARY_LIST_ID}.json"
    f"?sort=hybrid&geoId={GEO_ID}&deviceId={DEVICE_ID}&ifaId={IFA_ID}"
)
BROADCAST_NOW_URL_TEMPLATE = f"{ASSET_LOOKUP_ENDPOINT}/channels/channel/{{channel_id}}/broadcast.json?hour={{hour_num}}"
ASSET_DETAILS_URL_TEMPLATE = f"{ASSET_LOOKUP_ENDPOINT}/assets/asset/{{asset_id}}.json?f=providers"

# --- EPG Settings ---
EPG_FETCH_DAYS = 3  # Days fetched AFTER yesterday: 2 = yesterday/today/tomorrow, 3 adds +2 days
# The trailing path segment of the EPG URL selects a 6-hour slice of the UTC day.
# "0" alone only returns ~00:00-06:00 UTC (17-18h gaps). Valid values (currently 0-3) are
# discovered at runtime by probing (see discover_epg_blocks); 4+ return HTTP 400.
EPG_PROBE_RANGE = range(0, 6)  # confirmed: 0-3 valid (6-hour slices), 4+ invalid
EPG_PAGE_LIMIT = 50
EPG_MAX_PAGES = 50  # Safety cap per date
# f=asset.title / f=asset.descriptions are requested in case the API returns titles inline,
# but in practice it doesn't (0 inline hits), so titles come from per-asset lookups below.
EPG_FETCH_URL_TEMPLATE = (
    f"{VALENCIA_API_ENDPOINT}/epg/{PRIMARY_LIST_ID}/{{date_str}}/{{block}}.json"
    f"?f=asset.title&f=asset.descriptions&limit={EPG_PAGE_LIMIT}&offset={{offset}}"
)

XUMO_LOGO_URL_TEMPLATE = "https://image.xumo.com/v1/channels/channel/{channel_id}/168x168.png?type=color_onBlack"

# --- VOD-style channels ---
# ~70 channels (Stash TV, FilmRise, Hell's Kitchen, ...) only expose a per-program VOD file
# (live-content.xumo.com/<provider>/content/<assetId>/...), not a live stream. Players start
# these at the beginning of the file and the URL goes stale when the program changes.
# The official web player does NOT use that file for these channels. It plays a channel-level
# live (SSAI) stream: https://dbrb49pjoymg4.cloudfront.net/10001/<channelId>/hls/master.m3u8?...
# (seen in a Chrome net-export for Stash TV 99991300 and MGM Presents 99951573).
# "live" = rewrite to that live URL (recommended) | "keep" = leave as-is
# "tag"  = leave as-is but move to group VOD_GROUP_TITLE | "drop" = remove from M3U and EPG
VOD_STYLE_MODE = "live"
VOD_GROUP_TITLE = "VOD-style (starts at beginning)"
VOD_LIVE_URL_TEMPLATE = (
    "https://dbrb49pjoymg4.cloudfront.net/10001/{channel_id}/hls/master.m3u8"
    "?includeAssetTags=true&ads.xumo_channelId={channel_id}&ads.xumo_streamId={channel_id}"
    "&ads.channelId={channel_id}&ads.xumo_platform=web&ads.appName=xumo&ads.appVersion=1.0.0"
    "&ads._fw_app_bundle=web.xumo.com&ads._fw_deviceMake=GitHubAction&ads._fw_device_model=PythonScript"
    "&ads._fw_did={did}&ads._fw_is_lat=0&ads._fw_coppa=0&ads._fw_content_language=en"
)

# --- Script Settings ---
API_DELAY_SECONDS = 0.5
OUTPUT_DIR = "playlists"
PLAYLIST_FILENAME = "xumo_playlist.m3u"
EPG_FILENAME = "xumo_epg.xml.gz"
TITLE_CACHE_FILENAME = "xumo_asset_titles.json"
REQUEST_TIMEOUT = 45

# !!! GitHub Repo Info !!! (used to build the EPG URL written into the M3U; change if you fork)
GITHUB_USER = "jayeAch"
GITHUB_REPO = "xumo-playlist-generator"
GITHUB_BRANCH = "main"
EPG_RAW_URL = f"https://raw.githubusercontent.com/{GITHUB_USER}/{GITHUB_REPO}/{GITHUB_BRANCH}/{OUTPUT_DIR}/{EPG_FILENAME}"

# --- Headers ---
WEB_HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/114.0.0.0 Safari/537.36',
    'Accept': 'application/json, text/plain, */*',
    'Accept-Language': 'en-US,en;q=0.9',
    'Origin': 'https://play.xumo.com',
    'Referer': 'https://play.xumo.com/',
}
ANDROID_TV_HEADERS = {'User-Agent': 'okhttp/4.9.3'}

# --- Logging ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - [%(funcName)s] %(message)s',
    stream=sys.stdout,
)


# --- Helpers ---

def fetch_data(url, params=None, is_json=True, retries=2, delay=2, headers=WEB_HEADERS, timeout=None):
    logging.debug(f"URL: {url}, Params: {params}")
    for attempt in range(retries + 1):
        response = None
        try:
            response = requests.get(url, headers=headers, params=params,
                                    timeout=timeout or REQUEST_TIMEOUT, allow_redirects=True)
            logging.debug(f"Request URL: {response.url} -> Status: {response.status_code}")
            response.raise_for_status()
            if is_json:
                if not response.content:
                    return None
                try:
                    return response.json()
                except json.JSONDecodeError as e_final:
                    logging.error(f"Error decoding JSON. Content: {response.text[:500]}... - {e_final}")
                    return None
            else:
                return response.content.decode('utf-8', errors='ignore')
        except requests.exceptions.HTTPError as e:
            logging.warning(f"Attempt {attempt+1}/{retries+1} HTTP Error: {e}")
            if response is not None:
                logging.warning(f"Error Response Content: {response.text[:500]}...")
            if attempt < retries and response is not None and response.status_code not in [401, 403, 404, 429]:
                time.sleep(delay * (attempt + 1))
            elif attempt == retries:
                return None
            else:
                break
        except requests.exceptions.RequestException as e:
            logging.warning(f"Attempt {attempt+1}/{retries+1} Network Error: {e}")
            if attempt < retries:
                time.sleep(delay * (attempt + 1))
            elif attempt == retries:
                return None
    return None


_TZ_TAIL_RE = re.compile(r'([+-])(\d{2})(\d{2})$')

def parse_iso_datetime(iso_time_str):
    if not iso_time_str:
        return None
    try:
        original_str = iso_time_str
        if iso_time_str.endswith('Z'):
            iso_time_str = iso_time_str[:-1] + '+00:00'
        if '.' in iso_time_str:
            offset_str = ""
            plus_index = iso_time_str.rfind('+')
            minus_index = iso_time_str.rfind('-')
            t_index = iso_time_str.find('T')
            offset_index = -1
            if plus_index > t_index:
                offset_index = plus_index
            if minus_index > t_index:
                offset_index = max(offset_index, minus_index)
            if offset_index != -1:
                offset_str = iso_time_str[offset_index:]
                iso_time_str = iso_time_str[:offset_index]
            iso_time_str = iso_time_str.split('.', 1)[0]
            iso_time_str += offset_str

        # Normalize "+HHMM" to "+HH:MM" for Python <= 3.10 compatibility
        iso_time_str = _TZ_TAIL_RE.sub(lambda m: f"{m.group(1)}{m.group(2)}:{m.group(3)}", iso_time_str)
        if '+' not in iso_time_str[10:] and '-' not in iso_time_str[10:]:
            iso_time_str += "+00:00"
        dt_obj = datetime.fromisoformat(iso_time_str)
        return dt_obj.astimezone(timezone.utc)
    except Exception as e:
        logging.warning(f"Parse failed for input '{original_str}': {e}")
        return None


def format_xmltv_time(dt_obj):
    if not isinstance(dt_obj, datetime):
        return ""
    if not dt_obj.tzinfo:
        dt_obj_utc = dt_obj.replace(tzinfo=timezone.utc)
    else:
        dt_obj_utc = dt_obj.astimezone(timezone.utc)
    main_part = dt_obj_utc.strftime('%Y%m%d%H%M%S')
    offset_part = dt_obj_utc.strftime('%z').replace(':', '')
    return f"{main_part} {offset_part}"


def ensure_output_dir():
    if not os.path.exists(OUTPUT_DIR):
        logging.info(f"Creating output directory: {OUTPUT_DIR}")
        try:
            os.makedirs(OUTPUT_DIR)
        except OSError as e:
            logging.error(f"Failed to create directory {OUTPUT_DIR}: {e}")
            raise


def save_gzipped_xml(tree, filepath):
    try:
        xml_partial_string = ET.tostring(tree.getroot(), encoding='unicode', method='xml')
        xml_full_string = (
            '<?xml version="1.0" encoding="UTF-8"?>\n'
            '<!DOCTYPE tv SYSTEM "xmltv.dtd">\n'
            f'{xml_partial_string}'
        )
        xml_bytes = xml_full_string.encode('utf-8')
        with gzip.open(filepath, 'wb') as f:
            f.write(xml_bytes)
        logging.info(f"Gzipped EPG XML file saved: {filepath}")
    except Exception as e:
        logging.error(f"Error writing gzipped EPG file {filepath}: {e}")


def save_xml(tree, filepath):
    try:
        ET.indent(tree.getroot())
        tree.write(filepath, encoding="utf-8", xml_declaration=True)
        logging.info(f"XML file saved: {filepath}")
    except Exception as e:
        logging.error(f"Error writing XML file {filepath}: {e}")


def save_epg(tree, filepath):
    if filepath.endswith(".gz"):
        save_gzipped_xml(tree, filepath)
    else:
        save_xml(tree, filepath)


def save_m3u(content, filepath):
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        logging.info(f"M3U playlist file saved: {filepath}")
    except Exception as e:
        logging.error(f"Error writing M3U file {filepath}: {e}")


def _strip_unknown_placeholder(m):
    logging.warning(f"Unknown URI placeholder stripped: {m.group(0)}")
    return ""


def process_stream_uri(uri):
    """Fill known ad macros, strip unknown [PLACEHOLDER]s, and drop params left blank."""
    if not uri:
        return None
    try:
        replacements = {
            '[PLATFORM]': "web",
            '[APP_VERSION]': "1.0.0",
            '[timestamp]': str(int(time.time() * 1000)),
            '[app_bundle]': "web.xumo.com",
            '[device_make]': "GitHubAction",
            '[device_model]': "PythonScript",
            '[content_language]': "en",
            '[IS_LAT]': "0",
            '[IFA]': IFA_ID,
            '[IFA_TYPE]': "aaid",
            '[SESSION_ID]': str(uuid.uuid4()),
            '[DEVICE_ID]': DEVICE_ID.replace("-", ""),
            '[CCPA_Value]': "1---",
            '[publica_site_id]': "",
            '[LAT]': "",
            '[LON]': "",
            '[OS]': "web",
            '[OS_VERSION]': "",
            '[AMZN_APP_ID]': "",
            '[app_store_url]': "",
            '[CONTENT_IMDB_GENRE]': "",
            '[IAB_content_category]': "",
            '[content_genre]': "",
            '[content_rating]': "",
        }
        for old, new in replacements.items():
            uri = uri.replace(old, new)
        uri = re.sub(r'\[([^]]+)\]', _strip_unknown_placeholder, uri)

        # Remove empty query params left behind by stripped macros (&key=).
        parsed = urlparse(uri)
        pairs = [(k, v) for k, v in parse_qsl(parsed.query, keep_blank_values=False) if v != ""]
        return urlunparse(parsed._replace(query=urlencode(pairs, doseq=True)))
    except Exception as e:
        logging.error(f"Error processing stream URI '{uri[:50]}...': {e}")
        return None


_MANIFEST_SUFFIXES = (".m3u8", ".mpd")
_INDIRECTION_TIMEOUT = (3, 5)
_INDIRECTION_MAX_BYTES = 8192


def unwrap_playlist_indirection(url):
    """Follow one hop when a channel's source is a JSON pointer, not a manifest.

    A few channels (Local Now via ottcms.weathergroup.com) answer with a bare JSON string
    holding the real playlist URL. Lenient players follow it; strict ones (Shaka etc.) fail
    with a missing #EXTM3U header. Only probed when the URL has no .m3u8/.mpd suffix, and
    any unexpected response leaves the URL unchanged.
    """
    if urlparse(url).path.lower().endswith(_MANIFEST_SUFFIXES):
        return url
    try:
        with requests.get(url, headers=WEB_HEADERS, timeout=_INDIRECTION_TIMEOUT, stream=True) as r:
            r.raise_for_status()
            clen = r.headers.get("Content-Length")
            if clen and int(clen) > _INDIRECTION_MAX_BYTES:
                return url
            body = r.raw.read(_INDIRECTION_MAX_BYTES + 1, decode_content=True)
            ctype = (r.headers.get("Content-Type") or "").split(";", 1)[0].strip().lower()
    except Exception as e:
        logging.warning(f"Indirection probe failed for {url[:80]}: {e}")
        return url
    if len(body) > _INDIRECTION_MAX_BYTES or "json" not in ctype:
        return url
    try:
        payload = json.loads(body)
    except ValueError:
        return url
    if not isinstance(payload, str):
        return url
    candidate = payload.strip()
    pc = urlparse(candidate)
    if pc.scheme not in ("http", "https") or not pc.netloc:
        return url
    logging.debug(f"Unwrapped playlist indirection: {urlparse(url).netloc} -> {pc.netloc}")
    return candidate


# --- Channel list ---

def get_channels_via_primary_list():
    logging.info(f"Attempting Primary Channel List: {PRIMARY_CHANNEL_LIST_URL}")
    data = fetch_data(PRIMARY_CHANNEL_LIST_URL, is_json=True, retries=1, headers=WEB_HEADERS)
    if not data or not isinstance(data, dict):
        logging.warning("Failed to fetch valid dictionary data from primary list endpoint.")
        return None

    channel_items = []
    if 'channel' in data and isinstance(data['channel'], dict) \
            and 'item' in data['channel'] and isinstance(data['channel']['item'], list):
        channel_items = data['channel']['item']
    elif 'items' in data and isinstance(data['items'], list):
        channel_items = data['items']
    else:
        return None

    logging.info(f"Found {len(channel_items)} potential channel items.")
    if not channel_items:
        return None

    processed_channels = []
    for item in channel_items:
        callsign = item.get('callsign', '')
        properties = item.get('properties', {})
        is_live_raw = properties.get('is_live')
        is_live = is_live_raw is True or str(is_live_raw).lower() == "true"
        is_drm = callsign.endswith("-DRM") or callsign.endswith("DRM-CMS")
        if is_drm or not is_live:
            continue

        try:
            channel_id = item.get('guid', {}).get('value')
            title = item.get('title')
            number_str = item.get('number')
            logo_url = item.get('images', {}).get('logo') or item.get('logo')
            genre_list = item.get('genre')
            genre = 'General'
            if isinstance(genre_list, list) and genre_list and isinstance(genre_list[0], dict):
                genre = genre_list[0].get('value', 'General')
            elif isinstance(genre_list, str):
                genre = genre_list

            if not channel_id or not title:
                continue

            channel_id_str = str(channel_id)
            final_logo_url = None
            if logo_url:
                if logo_url.startswith('//'):
                    final_logo_url = 'https:' + logo_url
                elif logo_url.startswith('/'):
                    final_logo_url = 'https://image.xumo.com' + logo_url
                else:
                    final_logo_url = logo_url
            else:
                final_logo_url = XUMO_LOGO_URL_TEMPLATE.replace("{channel_id}", channel_id_str)

            processed_channels.append({
                'id': channel_id_str,
                'name': title,
                'number': str(number_str) if number_str else None,
                'callsign': callsign,
                'logo': final_logo_url,
                'group': genre,
                'stream_url': None,
            })
        except Exception as e:
            pass

    if not processed_channels:
        return None

    logging.info(f"Successfully processed {len(processed_channels)} live, non-DRM channels.")
    return processed_channels


# --- Stream URLs ---

def _asset_window(asset):
    """Return (start, end) datetimes for a broadcast.json asset.
    The API gives unix seconds under asset['timestamps'] (not ISO 'start'/'end' strings)."""
    ts = asset.get('timestamps')
    if isinstance(ts, dict):
        s, e = ts.get('start'), ts.get('end')
        if isinstance(s, (int, float)) and isinstance(e, (int, float)):
            return datetime.fromtimestamp(s, timezone.utc), datetime.fromtimestamp(e, timezone.utc)
    return parse_iso_datetime(asset.get('start')), parse_iso_datetime(asset.get('end'))


def fetch_stream_urls_via_asset_lookup(channels_list):
    logging.info(f"Attempting Android TV asset lookup for {len(channels_list)} channels...")
    processed_count = 0
    channels_with_streams = []

    for i, channel_info in enumerate(channels_list):
        channel_id = channel_info['id']
        current_hour = datetime.now(timezone.utc).hour
        broadcast_url = BROADCAST_NOW_URL_TEMPLATE.format(channel_id=channel_id, hour_num=current_hour)
        broadcast_data = fetch_data(broadcast_url, is_json=True, retries=1, headers=ANDROID_TV_HEADERS)

        asset_id = None
        current_asset = None
        if broadcast_data and 'assets' in broadcast_data and broadcast_data['assets']:
            now_utc = datetime.now(timezone.utc)
            current_asset = None
            for asset in broadcast_data['assets']:
                start_time, end_time = _asset_window(asset)
                if start_time and end_time and start_time <= now_utc < end_time:
                    current_asset = asset
                    break
            if not current_asset:
                logging.warning(f"No airing asset found for channel {channel_id}; using first asset in hour block.")
                current_asset = broadcast_data['assets'][0]
            asset_id = current_asset.get('id')

        if not asset_id:
            time.sleep(API_DELAY_SECONDS)
            continue

        asset_details_url = ASSET_DETAILS_URL_TEMPLATE.format(asset_id=asset_id)
        asset_data = fetch_data(asset_details_url, is_json=True, headers=ANDROID_TV_HEADERS)

        raw_stream_uri = None
        if asset_data and 'providers' in asset_data and isinstance(asset_data['providers'], list):
            for provider in asset_data['providers']:
                if 'sources' in provider and isinstance(provider['sources'], list):
                    for source in provider['sources']:
                        if source.get('uri') and (
                                source.get('type') == 'application/x-mpegURL'
                                or source.get('uri', '').endswith('.m3u8')):
                            raw_stream_uri = source['uri']
                            break
                        elif source.get('uri') and not raw_stream_uri:
                            raw_stream_uri = source['uri']
                    if raw_stream_uri:
                        break

        if not raw_stream_uri:
            time.sleep(API_DELAY_SECONDS)
            continue

        processed_stream_url = process_stream_uri(raw_stream_uri)
        if processed_stream_url:
            processed_stream_url = unwrap_playlist_indirection(processed_stream_url)
            updated = channel_info.copy()
            updated['stream_url'] = processed_stream_url
            channels_with_streams.append(updated)
            processed_count += 1

        time.sleep(API_DELAY_SECONDS)

    logging.info(f"Asset lookup obtained stream URLs for {processed_count} channels.")
    return channels_with_streams


# --- EPG Fetching ---

ASSET_INFO_URL_TEMPLATES = [
    f"{ANDROID_TV_ENDPOINT}/assets/asset/{{asset_id}}.json?f=title&f=descriptions",
    f"{VALENCIA_API_ENDPOINT}/assets/asset/{{asset_id}}.json?f=title&f=descriptions",
]
ASSET_INFO_WORKERS = 16
ASSET_INFO_TIMEOUT = 15
ASSET_LOOKUP_BUDGET_SECONDS = 420  # stop title lookups after this; cache fills over later runs


def fetch_asset_info(asset_id):
    for tmpl, headers in zip(ASSET_INFO_URL_TEMPLATES, (ANDROID_TV_HEADERS, WEB_HEADERS)):
        data = fetch_data(tmpl.format(asset_id=asset_id), is_json=True, retries=1,
                          delay=1, headers=headers, timeout=ASSET_INFO_TIMEOUT)
        if isinstance(data, dict) and data.get('title'):
            return data
    return None


def _extract_inline_asset_info(schedule_item):
    """Extract title/description fields embedded directly in the EPG schedule item.
    The API currently returns none, so this normally yields (None, {}, None) and the
    per-asset lookup is used instead. Kept in case inline data starts appearing."""
    asset = schedule_item.get('asset')
    if not isinstance(asset, dict):
        # Some responses nest under 'assetInfo' or return fields at top level
        asset = schedule_item.get('assetInfo') if isinstance(schedule_item.get('assetInfo'), dict) else schedule_item

    title = asset.get('title') if isinstance(asset, dict) else None
    descriptions = asset.get('descriptions') if isinstance(asset, dict) else None
    episode_title = asset.get('episodeTitle') if isinstance(asset, dict) else None

    # Title may be an object like {"value": "..."} depending on API version
    if isinstance(title, dict):
        title = title.get('value') or title.get('text')
    if isinstance(title, list) and title:
        first = title[0]
        title = first.get('value') if isinstance(first, dict) else first

    if not isinstance(descriptions, dict):
        descriptions = {}

    return title, descriptions, episode_title


def discover_epg_blocks(date_str):
    """Probe which trailing path values the EPG endpoint accepts (HTTP 200 + channels)."""
    valid = []
    for b in EPG_PROBE_RANGE:
        url = EPG_FETCH_URL_TEMPLATE.format(date_str=date_str, block=b, offset=0)
        data = fetch_data(url, is_json=True, retries=0, delay=0, headers=WEB_HEADERS)
        ok = isinstance(data, dict) and isinstance(data.get('channels'), list) and len(data['channels']) > 0
        logging.info(f"EPG block probe: date={date_str} block={b} -> {'VALID' if ok else 'invalid'}")
        if ok:
            valid.append(b)
        time.sleep(API_DELAY_SECONDS)
    if not valid:
        valid = [0]
    logging.info(f"Valid EPG blocks: {valid}")
    return valid


def fetch_epg_data(channel_list):
    if not channel_list:
        return {}
    logging.info(f"Fetching EPG for {len(channel_list)} channels...")
    channel_ids_in_final_list = {ch['id'] for ch in channel_list}
    schedule_rows = []

    # Fetch yesterday plus EPG_FETCH_DAYS days (yesterday catches programmes still airing from late UTC)
    today = datetime.now(timezone.utc)
    start_day = today - timedelta(days=1)
    dates_to_fetch = [start_day + timedelta(days=d) for d in range(EPG_FETCH_DAYS + 1)]

    epg_blocks = discover_epg_blocks(dates_to_fetch[1].strftime('%Y%m%d'))  # today's date

    for date_obj in dates_to_fetch:
        date_str = date_obj.strftime('%Y%m%d')
        for block in epg_blocks:
            logging.info(f"Fetching EPG for date: {date_str} block: {block}")
            offset = 0
            seen_channels = 0
            page_idx = 0

            while page_idx < EPG_MAX_PAGES:
                page_idx += 1
                fetch_url = EPG_FETCH_URL_TEMPLATE.format(date_str=date_str, block=block, offset=offset)
                page_data = fetch_data(fetch_url, is_json=True, retries=1, delay=1, headers=WEB_HEADERS)

                if not page_data or not isinstance(page_data, dict):
                    logging.warning(f"EPG page failed: date={date_str} block={block} offset={offset}")
                    break

                channels_on_page = page_data.get('channels', [])
                if not isinstance(channels_on_page, list) or not channels_on_page:
                    break

                for cs in channels_on_page:
                    channel_id = str(cs.get('channelId'))
                    if channel_id not in channel_ids_in_final_list:
                        continue
                    for ps in cs.get('schedule', []):
                        asset_id = ps.get('assetId')
                        start = ps.get('start')
                        end = ps.get('end')
                        if not asset_id or not start or not end:
                            continue
                        inline_title, inline_desc, inline_ep = _extract_inline_asset_info(ps)
                        schedule_rows.append({
                            'channel_id': channel_id,
                            'start': start,
                            'end': end,
                            'asset_id': asset_id,
                            'inline_title': inline_title,
                            'inline_desc': inline_desc,
                            'inline_episode': inline_ep,
                        })

                n = len(channels_on_page)
                seen_channels += n
                total = page_data.get('totalChannels') or 0
                logging.debug(f"  date={date_str} block={block} offset={offset} got={n} cumulative={seen_channels}/{total}")
                offset += n

                if total and seen_channels >= total:
                    break
                time.sleep(API_DELAY_SECONDS)

    logging.info(f"EPG pages done: {len(schedule_rows)} total schedule rows collected.")

    # Drop programmes that have already ended: useless for a live guide and the
    # bulk of the title lookups.
    now_utc = datetime.now(timezone.utc)
    kept_rows = []
    for r in schedule_rows:
        end_dt = parse_iso_datetime(r['end'])
        if end_dt and end_dt >= now_utc:
            kept_rows.append(r)
    logging.info(f"Dropped {len(schedule_rows) - len(kept_rows)} already-ended rows; {len(kept_rows)} remain.")
    schedule_rows = kept_rows

    # Diagnostics for EPG Coverage
    per_channel = Counter(r['channel_id'] for r in schedule_rows)
    channels_with_epg = sum(1 for cid in channel_ids_in_final_list if per_channel.get(cid, 0) > 0)
    channels_zero = len(channel_ids_in_final_list) - channels_with_epg
    logging.info(f"EPG coverage: {channels_with_epg}/{len(channel_ids_in_final_list)} channels have programmes; {channels_zero} have none.")

    # Count inline hits vs misses (expected to be 0 with the current API)
    inline_hits = sum(1 for r in schedule_rows if r.get('inline_title'))
    logging.info(f"Inline title coverage from EPG response: {inline_hits}/{len(schedule_rows)} rows.")

    # Load Cache
    cache_path = os.path.join(OUTPUT_DIR, TITLE_CACHE_FILENAME)
    assets_cache = {}
    try:
        with open(cache_path, encoding="utf-8") as f:
            title_cache = json.load(f)
            if isinstance(title_cache, dict):
                assets_cache.update(title_cache)
    except FileNotFoundError:
        pass

    # Seed cache with inline titles (no-op while the API returns none)
    for row in schedule_rows:
        aid = row['asset_id']
        if row.get('inline_title') and not (
                isinstance(assets_cache.get(aid), dict) and assets_cache[aid].get('title')):
            assets_cache[aid] = {
                'title': row['inline_title'],
                'descriptions': row.get('inline_desc') or {},
                'episodeTitle': row.get('inline_episode'),
            }

    def has_title(aid):
        d = assets_cache.get(aid)
        return isinstance(d, dict) and bool(d.get("title"))

    first_start = {}
    for r in sorted(schedule_rows, key=lambda r: r['start']):
        first_start.setdefault(r['asset_id'], r['start'])
    # soonest-airing first, so the current/next programmes always get titles
    missing = [aid for aid, _ in sorted(first_start.items(), key=lambda kv: kv[1]) if not has_title(aid)]

    # Look up the remaining titles one asset at a time, soonest-airing first, within a time budget.
    # Anything not resolved is skipped this run and picked up on later runs via the cache.
    if missing:
        lookup_limit = len(missing)
        logging.info(f"Attempting to look up {lookup_limit} missing titles (soonest first, {ASSET_LOOKUP_BUDGET_SECONDS}s budget)...")

        found = 0
        t0 = time.time()
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=ASSET_INFO_WORKERS)
        futures = {pool.submit(fetch_asset_info, aid): aid for aid in missing[:lookup_limit]}

        try:
            for fut in concurrent.futures.as_completed(futures, timeout=ASSET_LOOKUP_BUDGET_SECONDS):
                try:
                    info = fut.result()
                except Exception:
                    info = None
                if info:
                    assets_cache[futures[fut]] = info
                    found += 1
        except concurrent.futures.TimeoutError:
            logging.warning("Asset lookup timed out. Proceeding with whatever we got.")

        pool.shutdown(wait=False, cancel_futures=True)
        logging.info(f"Asset lookup resolved {found}/{lookup_limit} in {int(time.time()-t0)}s.")

    # Save pruned cache
    try:
        live_ids = {r['asset_id'] for r in schedule_rows}
        out = {
            aid: {
                "title": d.get("title"),
                "descriptions": d.get("descriptions") or {},
                "episodeTitle": d.get("episodeTitle"),
            }
            for aid, d in assets_cache.items()
            if aid in live_ids and isinstance(d, dict) and d.get("title")
        }
        ensure_output_dir()
        with open(cache_path, "w", encoding="utf-8") as f:
            json.dump(out, f, ensure_ascii=False, separators=(",", ":"))
    except Exception as e:
        logging.warning(f"Could not write title cache: {e}")

    # Consolidate
    consolidated_epg = {ch['id']: [] for ch in channel_list}
    seen = set()
    stored = 0
    unresolved = 0
    for row in schedule_rows:
        channel_id = row['channel_id']
        start = row['start']
        asset_id = row['asset_id']
        key = (channel_id, start, asset_id)
        if key in seen:
            continue
        seen.add(key)

        details = assets_cache.get(asset_id)

        # Fallback chain: cached -> inline -> skipped (never publish a raw asset ID as the title)
        if details and details.get('title'):
            title = details.get('title')
            descriptions = details.get('descriptions') or {}
            episode_title = details.get('episodeTitle')
        elif row.get('inline_title'):
            title = row['inline_title']
            descriptions = row.get('inline_desc') or {}
            episode_title = row.get('inline_episode')
        else:
            # Unresolved asset: skip rather than publish a raw ID like "XM0WYASIG6RGO3"
            unresolved += 1
            continue

        consolidated_epg[channel_id].append({
            'start': start,
            'end': row['end'],
            'assetId': asset_id,
            'title': title,
            'descriptions': descriptions,
            'episodeTitle': episode_title,
        })
        stored += 1

    logging.info(f"Consolidated: {len(schedule_rows)} raw rows -> {stored} stored, {unresolved} skipped (no title).")
    return consolidated_epg


# --- Generate XML & M3U ---

def generate_epg_xml(channel_list_with_streams, consolidated_epg_data):
    logging.info("Generating EPG XML structure...")
    tv_element = ET.Element('tv', attrib={'generator-info-name': f'{GITHUB_USER}-{GITHUB_REPO}'})
    programme_count = 0
    channel_ids_in_list = {c['id'] for c in channel_list_with_streams}

    for channel in channel_list_with_streams:
        chan_el = ET.SubElement(tv_element, 'channel', attrib={'id': channel['id']})
        ET.SubElement(chan_el, 'display-name').text = channel['name']
        if channel['logo']:
            ET.SubElement(chan_el, 'icon', attrib={'src': channel['logo']})

    for channel_id, programs in consolidated_epg_data.items():
        if channel_id not in channel_ids_in_list:
            continue
        for program in programs:
            try:
                start_time = parse_iso_datetime(program.get('start'))
                end_time = parse_iso_datetime(program.get('end'))
                if not start_time or not end_time:
                    continue

                title = program.get('title', 'Unknown Program')
                desc_obj = program.get('descriptions', {})
                desc = (desc_obj.get('large') or desc_obj.get('medium')
                        or desc_obj.get('small') or desc_obj.get('tiny'))
                episode_title = program.get('episodeTitle')
                asset_id = program.get('assetId')

                start_formatted = format_xmltv_time(start_time)
                stop_formatted = format_xmltv_time(end_time)
                if not start_formatted or not stop_formatted:
                    continue

                prog_el = ET.SubElement(tv_element, 'programme', attrib={
                    'start': start_formatted,
                    'stop': stop_formatted,
                    'channel': channel_id,
                })
                ET.SubElement(prog_el, 'title', attrib={'lang': 'en'}).text = title
                if desc:
                    ET.SubElement(prog_el, 'desc', attrib={'lang': 'en'}).text = desc
                if episode_title and episode_title != title:
                    ET.SubElement(prog_el, 'sub-title', attrib={'lang': 'en'}).text = episode_title
                if asset_id:
                    system_type = "dd_progid" if asset_id.startswith("EP") else "dd_assetid"
                    ET.SubElement(prog_el, 'episode-num', attrib={'system': system_type}).text = asset_id
                programme_count += 1
            except Exception:
                pass

    logging.info(f"Generated XML: {len(channel_list_with_streams)} channels, {programme_count} programmes.")
    return ET.ElementTree(tv_element)


def generate_m3u_playlist(channel_list_with_streams, epg_url=None):
    logging.info("Generating M3U playlist...")
    playlist_parts = [f'#EXTM3U url-tvg="{epg_url}"\n' if epg_url else '#EXTM3U\n']
    added_count = 0

    def sort_key(channel):
        try:
            num = int(channel.get('number', '999999'))
            return (num, channel['name'].lower())
        except (ValueError, TypeError):
            return (999999, channel['name'].lower())

    sorted_channels = sorted(channel_list_with_streams, key=sort_key)
    for channel in sorted_channels:
        stream_url = channel.get('stream_url')
        channel_id = channel['id']
        display_name = channel['name'].replace(',', ';')
        group_title = channel.get('group', 'General').replace(',', ';')
        tvg_name = channel['name'].replace('"', "'")
        logo = channel.get("logo", "")

        if stream_url:
            playlist_parts.append(
                f'#EXTINF:-1 tvg-id="{channel_id}" tvg-name="{tvg_name}" '
                f'tvg-logo="{logo}" group-title="{group_title}",{display_name}\n'
            )
            playlist_parts.append(f'{stream_url}\n')
            added_count += 1
        else:
            logging.error(f"Channel {channel_id} ({channel['name']!r}) reached M3U without stream URL!")

    logging.info(f"Added {added_count} channels with stream URLs to M3U.")
    return "".join(playlist_parts)


# --- Main ---

def main():
    global OUTPUT_DIR, PLAYLIST_FILENAME, EPG_FILENAME

    ap = argparse.ArgumentParser(description="Xumo Play m3u + XMLTV extractor")
    ap.add_argument("--out-dir", default=OUTPUT_DIR, help="output directory (created if missing)")
    ap.add_argument("--m3u", default=PLAYLIST_FILENAME, help="playlist filename (relative to --out-dir)")
    ap.add_argument("--epg", default=EPG_FILENAME, help="XMLTV filename (relative to --out-dir); .gz = gzipped")
    ap.add_argument("--no-epg", action="store_true", help="playlist only")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    explicit_epg = args.epg != EPG_FILENAME
    OUTPUT_DIR, PLAYLIST_FILENAME, EPG_FILENAME = args.out_dir, args.m3u, args.epg
    # Relative filename when --epg is given (matches the other generators); the raw GitHub
    # URL only for the default name.
    if args.no_epg:
        epg_url = None
    else:
        epg_url = EPG_FILENAME if explicit_epg else EPG_RAW_URL
    m3u_path = os.path.join(OUTPUT_DIR, PLAYLIST_FILENAME)
    epg_path = os.path.join(OUTPUT_DIR, EPG_FILENAME)

    logging.info(f"--- Starting Xumo Scraper (Primary List ID: {PRIMARY_LIST_ID}) ---")
    try:
        ensure_output_dir()
    except Exception as e:
        logging.error(f"Halting: cannot ensure output dir: {e}")
        return 1

    logging.info(f"Step 1: Getting channel metadata via Primary List endpoint ({PRIMARY_LIST_ID})...")
    primary_channel_list = get_channels_via_primary_list()
    if not primary_channel_list:
        logging.error("Failed to get primary channel list. Aborting.")
        return 1

    logging.info(f"Step 2: Fetching stream URLs via asset lookup for {len(primary_channel_list)} channels...")
    channels = fetch_stream_urls_via_asset_lookup(primary_channel_list)
    if not channels:
        logging.error("No channels with stream URLs found.")
        return 1

    vod_style = [c for c in channels if '/content/' in (c.get('stream_url') or '')]
    logging.info(f"{len(vod_style)} VOD-style channels detected (mode={VOD_STYLE_MODE}).")
    if VOD_STYLE_MODE == "drop":
        vod_ids = {c['id'] for c in vod_style}
        channels = [c for c in channels if c['id'] not in vod_ids]
    elif VOD_STYLE_MODE == "live":
        for c in vod_style:
            c['stream_url'] = VOD_LIVE_URL_TEMPLATE.format(channel_id=c['id'], did=uuid.uuid4())
    elif VOD_STYLE_MODE == "tag":
        for c in vod_style:
            c['group'] = VOD_GROUP_TITLE
    logging.info(f"Proceeding with {len(channels)} channels with stream URLs.")

    epg_tree = None
    if not args.no_epg:
        logging.info("Step 3: Fetching EPG data...")
        epg_data = fetch_epg_data(channels)
        logging.info("Step 4: Generating EPG XML...")
        epg_tree = generate_epg_xml(channels, epg_data)

    logging.info("Step 5: Generating M3U playlist...")
    m3u_content = generate_m3u_playlist(channels, epg_url)

    logging.info("Step 6: Saving files...")
    save_m3u(m3u_content, m3u_path)
    if epg_tree is not None:
        save_epg(epg_tree, epg_path)

    logging.info("--- Xumo Scraper Finished Successfully ---")
    return 0


if __name__ == "__main__":
    sys.exit(main())
