import os
import json
import re
import asyncio
import time
import requests
from datetime import datetime, timezone, date, timedelta
from zoneinfo import ZoneInfo
from statistics import mean, median
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import quote, urlsplit

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, CopyTextButton
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, filters

# ============================================================
# GOODBOT V8.4 HOLDER-ATH-TRADING-LINK FIX
# ============================================================

BOT_TOKEN = os.getenv("BOT_TOKEN")
DEX_API = "https://api.dexscreener.com"
RUGCHECK_API = "https://api.rugcheck.xyz/v1"
BUBBLEMAPS_API = "https://api.bubblemaps.io/v0"
BUBBLEMAPS_API_KEY = os.getenv("BUBBLEMAPS_API_KEY", "").strip()
GECKO_API = "https://api.geckoterminal.com/api/v2"
PUMPPORTAL_API_KEY = os.getenv("PUMPPORTAL_API_KEY", "").strip()
# BONKbot's documented CA deep link requires a valid referral code.
# Leave blank to open BONKbot normally; set your actual code to enable CA forwarding.
BONKBOT_REF_CODE = os.getenv("BONKBOT_REF_CODE", "").strip()
PUMPPORTAL_WS_URL = "wss://pumpportal.fun/api/data"
PUMPPORTAL_FILE = os.path.join(os.getenv("GOODBOT_DATA_DIR", "."), "goodbot_pumpportal_recent.json")

# -------------------- Strategy --------------------
MIN_MC = 5_000
MAX_MC = 1_000_000
MIN_LIQUIDITY = 5_000
MIN_VOLUME_24H = 2_500
MIN_SIGNAL_SCORE = 80
# Automatic runner signals require a verifiable market-pair age of at least 3 hours.
MIN_AUTO_TOKEN_AGE_MINUTES = 180
# For the first 24 hours, new-token discovery signals must remain below this MC.
MAX_AUTO_NEW_TOKEN_AGE_MINUTES = 24 * 60
MAX_AUTO_NEW_TOKEN_MC = 60_000
# Bundle/cluster share above this level blocks automatic signals when available.
MAX_AUTO_BUNDLE_CLUSTER_PCT = 15.0
MAX_DEEP_CHECKS_PER_SCAN = 18
AUTO_SCAN_SECONDS = 90
ALERT_COOLDOWN_SECONDS = 6 * 60 * 60
RISK_CACHE_SECONDS = 5 * 60
BUBBLE_CACHE_SECONDS = 15 * 60
bubble_cache = {}
HOLDER_CACHE_SECONDS = 5 * 60
HOLDER_NEGATIVE_CACHE_SECONDS = 60
HOLDER_REQUEST_TIMEOUT = 4
MAX_RESULTS = 10
REQUEST_TIMEOUT = 15

BLOCKED_SYMBOLS = {"SOL", "WSOL", "USDC", "USDT", "USDC.E", "USDT.E"}

# Chat IDs are kept in memory. After a Railway restart, send /start again.
DATA_DIR = os.getenv("GOODBOT_DATA_DIR", ".")
os.makedirs(DATA_DIR, exist_ok=True)
CHAT_IDS_FILE = os.path.join(DATA_DIR, "goodbot_chat_ids.json")
ATH_FILE = os.path.join(DATA_DIR, "goodbot_tracked_ath.json")
SIGNALS_FILE = os.path.join(DATA_DIR, "goodbot_signal_history.json")
REPORT_STATE_FILE = os.path.join(DATA_DIR, "goodbot_report_state.json")
MANUAL_TRACKING_FILE = os.path.join(DATA_DIR, "goodbot_manual_tracking.json")
AUTO_SIGNAL_STATE_FILE = os.path.join(DATA_DIR, "goodbot_auto_signal_state.json")
UPDATES_CHANNEL_URL = os.getenv("TG_CHANNEL_URL", "https://t.me/TheLuminaAi").strip()
DISCUSSION_GROUP_URL = os.getenv("TG_GROUP_URL", "").strip()
WAT = ZoneInfo("Africa/Lagos")
TRACKING_REFRESH_SECONDS = 300
TRACKING_MAX_AGE_DAYS = 30
DAILY_REPORT_HOUR = 23
DAILY_REPORT_MINUTE = 59


def load_json_file(path, default):
    try:
        with open(path, "r", encoding="utf-8") as handle:
            value = json.load(handle)
        return value if isinstance(value, type(default)) else default
    except (OSError, ValueError, TypeError):
        return default


def save_json_file(path, value):
    try:
        temp_path = path + ".tmp"
        with open(temp_path, "w", encoding="utf-8") as handle:
            json.dump(value, handle, separators=(",", ":"))
        os.replace(temp_path, path)
    except OSError as exc:
        print(f"Could not save {os.path.basename(path)}: {exc}")


# Saved locally to survive process restarts. For persistence across Railway redeploys,
# attach a Railway Volume and set GOODBOT_DATA_DIR to its mount path.
known_chat_ids = {int(value) for value in load_json_file(CHAT_IDS_FILE, []) if str(value).lstrip("-").isdigit()}


def private_chat_ids():
    """Return every registered personal user eligible for public bot broadcasts. Telegram private-chat IDs are positive; group/supergroup IDs are negative and are never included. Each person must open the bot and press /start at least once because Telegram does not allow bots to initiate a private conversation first. """
    return sorted({int(chat_id) for chat_id in known_chat_ids if int(chat_id) > 0})
alert_history = {}
risk_cache = {}
dex_paid_cache = {}
DEX_PAID_CACHE_SECONDS = 5 * 60
# This is the highest MC observed by GoodBot, not a guaranteed lifetime ATH.
tracked_ath = load_json_file(ATH_FILE, {})
gecko_ath_cache = {}
GECKO_ATH_CACHE_SECONDS = 60 * 60
signal_history = load_json_file(SIGNALS_FILE, {})
manual_tracking = load_json_file(MANUAL_TRACKING_FILE, {})
auto_signal_state = load_json_file(AUTO_SIGNAL_STATE_FILE, {})
token_metadata_cache = {}
solscan_holder_cache = {}
report_state = load_json_file(REPORT_STATE_FILE, {"last_daily_report": ""})
pumpportal_recent = load_json_file(PUMPPORTAL_FILE, [])
last_tracking_refresh = 0.0
last_oversold_scan = 0.0
scan_lock = asyncio.Lock()


# ============================================================
# SAFE HELPERS
# ============================================================

def get_num(value, default=0.0):
    try:
        if value is None or value == "":
            return default
        return float(value)
    except (TypeError, ValueError):
        return default


def pct(value):
    return f"{get_num(value):.1f}%"


def money(value):
    value = get_num(value)
    if value >= 1_000_000:
        return f"${value / 1_000_000:.2f}M"
    if value >= 1_000:
        return f"${value / 1_000:.1f}K"
    return f"${value:.0f}"


def short_address(address):
    if not address:
        return "N/A"
    return f"{address[:5]}…{address[-5:]}"


def clamp(value, low=0, high=100):
    return max(low, min(high, value))


def market_value(pair):
    """Return market cap when supplied, otherwise FDV as a screening proxy. Callers that display this value must use market_value_label() so FDV is not presented as a confirmed market capitalization. """
    market_cap = get_num((pair or {}).get("marketCap"))
    if market_cap > 0:
        return market_cap
    return get_num((pair or {}).get("fdv"))


def market_value_label(pair):
    """Describe whether the displayed valuation is market cap or an FDV proxy."""
    if get_num((pair or {}).get("marketCap")) > 0:
        return "Market Cap"
    if get_num((pair or {}).get("fdv")) > 0:
        return "FDV (market cap unavailable)"
    return "Market Cap unavailable"


def safe_get_json(url, params=None):
    try:
        r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
        if r.status_code == 429:
            return None
        if not r.ok:
            return None
        return r.json()
    except requests.RequestException:
        return None
    except ValueError:
        return None


def token_age_minutes(pair):
    created = pair.get("pairCreatedAt")
    if not created:
        return None
    try:
        created_ms = float(created)
        return max(0, (time.time() * 1000 - created_ms) / 60000)
    except (TypeError, ValueError):
        return None


def age_text(minutes):
    if minutes is None:
        return "N/A"
    if minutes < 60:
        return f"{minutes:.0f}m"
    if minutes < 1440:
        return f"{minutes / 60:.1f}h"
    return f"{minutes / 1440:.1f}d"


def now_wat():
    return datetime.now(WAT)


def day_key(timestamp=None):
    if timestamp is None:
        return now_wat().date().isoformat()
    return datetime.fromtimestamp(float(timestamp), WAT).date().isoformat()


def narrative_tags(name, symbol, pair=None):
    """Return cautious narrative hints using token metadata and available socials."""
    parts = [str(name or ""), str(symbol or "")]
    if isinstance(pair, dict):
        info = pair.get("info") or {}
        for key in ("header", "description", "title"):
            value = info.get(key)
            if value:
                parts.append(str(value))
        try:
            socials = extract_socials(pair)
            # URLs are weak evidence; include them to help identify explicit project domains,
            # but never treat a URL match as proof of the project's claims.
            parts.extend(str(socials.get(key) or "") for key in ("website", "x", "telegram"))
        except Exception:
            pass
    text = " ".join(parts).lower()
    padded = f" {re.sub(r'[^a-z0-9]+', ' ', text)} "
    groups = {
        "AI / AGENTS": (" artificial intelligence ", " ai ", " ai agent ", " ai agents ", " agentic ", " gpt ", " llm ", " neural ", " machine learning ", " robot "),
        "ANIMAL/MEME": (" cat ", " dog ", " frog ", " pepe ", " shib ", " inu ", " bear ", " bull ", " monkey ", " meme coin "),
        "POLITICS": (" trump ", " maga ", " politic ", " president ", " election ", " campaign "),
        "CULTURE/VIRAL": (" viral ", " trend ", " brainrot ", " meme ", " internet culture ", " sigma ", " chad "),
        "GAMING": (" game ", " gaming ", " pixel ", " arcade ", " play to earn ", " videogame "),
        "DEPIN": (" depin ", " decentralized physical infrastructure ", " wireless network ", " distributed compute "),
        "DEFI": (" defi ", " decentralized finance ", " liquidity pool ", " yield farming ", " lending protocol ", " dex "),
        "INFRASTRUCTURE": (" infrastructure ", " rpc provider ", " developer tools ", " blockchain infrastructure ", " sdk "),
        "RWA": (" real world asset ", " tokenized asset ", " tokenization ", " rwa "),
        "ORACLE/DATA": (" oracle network ", " price feed ", " data oracle ", " on chain data "),
        "PRIVACY": (" privacy protocol ", " private transaction ", " zero knowledge ", " zero-knowledge "),
        "SOLANA ECOSYSTEM": (" solana ecosystem ", " solana protocol ", " spl token ", " solana builder "),
    }
    found = []
    for label, phrases in groups.items():
        if any(phrase in padded for phrase in phrases):
            found.append(label)
    return found[:2]


def price_changes(pair):
    pc = pair.get("priceChange") or {}
    return {
        "5m": get_num(pc.get("m5")),
        "1h": get_num(pc.get("h1")),
        "6h": get_num(pc.get("h6")),
        "24h": get_num(pc.get("h24")),
    }


def extract_socials(pair):
    info = pair.get("info") or {}
    websites = info.get("websites") or []
    socials = info.get("socials") or []
    website = x = telegram = None

    for item in websites:
        url = item.get("url") if isinstance(item, dict) else None
        if url and not website:
            website = url

    for item in socials:
        if not isinstance(item, dict):
            continue
        platform = str(item.get("platform") or item.get("type") or "").lower()
        url = item.get("url")
        handle = str(item.get("handle") or "").strip().lstrip("@")
        if not url and handle:
            if platform in {"twitter", "x"}:
                url = f"https://x.com/{handle}"
            elif platform in {"telegram", "tg"}:
                url = f"https://t.me/{handle}"
        if platform in {"twitter", "x"} and url and not x:
            x = url
        elif platform in {"telegram", "tg"} and url and not telegram:
            telegram = url

    if not x:
        x = info.get("twitter") or info.get("x")
    if not telegram:
        telegram = info.get("telegram")
    if not website:
        website = info.get("website")
    return {"website": website, "x": x, "telegram": telegram}


def get_solscan_holder_total(mint, force=False):
    """Read Solscan's reported token-holder total, or return None if unavailable. This is explicitly labelled as a Solscan-reported total in cards. The endpoint's precise holder semantics must not be assumed to prove wallet-level uniqueness. """
    if not mint:
        return None
    now = time.time()
    cached = solscan_holder_cache.get(mint)
    if cached and not force:
        ttl = HOLDER_CACHE_SECONDS if cached.get("count") is not None else HOLDER_NEGATIVE_CACHE_SECONDS
        if now - get_num(cached.get("time")) < ttl:
            return cached.get("count")
    count = None
    try:
        response = requests.get(
            "https://api-v2.solscan.io/v2/token/holders",
            params={"address": mint, "page_size": 1, "page": 1},
            timeout=HOLDER_REQUEST_TIMEOUT,
            headers={"User-Agent": "GoodBot/8.4"},
        )
        if response.ok:
            payload = response.json()
            data = payload.get("data") if isinstance(payload, dict) else None
            if not isinstance(data, dict):
                data = payload if isinstance(payload, dict) else {}
            raw_total = data.get("total")
            if raw_total is None:
                raw_total = data.get("total_count")
            if raw_total is None and isinstance(payload, dict):
                raw_total = payload.get("total")
            if raw_total is not None and not isinstance(raw_total, bool):
                parsed = int(float(raw_total))
                if parsed >= 0:
                    count = parsed
        elif response.status_code not in (404, 429):
            print(f"Solscan holder lookup returned HTTP {response.status_code} for {mint[:8]}…")
    except (requests.RequestException, ValueError, TypeError, AttributeError, OverflowError) as exc:
        print(f"Solscan holder lookup failed for {mint[:8]}…: {exc}")
    solscan_holder_cache[mint] = {"time": now, "count": count}
    return count


def attach_holder_counts(analyses):
    """Fetch holder totals only for results we may show, using bounded concurrency."""
    if not analyses:
        return analyses
    unique = {}
    for analysis in analyses:
        mint = str(analysis.get("address") or "").strip()
        if mint:
            unique[mint] = None
        else:
            analysis["holder_count"] = None
    if not unique:
        return analyses
    with ThreadPoolExecutor(max_workers=min(4, len(unique))) as executor:
        futures = {executor.submit(get_solscan_holder_total, mint): mint for mint in unique}
        for future in as_completed(futures):
            mint = futures[future]
            try:
                unique[mint] = future.result()
            except Exception as exc:
                print(f"Holder lookup worker failed for {mint[:8]}…: {exc}")
                unique[mint] = None
    for analysis in analyses:
        mint = str(analysis.get("address") or "").strip()
        solscan_count = unique.get(mint) if mint else None
        analysis["holder_count"] = solscan_count
        analysis["holder_source"] = "Solscan" if solscan_count is not None else None
        # RugCheck already supplies a reported total in its full token report.
        # Use it as a fallback instead of showing unavailable when Solscan fails.
        if solscan_count is None:
            rugcheck_count = get_num(((analysis.get("risk") or {}).get("holders")))
            if rugcheck_count > 0:
                analysis["holder_count"] = int(rugcheck_count)
                analysis["holder_source"] = "RugCheck"
    return analyses


def track_ath(pair):
    """Track the highest market cap/price GoodBot has observed for this token."""
    address, _, _ = normalize_market_pair(pair)
    if not address:
        return {}

    mc = get_num(pair.get("marketCap"))
    price = get_num(pair.get("priceUsd"))
    previous = tracked_ath.get(address, {})
    changed = False

    if not previous:
        previous = {"mc": 0.0, "price": 0.0, "first_seen": time.time(), "observations": 0}
        changed = True

    if mc > get_num(previous.get("mc")):
        previous["mc"] = mc
        changed = True
    if price > get_num(previous.get("price")):
        previous["price"] = price
        changed = True

    previous["observations"] = int(get_num(previous.get("observations"))) + 1
    previous["updated"] = time.time()
    tracked_ath[address] = previous
    # Persist new highs and first observations, not every unchanged poll.
    if changed:
        save_json_file(ATH_FILE, tracked_ath)
    return previous


def historical_ath_mc(pair, include_other_pools=False):
    """Estimate historical ATH market cap from GeckoTerminal on-chain pool OHLCV. DexScreener supplies current pair metrics but not a lifetime ATH endpoint. GeckoTerminal provides OHLCV per pool, so inspect the active pool and (for final scans/signals) other pools for this mint. Historical MC is estimated by scaling the highest observed USD price by the current MC/price ratio; this assumes circulating/fully diluted supply is stable. """
    pool = str(pair.get("pairAddress") or "").strip()
    mint = str(((pair.get("baseToken") or {}).get("address")) or "").strip()
    current_price = get_num(pair.get("priceUsd"))
    current_mc = get_num(pair.get("marketCap"))
    if not pool or current_price <= 0 or current_mc <= 0:
        return None

    now = time.time()
    cache_key = f"solana:{mint or pool}:{'deep' if include_other_pools else 'shallow'}"
    cached = gecko_ath_cache.get(cache_key)
    if cached:
        cache_ttl = GECKO_ATH_CACHE_SECONDS if cached.get("ath_mc") else 5 * 60
        if now - cached.get("time", 0) < cache_ttl:
            return cached.get("ath_mc")

    headers = {"Accept": "application/json;version=20230203"}

    def pool_high(pool_address, token_side="base"):
        try:
            response = requests.get(
                f"{GECKO_API}/networks/solana/pools/{pool_address}/ohlcv/day",
                params={"aggregate": 1, "limit": 1000, "currency": "usd", "token": token_side},
                headers=headers,
                timeout=5,
            )
            if not response.ok:
                print(f"GeckoTerminal OHLCV returned HTTP {response.status_code} for {pool_address[:8]}…")
                return None
            payload = response.json()
            candles = (((payload.get("data") or {}).get("attributes") or {}).get("ohlcv_list") or [])
            # GeckoTerminal OHLCV rows normally contain [timestamp, open, high, low, close, volume].
            # Require an actual volume field and non-zero observed activity, but do not impose
            # a fixed $500 threshold because the returned volume unit may not be USD.
            valid_highs = [
                get_num(candle[2]) for candle in candles
                if isinstance(candle, list)
                and len(candle) >= 6
                and get_num(candle[2]) > 0
                and get_num(candle[5]) > 0
            ]
            return max(valid_highs) if valid_highs else None
        except (requests.RequestException, ValueError, TypeError, AttributeError) as exc:
            print(f"GeckoTerminal ATH lookup failed for pool {pool_address[:8]}…: {exc}")
            return None

    pool_highs = [pool_high(pool, "base")]

    # For user-facing scans/signals, always check alternate pools. This is important
    # when a token migrated and its old ATH happened in a previous pool. Keep the number
    # of calls bounded because GeckoTerminal's public API is rate limited.
    if include_other_pools and mint:
        try:
            response = requests.get(
                f"{GECKO_API}/networks/solana/tokens/{mint}/pools",
                params={"page": 1}, headers=headers, timeout=5,
            )
            if response.ok:
                payload = response.json()
                ranked = []
                for item in payload.get("data") or []:
                    attrs = item.get("attributes") or {}
                    other_pool = str(attrs.get("address") or item.get("id", "").split("_", 1)[-1]).strip()
                    if not other_pool or other_pool == pool:
                        continue
                    relationships = item.get("relationships") or {}
                    base_id = str((((relationships.get("base_token") or {}).get("data") or {}).get("id")) or "")
                    quote_id = str((((relationships.get("quote_token") or {}).get("data") or {}).get("id")) or "")
                    base_address = str(attrs.get("base_token_address") or base_id.split("_", 1)[-1]).strip()
                    quote_address = str(attrs.get("quote_token_address") or quote_id.split("_", 1)[-1]).strip()
                    if base_address == mint:
                        token_side = "base"
                    elif quote_address == mint:
                        token_side = "quote"
                    else:
                        continue
                    reserve = get_num(attrs.get("reserve_in_usd"))
                    volume = get_num((attrs.get("volume_usd") or {}).get("h24"))
                    ranked.append((reserve, volume, other_pool, token_side))
                ranked.sort(reverse=True)
                for _, _, other_pool, token_side in ranked[:3]:
                    pool_highs.append(pool_high(other_pool, token_side))
            else:
                print(f"GeckoTerminal token-pools lookup returned HTTP {response.status_code} for {mint[:8]}…")
        except (requests.RequestException, ValueError, TypeError, AttributeError) as exc:
            print(f"GeckoTerminal token-pools lookup failed for {mint[:8]}…: {exc}")

    # Do not label current price as a historical ATH when no historical candles were returned.
    valid_highs = [value for value in pool_highs if value is not None and value > 0]
    if not valid_highs:
        gecko_ath_cache[cache_key] = {"time": now, "ath_mc": None, "pool_count": 0}
        return None

    highest_price = max([current_price] + valid_highs)
    ath_mc = current_mc * highest_price / current_price
    if ath_mc > 0:
        gecko_ath_cache[cache_key] = {"time": now, "ath_mc": ath_mc, "pool_count": len(valid_highs)}
        return ath_mc

    gecko_ath_cache[cache_key] = {"time": now, "ath_mc": None, "pool_count": len(valid_highs)}
    return None


def normalize_market_pair(pair):
    base = pair.get("baseToken") or {}
    address = base.get("address")
    symbol = str(base.get("symbol") or "").strip()
    name = str(base.get("name") or "").strip()
    if not symbol or symbol.upper() == "UNKNOWN":
        symbol = name if name and name.upper() != "UNKNOWN" else "UNKNOWN"
    if not name or name.upper() == "UNKNOWN":
        name = symbol if symbol and symbol.upper() != "UNKNOWN" else "Unknown token"
    return address, symbol or "UNKNOWN", name or "Unknown token"


def enrich_token_metadata(pair, mint):
    """Retry token name/symbol lookups when a pool response contains UNKNOWN metadata."""
    base = pair.setdefault("baseToken", {})
    name = str(base.get("name") or "").strip()
    symbol = str(base.get("symbol") or "").strip()
    if name and symbol and name.upper() != "UNKNOWN" and symbol.upper() != "UNKNOWN":
        return pair
    now = time.time()
    cached = token_metadata_cache.get(mint)
    if cached:
        cached_metadata = cached.get("metadata") or {}
        has_cached_name = bool(cached_metadata.get("name") or cached_metadata.get("symbol"))
        cache_ttl = 3600 if has_cached_name else 60
        metadata = cached_metadata if now - cached.get("time", 0) < cache_ttl else None
    else:
        metadata = None
    if metadata is None:
        metadata = {}
        # GeckoTerminal token metadata endpoint is a separate lookup from pool data.
        try:
            response = requests.get(
                f"{GECKO_API}/networks/solana/tokens/{mint}",
                headers={"Accept": "application/json;version=20230302"}, timeout=4,
            )
            if response.ok:
                attrs = ((response.json().get("data") or {}).get("attributes") or {})
                metadata = {"name": attrs.get("name"), "symbol": attrs.get("symbol")}
        except (requests.RequestException, ValueError, TypeError, AttributeError) as exc:
            print(f"Token metadata lookup failed for {mint[:6]}…: {exc}")
        token_metadata_cache[mint] = {"time": now, "metadata": metadata}
    resolved_name = str(metadata.get("name") or "").strip()
    resolved_symbol = str(metadata.get("symbol") or "").strip()
    if resolved_name and resolved_name.upper() != "UNKNOWN":
        base["name"] = resolved_name
    if resolved_symbol and resolved_symbol.upper() != "UNKNOWN":
        base["symbol"] = resolved_symbol
    # If one field is available, use it as a reasonable fallback for the other.
    if not base.get("name") or str(base.get("name")).upper() == "UNKNOWN":
        base["name"] = base.get("symbol") or "Unknown token"
    if not base.get("symbol") or str(base.get("symbol")).upper() == "UNKNOWN":
        base["symbol"] = base.get("name") or "UNKNOWN"
    return pair


# ============================================================
# DEXSCREENER DISCOVERY / MARKET DATA
# ============================================================

def discover_addresses():
    # PumpPortal's optional free new-token/migration stream helps discover launchpad
    # mints earlier than pool-only feeds. It does not invent price/liquidity data.
    cutoff = time.time() - 24 * 3600
    addresses = [
        item.get("mint") for item in pumpportal_recent
        if isinstance(item, dict) and item.get("mint") and get_num(item.get("seen_at")) >= cutoff
    ]

    for endpoint in [
        f"{DEX_API}/token-profiles/latest/v1",
        f"{DEX_API}/community-takeovers/latest/v1",
        f"{DEX_API}/ads/latest/v1",
        f"{DEX_API}/token-boosts/latest/v1",
        f"{DEX_API}/token-boosts/top/v1",
    ]:
        data = safe_get_json(endpoint)
        if not isinstance(data, list):
            continue
        for item in data:
            if str(item.get("chainId", "")).lower() != "solana":
                continue
            address = item.get("tokenAddress")
            if address:
                addresses.append(address)

    # Preserve order while removing duplicates.
    return list(dict.fromkeys(addresses))


def _gecko_pool_to_pair(item, included=None):
    """Normalize GeckoTerminal pool data into the small common market shape GoodBot uses."""
    if not isinstance(item, dict):
        return None
    attrs = item.get("attributes") or {}
    rel = item.get("relationships") or {}
    included = included or []
    included_by_id = {x.get("id"): x.get("attributes", {}) for x in included if isinstance(x, dict)}
    base_id = ((rel.get("base_token") or {}).get("data") or {}).get("id")
    quote_id = ((rel.get("quote_token") or {}).get("data") or {}).get("id")
    base = included_by_id.get(base_id, {})
    quote = included_by_id.get(quote_id, {})
    mint = str(base_id or "").split("_", 1)[-1] if base_id else ""
    if not mint:
        mint = attrs.get("base_token_address") or ""
    if not mint:
        return None
    volume = attrs.get("volume_usd") or {}
    txns = attrs.get("transactions") or {}
    changes = attrs.get("price_change_percentage") or {}
    h1 = txns.get("h1") or {}
    h24 = txns.get("h24") or {}
    liq = get_num(attrs.get("reserve_in_usd"))
    # Keep market cap and FDV separate; downstream screening may use FDV as a
    # proxy, but user-facing cards must identify that basis explicitly.
    mc = get_num(attrs.get("market_cap_usd"))
    fdv = get_num(attrs.get("fdv_usd"))
    created = attrs.get("pool_created_at")
    created_ms = None
    if created:
        try:
            created_ms = int(datetime.fromisoformat(str(created).replace("Z", "+00:00")).timestamp() * 1000)
        except (ValueError, TypeError, OverflowError):
            pass
    return {
        "chainId": "solana", "dexId": "geckoterminal", "url": f"https://www.geckoterminal.com/solana/pools/{item.get('id', '').split('_', 1)[-1]}",
        "pairAddress": str(item.get("id", "")).split("_", 1)[-1],
        "baseToken": {"address": mint, "name": base.get("name") or attrs.get("name") or "UNKNOWN", "symbol": base.get("symbol") or "UNKNOWN"},
        "quoteToken": {"address": str(quote_id or "").split("_", 1)[-1], "name": quote.get("name") or "", "symbol": quote.get("symbol") or ""},
        "priceUsd": attrs.get("base_token_price_usd"), "marketCap": mc if mc > 0 else None, "fdv": fdv if fdv > 0 else None,
        "liquidity": {"usd": liq}, "volume": {"h1": get_num(volume.get("h1")), "h24": get_num(volume.get("h24"))},
        "txns": {"h1": {"buys": get_num(h1.get("buys")), "sells": get_num(h1.get("sells"))}, "h24": {"buys": get_num(h24.get("buys")), "sells": get_num(h24.get("sells"))}},
        "priceChange": {"m5": get_num(changes.get("m5")), "h1": get_num(changes.get("h1")), "h6": get_num(changes.get("h6")), "h24": get_num(changes.get("h24"))},
        "pairCreatedAt": created_ms, "info": {}, "_source": "GeckoTerminal",
    }


def gecko_discover_pools():
    """Supplement DexScreener discovery with GeckoTerminal new and trending pools."""
    markets = []
    headers = {"Accept": "application/json;version=20230302"}
    for endpoint in ("new_pools", "trending_pools"):
        url = f"{GECKO_API}/networks/solana/{endpoint}"
        try:
            response = requests.get(url, headers=headers, params={"page": 1}, timeout=8)
            if not response.ok:
                continue
            payload = response.json()
            included = payload.get("included") or []
            for item in (payload.get("data") or [])[:30]:
                pair = _gecko_pool_to_pair(item, included)
                if pair:
                    markets.append(pair)
        except (requests.RequestException, ValueError, TypeError) as exc:
            print(f"GeckoTerminal {endpoint} discovery failed: {exc}")
    return markets


def get_market_data(addresses):
    markets = []
    for i in range(0, len(addresses), 30):
        batch = addresses[i:i + 30]
        url = f"{DEX_API}/tokens/v1/solana/{','.join(batch)}"
        data = safe_get_json(url)
        if isinstance(data, list):
            markets.extend(data)

    # For manual checks, ask GeckoTerminal for pools for the mint as a fallback.
    for mint in addresses[:20]:
        try:
            response = requests.get(
                f"{GECKO_API}/networks/solana/tokens/{mint}/pools",
                headers={"Accept": "application/json;version=20230302"},
                params={"page": 1}, timeout=7,
            )
            if response.ok:
                payload = response.json()
                included = payload.get("included") or []
                for item in (payload.get("data") or [])[:5]:
                    pair = _gecko_pool_to_pair(item, included)
                    if pair:
                        markets.append(pair)
        except (requests.RequestException, ValueError, TypeError) as exc:
            print(f"GeckoTerminal token-pools lookup failed: {exc}")
    return markets


def choose_best_pair(pairs):
    valid = []
    for pair in pairs:
        if str(pair.get("chainId", "")).lower() != "solana":
            continue
        base = pair.get("baseToken") or {}
        address = base.get("address")
        if not address:
            continue
        valid.append(pair)

    if not valid:
        return None

    # Prefer liquidity, then volume.
    return max(
        valid,
        key=lambda p: (
            get_num((p.get("liquidity") or {}).get("usd")),
            get_num((p.get("volume") or {}).get("h24")),
        ),
    )


def collapse_pairs(markets):
    grouped = {}
    for pair in markets:
        address, _, _ = normalize_market_pair(pair)
        if not address:
            continue
        grouped.setdefault(address, []).append(pair)

    output = []
    for address, pairs in grouped.items():
        pair = choose_best_pair(pairs)
        if pair:
            output.append(pair)
    return output


# ============================================================
# MARKET ENGINE
# ============================================================

def market_score(pair):
    liquidity = get_num((pair.get("liquidity") or {}).get("usd"))
    volume = get_num((pair.get("volume") or {}).get("h24"))
    mc = market_value(pair)
    txns = pair.get("txns") or {}
    h24 = txns.get("h24") or {}
    buys = get_num(h24.get("buys"))
    sells = get_num(h24.get("sells"))
    total_trades = buys + sells
    changes = price_changes(pair)

    score = 0

    # Liquidity quality.
    if liquidity >= 50_000:
        score += 18
    elif liquidity >= 20_000:
        score += 15
    elif liquidity >= 10_000:
        score += 11
    elif liquidity >= 5_000:
        score += 7

    # Healthy volume, without blindly rewarding gigantic pumps.
    if volume >= 100_000:
        score += 14
    elif volume >= 50_000:
        score += 12
    elif volume >= 20_000:
        score += 9
    elif volume >= 5_000:
        score += 6

    # Buy pressure.
    if total_trades:
        buy_ratio = buys / total_trades
        if buy_ratio >= 0.65:
            score += 18
        elif buy_ratio >= 0.57:
            score += 13
        elif buy_ratio >= 0.50:
            score += 8
        elif buy_ratio < 0.35:
            score -= 12

    # Liquidity / MC.
    if mc > 0:
        liq_ratio = liquidity / mc
        if liq_ratio >= 0.30:
            score += 14
        elif liq_ratio >= 0.20:
            score += 11
        elif liq_ratio >= 0.10:
            score += 7
        elif liq_ratio < 0.04:
            score -= 8

        vol_ratio = volume / mc
        if vol_ratio >= 2:
            score += 8
        elif vol_ratio >= 1:
            score += 6
        elif vol_ratio >= 0.30:
            score += 4

    # Momentum: reward controlled positive movement, not giant vertical candles.
    h1 = changes["1h"]
    h6 = changes["6h"]
    h24 = changes["24h"]
    if 0 < h1 <= 30:
        score += 7
    elif 30 < h1 <= 80:
        score += 3
    elif h1 > 150:
        score -= 8
    elif h1 < -50:
        score -= 5

    if h6 > 0:
        score += 4
    if h24 > 0:
        score += 2

    # Do not reward a token simply because it has already exploded.
    # Large vertical moves are treated as late-entry risk.
    if h1 > 100:
        score -= 10
    elif h1 > 70:
        score -= 5
    if h24 > 500:
        score -= 18
    elif h24 > 300:
        score -= 12
    elif h24 > 200:
        score -= 7

    # Activity.
    if total_trades >= 2_000:
        score += 8
    elif total_trades >= 500:
        score += 6
    elif total_trades >= 100:
        score += 4

    return clamp(score)


def basic_market_ok(pair):
    base = pair.get("baseToken") or {}
    symbol = str(base.get("symbol") or "").upper()
    if symbol in BLOCKED_SYMBOLS:
        return False

    mc = market_value(pair)
    liquidity = get_num((pair.get("liquidity") or {}).get("usd"))
    volume = get_num((pair.get("volume") or {}).get("h24"))

    # Let low-liquidity/low-volume launches enter the candidate pool only when
    # they still meet a modest floor; hard safety rejection happens after deep checks.
    return (
        MIN_MC <= mc <= MAX_MC
        and liquidity >= MIN_LIQUIDITY
        and volume >= MIN_VOLUME_24H
    )


def setup_type(pair):
    age = token_age_minutes(pair)
    changes = price_changes(pair)
    h1, h6, h24 = changes["1h"], changes["6h"], changes["24h"]

    if age is not None and age <= 60:
        return "NEW LAUNCH"

    # This is a setup classification based on aggregate DexScreener changes.
    # It is NOT claiming a true candle-by-candle higher-low structure.
    if h24 <= -40 and h6 > -15 and h1 > 0:
        return "RECOVERY"
    if h1 > 0 and h6 > 0 and h1 < 80:
        return "MOMENTUM"
    return "QUALITY"


# ============================================================
# RUGCHECK ENGINE
# ============================================================

def rugcheck_summary(mint):
    return safe_get_json(f"{RUGCHECK_API}/tokens/{mint}/report/summary")


def rugcheck_report(mint):
    return safe_get_json(f"{RUGCHECK_API}/tokens/{mint}/report")


def parse_risk_from_report(report, summary=None):
    if not isinstance(report, dict):
        report = {}
    if not isinstance(summary, dict):
        summary = {}

    score = report.get("score_normalised")
    if score is None:
        score = report.get("score")
    if score is None:
        score = summary.get("score_normalised")
    if score is None:
        score = summary.get("score")

    risk_score = get_num(score, -1)

    top_holders = report.get("topHolders") or []
    top10 = 0.0
    top20 = 0.0
    creator_pct = 0.0
    insider_holder_pct = 0.0
    insider_accounts = 0

    for index, holder in enumerate(top_holders[:20]):
        p = get_num(holder.get("pct"))
        top20 += p
        if index < 10:
            top10 += p
        if holder.get("insider"):
            insider_holder_pct += p

    creator = report.get("creator")
    creator_balance = get_num(report.get("creatorBalance"))
    supply = get_num((report.get("token") or {}).get("supply"))
    if creator and supply > 0 and creator_balance > 0:
        creator_pct = creator_balance / supply * 100

    if not creator_pct:
        creator_pct = get_num(report.get("creatorPct"))

    # Insider network information is heuristic evidence, not proof of fake wallets.
    networks = report.get("insiderNetworks") or []
    transfer_pct = 0.0
    for network in networks:
        if str(network.get("type", "")).lower() == "transfer" and supply > 0:
            transfer_pct += get_num(network.get("tokenAmount")) / supply * 100

    insider_accounts = int(get_num(report.get("graphInsidersDetected"), 0))

    risks = report.get("risks") or summary.get("risks") or []
    danger_flags = 0
    risk_names = []
    for risk in risks:
        if not isinstance(risk, dict):
            continue
        level = str(risk.get("level") or risk.get("severity") or "").lower()
        name = risk.get("name") or risk.get("description") or risk.get("message")
        if name:
            risk_names.append(str(name))
        if level in {"danger", "critical", "high"}:
            danger_flags += 1

    token = report.get("token") or {}
    mint_authority = token.get("mintAuthority")
    freeze_authority = token.get("freezeAuthority")

    lp_locked_pct = None
    markets = report.get("markets") or []
    for market in markets:
        lp = market.get("lp") or {}
        if lp.get("lpLockedPct") is not None:
            val = get_num(lp.get("lpLockedPct"))
            lp_locked_pct = val if lp_locked_pct is None else max(lp_locked_pct, val)

    total_holders = int(get_num(report.get("totalHolders"), 0))

    # Upstream holder data can occasionally be malformed; keep percentages sane.
    top10 = max(0.0, min(100.0, top10))
    top20 = max(top10, min(100.0, top20))

    return {
        "available": bool(report),
        "risk_score": risk_score,
        "top10": top10,
        "top20": top20,
        "creator_pct": creator_pct,
        "insider_holder_pct": insider_holder_pct,
        "transfer_cluster_pct": transfer_pct,
        "insider_accounts": insider_accounts,
        "danger_flags": danger_flags,
        "risk_names": risk_names[:5],
        "mint_authority": bool(mint_authority),
        "freeze_authority": bool(freeze_authority),
        "lp_locked_pct": lp_locked_pct,
        "holders": total_holders,
        "mutable": bool((report.get("tokenMeta") or {}).get("mutable")),
        "verification": report.get("verification"),
    }


def dexscreener_orders(mint, force=False):
    """Fetch and cache DexScreener paid orders; None means API unavailable."""
    now = time.time()
    cached = dex_paid_cache.get(mint)
    if cached and not force:
        # Successful responses are cached longer; API failures retry quickly so UNKNOWN
        # does not remain stuck for several minutes after a temporary timeout/429.
        cache_ttl = DEX_PAID_CACHE_SECONDS if cached.get("orders") is not None else 30
        if now - cached["time"] < cache_ttl:
            return cached["orders"]

    url = f"{DEX_API}/orders/v1/solana/{mint}"
    orders = None
    # A small retry helps with temporary DexScreener 429/5xx/network hiccups.
    for attempt in range(3):
        try:
            response = requests.get(
                url,
                timeout=REQUEST_TIMEOUT,
                headers={"Accept": "application/json", "User-Agent": "GoodBot-SolanaSignals/1.0"},
            )
            if response.status_code == 200:
                parsed = response.json()
                if isinstance(parsed, list):
                    orders = parsed
                    break
            elif response.status_code not in {429, 500, 502, 503, 504}:
                # A non-retryable error is not the same as a confirmed negative.
                break
        except (requests.RequestException, ValueError):
            pass
        if attempt < 2:
            time.sleep(0.5 * (attempt + 1))

    dex_paid_cache[mint] = {"time": now, "orders": orders}
    return orders


def dexscreener_paid_badge(mint, force=False):
    """YES means DexScreener reports an approved tokenProfile order."""
    orders = dexscreener_orders(mint, force=force)
    if not isinstance(orders, list):
        return "UNKNOWN"
    profile_orders = [
        item for item in orders
        if isinstance(item, dict) and str(item.get("type", "")).lower() == "tokenprofile"
    ]
    if any(str(item.get("status", "")).lower() == "approved" for item in profile_orders):
        return "YES"
    if any(str(item.get("status", "")).lower() in {"processing", "on-hold"} for item in profile_orders):
        return "PENDING"
    return "NO"


def dexscreener_ads_status(mint):
    orders = dexscreener_orders(mint)
    if not isinstance(orders, list):
        return "UNKNOWN"
    ad_orders = [
        item for item in orders
        if isinstance(item, dict) and str(item.get("type", "")).lower() in {"tokenad", "trendingbarad"}
    ]
    if any(str(item.get("status", "")).lower() == "approved" for item in ad_orders):
        return "YES"
    if any(str(item.get("status", "")).lower() in {"processing", "on-hold"} for item in ad_orders):
        return "PENDING"
    return "NO"


def get_bubblemap_bundle_pct(mint, force=False):
    """Return Bubblemaps' largest detected cluster share when API credentials are configured. This is a cluster-share indicator, not proof that every wallet in the cluster is bundled. """
    if not BUBBLEMAPS_API_KEY:
        return None
    now = time.time()
    cached = bubble_cache.get(mint)
    if not force and cached and now - cached["time"] < BUBBLE_CACHE_SECONDS:
        return cached.get("pct")
    pct_value = None
    try:
        response = requests.get(
            f"{BUBBLEMAPS_API}/tokens/map/solana/{mint}",
            headers={"X-API-Key": BUBBLEMAPS_API_KEY, "Accept": "application/json"},
            params={"return_clusters": "true", "refresh": "true" if force else "false"},
            timeout=10,
        )
        if response.ok:
            payload = response.json()
            clusters = payload.get("clusters") or []
            shares = []
            for cluster in clusters:
                if not isinstance(cluster, dict):
                    continue
                share = cluster.get("share")
                if share is not None:
                    value = get_num(share, -1)
                    if value >= 0:
                        # Bubblemaps share may be represented as a fraction or percentage.
                        shares.append(value * 100 if value <= 1 else value)
            if shares:
                pct_value = max(shares)
    except (requests.RequestException, ValueError, TypeError) as exc:
        print(f"Bubblemaps lookup failed for {mint}: {exc}")
    bubble_cache[mint] = {"time": now, "pct": pct_value}
    return pct_value


def get_risk(mint, force=False):
    now = time.time()
    cached = risk_cache.get(mint)
    if not force and cached and now - cached["time"] < RISK_CACHE_SECONDS:
        return cached["risk"]

    summary = rugcheck_summary(mint)
    report = rugcheck_report(mint)
    risk = parse_risk_from_report(report, summary)

    # If full report failed, still retain summary if available.
    if not risk["available"] and isinstance(summary, dict):
        risk = parse_risk_from_report({}, summary)

    risk_cache[mint] = {"time": now, "risk": risk}
    return risk


def hard_reject(risk):
    if not risk.get("available"):
        return False
    if risk.get("risk_score", -1) >= 85:
        return True
    if risk.get("top10", 0) >= 55:
        return True
    if risk.get("top20", 0) >= 75:
        return True
    if risk.get("creator_pct", 0) >= 20:
        return True
    if risk.get("insider_holder_pct", 0) >= 20:
        return True
    if risk.get("danger_flags", 0) >= 3:
        return True
    # More conservative thresholds for connected-wallet/insider risk.
    if risk.get("transfer_cluster_pct", 0) >= 25:
        return True
    if risk.get("insider_accounts", 0) >= 50 and risk.get("transfer_cluster_pct", 0) >= 15:
        return True
    return False


def risk_label(risk):
    if not risk.get("available"):
        return "UNKNOWN"
    score = risk.get("risk_score", -1)
    if score < 0:
        return "UNKNOWN"
    if score <= 20:
        return "LOW"
    if score <= 40:
        return "LOW/MED"
    if score <= 60:
        return "MEDIUM"
    if score <= 80:
        return "HIGH"
    return "CRITICAL"


def final_score(market, risk):
    # Market action alone cannot dominate the total score.
    score = float(market) * 0.70

    # Unknown security data is uncertainty, never a safety bonus.
    if not risk.get("available") or risk.get("risk_score", -1) < 0:
        return int(min(69, clamp(score)))

    rc = risk.get("risk_score", -1)
    if rc <= 20:
        score += 5
    elif rc <= 40:
        score += 1
    elif rc <= 60:
        score -= 10
    elif rc <= 80:
        score -= 22
    else:
        score -= 40

    top10 = risk.get("top10", 0)
    if top10 >= 55:
        score -= 28
    elif top10 >= 45:
        score -= 18
    elif top10 >= 35:
        score -= 9
    elif top10 <= 20:
        score += 3

    top20 = risk.get("top20", 0)
    if top20 >= 75:
        score -= 20
    elif top20 >= 60:
        score -= 12
    elif top20 >= 45:
        score -= 5

    creator = risk.get("creator_pct", 0)
    if creator >= 20:
        score -= 25
    elif creator >= 10:
        score -= 15
    elif creator >= 5:
        score -= 7

    insider = risk.get("insider_holder_pct", 0)
    if insider >= 20:
        score -= 18
    elif insider >= 10:
        score -= 10
    elif insider >= 5:
        score -= 4

    accounts = risk.get("insider_accounts", 0)
    cluster = risk.get("transfer_cluster_pct", 0)
    if accounts >= 100:
        score -= 18
    elif accounts >= 30:
        score -= 10
    elif accounts >= 10:
        score -= 5

    if risk.get("mint_authority"):
        score -= 12
    if risk.get("freeze_authority"):
        score -= 12

    lp = risk.get("lp_locked_pct")
    if lp is None:
        score -= 5  # unknown LP status should not be rewarded
    elif lp < 20:
        score -= 15
    elif lp < 50:
        score -= 8
    elif lp >= 90:
        score += 3

    score -= min(24, risk.get("danger_flags", 0) * 8)
    if cluster >= 30:
        score -= 22
    elif cluster >= 20:
        score -= 14
    elif cluster >= 10:
        score -= 6

    return int(clamp(score))


# ============================================================
# ANALYSIS
# ============================================================

def historical_score_adjustment(setup, tags):
    """Lightweight outcome calibration from prior comparable calls, including failed tokens. It activates only after at least five comparable, sufficiently observed wins/losses; this is a modest heuristic adjustment, not machine learning or a guarantee. """
    tag_set = set(tags or [])
    outcomes = []
    cutoff = time.time() - 90 * 86400
    for record in signal_history.values():
        if record.get("setup") != setup or get_num(record.get("created_at")) < cutoff:
            continue
        if int(get_num(record.get("price_updates"))) < 2:
            continue
        record_tags = set(record.get("narrative_tags") or [])
        if tag_set and record_tags and not tag_set.intersection(record_tags):
            continue
        current_return = get_num(record.get("current_return_pct"))
        max_return = get_num(record.get("max_return_pct"))
        min_return = get_num(record.get("min_return_pct"))
        if max_return >= 50:
            outcomes.append(1)   # historical runner
        elif current_return <= -20 or min_return <= -50:
            outcomes.append(-1)  # historical failure / severe drawdown
    if len(outcomes) < 5:
        return 0, {"samples": len(outcomes), "win_rate": None}
    win_rate = sum(1 for value in outcomes if value > 0) / len(outcomes)
    adjustment = int(round(max(-10, min(10, (win_rate - 0.5) * 20))))
    return adjustment, {"samples": len(outcomes), "win_rate": win_rate}


def analyze_pair(pair, deep=True):
    base_metadata = pair.get("baseToken") or {}
    address = base_metadata.get("address")
    raw_name = str(base_metadata.get("name") or "").strip()
    raw_symbol = str(base_metadata.get("symbol") or "").strip()
    if address and (not raw_name or raw_name.upper() == "UNKNOWN" or not raw_symbol or raw_symbol.upper() == "UNKNOWN"):
        enrich_token_metadata(pair, address)
    address, symbol, name = normalize_market_pair(pair)
    market = market_score(pair)
    # Track observed highs internally, but do not fetch historical ATH for every analysis.
    # The ATH display has been removed from token cards because the public history source
    # frequently has no usable candles. The dedicated oversold scanner still performs its
    # own historical lookup when it needs that data.
    tracked = track_ath(pair)
    ath = dict(tracked)
    ath["observed_mc"] = get_num(tracked.get("mc"))
    ath["historical_mc"] = None
    ath["mc"] = 0.0
    ath["historical_estimate"] = False

    risk = get_risk(address) if deep and address else {
        "available": False,
        "risk_score": -1,
        "top10": 0,
        "creator_pct": 0,
        "insider_holder_pct": 0,
        "transfer_cluster_pct": 0,
        "insider_accounts": 0,
        "danger_flags": 0,
        "risk_names": [],
        "mint_authority": False,
        "freeze_authority": False,
        "lp_locked_pct": None,
        "holders": 0,
        "mutable": False,
    }

    setup = setup_type(pair)
    raw_score = final_score(market, risk)
    tags = narrative_tags(name, symbol, pair)
    historical_adjustment, historical_stats = historical_score_adjustment(setup, tags)
    score = int(clamp(raw_score + historical_adjustment))
    bundle_pct = get_bubblemap_bundle_pct(address) if address else None
    return {
        "pair": pair,
        "address": address,
        "symbol": symbol,
        "name": name,
        "market_score": market,
        "raw_score": raw_score,
        "historical_adjustment": historical_adjustment,
        "historical_outcomes": historical_stats,
        "score": score,
        "risk": risk,
        "setup": setup,
        "ath": ath,
        "dex_paid_badge": dexscreener_paid_badge(address) if address else "UNKNOWN",
        "bundle_pct": bundle_pct,
    }


def signal_reasons(analysis):
    pair = analysis["pair"]
    risk = analysis["risk"]
    reasons = []

    liquidity = get_num((pair.get("liquidity") or {}).get("usd"))
    volume = get_num((pair.get("volume") or {}).get("h24"))
    txns = pair.get("txns") or {}
    h24 = txns.get("h24") or {}
    buys = get_num(h24.get("buys"))
    sells = get_num(h24.get("sells"))

    if liquidity >= 20_000:
        reasons.append("Good liquidity")
    if volume >= 50_000:
        reasons.append("Strong volume")
    if buys + sells > 0 and buys / (buys + sells) >= 0.57:
        reasons.append("Buyers dominant")
    if risk.get("top10", 100) <= 35:
        reasons.append("Healthy holder spread")
    if risk.get("lp_locked_pct") is not None and risk["lp_locked_pct"] >= 90:
        reasons.append("LP strongly locked")
    if analysis["setup"] == "RECOVERY":
        reasons.append("Recovery structure")
    elif analysis["setup"] == "MOMENTUM":
        reasons.append("Controlled momentum")
    elif analysis["setup"] == "NEW LAUNCH":
        reasons.append("Fresh launch activity")

    return reasons[:4]


def auto_risk_blocked(analysis):
    """Conservatively block automatic calls when available data flags bundle risk."""
    risk = analysis.get("risk") or {}
    # Do not auto-promote a token when its basic risk report could not be verified.
    if not risk.get("available") or get_num(risk.get("risk_score"), -1) < 0:
        return True
    if hard_reject(risk):
        return True
    bundle_pct = analysis.get("bundle_pct")
    if bundle_pct is not None and get_num(bundle_pct) >= MAX_AUTO_BUNDLE_CLUSTER_PCT:
        return True
    return False


def should_alert(analysis):
    pair = analysis["pair"]
    risk = analysis["risk"]
    if not basic_market_ok(pair):
        return False
    if auto_risk_blocked(analysis):
        return False
    if not risk.get("available") or risk.get("risk_score", -1) < 0:
        return False
    if hard_reject(risk):
        return False
    changes = price_changes(pair)
    # Avoid chasing vertical moves; users can still manually check these tokens.
    if changes["1h"] >= 100 or changes["24h"] >= 300:
        return False
    if risk.get("transfer_cluster_pct", 0) >= 25:
        return False
    return analysis["score"] >= MIN_SIGNAL_SCORE


# ============================================================
# FORMATTING
# ============================================================

def refresh_analysis_historical_ath(analysis, include_other_pools=True):
    """Upgrade an analysis from current-pool history to a multi-pool ATH estimate."""
    pair = analysis.get("pair") or {}
    ath = dict(analysis.get("ath") or {})
    if ath.get("historical_deep_checked"):
        return ath
    historical_mc = historical_ath_mc(pair, include_other_pools=include_other_pools)
    existing = get_num(ath.get("historical_mc"))
    if historical_mc and historical_mc > 0:
        ath["historical_mc"] = max(existing, historical_mc)
        ath["mc"] = ath["historical_mc"]
        ath["historical_estimate"] = True
    else:
        ath["mc"] = existing if existing > 0 else 0.0
        ath["historical_mc"] = existing if existing > 0 else None
        ath["historical_estimate"] = existing > 0
    ath["historical_deep_checked"] = True
    analysis["ath"] = ath
    return ath


def signal_text(analysis, manual=False, scan_label=None):
    """Compact token card: buttons carry links and the CA, so the body avoids repetition."""
    pair = analysis["pair"]
    risk = analysis["risk"]
    symbol = analysis["symbol"]
    mc = market_value(pair)
    liq = get_num((pair.get("liquidity") or {}).get("usd"))
    volume = pair.get("volume") or {}
    vol_1h = get_num(volume.get("h1"))
    vol_label = "1h"
    if not vol_1h:
        vol_1h = get_num(volume.get("h24"))
        vol_label = "24h"
    age = age_text(token_age_minutes(pair))
    # Show GoodBot-observed highs in every card. These are not guaranteed lifetime ATHs;
    # a GeckoTerminal historical estimate is shown separately when available.
    ath = analysis.get("ath") or {}
    observed_ath_mc = get_num(ath.get("observed_mc") or ath.get("mc"))
    observed_ath_price = get_num(ath.get("price"))
    historical_ath_mc_value = get_num(ath.get("historical_mc"))
    current_actual_mc = get_num(pair.get("marketCap"))
    observed_drawdown = (1 - current_actual_mc / observed_ath_mc) * 100 if current_actual_mc > 0 and observed_ath_mc > 0 else None
    holder_data = risk.get("available", False)
    holder_count = analysis.get("holder_count")
    holder_source = analysis.get("holder_source")
    if holder_count is None:
        rugcheck_count = get_num(risk.get("holders"))
        if rugcheck_count > 0:
            holder_count = int(rugcheck_count)
            holder_source = "RugCheck"
    holders = int(holder_count) if holder_count is not None else None
    top10_v = max(0.0, min(100.0, get_num(risk.get("top10")))) if holder_data else None
    top20_v = max(0.0, min(100.0, get_num(risk.get("top20")))) if holder_data else None
    if top20_v is not None and top10_v is not None:
        top20_v = max(top10_v, top20_v)
    dev_v = max(0.0, min(100.0, get_num(risk.get("creator_pct")))) if holder_data else None
    insider_v = max(0.0, min(100.0, get_num(risk.get("insider_holder_pct")))) if holder_data else None
    paid = analysis.get("dex_paid_badge", "UNKNOWN")
    def dex_mark(value):
        return {"YES": "✅", "NO": "❌", "PENDING": "⏳", "UNKNOWN": "❓"}.get(value, "❓")
    dex_status_line = f"🦅 Dex: Paid{dex_mark(paid)}"
    risk_text = risk_label(risk) if holder_data else "UNKNOWN"
    title = "🔎 MANUAL CHECK" if manual else "📡 AUTO SIGNAL"
    setup = scan_label or analysis.get("setup") or "SETUP"
    tags = narrative_tags(analysis.get("name"), symbol, pair)
    narrative_line = f"🧭 Narrative: {' / '.join(tags)}" if tags else "🧭 Narrative: unclassified"

    lines = [
        f"{title} • ${symbol} | {setup}",
        "",
        f"🕒 Age: {age}",
        f"💰 {market_value_label(pair)}: {money(mc)}" if mc > 0 else "💰 Market Cap: unavailable",
        f"📈 ATH MC (GoodBot observed): {money(observed_ath_mc)}" if observed_ath_mc > 0 else "📈 ATH MC (GoodBot observed): unavailable",
        f" ATH price (observed): ${observed_ath_price:.10g}" if observed_ath_price > 0 else " ATH price (observed): unavailable",
        f" Drawdown from observed ATH: {observed_drawdown:.1f}%" if observed_drawdown is not None else " Drawdown from observed ATH: unavailable",
        f" Historical ATH MC (estimated): {money(historical_ath_mc_value)}" if historical_ath_mc_value > 0 else None,
        f"💧 Liquidity: {money(liq)}",
        f"📊 Volume: {money(vol_1h)} ({vol_label})",
        dex_status_line,
        narrative_line,
        "",
        "👥 HOLDERS",
        f" Total: {holders:,} ({holder_source or 'reported'})" if holders is not None else " Total: unavailable",
        f" Top 10: {top10_v:.1f}%" if top10_v is not None else " Top 10: unavailable",
        f" Top 20: {top20_v:.1f}%" if top20_v is not None else " Top 20: unavailable",
        "",
        "🛠️ DEVELOPER",
        f" Dev holdings: {dev_v:.1f}%" if dev_v is not None else " Dev holdings: unavailable",
        f" Insider holdings: {insider_v:.1f}%" if insider_v is not None else " Insider holdings: unavailable",
        "",
        "🛡️ SECURITY",
        f" Risk: {risk_text}",
        f" LP locked: {pct(risk.get('lp_locked_pct'))}" if holder_data and risk.get("lp_locked_pct") is not None else " LP locked: unavailable",
        "",
        "⚠️ Informational only — verify token and trade risk before acting.",
    ]
    return "\n".join(line for line in lines if line is not None)


def normalize_external_url(value):
    """Return a safe, absolute HTTP(S) URL for Telegram inline buttons."""
    url = str(value or "").strip()
    if not url:
        return None
    if not url.startswith(("https://", "http://")):
        url = "https://" + url
    try:
        parsed = urlsplit(url)
        if parsed.scheme not in {"https", "http"} or not parsed.netloc or " " in url:
            return None
    except ValueError:
        return None
    return url


def buttons(pair, risk_available=True):
    """Build the requested order: CA, token socials, analysis, bots, then community."""
    mint = str(((pair.get("baseToken") or {}).get("address")) or "").strip()
    keyboard = []
    socials = extract_socials(pair)

    if mint:
        keyboard.append([
            InlineKeyboardButton("📋 Copy CA", copy_text=CopyTextButton(text=mint)),
            InlineKeyboardButton("🔄 Refresh", callback_data=f"refresh:{mint}"),
        ])

    # Token community links come immediately after Copy CA / Refresh.
    social_buttons = []
    for label, raw_url in [
        ("𝕏 X", socials.get("x")),
        ("🌐 Website", socials.get("website")),
        ("✈️ Token TG", socials.get("telegram")),
    ]:
        url = normalize_external_url(raw_url)
        if url:
            social_buttons.append(InlineKeyboardButton(label, url=url))
    for i in range(0, len(social_buttons), 3):
        keyboard.append(social_buttons[i:i + 3])

    # Analysis links: prefer the current official Bubblemaps app route.
    analysis_buttons = []
    if mint:
        chart_url = normalize_external_url(pair.get("url") or f"https://dexscreener.com/solana/{mint}")
        bubble_url = f"https://app.bubblemaps.io/sol/token/{mint}"
        rug_url = f"https://rugcheck.xyz/tokens/{mint}"
        for label, url in [
            ("📊 DexScreener", chart_url),
            ("🫧 Bubblemaps", bubble_url),
            ("🛡️ RugCheck", rug_url),
        ]:
            normalized = normalize_external_url(url)
            if normalized:
                analysis_buttons.append(InlineKeyboardButton(label, url=normalized))
    for i in range(0, len(analysis_buttons), 2):
        keyboard.append(analysis_buttons[i:i + 2])

    # Trading bot links follow the analysis tools. They never execute a trade by themselves.
    if mint:
        encoded_mint = quote(mint, safe="")
        bonk_ref = re.sub(r"[^A-Za-z0-9_-]", "", BONKBOT_REF_CODE)
        bonk_url = (
            f"https://t.me/bonkbot_bot?start=ref_{quote(bonk_ref, safe='')}_ca_{encoded_mint}"
            if bonk_ref else "https://t.me/bonkbot_bot"
        )
        trade_links = [
            # These bots' public docs do not confirm that arbitrary /start payloads
            # are consumed as a token message, so open their bot chats directly.
            # Use the always-visible Copy CA button above if the bot asks for the mint.
            InlineKeyboardButton("🟢 GMGN", url="https://t.me/GMGN_sol03_bot"),
            InlineKeyboardButton("⚡ Trojan", url="https://t.me/solana_trojanbot"),
            InlineKeyboardButton("🚀 BONKbot", url=bonk_url),
            InlineKeyboardButton("💎 Maestro", url="https://t.me/Maestro"),
            InlineKeyboardButton("🐂 BullX", url="https://t.me/BullXBetaBot"),
        ]
        keyboard.append(trade_links[:2])
        keyboard.append(trade_links[2:4])
        keyboard.append(trade_links[4:])

    # GoodBot's community links always come last.
    community_buttons = []
    for label, raw_url in [("📢 Updates", UPDATES_CHANNEL_URL), ("💬 Discussion", DISCUSSION_GROUP_URL)]:
        url = normalize_external_url(raw_url)
        if url:
            community_buttons.append(InlineKeyboardButton(label, url=url))
    if community_buttons:
        keyboard.append(community_buttons)

    return InlineKeyboardMarkup(keyboard) if keyboard else None


async def pumpportal_listener():
    """Optional new-token/migration discovery stream; never submits trades."""
    if not PUMPPORTAL_API_KEY:
        print("PumpPortal feed disabled: set PUMPPORTAL_API_KEY to enable early launch discovery.")
        return
    try:
        import websockets
    except ImportError:
        print("PumpPortal feed disabled: install websockets to enable it.")
        return
    uri = f"{PUMPPORTAL_WS_URL}?api-key={quote(PUMPPORTAL_API_KEY, safe='')}"
    while True:
        try:
            async with websockets.connect(uri, ping_interval=20, ping_timeout=20, close_timeout=5) as websocket:
                await websocket.send(json.dumps({"method": "subscribeNewToken"}))
                await websocket.send(json.dumps({"method": "subscribeMigration"}))
                print("PumpPortal new-token/migration feed connected.")
                async for raw in websocket:
                    try:
                        payload = json.loads(raw)
                    except (TypeError, ValueError):
                        continue
                    mint = payload.get("mint")
                    if not mint:
                        continue
                    event_type = str(payload.get("txType") or payload.get("type") or "launch").lower()
                    entry = {
                        "mint": str(mint),
                        "name": str(payload.get("name") or "UNKNOWN")[:100],
                        "symbol": str(payload.get("symbol") or "UNKNOWN")[:40],
                        "creator": str(payload.get("traderPublicKey") or "")[:64],
                        "event": event_type,
                        "seen_at": time.time(),
                    }
                    existing = {item.get("mint"): item for item in pumpportal_recent if isinstance(item, dict)}
                    previous = existing.get(entry["mint"], {})
                    previous.update(entry)
                    existing[entry["mint"]] = previous
                    pumpportal_recent[:] = sorted(existing.values(), key=lambda item: get_num(item.get("seen_at")), reverse=True)[:300]
                    save_json_file(PUMPPORTAL_FILE, pumpportal_recent)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            print(f"PumpPortal feed disconnected; reconnecting: {exc}")
            await asyncio.sleep(10)


# ============================================================
# SCAN
# ============================================================

def scan_market(include_watch=False):
    addresses = discover_addresses()
    gecko_markets = gecko_discover_pools()
    gecko_addresses = [normalize_market_pair(p)[0] for p in gecko_markets if normalize_market_pair(p)[0]]
    addresses = list(dict.fromkeys(addresses + gecko_addresses))
    markets = collapse_pairs(get_market_data(addresses) + gecko_markets)
    if not markets:
        return []
    # Keep the observed ATH tracker updated for all discovered Solana tokens,
    # including tokens that don't pass signal filters on this scan.
    for market_pair in markets:
        try:
            track_ath(market_pair)
        except Exception as exc:
            print(f"ATH tracking error: {exc}")
    candidates = [p for p in markets if basic_market_ok(p)]

    # Wider discovery pool; scoring/rejection rules remain unchanged.
    candidates.sort(key=market_score, reverse=True)
    analyses = []
    for pair in candidates[:MAX_DEEP_CHECKS_PER_SCAN]:
        try:
            analyses.append(analyze_pair(pair, deep=True))
        except Exception as exc:
            print(f"Scan analysis error: {exc}")

    high = [a for a in analyses if should_alert(a)]
    high.sort(key=lambda x: x["score"], reverse=True)

    if include_watch:
        watch = [
            a for a in analyses
            if not should_alert(a)
            and a.get("score", 0) >= 55
            and not auto_risk_blocked(a)
        ]
        watch.sort(key=lambda x: x["score"], reverse=True)
        # Keep high-confidence signals first, then up to three watch candidates.
        results = high[:MAX_RESULTS] + watch[:3]
        attach_holder_counts(results)
        return results

    results = high[:MAX_RESULTS]
    attach_holder_counts(results)
    return results


def manual_check(mint, force=False):
    if force:
        risk_cache.pop(mint, None)
        dex_paid_cache.pop(mint, None)
        bubble_cache.pop(mint, None)
        solscan_holder_cache.pop(mint, None)
        token_metadata_cache.pop(mint, None)
        for cache_key in list(gecko_ath_cache):
            if cache_key.startswith(f"solana:{mint}:"):
                gecko_ath_cache.pop(cache_key, None)
    markets = collapse_pairs(get_market_data([mint]))
    if not markets:
        return None
    pair = choose_best_pair(markets)
    if not pair:
        return None
    enrich_token_metadata(pair, mint)
    analysis = analyze_pair(pair, deep=True)
    # /check is a deliberate deep check, so try one historical OHLCV lookup here.
    # The card labels it as an estimate and keeps the GoodBot-observed high separate.
    try:
        refresh_analysis_historical_ath(analysis, include_other_pools=False)
    except Exception as exc:
        print(f"Manual historical ATH lookup failed for {mint[:8]}…: {exc}")
    attach_holder_counts([analysis])
    return analysis


def can_alert(address):
    last = alert_history.get(address, 0)
    return time.time() - last >= ALERT_COOLDOWN_SECONDS


def mark_alert(address):
    alert_history[address] = time.time()


def persist_signal_history():
    # Retain 90 days of signal outcomes for meaningful reporting.
    cutoff = time.time() - 90 * 86400
    for key, record in list(signal_history.items()):
        if get_num(record.get("created_at")) < cutoff:
            signal_history.pop(key, None)
    save_json_file(SIGNALS_FILE, signal_history)


def record_signal(analysis, origin):
    """Persist a baseline and market/security snapshot for a unique daily token call."""
    mint = analysis.get("address")
    pair = analysis.get("pair") or {}
    price = get_num(pair.get("priceUsd"))
    if not mint or price <= 0:
        return None
    today = day_key()
    # Every accepted call/scan is a separate event. Auto calls are already gated by
    # price-movement thresholds; manual scans should also retain their own baseline.
    key = f"{mint}|{origin}|{time.time_ns()}"
    txns = pair.get("txns") or {}
    h24 = txns.get("h24") or {}
    changes = price_changes(pair)
    mc = market_value(pair)
    liq = get_num((pair.get("liquidity") or {}).get("usd"))
    volume = get_num((pair.get("volume") or {}).get("h24"))
    tags = narrative_tags(analysis.get("name"), analysis.get("symbol"), pair)
    record = {
        "mint": mint,
        "symbol": analysis.get("symbol") or "UNKNOWN",
        "name": analysis.get("name") or "UNKNOWN",
        "origin": origin,
        "day": today,
        "created_at": time.time(),
        "initial_price": price,
        "current_price": price,
        "max_price": price,
        "min_price": price,
        "initial_mc": mc,
        "current_mc": mc,
        "initial_liquidity": liq,
        "initial_volume_24h": volume,
        "initial_buys_24h": get_num(h24.get("buys")),
        "initial_sells_24h": get_num(h24.get("sells")),
        "initial_change_5m": changes["5m"],
        "initial_change_1h": changes["1h"],
        "initial_change_24h": changes["24h"],
        "score_internal": get_num(analysis.get("score")),
        "setup": analysis.get("setup") or "UNKNOWN",
        "narrative_tags": tags,
        "max_return_pct": 0.0,
        "min_return_pct": 0.0,
        "current_return_pct": 0.0,
        "price_updates": 0,
        "up_milestones": [],
        "down_milestones": [],
        "last_updated": time.time(),
    }
    signal_history[key] = record
    persist_signal_history()
    return record



def register_manual_tracking(analysis, user_id, chat_id):
    """Track a manual scan from its own price baseline and route +50% alerts to its scanner."""
    mint = analysis.get("address")
    pair = analysis.get("pair") or {}
    price = get_num(pair.get("priceUsd"))
    if not mint or price <= 0 or not user_id:
        return
    key = f"{int(user_id)}|{mint}|{time.time_ns()}"
    manual_tracking[key] = {
        "user_id": int(user_id),
        "chat_id": int(chat_id) if chat_id is not None else int(user_id),
        "mint": mint,
        "symbol": analysis.get("symbol") or "UNKNOWN",
        "initial_price": price,
        "current_price": price,
        "initial_mc": market_value(pair),
        "current_mc": market_value(pair),
        "created_at": time.time(),
        "up_milestones": [],
        "down_milestones": [],
        "price_updates": 0,
    }
    save_json_file(MANUAL_TRACKING_FILE, manual_tracking)


def auto_age_eligible(analysis):
    """Only allow automatic signals for pairs at least 3 hours old with known age. Unknown age is treated conservatively: it can still be manually scanned, but it cannot qualify for an automatic runner signal until age can be verified. """
    pair = analysis.get("pair") or {}
    age_minutes = token_age_minutes(pair)
    return age_minutes is not None and age_minutes >= MIN_AUTO_TOKEN_AGE_MINUTES


def auto_signal_is_same_day_reentry(mint):
    previous = auto_signal_state.get(mint) or {}
    last_time = get_num(previous.get("time"))
    last_day = previous.get("signal_day") or (day_key(last_time) if last_time > 0 else "")
    return bool(last_day == day_key() and previous.get("reentry_ready"))


def auto_signal_allowed(analysis):
    """One automatic call per token per WAT day; same-day re-entry needs +30%, retrace, and a fresh setup."""
    mint = analysis.get("address")
    pair = analysis.get("pair") or {}
    price = get_num(pair.get("priceUsd"))
    if not mint or price <= 0:
        return False
    previous = auto_signal_state.get(mint)
    if not previous or get_num(previous.get("price")) <= 0:
        return True
    last_time = get_num(previous.get("time"))
    last_day = previous.get("signal_day") or (day_key(last_time) if last_time > 0 else "")
    if last_day != day_key():
        return True
    return bool(previous.get("reentry_ready"))


def mark_auto_signal(analysis, signal_record=None):
    mint = analysis.get("address")
    pair = analysis.get("pair") or {}
    price = get_num(pair.get("priceUsd"))
    mc = market_value(pair)
    if mint and price > 0:
        auto_signal_state[mint] = {
            "price": price,
            "initial_mc": mc,
            "max_mc": mc,
            "max_price": price,
            "time": time.time(),
            "signal_day": day_key(),
            "reached_30": False,
            "reentry_ready": False,
            "signal_record_created_at": get_num((signal_record or {}).get("created_at")),
        }
        save_json_file(AUTO_SIGNAL_STATE_FILE, auto_signal_state)


def profit_milestones_for(current_return):
    """Milestones requested: +30, +50, +70, +100, then +50% steps."""
    fixed = [30, 50, 70, 100]
    fixed.extend(range(150, min(5000, int(current_return)) + 1, 50))
    return [value for value in fixed if value <= min(5000, current_return)]


def refresh_tracking_prices():
    """Refresh recent tracked mints using the available market providers."""
    active_cutoff = time.time() - TRACKING_MAX_AGE_DAYS * 86400
    records = [(key, rec) for key, rec in signal_history.items()
               if get_num(rec.get("created_at")) >= active_cutoff]
    # Keep API requests bounded; most recent records are most useful to live alerts.
    records.sort(key=lambda item: get_num(item[1].get("created_at")), reverse=True)
    mints = list(dict.fromkeys(rec.get("mint") for _, rec in records if rec.get("mint")))[:60]
    markets = get_market_data(mints) if mints else []
    pairs_by_mint = {}
    for pair in markets:
        mint, _, _ = normalize_market_pair(pair)
        if not mint:
            continue
        current = pairs_by_mint.get(mint)
        selected = choose_best_pair([current, pair]) if current else pair
        if selected:
            pairs_by_mint[mint] = selected

    alerts = []
    changed = False
    auto_state_changed = False
    for key, record in records:
        pair = pairs_by_mint.get(record.get("mint"))
        if not pair:
            continue
        price = get_num(pair.get("priceUsd"))
        if price <= 0:
            continue
        initial = get_num(record.get("initial_price"))
        if initial <= 0:
            continue
        current_mc = market_value(pair)
        initial_mc = get_num(record.get("initial_mc"))
        current_return = ((current_mc / initial_mc - 1) * 100) if current_mc > 0 and initial_mc > 0 else (price / initial - 1) * 100
        record["current_price"] = price
        record["current_mc"] = current_mc
        record["current_return_pct"] = current_return
        record["max_price"] = max(price, get_num(record.get("max_price"), price))
        record["min_price"] = min(price, get_num(record.get("min_price"), price))
        record["max_return_pct"] = max(current_return, get_num(record.get("max_return_pct")))
        record["min_return_pct"] = min(current_return, get_num(record.get("min_return_pct")))
        record["last_updated"] = time.time()
        record["price_updates"] = int(get_num(record.get("price_updates"))) + 1
        changed = True

        # Arm same-day re-entry only after this exact auto/oversold entry reaches +30%,
        # then retraces at least 15% from its observed peak while remaining above entry.
        if record.get("origin") in {"auto_signal", "oversold_watch"}:
            state = auto_signal_state.get(record.get("mint")) or {}
            state_record_time = get_num(state.get("signal_record_created_at"))
            record_time = get_num(record.get("created_at"))
            if state and state_record_time > 0 and abs(state_record_time - record_time) < 0.01:
                entry_price = get_num(state.get("price"))
                entry_mc = get_num(state.get("initial_mc"))
                if entry_price > 0:
                    old_peak = get_num(state.get("max_price"), entry_price)
                    peak = max(old_peak, price)
                    old_peak_mc = get_num(state.get("max_mc"), entry_mc)
                    peak_mc = max(old_peak_mc, current_mc) if current_mc > 0 else old_peak_mc
                    if current_mc > 0 and entry_mc > 0:
                        gained_30 = current_mc >= entry_mc * 1.30
                        retraced_15 = peak_mc > 0 and current_mc <= peak_mc * 0.85 and current_mc >= entry_mc * 1.05
                    else:
                        gained_30 = price >= entry_price * 1.30
                        retraced_15 = peak > 0 and price <= peak * 0.85 and price >= entry_price * 1.05
                    reached_30 = bool(state.get("reached_30")) or gained_30
                    ready = bool(state.get("reentry_ready"))
                    if reached_30 and retraced_15:
                        ready = True
                    if peak != old_peak or peak_mc != old_peak_mc or reached_30 != bool(state.get("reached_30")) or ready != bool(state.get("reentry_ready")):
                        state["max_price"] = peak
                        state["max_mc"] = peak_mc
                        state["reached_30"] = reached_30
                        state["reentry_ready"] = ready
                        auto_signal_state[record.get("mint")] = state
                        auto_state_changed = True

        up_hit = set(int(v) for v in record.get("up_milestones", []))
        crossed_up = []
        for milestone in profit_milestones_for(current_return):
            if milestone not in up_hit:
                up_hit.add(milestone)
                crossed_up.append(milestone)
        record["up_milestones"] = sorted(up_hit)

        down_hit = set(int(v) for v in record.get("down_milestones", []))
        crossed_down = []
        for threshold in (-50, -70, -90):
            if current_return <= threshold and threshold not in down_hit:
                down_hit.add(threshold)
                crossed_down.append(threshold)
        record["down_milestones"] = sorted(down_hit)
        # Manual-scan alerts are routed from the per-user tracker below, never broadcast.
        if (crossed_up or crossed_down) and record.get("origin") != "manual_scan":
            alerts.append({
                "symbol": record.get("symbol", "UNKNOWN"),
                "name": record.get("name", record.get("symbol", "UNKNOWN")),
                "mint": record.get("mint"),
                "origin": record.get("origin", "signal"),
                "initial_mc": record.get("initial_mc", 0),
                "current_return": current_return,
                "current_mc": record.get("current_mc", 0),
                "up": crossed_up,
                "down": crossed_down,
                "elapsed_hours": max(0, (time.time() - get_num(record.get("created_at"))) / 3600),
            })
    if changed:
        persist_signal_history()
    if auto_state_changed:
        save_json_file(AUTO_SIGNAL_STATE_FILE, auto_signal_state)

    # Separate per-user manual scan baselines; alerts belong to the person who scanned.
    manual_changed = False
    for tracking_key, tracking_record in list(manual_tracking.items()):
        if get_num(tracking_record.get("created_at")) < active_cutoff:
            manual_tracking.pop(tracking_key, None)
            manual_changed = True
    manual_mints = list(dict.fromkeys(
        rec.get("mint") for rec in manual_tracking.values()
        if rec.get("mint") and get_num(rec.get("created_at")) >= active_cutoff
    ))
    if manual_mints:
        manual_pairs = get_market_data(manual_mints)
        manual_by_mint = {}
        for pair in manual_pairs:
            mint, _, _ = normalize_market_pair(pair)
            if mint:
                current = manual_by_mint.get(mint)
                manual_by_mint[mint] = choose_best_pair([current, pair]) if current else pair
        for record in manual_tracking.values():
            if get_num(record.get("created_at")) < active_cutoff:
                continue
            pair = manual_by_mint.get(record.get("mint"))
            if not pair:
                continue
            price = get_num(pair.get("priceUsd"))
            initial = get_num(record.get("initial_price"))
            if price <= 0 or initial <= 0:
                continue
            current_mc = market_value(pair)
            initial_mc = get_num(record.get("initial_mc"))
            current_return = ((current_mc / initial_mc - 1) * 100) if current_mc > 0 and initial_mc > 0 else (price / initial - 1) * 100
            record["current_price"] = price
            record["current_mc"] = current_mc
            record["current_return_pct"] = current_return
            record["price_updates"] = int(get_num(record.get("price_updates"))) + 1
            manual_changed = True
            up_hit = set(int(v) for v in record.get("up_milestones", []))
            crossed_up = []
            for milestone in profit_milestones_for(current_return):
                if milestone not in up_hit:
                    up_hit.add(milestone)
                    crossed_up.append(milestone)
            record["up_milestones"] = sorted(up_hit)
            down_hit = set(int(v) for v in record.get("down_milestones", []))
            crossed_down = []
            for threshold in (-50, -70, -90):
                if current_return <= threshold and threshold not in down_hit:
                    down_hit.add(threshold)
                    crossed_down.append(threshold)
            record["down_milestones"] = sorted(down_hit)
            if crossed_up or crossed_down:
                alerts.append({
                    "symbol": record.get("symbol", "UNKNOWN"),
                    "name": record.get("symbol", "UNKNOWN"),
                    "mint": record.get("mint"),
                    "origin": "manual_scan",
                    "initial_mc": record.get("initial_mc", 0),
                    "current_return": current_return,
                    "current_mc": record.get("current_mc", 0),
                    "up": crossed_up,
                    "down": crossed_down,
                    "target_user_id": record.get("user_id"),
                    "fallback_chat_id": record.get("chat_id"),
                    "elapsed_hours": max(0, (time.time() - get_num(record.get("created_at"))) / 3600),
                })
    if manual_changed:
        save_json_file(MANUAL_TRACKING_FILE, manual_tracking)
    return alerts


def daily_report_text(report_day=None):
    report_day = report_day or day_key()
    records = [rec for rec in signal_history.values() if rec.get("day") == report_day]
    total = len(records)
    automatic = sum(1 for rec in records if rec.get("origin") == "auto_signal")
    manual = sum(1 for rec in records if rec.get("origin") == "manual_scan")
    oversold = sum(1 for rec in records if rec.get("origin") == "oversold_watch")
    available = [rec for rec in records if get_num(rec.get("initial_price")) > 0 and rec.get("current_price") and int(get_num(rec.get("price_updates"))) > 0]
    returns = [get_num(rec.get("current_return_pct")) for rec in available]
    profitable = sum(1 for value in returns if value > 5)
    losing = sum(1 for value in returns if value < -5)
    flat = sum(1 for value in returns if -5 <= value <= 5)
    unavailable = total - len(available)
    reached50 = sum(1 for rec in records if get_num(rec.get("max_return_pct")) >= 50)
    reached100 = sum(1 for rec in records if get_num(rec.get("max_return_pct")) >= 100)
    reached200 = sum(1 for rec in records if get_num(rec.get("max_return_pct")) >= 200)
    dropped50 = sum(1 for rec in records if get_num(rec.get("min_return_pct")) <= -50)
    dropped80 = sum(1 for rec in records if get_num(rec.get("min_return_pct")) <= -80)
    best = max(available, key=lambda r: get_num(r.get("current_return_pct")), default=None)
    worst = min(available, key=lambda r: get_num(r.get("current_return_pct")), default=None)
    avg = mean(returns) if returns else None
    med = median(returns) if returns else None
    win_rate = (profitable / len(returns) * 100) if returns else None
    best_text = f"${best.get('symbol', 'UNKNOWN')} ({get_num(best.get('current_return_pct')):+.1f}%)" if best else "N/A"
    worst_text = f"${worst.get('symbol', 'UNKNOWN')} ({get_num(worst.get('current_return_pct')):+.1f}%)" if worst else "N/A"
    fmt = lambda value: f"{value:+.1f}%" if value is not None else "N/A"
    return "\n".join([
        "📊 GOODBOT | DAILY PERFORMANCE REPORT",
        f"📅 Date: {report_day} (WAT)",
        "━━━━━━━━━━━━━━━━━━",
        "SIGNAL ACTIVITY",
        f"• Total unique calls/scans: {total}",
        f"• Automatic signals: {automatic}",
        f"• Manual scans: {manual}",
        f"• Oversold recovery watches: {oversold}",
        "",
        "CURRENT OUTCOME (±5% = near break-even)",
        f"• Profitable: {profitable}",
        f"• Losing: {losing}",
        f"• Near break-even: {flat}",
        f"• Price data unavailable: {unavailable}",
        f"• Current profitable rate: {win_rate:.1f}%" if win_rate is not None else "• Current profitable rate: N/A",
        "",
        "MILESTONES REACHED AT ANY TIME",
        f"• +50%: {reached50} tokens",
        f"• +100%: {reached100} tokens",
        f"• +200%: {reached200} tokens",
        f"• −50% drawdown: {dropped50} tokens",
        f"• −80% drawdown: {dropped80} tokens",
        "",
        "PERFORMANCE SUMMARY",
        f"• Average current return: {fmt(avg)}",
        f"• Median current return: {fmt(med)}",
        f"• Best current performer: {best_text}",
        f"• Worst current performer: {worst_text}",
        "━━━━━━━━━━━━━━━━━━",
        "Results are measured from each record's initial call/scan price. Historical highs are not guaranteed future targets.",
    ])


def oversold_recovery_scan():
    """Find active tokens whose estimated pool ATH MC was >= $10M and drawdown >= 80%."""
    addresses = discover_addresses()
    gecko_markets = gecko_discover_pools()
    gecko_addresses = [normalize_market_pair(p)[0] for p in gecko_markets if normalize_market_pair(p)[0]]
    addresses = list(dict.fromkeys(addresses + gecko_addresses))
    markets = collapse_pairs(get_market_data(addresses) + gecko_markets)
    candidates = []
    for pair in markets:
        mc = market_value(pair)
        liq = get_num((pair.get("liquidity") or {}).get("usd"))
        vol = get_num((pair.get("volume") or {}).get("h24"))
        txns = pair.get("txns") or {}
        h24 = txns.get("h24") or {}
        activity = get_num(h24.get("buys")) + get_num(h24.get("sells"))
        # Keep enough activity/liquidity to distinguish a live setup from a dead pool.
        if 10_000 <= mc <= 2_000_000 and liq >= 5_000 and vol >= 1_000 and (activity >= 10 or get_num((pair.get("volume") or {}).get("h1")) >= 200):
            candidates.append(pair)
    candidates.sort(key=lambda p: get_num((p.get("liquidity") or {}).get("usd")), reverse=True)
    results = []
    for pair in candidates[:8]:
        try:
            analysis = analyze_pair(pair, deep=True)
            historical_ath = refresh_analysis_historical_ath(analysis, include_other_pools=True)
            ath_mc = get_num(historical_ath.get("mc"))
            current_mc = market_value(pair)
            if ath_mc < 10_000_000 or current_mc <= 0:
                continue
            drawdown = (current_mc / ath_mc - 1) * 100
            if drawdown > -80:
                continue
            if not analysis["risk"].get("available") or hard_reject(analysis["risk"]):
                continue
            analysis["setup"] = "OVERSOLD RECOVERY WATCH"
            analysis["oversold_ath_mc"] = ath_mc
            analysis["oversold_drawdown"] = drawdown
            results.append(analysis)
        except Exception as exc:
            print(f"Oversold scan error: {exc}")
    results.sort(key=lambda a: (get_num((a["pair"].get("liquidity") or {}).get("usd")), get_num((a["pair"].get("volume") or {}).get("h24"))), reverse=True)
    results = results[:5]
    attach_holder_counts(results)
    return results


# ============================================================
# TELEGRAM COMMANDS
# ============================================================

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # Subscribe only personal chats to automatic broadcasts. Group scans still work,
    # but groups must never be added to the automatic notification audience.
    if update.effective_chat and update.effective_chat.type == "private":
        known_chat_ids.add(update.effective_chat.id)
        save_json_file(CHAT_IDS_FILE, sorted(known_chat_ids))

    start_buttons = []
    if UPDATES_CHANNEL_URL:
        start_buttons.append(InlineKeyboardButton("📢 Join Updates", url=UPDATES_CHANNEL_URL))
    if DISCUSSION_GROUP_URL:
        start_buttons.append(InlineKeyboardButton("💬 Join Discussion", url=DISCUSSION_GROUP_URL))
    keyboard = InlineKeyboardMarkup([start_buttons]) if start_buttons else None
    await update.message.reply_text(
        "🤖 GOODBOT | SOLANA TOKEN INTELLIGENCE\n\n"
        "Discover emerging runners, inspect token risks, track price milestones, and review measurable signal performance.\n\n"
        "/scan — scan the current market\n"
        "/check <CA> — analyze and track a token\n"
        "/oversold — find active former runners down 80%+ from estimated ATH\n"
        "/report — view today's performance recap\n\n"
        "📢 Automatic signals and general alerts are broadcast to all personal users who have started GoodBot. If you do not receive them, open the bot privately and send /start again. Telegram does not let bots message users who have never started them.\n\n"
        "👥 When added to a group, GoodBot scans pasted Solana CAs and explicit token tickers and replies with the scan in that same group. Automatic signals are never broadcast to groups. If group messages are not detected, disable BotFather privacy mode (or make the bot an admin).\n\n"
        "Trading links open third-party bots; GoodBot never executes trades for you. Always verify the mint and review risk before trading.",
        reply_markup=keyboard,
        disable_web_page_preview=True,
    )


async def scan_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat:
        known_chat_ids.add(update.effective_chat.id)
        save_json_file(CHAT_IDS_FILE, sorted(known_chat_ids))

    if scan_lock.locked():
        await update.message.reply_text("⏳ GoodBot is already scanning. Try again shortly.")
        return

    await update.message.reply_text("🔎 Scanning Solana…")
    async with scan_lock:
        results = await asyncio.to_thread(scan_market, True)

    if not results:
        await update.message.reply_text(
            "🔎 GOODBOT SCAN\n\n"
            "No eligible setup found in the current source snapshots.\n"
            "GoodBot now checks DexScreener + GeckoTerminal pools.\n"
            "Some pre-migration bonding-curve tokens may still need a PumpPortal stream integration."
        )
        return

    high = [a for a in results if should_alert(a)]
    watch = [a for a in results if not should_alert(a)]

    await update.message.reply_text(
        "\n".join([
            "🔎 GOODBOT SCAN",
            "",
            f"🟢 High confidence: {len(high)}",
            f"🟡 Watch: {len(watch)}",
        ])
    )

    for analysis in results:
        label = "HIGH CONFIDENCE" if should_alert(analysis) else "WATCH"
        record_signal(analysis, "manual_scan")
        if update.effective_user:
            register_manual_tracking(analysis, update.effective_user.id, update.effective_chat.id if update.effective_chat else update.effective_user.id)
        await update.message.reply_text(
            signal_text(analysis, manual=True, scan_label=label),
            disable_web_page_preview=True,
            reply_markup=buttons(analysis["pair"]),
        )


async def check_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat:
        known_chat_ids.add(update.effective_chat.id)
        save_json_file(CHAT_IDS_FILE, sorted(known_chat_ids))

    if not context.args:
        await update.message.reply_text("Usage: /check <Solana_CA>\n\nYou can also paste the CA by itself.")
        return

    mint = context.args[0].strip()
    await run_manual_check(update, mint)


async def run_manual_check(update: Update, mint: str):
    # Basic Solana address shape check. We intentionally do not try to prove
    # validity locally because the RPC/DexScreener lookup is authoritative.
    if not (32 <= len(mint) <= 44):
        await update.message.reply_text("❌ That does not look like a valid Solana contract address.")
        return

    await update.message.reply_text("🧪 Deep-checking token…")
    try:
        analysis = await asyncio.to_thread(manual_check, mint)
    except Exception as exc:
        print(f"/check error for {mint}: {exc}")
        await update.message.reply_text("❌ GoodBot could not analyze that token right now. Try again in a moment.")
        return

    if not analysis:
        await update.message.reply_text(
            "❌ I couldn't find that CA on DexScreener.\n"
            "Make sure you copied the token mint address, not a pair/transaction address."
        )
        return

    try:
        record_signal(analysis, "manual_scan")
        if update.effective_user:
            register_manual_tracking(analysis, update.effective_user.id, update.effective_chat.id if update.effective_chat else update.effective_user.id)
        await update.message.reply_text(
            signal_text(analysis, manual=True),
            reply_markup=buttons(analysis["pair"]),
        )
    except Exception as exc:
        print(f"/check reply error for {mint}: {exc}")
        await update.message.reply_text("⚠️ Analysis completed, but Telegram couldn't display the result.")


def ticker_candidates_from_message(text):
    """Extract explicit cashtags/ticker labels and standalone all-caps symbols."""
    found = []
    for match in re.findall(r"\$([A-Za-z][A-Za-z0-9]{1,14})", text or ""):
        found.append(match.upper())
    for match in re.findall(r"(?i)\b(?:ticker|symbol|token)\s*[:=]\s*([A-Za-z][A-Za-z0-9]{1,14})\b", text or ""):
        found.append(match.upper())
    stripped = (text or "").strip()
    common_chat_words = {"GM", "GN", "LOL", "LFG", "WAGMI", "NGMI", "DYOR", "NFA", "IMO", "LMAO", "FOMO", "ATH", "MC", "CA", "TG", "NFT", "IMO"}
    if re.fullmatch(r"[A-Z][A-Z0-9]{1,11}", stripped) and stripped.upper() not in common_chat_words:
        found.append(stripped.upper())
    # Keep order and avoid treating obvious base assets as token candidates.
    return [item for item in dict.fromkeys(found) if item not in BLOCKED_SYMBOLS]


def resolve_ticker(ticker):
    """Resolve a ticker only when DexScreener returns one unambiguous Solana mint."""
    payload = safe_get_json(f"{DEX_API}/latest/dex/search", params={"q": ticker}) or {}
    pairs = payload.get("pairs") or []
    exact = []
    seen = set()
    for pair in pairs:
        if str(pair.get("chainId", "")).lower() != "solana":
            continue
        base = pair.get("baseToken") or {}
        address = str(base.get("address") or "").strip()
        symbol = str(base.get("symbol") or "").strip().upper()
        if not address or symbol != ticker.upper() or address in seen:
            continue
        seen.add(address)
        exact.append({
            "address": address,
            "name": str(base.get("name") or ticker),
            "symbol": symbol,
            "liquidity": get_num((pair.get("liquidity") or {}).get("usd")),
        })
    exact.sort(key=lambda item: item["liquidity"], reverse=True)
    return exact


async def run_ticker_check(update: Update, ticker):
    candidates = await asyncio.to_thread(resolve_ticker, ticker)
    if not candidates:
        await update.message.reply_text(
            f"🔎 I couldn't find a matching Solana token for ${ticker}. Please post its contract address (CA) so I can scan the exact token."
        )
        return
    if len(candidates) > 1:
        options = candidates[:5]
        lines = [f"⚠️ More than one Solana token uses ${ticker}. To avoid scanning the wrong token, please post the CA for the one you mean:"]
        lines.extend(f"• {item['name']} (${item['symbol']}) — liquidity {money(item['liquidity'])} — CA: {item['address']}" for item in options)
        await update.message.reply_text("\n".join(lines), disable_web_page_preview=True)
        return
    await update.message.reply_text(f"🔎 Ticker ${ticker} resolved. Scanning the matching Solana token…")
    await run_manual_check(update, candidates[0]["address"])


async def plain_ca_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Scan CAs posted in chats; groups get scan replies, never auto signals."""
    if not update.message or not update.message.text:
        return
    text = update.message.text.strip()
    candidates = list(dict.fromkeys(re.findall(r"(?<![1-9A-HJ-NP-Za-km-z])[1-9A-HJ-NP-Za-km-z]{32,44}(?![1-9A-HJ-NP-Za-km-z])", text)))
    if update.effective_chat:
        known_chat_ids.add(update.effective_chat.id)
        save_json_file(CHAT_IDS_FILE, sorted(known_chat_ids))
    if candidates:
        for mint in candidates[:3]:
            await run_manual_check(update, mint)
        return

    # In groups, accept explicit $TICKER / Ticker: ABC and standalone uppercase
    # symbols. For private chat messages, only explicit ticker labels/cashtags are used
    # to avoid interpreting ordinary short text as a symbol.
    tickers = ticker_candidates_from_message(text)
    if not tickers:
        return
    if update.effective_chat and update.effective_chat.type == "private":
        if not ("$" in text or re.search(r"(?i)\b(?:ticker|symbol|token)\s*[:=]", text)):
            return
    for ticker in tickers[:2]:
        await run_ticker_check(update, ticker)


async def report_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat:
        known_chat_ids.add(update.effective_chat.id)
        save_json_file(CHAT_IDS_FILE, sorted(known_chat_ids))
    await update.message.reply_text(daily_report_text(), disable_web_page_preview=True)


async def oversold_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat:
        known_chat_ids.add(update.effective_chat.id)
        save_json_file(CHAT_IDS_FILE, sorted(known_chat_ids))
    if scan_lock.locked():
        await update.message.reply_text("⏳ GoodBot is already scanning. Try /oversold again shortly.")
        return
    await update.message.reply_text("🔎 Checking active former runners with estimated ATH market cap ≥ $10M and drawdown ≥ 80%…")
    async with scan_lock:
        results = await asyncio.to_thread(oversold_recovery_scan)
    if not results:
        await update.message.reply_text(
            "No qualifying active recovery candidates found in this scan.\n"
            "Historical ATH is estimated from available pool history; tokens with missing history are not treated as confirmed former runners."
        )
        return
    await update.message.reply_text(f"🟡 OVERSOLD RECOVERY WATCH\nCandidates meeting current activity and risk filters: {len(results)}")
    for analysis in results:
        record_signal(analysis, "oversold_watch")
        pair = analysis["pair"]
        mc = market_value(pair)
        ath_mc = get_num(analysis.get("oversold_ath_mc"))
        drawdown = get_num(analysis.get("oversold_drawdown"))
        text = signal_text(analysis, scan_label="OVERSOLD RECOVERY WATCH") + "\n\n" + f"📉 Estimated ATH drawdown: {drawdown:.1f}%\n🔝 Estimated previous peak MC: {money(ath_mc)}\n💰 Current {market_value_label(pair)}: {money(mc)}\n⚠️ A deep drawdown is not proof of undervaluation or recovery."
        await update.message.reply_text(text, reply_markup=buttons(pair), disable_web_page_preview=True)


async def refresh_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query:
        return
    await query.answer("Refreshing market and security data…")
    data = query.data or ""
    mint = data.partition(":")[2].strip()
    if not (32 <= len(mint) <= 44):
        await query.edit_message_text("❌ Invalid token address. Please run /check with the token mint.")
        return
    try:
        analysis = await asyncio.to_thread(manual_check, mint, True)
        if not analysis:
            await query.edit_message_text("Could not refresh this token right now. Try again shortly.")
            return
        from telegram.error import BadRequest
        try:
            await query.edit_message_text(
                signal_text(analysis, manual=True),
                reply_markup=buttons(analysis["pair"]),
                disable_web_page_preview=True,
            )
        except BadRequest as edit_exc:
            if "message is not modified" not in str(edit_exc).lower():
                raise
    except Exception as exc:
        print(f"Refresh error for {mint}: {exc}")
        try:
            await query.edit_message_text(
                f"⚠️ Refresh failed for {short_address(mint)}. Please tap Refresh again in a moment."
            )
        except Exception:
            pass


# ============================================================
# AUTOMATIC SCANNER
# ============================================================

async def automatic_scan_job(context: ContextTypes.DEFAULT_TYPE):
    # Legacy placeholder. Automatic scanning now uses automatic_scan_loop().
    return


async def automatic_scan_loop(application: Application):
    """Background scanner, price milestone tracker, oversold watcher and daily recap."""
    global last_tracking_refresh, last_oversold_scan
    await asyncio.sleep(15)
    while True:
        try:
            private_ids = private_chat_ids()
            if private_ids and not scan_lock.locked():
                async with scan_lock:
                    results = await asyncio.to_thread(scan_market, True)
                for analysis in results:
                    address = analysis["address"]
                    # Never send automatic runner/watch alerts for pairs younger than 3 hours.
                    # Group/manual CA scans remain available regardless of age.
                    if not auto_age_eligible(analysis):
                        continue
                    pair = analysis.get("pair") or {}
                    age_minutes = token_age_minutes(pair)
                    current_mc = market_value(pair)
                    # In the first 24h, discovery signals must be strictly below $60k MC.
                    if age_minutes is not None and age_minutes <= MAX_AUTO_NEW_TOKEN_AGE_MINUTES and current_mc >= MAX_AUTO_NEW_TOKEN_MC:
                        continue
                    if not auto_signal_allowed(analysis):
                        continue
                    # Same-day re-entry is stricter than an ordinary first call: require a fresh high-confidence setup.
                    previous_state = auto_signal_state.get(address) or {}
                    previous_day = previous_state.get("signal_day") or (day_key(get_num(previous_state.get("time"))) if get_num(previous_state.get("time")) > 0 else "")
                    if previous_day == day_key() and previous_state.get("reentry_ready") and not should_alert(analysis):
                        continue
                    if auto_risk_blocked(analysis):
                        continue
                    if age_minutes is not None and age_minutes <= MAX_AUTO_NEW_TOKEN_AGE_MINUTES:
                        label = "NEW TOKEN DISCOVERY" if should_alert(analysis) else "NEW TOKEN WATCH"
                    else:
                        label = "HIGH CONFIDENCE" if should_alert(analysis) else "WATCH"
                    message = signal_text(analysis, scan_label=label)
                    signal_record = record_signal(analysis, "auto_signal")
                    for chat_id in private_chat_ids():
                        try:
                            await application.bot.send_message(
                                chat_id=chat_id,
                                text=message,
                                reply_markup=buttons(analysis["pair"]),
                                disable_web_page_preview=True,
                            )
                        except Exception as send_exc:
                            print(f"Could not send alert to chat {chat_id}: {send_exc}")
                    mark_alert(address)
                    mark_auto_signal(analysis, signal_record)

            # Historical oversold recovery scan runs less often because it uses OHLCV history.
            if private_chat_ids() and time.time() - last_oversold_scan >= 900 and not scan_lock.locked():
                last_oversold_scan = time.time()
                async with scan_lock:
                    recovery_results = await asyncio.to_thread(oversold_recovery_scan)
                for analysis in recovery_results:
                    address = analysis["address"]
                    if not can_alert(address) or not auto_signal_allowed(analysis):
                        continue
                    signal_record = record_signal(analysis, "oversold_watch")
                    pair = analysis["pair"]
                    drawdown = get_num(analysis.get("oversold_drawdown"))
                    text = signal_text(analysis, scan_label="OVERSOLD RECOVERY WATCH") + "\n\n" + f"📉 Estimated ATH drawdown: {drawdown:.1f}%\n🔝 Estimated previous peak MC: {money(analysis.get('oversold_ath_mc'))}\n⚠️ Active candidate only; recovery is not guaranteed."
                    for chat_id in private_chat_ids():
                        try:
                            await application.bot.send_message(chat_id=chat_id, text=text, reply_markup=buttons(pair), disable_web_page_preview=True)
                        except Exception as send_exc:
                            print(f"Could not send oversold alert to chat {chat_id}: {send_exc}")
                    mark_alert(address)
                    mark_auto_signal(analysis, signal_record)

            # Refresh prices every five minutes and alert once per profit/downside milestone.
            if private_chat_ids() and time.time() - last_tracking_refresh >= TRACKING_REFRESH_SECONDS:
                last_tracking_refresh = time.time()
                performance_alerts = await asyncio.to_thread(refresh_tracking_prices)
                for item in performance_alerts:
                    current = get_num(item.get("current_return"))
                    origin = str(item.get("origin", "signal")).replace("_", " ").title()
                    if item.get("up"):
                        highest = max(item["up"])
                        if highest >= 100:
                            multiple = 1 + highest / 100
                            headline = f"🚀💎 {multiple:g}X MILESTONE REACHED! 💎🚀"
                        elif highest >= 70:
                            headline = "🔥 STRONG EXPANSION!"
                        elif highest >= 50:
                            headline = "🚀 RUNNER ALERT!"
                        else:
                            headline = "🟢 BULLISH MOMENTUM!"
                        message = "\n".join([
                            headline,
                            "",
                            f"🪙 Token: {item.get('name', 'UNKNOWN')} (${item.get('symbol', 'UNKNOWN')})",
                            f"🎯 Initial Call MC: {money(item.get('initial_mc'))}",
                            f"📈 Current MC: {money(item.get('current_mc'))}",
                            f"💚 Market-cap performance: {current:+.1f}%",
                            f"🔔 Milestone(s) reached: {', '.join('+' + str(v) + '%' for v in item['up'])}",
                            f"⏱️ Time since call: {get_num(item.get('elapsed_hours')):.1f} hours",
                            "Performance milestones are sent once per entry. Displayed MC is not a guarantee of sellable proceeds.",
                        ])
                        target_user_id = item.get("target_user_id")
                        if target_user_id:
                            try:
                                await application.bot.send_message(chat_id=int(target_user_id), text=message)
                            except Exception as send_exc:
                                fallback_chat = item.get("fallback_chat_id")
                                mention = f'<a href="tg://user?id={int(target_user_id)}">scanner</a>'
                                try:
                                    if fallback_chat:
                                        await application.bot.send_message(chat_id=int(fallback_chat), text=f"{mention}, your manual scan update:\n{message}", parse_mode="HTML")
                                except Exception as fallback_exc:
                                    print(f"Targeted manual alert failed: {send_exc}; fallback failed: {fallback_exc}")
                        else:
                            for chat_id in private_chat_ids():
                                try:
                                    await application.bot.send_message(chat_id=chat_id, text=message)
                                except Exception as send_exc:
                                    print(f"Performance alert send failed: {send_exc}")
                    if item.get("down"):
                        message = "\n".join([
                            "⚠️ GOODBOT DOWNSIDE ALERT",
                            f"Token: {item.get('name', 'UNKNOWN')} (${item.get('symbol', 'UNKNOWN')})",
                            f"🎯 Initial Call MC: {money(item.get('initial_mc'))}",
                            f"📉 Current MC: {money(item.get('current_mc'))}",
                            f"Performance since call: {current:+.1f}%",
                            f"Time since call: {get_num(item.get('elapsed_hours')):.1f} hours",
                            f"New downside thresholds: {', '.join(str(v) + '%' for v in item['down'])}",
                            "Review liquidity and exit risk; this is not an instruction to buy or sell.",
                        ])
                        target_user_id = item.get("target_user_id")
                        if target_user_id:
                            try:
                                await application.bot.send_message(chat_id=int(target_user_id), text=message)
                            except Exception as send_exc:
                                fallback_chat = item.get("fallback_chat_id")
                                mention = f'<a href="tg://user?id={int(target_user_id)}">scanner</a>'
                                try:
                                    if fallback_chat:
                                        await application.bot.send_message(chat_id=int(fallback_chat), text=f"{mention}, your manual scan update:\n{message}", parse_mode="HTML")
                                except Exception as fallback_exc:
                                    print(f"Targeted manual downside alert failed: {send_exc}; fallback failed: {fallback_exc}")
                        else:
                            for chat_id in private_chat_ids():
                                try:
                                    await application.bot.send_message(chat_id=chat_id, text=message)
                                except Exception as send_exc:
                                    print(f"Downside alert send failed: {send_exc}")

            # Daily report at 23:59 WAT; the short midnight grace window catches a skipped loop tick.
            local_now = now_wat()
            today = local_now.date().isoformat()
            yesterday = (local_now.date() - timedelta(days=1)).isoformat()
            last_report = str(report_state.get("last_daily_report", ""))
            due_day = None
            if local_now.hour == DAILY_REPORT_HOUR and local_now.minute >= DAILY_REPORT_MINUTE:
                due_day = today
            elif local_now.hour == 0 and local_now.minute < 5 and last_report != yesterday:
                due_day = yesterday
            if private_chat_ids() and due_day and last_report != due_day:
                report = daily_report_text(due_day)
                for chat_id in private_chat_ids():
                    try:
                        await application.bot.send_message(chat_id=chat_id, text=report, disable_web_page_preview=True)
                    except Exception as send_exc:
                        print(f"Daily report send failed: {send_exc}")
                report_state["last_daily_report"] = due_day
                save_json_file(REPORT_STATE_FILE, report_state)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            print(f"Automatic scan error: {exc}")

        await asyncio.sleep(AUTO_SCAN_SECONDS)


async def post_init(application: Application):
    # Do not use application.job_queue. This keeps automatic scanning
    # working even when the optional JobQueue dependency is absent.
    application.create_task(
        automatic_scan_loop(application),
        name="goodbot-auto-scan",
    )
    if PUMPPORTAL_API_KEY:
        application.create_task(pumpportal_listener(), name="goodbot-pumpportal-discovery")


# ============================================================
# MAIN
# ============================================================

def main():
    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN environment variable is missing.")

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .build()
    )

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("scan", scan_command))
    app.add_handler(CommandHandler("check", check_command))
    app.add_handler(CommandHandler("oversold", oversold_command))
    app.add_handler(CommandHandler("report", report_command))
    app.add_handler(CallbackQueryHandler(refresh_callback, pattern=r"^refresh:"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, plain_ca_message))

    app.add_handler(CommandHandler("subscribe", start))
    print("GoodBot V8 public private-user broadcasts, group ticker/CA scanner, and performance tracker are running...")
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
