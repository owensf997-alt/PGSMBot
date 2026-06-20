"""
PGSM Bot — Clean Version
========================
Sadece yapılan şeyler:
1. /start → Kayıtsız kullanıcıya karşılama + abonelik ekranı
2. Abonelik ödeme akışı (Monthly $29 / Lifetime $199 — LTC & USDC)
3. Ödeme onaylandığında otomatik aktivasyon
4. Aktif üye → Railway dashboard auth linki
5. Kayıtsız kullanıcı → Support (admin'e mesaj iletir)
6. Admin: /setbalance, /approve, /removeaccess, /maintenance, /reply, /broadcast
"""

import os
import sys
import json
import time
import random
import logging
import asyncio
import hashlib
import sqlite3
import threading
import traceback
import contextlib
import struct
import base64
import hmac
from datetime import datetime, timedelta

import requests as http_requests
from dotenv import load_dotenv

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    BotCommand,
)
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ChatJoinRequestHandler,
    ContextTypes,
    filters,
)
from telegram.request import HTTPXRequest

load_dotenv()

# Notify-server global state (webhook'tan stok bildirimi göndermek için kullanılır)
_notify_bot_app  = None  # global bot referansı (main'de set edilir)
_notify_loop     = None  # botun çalıştığı asyncio event loop (post_init'te set edilir)

# ============================================================
# LOGGING
# ============================================================
_LOG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot.log")
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    handlers=[
        logging.FileHandler(_LOG_FILE, encoding="utf-8"),
        logging.StreamHandler(sys.stdout),
    ],
)
logger = logging.getLogger("pgsm_bot")
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("telegram").setLevel(logging.WARNING)

# ============================================================
# CONFIG
# ============================================================
def _env(name: str, default: str = "") -> str:
    return os.getenv(name, default) or default

def _env_int(name: str, default: int = 0) -> int:
    try:
        return int(os.getenv(name, str(default)))
    except Exception:
        return default

APP_VERSION           = "pgsm_gateway_v1"
TOKEN                 = _env("BOT_TOKEN")
ADMIN_CHAT_ID         = _env_int("ADMIN_CHAT_ID")
NOTIFY_BOT_SECRET     = _env("NOTIFY_BOT_SECRET", "")   # Railway 1'den gelen webhook güvenlik anahtarı
NOTIFY_HTTP_PORT      = _env_int("NOTIFY_HTTP_PORT", 8080)  # İç HTTP sunucu portu
WEB_BASE_URL          = _env("WEB_BASE_URL", "http://localhost:5000")
BOT_SECRET            = _env("BOT_SECRET", "changeme")
DATA_DIR              = _env("BOT_DATA_DIR", ".") or "."
MAIN_CHANNEL_LINK     = _env("MAIN_CHANNEL_LINK", "https://t.me/your_channel")
CHAT_LINK_MEMBER      = _env("CHAT_LINK_MEMBER",  "https://t.me/your_chat")
CHAT_LINK_PUBLIC      = _env("CHAT_LINK_PUBLIC",  "https://t.me/your_chat")
NEWS_LINK_MEMBER      = _env("NEWS_LINK_MEMBER",  "https://t.me/your_news")
NEWS_LINK_PUBLIC      = _env("NEWS_LINK_PUBLIC",  "https://t.me/your_news")

# Wallet / crypto
WALLET_PASSWORD       = _env("WALLET_PASSWORD")
ENCRYPTED_SEED        = _env("ENCRYPTED_SEED")
ALCHEMY_API_KEY       = _env("ALCHEMY_API_KEY")
HELIUS_API_KEY        = _env("HELIUS_API_KEY")
BLOCKCYPHER_TOKEN     = _env("BLOCKCYPHER_TOKEN")

# Abonelik fiyatları
MONTHLY_PRICE_USD     = 29.0
LIFETIME_PRICE_USD    = 199.0
MONTHLY_ACCESS_NAME   = "PGSM Monthly Access"
LIFETIME_ACCESS_NAME  = "PGSM Lifetime Access"

# Ödeme parametreleri
PAYMENT_TIMEOUT_SECONDS      = 3600
MIN_DEPOSIT_USD              = 15.0   # Minimum deposit miktarı
BLOCKCYPHER_REQUEST_DELAY    = 2.0
CALLBACK_DEBOUNCE_SECONDS    = 0.8

os.makedirs(DATA_DIR, exist_ok=True)

def _path(*parts) -> str:
    return os.path.join(DATA_DIR, *parts)

ACCESS_FILE            = _path("access.json")
PENDING_ACTIVATIONS_FILE = _path("pending_activations.json")
SQLITE_DB_FILE         = _path("elite_bot.db")
PAYMENT_INDEX_FILE     = _path("payment_index.json")
MAINTENANCE_FILE       = _path("maintenance.json")

# ============================================================
# RUNTIME STATE
# ============================================================
_master_seed_bytes: bytes | None = None
_wallet_ready = False
_sqlite_wal_set = False
_sqlite_init_lock = threading.Lock()
_sqlite_db_initialized = False
_sqlite_db_init_lock = threading.Lock()
_last_callback_time: dict = {}
support_mode_users: set = set()

# ============================================================
# JSON HELPERS
# ============================================================
_file_lock = threading.Lock()

def load_json(path: str, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default

def save_json(path: str, data) -> None:
    with _file_lock:
        try:
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(tmp, path)
        except Exception as e:
            logger.error(f"save_json {path}: {e}")

# ============================================================
# SQLITE
# ============================================================
def get_sqlite_connection():
    global _sqlite_wal_set
    conn = sqlite3.connect(SQLITE_DB_FILE, timeout=30, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA busy_timeout=30000")
    conn.execute("PRAGMA synchronous=NORMAL")
    if not _sqlite_wal_set:
        with _sqlite_init_lock:
            if not _sqlite_wal_set:
                conn.execute("PRAGMA journal_mode=WAL")
                _sqlite_wal_set = True
    return conn

def close_sqlite_connection() -> None:
    try:
        conn = sqlite3.connect(SQLITE_DB_FILE, timeout=5)
        conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        conn.close()
    except Exception:
        pass

def init_sqlite_db() -> None:
    global _sqlite_db_initialized
    if _sqlite_db_initialized:
        return
    with _sqlite_db_init_lock:
        if _sqlite_db_initialized:
            return
        conn = get_sqlite_connection()
        conn.execute("""
            CREATE TABLE IF NOT EXISTS metadata (
                key TEXT PRIMARY KEY,
                value TEXT
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS payments (
                payment_id        TEXT PRIMARY KEY,
                user_id           INTEGER NOT NULL,
                coin              TEXT NOT NULL,
                address           TEXT NOT NULL,
                address_index     INTEGER,
                usd_amount        REAL NOT NULL,
                status            TEXT NOT NULL DEFAULT 'waiting',
                credited          INTEGER NOT NULL DEFAULT 0,
                tx_hash           TEXT,
                name              TEXT,
                username          TEXT,
                plan              TEXT,
                created_at        TEXT NOT NULL,
                expires_at        TEXT NOT NULL,
                credited_at       TEXT
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS waitlist (
                user_id    INTEGER PRIMARY KEY,
                username   TEXT,
                full_name  TEXT,
                joined_at  TEXT NOT NULL
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS processed_transactions (
                tx_hash    TEXT PRIMARY KEY,
                payment_id TEXT,
                coin       TEXT,
                amount     REAL,
                processed_at TEXT NOT NULL
            )
        """)
        conn.commit()
        conn.close()
        _sqlite_db_initialized = True
        logger.info("SQLite initialized")

# ============================================================
# ACCESS / SUBSCRIPTION
# ============================================================
access_data: dict = {}

def load_access() -> dict:
    default = {"mode": "restricted", "approved_users": [], "subscriptions": {}}
    data = load_json(ACCESS_FILE, default)
    for k in ("mode", "approved_users", "subscriptions"):
        if k not in data:
            data[k] = default[k]
    return data

def save_access(data: dict) -> None:
    save_json(ACCESS_FILE, data)

def _is_subscription_active(user_id: int) -> bool:
    subs = access_data.get("subscriptions", {})
    rec = subs.get(str(user_id))
    if not rec:
        return user_id in access_data.get("approved_users", [])
    if rec.get("plan") == "lifetime":
        return True
    expires_str = rec.get("expires_at")
    if not expires_str:
        return False
    try:
        return datetime.now() < datetime.strptime(expires_str, "%Y-%m-%d %H:%M:%S")
    except Exception:
        return False

def get_subscription_info(user_id: int) -> dict | None:
    return access_data.get("subscriptions", {}).get(str(user_id))

def set_subscription(user_id: int, plan: str, payment_id: str, tx_hash: str, usd_amount: float) -> None:
    global access_data
    now = datetime.now()
    expires_at = None if plan == "lifetime" else (now + timedelta(days=30)).strftime("%Y-%m-%d %H:%M:%S")
    subs = access_data.get("subscriptions", {})
    subs[str(user_id)] = {
        "plan": plan,
        "started_at": now.strftime("%Y-%m-%d %H:%M:%S"),
        "expires_at": expires_at,
        "payment_id": payment_id,
        "tx_hash": tx_hash,
        "usd_amount": usd_amount,
    }
    access_data["subscriptions"] = subs
    approved = access_data.get("approved_users", [])
    if user_id not in approved:
        approved.append(user_id)
        access_data["approved_users"] = approved
    save_access(access_data)

def is_admin(chat_id: int) -> bool:
    return chat_id == ADMIN_CHAT_ID

def can_use_bot(chat_id: int) -> bool:
    if is_admin(chat_id):
        return True
    if access_data.get("mode", "restricted") == "open":
        return True
    return _is_subscription_active(chat_id)

# ============================================================
# MAINTENANCE
# ============================================================
def maintenance_enabled() -> bool:
    data = load_json(MAINTENANCE_FILE, {"enabled": False})
    return bool(data.get("enabled"))

def blocked_by_maintenance(chat_id: int) -> bool:
    return maintenance_enabled() and not is_admin(chat_id)

# ============================================================
# WALLET / HD KEY DERIVATION
# ============================================================
def decrypt_seed(encrypted_b64: str, password: str) -> str:
    raw = base64.b64decode(encrypted_b64.strip())
    salt, nonce, ct = raw[:16], raw[16:28], raw[28:]
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100_000)
    key = kdf.derive(password.encode())
    return AESGCM(key).decrypt(nonce, ct, None).decode()

def _hmac_sha512(key: bytes, data: bytes) -> bytes:
    return hmac.new(key, data, hashlib.sha512).digest()

def _derive_child(key: bytes, chain: bytes, index: int) -> tuple[bytes, bytes]:
    import ecdsa as _ecdsa  # FIX: her durumda erişilebilir olmalı
    if index >= 0x80000000:
        data = b"\x00" + key + struct.pack(">I", index)
    else:
        pub = _ecdsa.SigningKey.from_string(key, curve=_ecdsa.SECP256k1).get_verifying_key().to_string("compressed")
        data = pub + struct.pack(">I", index)
    I = _hmac_sha512(chain, data)
    il, ir = I[:32], I[32:]
    child_key = (int.from_bytes(il, "big") + int.from_bytes(key, "big")) % _ecdsa.SECP256k1.order
    return child_key.to_bytes(32, "big"), ir

def _master_from_seed(seed: bytes) -> tuple[bytes, bytes]:
    I = _hmac_sha512(b"Bitcoin seed", seed)
    return I[:32], I[32:]

def _derive_path(seed: bytes, path: list[int]) -> bytes:
    key, chain = _master_from_seed(seed)
    for idx in path:
        key, chain = _derive_child(key, chain, idx)
    return key

def _privkey_to_ltc_address(privkey: bytes) -> str:
    import ecdsa, hashlib
    signing_key = ecdsa.SigningKey.from_string(privkey, curve=ecdsa.SECP256k1)
    pub = signing_key.get_verifying_key().to_string("compressed")
    sha256 = hashlib.sha256(pub).digest()
    ripemd160 = hashlib.new("ripemd160", sha256).digest()
    payload = b"\x30" + ripemd160
    checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    return base64.b58encode_check(payload + checksum) if False else _b58encode(payload + checksum)

def _b58encode(data: bytes) -> str:
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    count = 0
    for byte in data:
        if byte == 0:
            count += 1
        else:
            break
    num = int.from_bytes(data, "big")
    result = ""
    while num > 0:
        num, rem = divmod(num, 58)
        result = alphabet[rem] + result
    return "1" * count + result

def _privkey_to_ltc_address(privkey: bytes) -> str:
    import ecdsa
    signing_key = ecdsa.SigningKey.from_string(privkey, curve=ecdsa.SECP256k1)
    vk = signing_key.get_verifying_key()
    pub_compressed = (b"\x02" if vk.pubkey.point.y() % 2 == 0 else b"\x03") + vk.pubkey.point.x().to_bytes(32, "big")
    sha256 = hashlib.sha256(pub_compressed).digest()
    ripemd160 = hashlib.new("ripemd160", sha256).digest()
    payload = b"\x30" + ripemd160
    checksum = hashlib.sha256(hashlib.sha256(payload).digest()).digest()[:4]
    return _b58encode(payload + checksum)

def _keccak256(data: bytes) -> bytes:
    """Pure-python keccak256 — eth_hash veya pycryptodome gerekmez."""
    import struct as _struct

    RC = [
        0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
        0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
        0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
        0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
        0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
        0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
    ]
    ROT = [
        [0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]
    ]

    def rot64(x, n): return ((x << n) | (x >> (64 - n))) & 0xFFFFFFFFFFFFFFFF

    rate = 136  # keccak256: rate = 1088 bits = 136 bytes
    msg = bytearray(data)
    msg += b''
    pad = rate - (len(msg) % rate)
    msg += b'\x00' * (pad - 1) + b'\x80'

    state = [[0]*5 for _ in range(5)]

    for block_start in range(0, len(msg), rate):
        block = msg[block_start:block_start+rate]
        for i in range(rate // 8):
            x, y = i % 5, i // 5
            state[x][y] ^= _struct.unpack_from('<Q', block, i*8)[0]
        for _ in range(24):
            C = [state[x][0]^state[x][1]^state[x][2]^state[x][3]^state[x][4] for x in range(5)]
            D = [C[(x-1)%5]^rot64(C[(x+1)%5],1) for x in range(5)]
            for x in range(5):
                for y in range(5):
                    state[x][y] ^= D[x]
            B = [[0]*5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    B[y%5][(2*x+3*y)%5] = rot64(state[x][y], ROT[x][y])
            for x in range(5):
                for y in range(5):
                    state[x][y] = B[x][y] ^ ((~B[(x+1)%5][y]) & B[(x+2)%5][y])
            state[0][0] ^= RC[_]

    out = b''
    for y in range(5):
        for x in range(5):
            out += _struct.pack('<Q', state[x][y])
            if len(out) >= 32:
                return out[:32]
    return out[:32]


def _privkey_to_eth_address(privkey: bytes) -> str:
    """⚠️ ARTIK KULLANILMIYOR — _privkey_to_sol_address kullanın."""
    logger.error("_privkey_to_eth_address CALLED — should not happen.")
    return ""

def _privkey_to_sol_address(privkey_seed: bytes) -> str:
    """Gerçek Solana (ed25519) adresi — base58. Sadece stdlib gerekir."""
    import hashlib as _hl
    h  = _hl.sha512(privkey_seed).digest()
    a  = bytearray(h[:32])
    a[0] &= 248; a[31] &= 127; a[31] |= 64
    a  = int.from_bytes(a, "little")
    P  = (2**255) - 19
    def _inv(x): return pow(x, P-2, P)
    d  = -121665 * _inv(121666) % P
    Bx = 15112221349535807912866137220509078750507884956996801867914974660316018259358 % P
    By = 46316835694926478169428394003475163141307993866256225615783033011972563625925 % P
    Bz, Bt = 1, Bx*By%P
    def _add(P1, P2):
        x1,y1,z1,t1=P1; x2,y2,z2,t2=P2
        A=(y1-x1)*(y2-x2)%P; B_=(y1+x1)*(y2+x2)%P
        C=t1*2*d*t2%P; D_=z1*2*z2%P
        E=B_-A; F=D_-C; G=D_+C; H=B_+A
        return (E*F%P,G*H%P,F*G%P,E*H%P)
    def _mul(pt, s):
        Q=(0,1,1,0)
        while s>0:
            if s&1: Q=_add(Q,pt)
            pt=_add(pt,pt); s>>=1
        return Q
    R=_mul((Bx,By,Bz,Bt),a)
    zi=_inv(R[2]); x,y=R[0]*zi%P,R[1]*zi%P
    pub=bytearray(y.to_bytes(32,"little"))
    pub[31]^=(x&1)<<7
    return _b58encode(bytes(pub))

def _ltc_privkey_for_index(index: int) -> bytes:
    if _master_seed_bytes is None:
        raise RuntimeError("Wallet not initialized")
    path = [0x8000002C, 0x80000002, 0x80000000, 0, index]
    return _derive_path(_master_seed_bytes, path)

def _sol_privkey_for_index(index: int) -> bytes:
    """
    Solana için ed25519 seed türetir.
    SECP256k1 path kullanamayız (ed25519 farklı eğri).
    Master seed + index'ten HMAC-SHA512 ile deterministik 32 byte üretiriz.
    """
    if _master_seed_bytes is None:
        raise RuntimeError("Wallet not initialized")
    import hmac as _hmac, hashlib as _hashlib
    data = b"solana-deposit-" + index.to_bytes(4, "big")
    derived = _hmac.new(_master_seed_bytes, data, _hashlib.sha512).digest()
    return derived[:32]  # ed25519 için 32 byte yeterli

def derive_ltc_address(index: int) -> str:
    return _privkey_to_ltc_address(_ltc_privkey_for_index(index))

def derive_sol_address(index: int) -> str:
    """Gerçek Solana (ed25519/base58) adresi — USDC için."""
    return _privkey_to_sol_address(_sol_privkey_for_index(index))

def derive_eth_address(index: int) -> str:
    """⚠️ Alias — derive_sol_address() kullanın."""
    return derive_sol_address(index)

def init_wallet() -> bool:
    global _master_seed_bytes, _wallet_ready
    try:
        if not ENCRYPTED_SEED or not WALLET_PASSWORD:
            logger.error("WALLET: ENCRYPTED_SEED or WALLET_PASSWORD missing")
            return False
        import unicodedata
        seed_phrase = decrypt_seed(ENCRYPTED_SEED, WALLET_PASSWORD)
        normalized = unicodedata.normalize("NFKD", seed_phrase)
        _master_seed_bytes = hashlib.pbkdf2_hmac("sha512", normalized.encode(), b"mnemonic", 2048, 64)
        _wallet_ready = True
        logger.info("WALLET: Ready")
        return True
    except Exception as e:
        logger.error(f"WALLET: {e}")
        return False

# ============================================================
# PAYMENT INDEX
# ============================================================
_index_lock = threading.Lock()

def _increment_payment_index() -> int:
    try:
        init_sqlite_db()
        conn = get_sqlite_connection()
        conn.execute("BEGIN IMMEDIATE")
        cur = conn.cursor()
        cur.execute("SELECT value FROM metadata WHERE key = 'payment_index'")
        row = cur.fetchone()
        idx = int(row["value"]) + 1 if row else 1
        conn.execute("INSERT OR REPLACE INTO metadata (key, value) VALUES ('payment_index', ?)", (str(idx),))
        conn.execute("COMMIT")
        conn.close()
        return idx
    except Exception as e:
        logger.error(f"_increment_payment_index: {e}")
        return int(time.time()) % 1000000

# ============================================================
# PENDING ACTIVATIONS
# ============================================================
def load_pending_activations() -> dict:
    return load_json(PENDING_ACTIVATIONS_FILE, {})

def save_pending_activations(data: dict) -> None:
    save_json(PENDING_ACTIVATIONS_FILE, data)

def create_activation_payment(user_id: int, coin: str, full_name: str, username: str, plan: str) -> dict:
    idx = _increment_payment_index()
    price = MONTHLY_PRICE_USD if plan == "monthly" else LIFETIME_PRICE_USD
    if coin == "LTC":
        address = derive_ltc_address(idx)
    else:  # USDC_SOLANA
        address = derive_sol_address(idx)

    payment_id = f"ACT-{int(time.time())}-{random.randint(100, 999)}"
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    expires_str = datetime.fromtimestamp(time.time() + PAYMENT_TIMEOUT_SECONDS).strftime("%Y-%m-%d %H:%M:%S")
    record = {
        "payment_id": payment_id,
        "user_id": user_id,
        "name": full_name,
        "username": username,
        "coin": coin,
        "address": address,
        "address_index": idx,
        "usd_amount": price,
        "plan": plan,
        "status": "waiting",
        "created_at": now_str,
        "expires_at": expires_str,
        "credited": False,
        "tx_hash": None,
        "activated_at": None,
    }
    acts = load_pending_activations()
    acts[payment_id] = record
    save_pending_activations(acts)
    return record

def get_user_activation_payment(user_id: int) -> dict | None:
    acts = load_pending_activations()
    for rec in acts.values():
        if int(rec.get("user_id", 0)) == user_id and not rec.get("credited"):
            if rec.get("status") in ("waiting", "expired"):
                return rec
    return None

# ============================================================
# CRYPTO PRICE & TX VERIFICATION
# ============================================================
def get_ltc_price_usd() -> float:
    try:
        r = http_requests.get("https://api.coingecko.com/api/v3/simple/price?ids=litecoin&vs_currencies=usd", timeout=8)
        return float(r.json()["litecoin"]["usd"])
    except Exception:
        try:
            r = http_requests.get("https://api.coinbase.com/v2/prices/LTC-USD/spot", timeout=8)
            return float(r.json()["data"]["amount"])
        except Exception:
            return 0.0

def get_ltc_received(address: str) -> list:
    try:
        url = f"https://api.blockcypher.com/v1/ltc/main/addrs/{address}/full?limit=50"
        if BLOCKCYPHER_TOKEN:
            url += f"&token={BLOCKCYPHER_TOKEN}"
        time.sleep(BLOCKCYPHER_REQUEST_DELAY)
        r = http_requests.get(url, timeout=15)
        data = r.json()
        txs = []
        for tx in data.get("txs", []):
            confirmations = tx.get("confirmations", 0)
            for out in tx.get("outputs", []):
                if address in out.get("addresses", []):
                    txs.append({
                        "hash": tx["hash"],
                        "confirmations": confirmations,
                        "value_ltc": out["value"] / 1e8,
                    })
        return txs
    except Exception as e:
        logger.warning(f"get_ltc_received {address}: {e}")
        return []

def get_usdc_received(address: str) -> list:
    USDC_MINT = "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v"
    try:
        url = f"https://mainnet.helius-rpc.com/?api-key={HELIUS_API_KEY}"
        payload = {
            "jsonrpc": "2.0", "id": 1,
            "method": "getSignaturesForAddress",
            "params": [address, {"limit": 20}],
        }
        r = http_requests.post(url, json=payload, timeout=15)
        sigs = [s["signature"] for s in r.json().get("result", [])]
        txs = []
        for sig in sigs[:10]:
            r2 = http_requests.post(url, json={
                "jsonrpc": "2.0", "id": 1,
                "method": "getTransaction",
                "params": [sig, {"encoding": "jsonParsed", "maxSupportedTransactionVersion": 0}],
            }, timeout=15)
            tx = r2.json().get("result") or {}
            for inst in tx.get("transaction", {}).get("message", {}).get("instructions", []):
                parsed = inst.get("parsed", {})
                if isinstance(parsed, dict):
                    info = parsed.get("info", {})
                    if info.get("mint") == USDC_MINT and info.get("destination") == address:
                        amount_raw = info.get("tokenAmount", {}).get("amount", "0")
                        txs.append({
                            "hash": sig,
                            "value_usdc": int(amount_raw) / 1e6,
                            "confirmations": 1,
                        })
        return txs
    except Exception as e:
        logger.warning(f"get_usdc_received {address}: {e}")
        return []

def is_tx_processed(tx_hash: str) -> bool:
    try:
        init_sqlite_db()
        conn = get_sqlite_connection()
        cur = conn.cursor()
        cur.execute("SELECT 1 FROM processed_transactions WHERE tx_hash=?", (tx_hash,))
        result = cur.fetchone() is not None
        conn.close()
        return result
    except Exception:
        return False

def mark_tx_processed(tx_hash: str, payment_id: str, coin: str, amount: float) -> None:
    try:
        init_sqlite_db()
        conn = get_sqlite_connection()
        conn.execute(
            "INSERT OR IGNORE INTO processed_transactions (tx_hash, payment_id, coin, amount, processed_at) VALUES (?,?,?,?,?)",
            (tx_hash, payment_id, coin, amount, datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
        )
        conn.commit()
        conn.close()
    except Exception as e:
        logger.error(f"mark_tx_processed: {e}")

def verify_ltc_tx(tx: dict, expected_address: str, expected_ltc: float) -> tuple[bool, str]:
    if is_tx_processed(tx.get("hash", "")):
        return False, "already processed"
    if tx.get("confirmations", 0) < 1:
        return False, "Insufficient confirmations"
    if tx["value_ltc"] < expected_ltc * 0.98:
        return False, f"Low amount: {tx['value_ltc']:.6f} < {expected_ltc:.6f}"
    return True, "ok"

def verify_usdc_tx(tx: dict, expected_address: str, expected_usdc: float) -> tuple[bool, str]:
    if is_tx_processed(tx.get("hash", "")):
        return False, "already processed"
    if tx["value_usdc"] < expected_usdc * 0.98:
        return False, f"Low amount: {tx['value_usdc']:.2f} < {expected_usdc:.2f}"
    return True, "ok"

# ============================================================
# QR CODE
# ============================================================
def generate_qr_bytes(data: str) -> bytes | None:
    try:
        import qrcode
        from io import BytesIO
        img = qrcode.make(data)
        buf = BytesIO()
        img.save(buf, format="PNG")
        result = buf.getvalue()
        if not result:
            logger.warning(f"generate_qr_bytes: empty result for data={data[:30]}")
            return None
        return result
    except ImportError:
        logger.warning("generate_qr_bytes: qrcode library not installed — pip install qrcode[pil]")
        return None
    except Exception as e:
        logger.warning(f"generate_qr_bytes failed: {e} | data={data[:30]}")
        return None

# ============================================================
# UI HELPERS
# ============================================================
def subscription_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📅 Monthly Plan — $29/mo",  callback_data="sub_monthly")],
        [InlineKeyboardButton("♾️ Lifetime Plan — $199",   callback_data="sub_lifetime")],
        [InlineKeyboardButton("📋 Join the Waitlist",      callback_data="join_waitlist")],
        [InlineKeyboardButton("💬 PGSM Chat",              url=CHAT_LINK_PUBLIC)],
        [InlineKeyboardButton("📢 PGSM Stock News",        url=NEWS_LINK_PUBLIC)],
        [InlineKeyboardButton("🎧 Support",                callback_data="support_unregistered")],
    ])

def sub_payment_markup(plan: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💵 Pay with USDC (Solana)", callback_data=f"subpay_{plan}_usdc")],
        [InlineKeyboardButton("🪙 Pay with LTC",           callback_data=f"subpay_{plan}_ltc")],
        [InlineKeyboardButton("🔙 Back",                   callback_data="restricted_home")],
    ])

def main_menu_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🌐 Open Dashboard",    callback_data="web_login")],
        [InlineKeyboardButton("👤 My Profile",        callback_data="my_profile"),
         InlineKeyboardButton("💰 Add Funds",         callback_data="deposit_menu")],
        [InlineKeyboardButton("💬 PGSM Chat",         url=CHAT_LINK_MEMBER)],
        [InlineKeyboardButton("📢 PGSM Stock News",   url=NEWS_LINK_MEMBER)],
        [InlineKeyboardButton("🎧 Support",           callback_data="support")],
    ])

async def send_restricted_message(target, user=None) -> None:
    name = user.first_name if user and getattr(user, "first_name", None) else "there"
    text = (
        f"👋 Welcome to PGSM, {name}!\n\n"
        "<b>PGSM Marketplace — Prepaid & Gift Card Stocks</b>\n\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "🔒 <b>New memberships are temporarily suspended.</b>\n\n"
        "We are currently limiting access to maintain the quality and "
        "exclusivity of our marketplace. Enrollment will reopen soon.\n\n"
        "📅 <b>Monthly Plan — $29/month</b>\n"
        "   Renews every 30 days\n\n"
        "♾️ <b>Lifetime Plan — $199 one-time</b>\n"
        "   Pay once, access forever\n\n"
        "✅ Instant delivery\n"
        "✅ Fresh stock, never relisted\n"
        "✅ Secure web dashboard\n"
        "✅ LTC & USDC payments\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "📋 <b>Want to be notified when registrations open?</b>\n"
        "Join our waitlist and you'll receive a direct notification "
        "the moment new spots become available — before anyone else."
    )
    await target.reply_html(text, reply_markup=subscription_markup())

async def show_main_menu(target) -> None:
    await target.reply_text(
        "⚡ Welcome to PGSM!\n\nYour subscription is active. Use the dashboard to access your cards.",
        reply_markup=main_menu_markup(),
    )

async def send_payment_with_qr(target, coin: str, usd_amount: float, address: str,
                                payment_id: str, expires: str, reply_markup=None) -> None:
    if coin == "LTC":
        network = "Litecoin"
        coin_label = "LTC"
        ltc_price = get_ltc_price_usd()
        ltc_line = f"• Send exactly: {round(usd_amount / ltc_price, 6)} LTC\n" if ltc_price > 0 else ""
    else:
        network = "Solana (SPL Token)"
        coin_label = "USDC (Solana)"
        ltc_line = f"• Send exactly: {usd_amount:.2f} USDC\n"

    if coin == "LTC":
        warning = (
            "⚠️ WARNING:\n"
            "- Send only on the Litecoin (LTC) network.\n"
            "- Sending via any other network will result in permanent loss of funds.\n"
            "- This address is valid only for your account. Do not share it."
        )
    else:
        warning = (
            "⚠️ WARNING:\n"
            "- Send only USDC on the Solana (SPL Token) network.\n"
            "- Sending via Ethereum, BSC or any other network will result in permanent loss of funds.\n"
            "- This address is valid only for your account. Do not share it."
        )

    caption = (
        f"{coin_label} — ${usd_amount:.0f}\n"
        f"Network: {network}\n\n"
        f"Address:\n{address}\n\n"
        f"{ltc_line}"
        f"Expires: {expires}\n\n"
        f"{warning}"
    )
    if len(caption) > 1024:
        caption = caption[:1020] + "..."

    qr_bytes = generate_qr_bytes(address)
    try:
        if qr_bytes:
            from io import BytesIO
            await target.reply_photo(photo=BytesIO(qr_bytes), caption=caption, reply_markup=reply_markup)
            return
        else:
            logger.warning(f"send_payment_with_qr: no QR bytes for coin={coin} address={address[:20]}")
    except Exception as e:
        logger.error(f"send_payment_with_qr reply_photo failed (coin={coin}): {e}")
    # QR başarısız — düz metin ile gönder
    await target.reply_text(caption, reply_markup=reply_markup)

# ============================================================
# ACTIVATION
# ============================================================
async def activate_user(user_id: int, payment_id: str, tx_hash: str,
                        coin: str, usd_amount: float, bot) -> None:
    global access_data
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    acts = load_pending_activations()
    plan = "monthly"
    rec = {"name": "-", "username": "-"}
    if payment_id in acts:
        acts[payment_id]["credited"] = True
        acts[payment_id]["status"] = "activated"
        acts[payment_id]["tx_hash"] = tx_hash
        acts[payment_id]["activated_at"] = now_str
        plan = acts[payment_id].get("plan", "monthly")
        rec = acts[payment_id]
        save_pending_activations(acts)

    mark_tx_processed(tx_hash, payment_id, coin, usd_amount)
    set_subscription(user_id, plan, payment_id, tx_hash, usd_amount)
    logger.info(f"[ACTIVATION] user={user_id} plan={plan} coin={coin} amount={usd_amount} tx={tx_hash}")

    plan_label = MONTHLY_ACCESS_NAME if plan == "monthly" else LIFETIME_ACCESS_NAME
    try:
        await bot.send_message(
            chat_id=user_id,
            text=(
                f"✅ Your account has been activated!\n\n"
                f"Plan: {plan_label}\n"
                f"Payment ID: {payment_id}\n"
                f"Coin: {coin}\n"
                f"Amount: ${usd_amount:.2f}\n"
                f"TX: {tx_hash[:24]}...\n\n"
                "Welcome to PGSM! Tap below to access your dashboard."
            ),
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🌐 Open Dashboard", callback_data="web_login")],
            ]),
        )
    except Exception as e:
        logger.warning(f"Activation notify failed {user_id}: {e}")

    try:
        await bot.send_message(
            chat_id=ADMIN_CHAT_ID,
            text=(
                f"✅ New Member Activated\n\n"
                f"Plan: {plan_label}\n"
                f"User: {rec.get('name', '-')} ({rec.get('username', '-')})\n"
                f"User ID: {user_id}\n"
                f"Coin: {coin}\n"
                f"Amount: ${usd_amount:.2f}\n"
                f"TX: {tx_hash}\n"
                f"Time: {now_str}"
            ),
        )
    except Exception:
        pass

# ============================================================
# PAYMENT MONITOR JOB
# ============================================================
async def check_deposits_expiry_job(context) -> None:
    """Her 60s — süresi dolan deposit kayıtlarını expired olarak işaretle."""
    deps = load_pending_deposits()
    now_ts = time.time()
    changed = False
    for pid, rec in deps.items():
        if rec.get("status") != "waiting" or rec.get("credited"):
            continue
        try:
            exp_ts = datetime.strptime(rec["expires_at"], "%Y-%m-%d %H:%M:%S").timestamp()
        except Exception:
            continue
        if now_ts > exp_ts:
            deps[pid]["status"] = "expired"
            changed = True
            logger.info(f"[DEPOSIT EXPIRY] {pid} user={rec.get('user_id')} expired")
    if changed:
        save_pending_deposits(deps)

async def check_activation_payments_job(context) -> None:
    acts = load_pending_activations()
    now_ts = time.time()
    to_check = {
        pid: rec for pid, rec in acts.items()
        if not rec.get("credited") and rec.get("status") in ("waiting", "expired")
    }
    if not to_check:
        return

    # Mark expired
    for pid, rec in to_check.items():
        if rec.get("status") == "waiting":
            try:
                exp_ts = datetime.strptime(rec["expires_at"], "%Y-%m-%d %H:%M:%S").timestamp()
            except Exception:
                exp_ts = now_ts + 1
            if now_ts > exp_ts:
                acts[pid]["status"] = "expired"
    save_pending_activations(acts)

    ltc_acts  = {pid: r for pid, r in to_check.items() if r["coin"] == "LTC"}
    usdc_acts = {pid: r for pid, r in to_check.items() if r["coin"] in ("USDC", "USDC_SOLANA")}

    loop = asyncio.get_event_loop()
    ltc_price = None
    for pid, rec in ltc_acts.items():
        if ltc_price is None:
            ltc_price = await loop.run_in_executor(None, get_ltc_price_usd)
        if ltc_price <= 0:
            continue
        plan_fee = float(rec.get("usd_amount", MONTHLY_PRICE_USD))
        expected_ltc = plan_fee / ltc_price
        txs = await loop.run_in_executor(None, get_ltc_received, rec["address"])
        for tx in txs:
            is_valid, reason = verify_ltc_tx(tx, rec["address"], expected_ltc)
            if not is_valid:
                if "already processed" not in reason and "Insufficient" not in reason:
                    logger.warning(f"LTC TX rejected [{pid}]: {reason}")
                continue
            received_usd = round(tx["value_ltc"] * ltc_price, 2)
            await activate_user(int(rec["user_id"]), pid, tx["hash"], "LTC", received_usd, context.bot)
            break

    for pid, rec in usdc_acts.items():
        txs = await loop.run_in_executor(None, get_usdc_received, rec["address"])
        for tx in txs:
            plan_fee = float(rec.get("usd_amount", MONTHLY_PRICE_USD))
            is_valid, reason = verify_usdc_tx(tx, rec["address"], plan_fee)
            if not is_valid:
                if "already processed" not in reason:
                    logger.warning(f"USDC TX rejected [{pid}]: {reason}")
                continue
            await activate_user(int(rec["user_id"]), pid, tx["hash"], "USDC", round(tx["value_usdc"], 2), context.bot)
            break

# ============================================================
# WEB LOGIN
# ============================================================


# ============================================================
# DEPOSIT — Abone kullanıcıların bakiye yüklemesi
# Mevcut aktivasyon altyapısını (cüzdan türetme, TX kontrol)
# yeniden kullanır. Ayrı bir JSON dosyasında saklanır.
# ============================================================

PENDING_DEPOSITS_FILE = _path("pending_deposits.json")

def load_pending_deposits() -> dict:
    return load_json(PENDING_DEPOSITS_FILE, {})

def save_pending_deposits(data: dict) -> None:
    save_json(PENDING_DEPOSITS_FILE, data)

def _cleanup_expired_deposits(user_id: int) -> None:
    """Kullanıcının expired deposit kayıtlarını sil — JSON şişmesin."""
    deps = load_pending_deposits()
    to_del = [pid for pid, rec in deps.items()
              if int(rec.get("user_id", 0)) == user_id and rec.get("status") == "expired"]
    if to_del:
        for pid in to_del: del deps[pid]
        save_pending_deposits(deps)

def create_deposit_payment(user_id: int, coin: str, usd_amount: float) -> dict:
    """Yeni bir deposit oluştur — aktivasyon gibi ama type=deposit."""
    _cleanup_expired_deposits(user_id)
    idx     = _increment_payment_index()
    address = derive_ltc_address(idx) if coin == "LTC" else derive_sol_address(idx)
    dep_id  = f"DEP-{int(time.time())}-{random.randint(100, 999)}"
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    expires = datetime.fromtimestamp(time.time() + PAYMENT_TIMEOUT_SECONDS).strftime("%Y-%m-%d %H:%M:%S")
    record  = {
        "deposit_id":    dep_id,
        "user_id":       user_id,
        "coin":          coin,
        "address":       address,
        "address_index": idx,
        "usd_amount":    usd_amount,
        "status":        "waiting",
        "created_at":    now_str,
        "expires_at":    expires,
        "credited":      False,
        "tx_hash":       None,
    }
    deps = load_pending_deposits()
    deps[dep_id] = record
    save_pending_deposits(deps)
    return record

def get_user_pending_deposit(user_id: int) -> dict | None:
    """Aktif (süresi dolmamış) bekleyen depositi döner. Expired olanlar bloke etmez."""
    now = datetime.now()
    deps = load_pending_deposits()
    changed = False
    for pid, rec in deps.items():
        if int(rec.get("user_id", 0)) != user_id or rec.get("credited"):
            continue
        if rec.get("status") != "waiting":
            continue
        try:
            if now > datetime.strptime(rec["expires_at"], "%Y-%m-%d %H:%M:%S"):
                deps[pid]["status"] = "expired"
                changed = True
                continue
        except Exception:
            pass
        if changed:
            save_pending_deposits(deps)
        return rec
    if changed:
        save_pending_deposits(deps)
    return None

async def credit_deposit(user_id: int, dep_id: str, tx_hash: str,
                          coin: str, usd_amount: float, bot) -> None:
    """TX onaylandı — Railway'e bakiye ekle ve kullanıcıya bildir."""
    # 1. Lokal kayıt güncelle
    deps = load_pending_deposits()
    if dep_id in deps:
        deps[dep_id]["credited"]  = True
        deps[dep_id]["status"]    = "completed"
        deps[dep_id]["tx_hash"]   = tx_hash
        deps[dep_id]["credited_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        save_pending_deposits(deps)

    mark_tx_processed(tx_hash, dep_id, coin, usd_amount)

    # 2. Railway'e deposit bildir — var olan /api/deposit_request endpoint'ini kullan
    try:
        resp = http_requests.post(
            f"{WEB_BASE_URL}/api/bot/deposit_credit",
            json={
                "user_id":   user_id,
                "amount":    usd_amount,
                "coin":      coin,
                "tx_hash":   tx_hash,
                "deposit_id": dep_id,
                "secret":    BOT_SECRET,
            },
            headers={"X-Bot-Secret": BOT_SECRET},
            timeout=10,
        )
        if resp.status_code != 200:
            logger.error(f"deposit_credit Railway error {resp.status_code}: {resp.text[:200]}")
    except Exception as e:
        logger.error(f"deposit_credit request error: {e}")

    logger.info(f"[DEPOSIT] user={user_id} amount=${usd_amount} coin={coin} tx={tx_hash}")

    # 3. Kullanıcıya bildir
    try:
        await bot.send_message(
            chat_id=user_id,
            text=(
                f"✅ <b>Deposit Confirmed!</b>\n\n"
                f"💰 Amount: <b>${usd_amount:.2f}</b>\n"
                f"🪙 Coin: {coin}\n"
                f"🔑 TX: <code>{tx_hash[:24]}...</code>\n\n"
                f"Your balance has been updated. Tap below to check your profile."
            ),
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("👤 My Profile", callback_data="my_profile")],
                [InlineKeyboardButton("🏠 Main Menu",  callback_data="main_menu")],
            ]),
        )
    except Exception as e:
        logger.warning(f"Deposit notify failed {user_id}: {e}")

    # 4. Admini bildir
    try:
        await bot.send_message(
            chat_id=ADMIN_CHAT_ID,
            text=(
                f"💰 <b>Deposit Credited</b>\n"
                f"User ID: <code>{user_id}</code>\n"
                f"Amount: ${usd_amount:.2f}\n"
                f"Coin: {coin}\n"
                f"TX: {tx_hash}"
            ),
            parse_mode="HTML",
        )
    except Exception:
        pass


async def handle_deposit_menu(update, context) -> None:
    """💰 Add Funds — coin seçim ekranı."""
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass
    await query.message.reply_html(
        "💰 <b>Add Funds to Your Account</b>\n\n"
        f"Minimum deposit: <b>${MIN_DEPOSIT_USD:.0f}</b>\n"
        "Choose your payment method:",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("💵 USDC (Solana)", callback_data="dep_usdc")],
            [InlineKeyboardButton("🪙 LTC",           callback_data="dep_ltc")],
            [InlineKeyboardButton("🏠 Main Menu",     callback_data="main_menu")],
        ]),
    )


async def handle_deposit_amount(update, context, coin: str) -> None:
    """Kullanıcıdan miktar al."""
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass
    user_id = query.from_user.id

    # Bekleyen deposit varsa — iptal et veya devam et
    existing = get_user_pending_deposit(user_id)
    if existing and existing.get("status") == "waiting":
        coin_label = existing["coin"]
        await query.message.reply_html(
            f"⚠️ You already have a pending deposit (${existing['usd_amount']:.2f} via {coin_label}).\n\n"
            "Please complete or wait for it to expire before creating a new one.",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Check Status", callback_data="dep_check")],
                [InlineKeyboardButton("🏠 Main Menu",   callback_data="main_menu")],
            ]),
        )
        return

    coin_key = "USDC_SOLANA" if coin == "usdc" else "LTC"
    context.user_data["dep_coin"] = coin_key
    context.user_data["dep_step"] = "awaiting_amount"
    coin_label = "USDC (Solana)" if coin == "usdc" else "LTC"

    await query.message.reply_html(
        f"🪙 <b>Deposit via {coin_label}</b>\n\n"
        f"Minimum: <b>${MIN_DEPOSIT_USD:.0f}</b>\n\n"
        "Please type the <b>USD amount</b> you want to deposit (e.g. <code>50</code>):",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("❌ Cancel", callback_data="main_menu")],
        ]),
    )


async def handle_deposit_confirm(update, context) -> None:
    """Miktar mesajı geldi — QR + adres göster."""
    user_id = update.effective_user.id

    dep_step = context.user_data.get("dep_step")
    if dep_step != "awaiting_amount":
        return

    try:
        usd_amount = float(update.message.text.strip().replace("$", "").replace(",", "."))
    except ValueError:
        await update.message.reply_text("⚠️ Please enter a valid number (e.g. 50).")
        return

    if usd_amount < MIN_DEPOSIT_USD:
        await update.message.reply_text(f"⚠️ Minimum deposit is ${MIN_DEPOSIT_USD:.0f}.")
        return

    coin = context.user_data.get("dep_coin", "LTC")
    context.user_data.pop("dep_step", None)
    context.user_data.pop("dep_coin", None)

    try:
        rec = create_deposit_payment(user_id, coin, usd_amount)
    except Exception as e:
        logger.error(f"create_deposit_payment error: {e}", exc_info=True)
        await update.message.reply_text(f"⚠️ Could not generate address. Please try again.\nError: {e}")
        return

    # LTC için döviz miktarı hesapla
    coin_amount_str = ""
    if coin == "LTC":
        try:
            ltc_price = get_ltc_price_usd()
            if ltc_price > 0:
                ltc_needed = usd_amount / ltc_price
                coin_amount_str = f"\n🪙 LTC Amount: <b>{ltc_needed:.6f} LTC</b> (approx)"
        except Exception:
            pass

    address = rec["address"]
    expires = rec["expires_at"]
    coin_label = "USDC (Solana)" if coin == "USDC_SOLANA" else "LTC"

    if coin == "USDC_SOLANA":
        network_warning = (
            "⚠️ <b>WARNING:</b>\n"
            "- Deposits below the minimum amount will not be processed.\n"
            "- Send only <b>USDC on the Solana network</b>. Sending via Ethereum, BSC or any other network will result in <b>permanent loss of funds</b>.\n"
            "- This address is valid only for your account. Do not share it.\n\n"
            "📌 <i>Note: This deposit session is only active for 60 minutes. Please send before it expires.</i>"
        )
    else:
        network_warning = (
            "⚠️ <b>WARNING:</b>\n"
            "- Deposits below the minimum amount will not be processed.\n"
            "- Send only on the <b>Litecoin (LTC) network</b>. Sending via any other network will result in <b>permanent loss of funds</b>.\n"
            "- This address is valid only for your account. Do not share it.\n\n"
            "📌 <i>Note: This deposit session is only active for 60 minutes. Please send before it expires.</i>"
        )

    text = (
        f"💰 <b>Deposit ${usd_amount:.2f} via {coin_label}</b>\n\n"
        f"Send <b>exactly ${usd_amount:.2f}</b> worth of {coin_label} to:{coin_amount_str}\n\n"
        f"📬 <code>{address}</code>\n\n"
        f"⏳ Expires: {expires}\n\n"
        "After sending, tap <b>Check Status</b> to confirm.\n\n"
        f"{network_warning}"
    )

    # QR kod
    qr_bytes = generate_qr_bytes(address)
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Check Status", callback_data="dep_check")],
        [InlineKeyboardButton("🏠 Main Menu",   callback_data="main_menu")],
    ])

    if qr_bytes:
        from io import BytesIO
        from telegram import InputFile
        try:
            await update.message.reply_photo(
                photo=InputFile(BytesIO(qr_bytes), filename="deposit_qr.png"),
                caption=text,
                parse_mode="HTML",
                reply_markup=markup,
            )
        except Exception:
            await update.message.reply_html(text, reply_markup=markup)
    else:
        await update.message.reply_html(text, reply_markup=markup)


async def handle_deposit_check(update, context) -> None:
    """Manuel 'Check Status' — TX'i hemen kontrol et."""
    query = update.callback_query
    try:
        await query.answer("Checking...")
    except Exception:
        pass
    user_id = query.from_user.id
    rec = get_user_pending_deposit(user_id)

    if not rec:
        await query.message.reply_text("No pending deposit found.")
        return

    if rec.get("status") == "expired":
        await query.message.reply_html(
            "⌛ Your deposit has <b>expired</b>. Please create a new one.",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("💰 New Deposit", callback_data="deposit_menu")],
                [InlineKeyboardButton("🏠 Main Menu",  callback_data="main_menu")],
            ]),
        )
        return

    # TX kontrol et
    coin     = rec["coin"]
    address  = rec["address"]
    usd_amt  = float(rec["usd_amount"])
    dep_id   = rec["deposit_id"]
    found    = False

    loop = asyncio.get_event_loop()
    if coin == "LTC":
        ltc_price = await loop.run_in_executor(None, get_ltc_price_usd)
        if ltc_price > 0:
            expected_ltc = usd_amt / ltc_price
            txs = await loop.run_in_executor(None, get_ltc_received, address)
            for tx in txs:
                ok, reason = verify_ltc_tx(tx, address, expected_ltc)
                if ok:
                    received_usd = round(tx["value_ltc"] * ltc_price, 2)
                    await credit_deposit(user_id, dep_id, tx["hash"], coin, received_usd, query.get_bot())
                    found = True
                    break
    else:
        txs = await loop.run_in_executor(None, get_usdc_received, address)
        for tx in txs:
            ok, reason = verify_usdc_tx(tx, address, usd_amt)
            if ok:
                await credit_deposit(user_id, dep_id, tx["hash"], coin, round(tx["value_usdc"], 2), query.get_bot())
                found = True
                break

    if not found:
        await query.message.reply_html(
            "⏳ <b>Payment not detected yet.</b>\n\n"
            f"Address: <code>{address}</code>\n"
            f"Amount: ${usd_amt:.2f}\n\n"
            "Please wait a few minutes after sending and check again.",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 Check Again", callback_data="dep_check")],
                [InlineKeyboardButton("🏠 Main Menu",  callback_data="main_menu")],
            ]),
        )

async def handle_profile(update, context) -> None:
    """👤 My Profile — Railway'den kullanıcı özeti çekip Telegram'da göster."""
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass

    user_id = query.from_user.id

    try:
        resp = http_requests.get(
            f"{WEB_BASE_URL}/api/user/summary",
            params={"user_id": user_id},
            headers={"X-Bot-Secret": BOT_SECRET},
            timeout=10,
        )
        d = resp.json()
    except Exception as e:
        logger.error(f"profile fetch error: {e}")
        await query.message.reply_text("⚠️ Could not load profile. Please try again.")
        return

    # Plan satırı
    plan = d.get("plan", "unknown").capitalize()
    is_active = d.get("is_active", False)
    days_left = d.get("days_left")
    expires_at = d.get("expires_at", "")

    if plan.lower() == "lifetime":
        plan_line = "♾️ Lifetime"
    elif is_active and days_left is not None:
        plan_line = f"📅 {plan} — {days_left} days left ({expires_at})"
    elif not is_active:
        plan_line = "❌ No active plan"
    else:
        plan_line = f"📅 {plan}"

    # İstatistikler
    total_cards   = d.get("total_cards", 0)
    total_spent   = d.get("total_spent", 0.0)
    last_purchase = d.get("last_purchase") or "—"
    balance       = d.get("balance", 0.0)

    # Kullanıcı adını al
    tg_user = query.from_user
    display_name = tg_user.full_name or tg_user.username or "User"

    text = (
        f"👤 <b>{display_name}</b>\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"🎫 <b>Plan:</b> {plan_line}\n"
        f"💰 <b>Balance:</b> ${balance:.2f}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"📦 <b>Cards Purchased:</b> {total_cards}\n"
        f"💸 <b>Total Spent:</b> ${total_spent:.2f}\n"
        f"🕐 <b>Last Purchase:</b> {last_purchase}\n"
    )

    await query.message.reply_html(
        text,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
        ]),
    )


async def handle_web_login(update, context) -> None:
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass
    user_id = query.from_user.id
    user = query.from_user
    tg_name = ""
    if user.username:
        tg_name = f"@{user.username}"
    elif user.full_name:
        tg_name = user.full_name
    try:
        resp = http_requests.post(
            f"{WEB_BASE_URL}/api/gen_code",
            json={"user_id": user_id, "lang": "en", "tg_name": tg_name},
            headers={"X-Bot-Secret": BOT_SECRET},
            timeout=10,
        )
        data = resp.json()
        login_url = data.get("url")
        if not login_url:
            raise ValueError("no url")
    except Exception as e:
        logger.error(f"gen_code error: {e}")
        await query.message.reply_text("Could not generate login link. Please try again.")
        return
    await query.message.reply_html(
        "🔐 <b>Your secure login link is ready!</b>\n\n"
        "⚠️ This link expires in <b>5 minutes</b> and can only be used once.\n"
        "Do not share it with anyone.",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🌐 Open Dashboard", url=login_url)],
            [InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")],
        ]),
    )

# ============================================================
# HANDLERS
# ============================================================
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    if blocked_by_maintenance(chat_id):
        await update.message.reply_text("🔧 Bot is under maintenance. Please try again later.")
        return

    # ── Referral parametresi kontrol ──────────────────────────
    if context.args:
        arg = context.args[0]
        if arg.startswith("ref_"):
            referrer_id = arg[4:]  # "ref_1927811621" → "1927811621"
            if referrer_id.isdigit() and int(referrer_id) != chat_id:
                try:
                    resp = http_requests.post(
                        f"{WEB_BASE_URL}/api/referral/register",
                        json={"referrer_id": referrer_id, "referred_id": str(chat_id),
                              "secret": BOT_SECRET},
                        timeout=5
                    )
                    if resp.status_code == 200 and resp.json().get("success"):
                        await update.message.reply_text(
                            "🎁 You were referred by a friend!\n"
                            "Both of you will receive <b>$5.00</b> bonus after your first deposit.",
                            parse_mode="HTML"
                        )
                except Exception as _re:
                    logger.warning(f"referral register error: {_re}")

    if can_use_bot(chat_id):
        await show_main_menu(update.message)
    else:
        await send_restricted_message(update.message, update.effective_user)

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = update.effective_chat.id
    if can_use_bot(chat_id):
        await update.message.reply_text(
            "Commands:\n/start — Main menu\n/help — This message",
            reply_markup=main_menu_markup(),
        )
    else:
        await send_restricted_message(update.message, update.effective_user)

async def myid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(f"Your ID: {update.effective_user.id}")

# ── Admin commands ─────────────────────────────────────────────
async def approve_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    global access_data
    if not context.args:
        await update.message.reply_text("Usage: /approve <user_id>")
        return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("Invalid user ID.")
        return
    approved = access_data.get("approved_users", [])
    if uid not in approved:
        approved.append(uid)
        access_data["approved_users"] = approved
        save_access(access_data)
    await update.message.reply_text(f"✅ User {uid} approved.")

async def removeaccess_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    global access_data
    if not context.args:
        await update.message.reply_text("Usage: /removeaccess <user_id>")
        return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("Invalid user ID.")
        return
    approved = access_data.get("approved_users", [])
    if uid in approved:
        approved.remove(uid)
        access_data["approved_users"] = approved
    subs = access_data.get("subscriptions", {})
    subs.pop(str(uid), None)
    access_data["subscriptions"] = subs
    save_access(access_data)
    await update.message.reply_text(f"✅ User {uid} removed.")

async def maintenance_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    data = load_json(MAINTENANCE_FILE, {"enabled": False})
    data["enabled"] = not data.get("enabled", False)
    save_json(MAINTENANCE_FILE, data)
    status = "ON" if data["enabled"] else "OFF"
    await update.message.reply_text(f"Maintenance mode: {status}")

async def broadcast_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    if not context.args:
        await update.message.reply_text("Usage: /broadcast <message>")
        return
    text = " ".join(context.args)
    approved = access_data.get("approved_users", [])
    sent, failed = 0, 0
    for uid in approved:
        try:
            await context.bot.send_message(chat_id=uid, text=text)
            sent += 1
        except Exception:
            failed += 1
        await asyncio.sleep(0.05)
    await update.message.reply_text(f"Broadcast done. Sent: {sent}, Failed: {failed}")

async def approvedlist_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    approved = access_data.get("approved_users", [])
    subs = access_data.get("subscriptions", {})
    lines = [f"Total: {len(approved)} users\n"]
    for uid in approved[:50]:
        sub = subs.get(str(uid), {})
        plan = sub.get("plan", "approved")
        expires = sub.get("expires_at", "—")[:10] if sub.get("expires_at") else "lifetime"
        lines.append(f"• {uid} [{plan}] exp:{expires}")
    await update.message.reply_text("\n".join(lines) or "No users.")

async def waitlist_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    try:
        conn = get_sqlite_connection()
        rows = conn.execute("SELECT user_id, username, full_name, joined_at FROM waitlist ORDER BY joined_at DESC").fetchall()
        conn.close()
    except Exception as e:
        await update.message.reply_text(f"Error: {e}")
        return
    if not rows:
        await update.message.reply_text("Waitlist is empty.")
        return
    lines = [f"📋 Waitlist — {len(rows)} users\n"]
    for r in rows[:50]:
        tag = f"@{r['username']}" if r['username'] else r['full_name'] or "—"
        lines.append(f"• {r['user_id']} {tag} ({r['joined_at'][:10]})")
    await update.message.reply_text("\n".join(lines))

async def notify_waitlist_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Admin: /notifywaitlist <message> — Bekleme listesindeki herkese mesaj gönder."""
    if not is_admin(update.effective_chat.id):
        return
    if not context.args:
        await update.message.reply_text("Usage: /notifywaitlist <message>")
        return
    text = " ".join(context.args)
    try:
        conn = get_sqlite_connection()
        rows = conn.execute("SELECT user_id FROM waitlist").fetchall()
        conn.close()
    except Exception as e:
        await update.message.reply_text(f"Error: {e}")
        return
    sent, failed = 0, 0
    for r in rows:
        try:
            await context.bot.send_message(chat_id=r["user_id"], text=f"📢 PGSM Update\n\n{text}")
            sent += 1
        except Exception:
            failed += 1
        await asyncio.sleep(0.05)
    await update.message.reply_text(f"Waitlist notified. Sent: {sent}, Failed: {failed}")

async def messageuser_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not is_admin(update.effective_chat.id):
        return
    if len(context.args) < 2:
        await update.message.reply_text("Usage: /messageuser <user_id> <message>")
        return
    try:
        uid = int(context.args[0])
    except ValueError:
        await update.message.reply_text("Invalid user ID.")
        return
    text = " ".join(context.args[1:])
    try:
        await context.bot.send_message(chat_id=uid, text=f"📢 Message from admin:\n\n{text}")
        await update.message.reply_text(f"✅ Sent to {uid}.")
    except Exception as e:
        await update.message.reply_text(f"Failed: {e}")

# ============================================================
# BUTTON HANDLER
# ============================================================
async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass
    chat_id = query.message.chat_id
    user_id = query.from_user.id

    # Debounce
    now_ts = time.time()
    if now_ts - _last_callback_time.get(user_id, 0) < CALLBACK_DEBOUNCE_SECONDS:
        return
    _last_callback_time[user_id] = now_ts

    if blocked_by_maintenance(chat_id) and query.data not in ("support_unregistered", "restricted_home"):
        await query.message.reply_text("🔧 Bot is under maintenance. Please try again later.")
        return

    data = query.data

    # ── My Profile ──
    if data == "my_profile":
        if not can_use_bot(chat_id):
            await send_restricted_message(query.message, query.from_user)
            return
        await handle_profile(update, context)
        return

    # ── Deposit (Add Funds) ──
    if data == "deposit_menu":
        if not can_use_bot(chat_id):
            await send_restricted_message(query.message, query.from_user)
            return
        await handle_deposit_menu(update, context)
        return

    if data in ("dep_usdc", "dep_ltc"):
        if not can_use_bot(chat_id):
            await send_restricted_message(query.message, query.from_user)
            return
        coin = "usdc" if data == "dep_usdc" else "ltc"
        await handle_deposit_amount(update, context, coin)
        return

    if data == "dep_check":
        if not can_use_bot(chat_id):
            await send_restricted_message(query.message, query.from_user)
            return
        await handle_deposit_check(update, context)
        return

    # ── Web login ──
    if data == "web_login":
        if not can_use_bot(chat_id):
            await send_restricted_message(query.message, query.from_user)
            return
        await handle_web_login(update, context)
        return

    # ── Main menu ──
    if data == "main_menu":
        support_mode_users.discard(user_id)
        if can_use_bot(chat_id):
            await show_main_menu(query.message)
        else:
            await send_restricted_message(query.message, query.from_user)
        return

    # ── Restricted home ──
    if data == "restricted_home":
        support_mode_users.discard(user_id)
        await send_restricted_message(query.message, query.from_user)
        return

    # ── Support (aktif üye) ──
    if data == "support":
        if not can_use_bot(chat_id):
            await send_restricted_message(query.message, query.from_user)
            return
        support_mode_users.add(user_id)
        await query.message.reply_text(
            "🎧 Support\n\nType your message and send it.\n\nFormat:\nIssue: ...\nMessage: ...\n\nWe'll get back to you shortly.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="main_menu")]]),
        )
        return

    # ── Support (kayıtsız kullanıcı) ──
    if data == "support_unregistered":
        support_mode_users.add(user_id)
        await query.message.reply_text(
            "🎧 Support\n\nYou can reach our team below.\nType your message and send it.",
            reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="restricted_home")]]),
        )
        return

    # ── Abonelik plan seçimi ──
    if data in ("sub_monthly", "sub_lifetime"):
        plan = "monthly" if data == "sub_monthly" else "lifetime"
        price = MONTHLY_PRICE_USD if plan == "monthly" else LIFETIME_PRICE_USD
        plan_name = MONTHLY_ACCESS_NAME if plan == "monthly" else LIFETIME_ACCESS_NAME
        price_str = f"${price:.0f}/month" if plan == "monthly" else f"${price:.0f} one-time"
        await query.message.reply_html(
            f"📋 <b>{plan_name}</b>\n\nPrice: <b>{price_str}</b>\n\n"
            "🔒 <b>Enrollment is currently closed.</b>\n\n"
            "New memberships are temporarily suspended. "
            "Join the waitlist to be notified the moment spots open up.",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("📋 Join the Waitlist", callback_data="join_waitlist")],
                [InlineKeyboardButton("🔙 Back",              callback_data="restricted_home")],
            ]),
        )
        return

    # ── Ödeme başlat ──
    if data.startswith("subpay_"):
        parts = data.split("_")
        plan = parts[1]
        coin_key = parts[2]
        coin = "USDC_SOLANA" if coin_key == "usdc" else "LTC"
        price = MONTHLY_PRICE_USD if plan == "monthly" else LIFETIME_PRICE_USD
        plan_name = MONTHLY_ACCESS_NAME if plan == "monthly" else LIFETIME_ACCESS_NAME

        # Bekleyen ödeme var mı?
        existing = get_user_activation_payment(user_id)
        if existing and existing.get("plan") == plan and existing.get("coin") == coin:
            address = existing["address"]
            expires = existing.get("expires_at", "")[:16]
            # QR kodlu gösterim — send_payment_with_qr ile tutarlı
            await send_payment_with_qr(
                target=query.message,
                coin=coin,
                usd_amount=price,
                address=address,
                payment_id=existing.get("payment_id", ""),
                expires=expires,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("✅ I Paid — Check Status", callback_data="check_activation")],
                    [InlineKeyboardButton("🔙 Back", callback_data="restricted_home")],
                ]),
            )
            return

        # Yeni ödeme oluştur
        try:
            rec = create_activation_payment(
                user_id=user_id,
                coin=coin,
                full_name=query.from_user.full_name,
                username=f"@{query.from_user.username}" if query.from_user.username else "No username",
                plan=plan,
            )
        except Exception as e:
            logger.error(f"create_activation_payment error: {e}", exc_info=True)
            await query.message.reply_text(f"⚠️ Could not generate payment address.\nError: {e}\n\nPlease try again or contact support.")
            return
        address = rec["address"]
        expires = rec.get("expires_at", "")[:16]

        await send_payment_with_qr(
            target=query.message,
            coin=coin,
            usd_amount=price,
            address=address,
            payment_id=rec["payment_id"],
            expires=expires,
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ I Paid — Check Status", callback_data="check_activation")],
                [InlineKeyboardButton("🔙 Back", callback_data="restricted_home")],
            ]),
        )

        # Admin'e bildir
        try:
            price_str = f"${price:.0f}/month" if plan == "monthly" else f"${price:.0f} one-time"
            await context.bot.send_message(
                chat_id=ADMIN_CHAT_ID,
                text=(
                    f"🔔 New Subscription Payment Started\n\n"
                    f"Plan: {plan_name}\nPrice: {price_str}\n"
                    f"Payment ID: {rec['payment_id']}\n"
                    f"User: {query.from_user.full_name} ({f'@{query.from_user.username}' if query.from_user.username else 'No username'})\n"
                    f"User ID: {user_id}\nCoin: {coin}\nAddress: {address}"
                ),
            )
        except Exception:
            pass
        return

    # ── Ödeme kontrol ──
    if data == "check_activation":
        if _is_subscription_active(user_id):
            await query.answer("Your account is already active!", show_alert=True)
            await show_main_menu(query.message)
            return
        existing = get_user_activation_payment(user_id)
        if not existing:
            await query.answer("No pending payment found.", show_alert=True)
            return
        await query.answer("Payment is being monitored automatically. You'll be notified once confirmed.", show_alert=True)
        return

    # ── Waitlist ──
    if data == "join_waitlist":
        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        username = query.from_user.username or ""
        full_name = query.from_user.full_name or ""
        try:
            conn = get_sqlite_connection()
            conn.execute(
                "INSERT OR IGNORE INTO waitlist (user_id, username, full_name, joined_at) VALUES (?, ?, ?, ?)",
                (user_id, username, full_name, now_str),
            )
            conn.commit()
            already = conn.execute("SELECT joined_at FROM waitlist WHERE user_id = ?", (user_id,)).fetchone()
            conn.close()
            if already and already["joined_at"] != now_str:
                await query.answer("You're already on the waitlist!", show_alert=True)
            else:
                await query.message.reply_html(
                    "✅ <b>You're on the waitlist!</b>\n\n"
                    "We'll notify you directly as soon as new memberships open up. "
                    "Thank you for your interest in PGSM.",
                    reply_markup=InlineKeyboardMarkup([
                        [InlineKeyboardButton("💬 PGSM Chat",       url=CHAT_LINK_PUBLIC)],
                        [InlineKeyboardButton("📢 PGSM Stock News", url=NEWS_LINK_PUBLIC)],
                    ]),
                )
                try:
                    tg_tag = f"@{username}" if username else full_name
                    await query.get_bot().send_message(
                        chat_id=ADMIN_CHAT_ID,
                        text=f"📋 New Waitlist Entry\n\nUser: {tg_tag}\nID: {user_id}\nTime: {now_str}",
                    )
                except Exception:
                    pass
        except Exception as e:
            logger.error(f"waitlist error: {e}")
            await query.answer("Could not process your request. Please try again.", show_alert=True)
        return

    # Bilinmeyen callback
    logger.debug(f"Unhandled callback: {data}")

# ============================================================
# MESSAGE HANDLER
# ============================================================
async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message or not update.message.text:
        return
    text = update.message.text
    if text.startswith("/"):
        return
    user = update.message.from_user
    user_id = user.id
    chat_id = update.effective_chat.id
    username = f"@{user.username}" if user.username else "No username"
    full_name = user.full_name

    # ── Deposit miktar girişini yakala ──
    if context.user_data.get("dep_step") == "awaiting_amount" and can_use_bot(user_id):
        await handle_deposit_confirm(update, context)
        return

    # Support mode aktifse ilet
    if user_id in support_mode_users:
        tg_name = f"@{user.username}" if user.username else user.full_name
        endpoint = f"{WEB_BASE_URL}/api/support/unregistered"
        category = "general" if can_use_bot(user_id) else "unregistered"
        payload  = {
            "secret":   BOT_SECRET,
            "user_id":  user_id,
            "tg_name":  tg_name,
            "subject":  "Support via Telegram Bot",
            "message":  text,
            "category": category,
        }
        try:
            resp = http_requests.post(endpoint, json=payload, timeout=10)
            if resp.status_code != 200:
                raise ValueError(resp.text[:100])
        except Exception as e:
            logger.error(f"Support forward error: {e}")
            await update.message.reply_text("Could not send support message. Please try again shortly.")
            return
        support_mode_users.discard(user_id)
        back_markup = InlineKeyboardMarkup([[InlineKeyboardButton("🏠 Main Menu", callback_data="main_menu")]])
        await update.message.reply_text("✅ Your support request has been received. Our team will get back to you shortly.", reply_markup=back_markup)
        return

    # Diğer mesajlar
    if can_use_bot(chat_id):
        await show_main_menu(update.message)
    else:
        await send_restricted_message(update.message, update.effective_user)

# ============================================================
# ERROR HANDLER
# ============================================================
async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.error(f"Exception: {context.error}", exc_info=context.error)

# ============================================================
# JOIN REQUEST HANDLER
# ============================================================
async def handle_join_request(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Kanala/gruba katılım isteğini abonelik kontrolüyle onayla veya reddet."""
    req     = update.chat_join_request
    user_id = req.from_user.id
    chat_id = req.chat.id
    sub     = check_subscription(user_id)
    if sub.get("active"):
        await context.bot.approve_chat_join_request(chat_id, user_id)
        logger.info(f"JOIN REQUEST APPROVED: user={user_id} chat={chat_id}")
    else:
        await context.bot.decline_chat_join_request(chat_id, user_id)
        logger.info(f"JOIN REQUEST DECLINED: user={user_id} chat={chat_id}")
        try:
            await context.bot.send_message(
                user_id,
                "❌ Bu kanala erişim için aktif abonelik gereklidir.\n\n"
                "Abone olmak için /start komutunu kullanabilirsin.",
            )
        except Exception:
            pass  # Kullanıcı botu başlatmamış olabilir


# ============================================================
# BUILD & MAIN
# ============================================================
def build_application() -> Application:
    global access_data
    access_data = load_access()
    init_sqlite_db()

    if not init_wallet():
        logger.warning("Wallet not initialized — payments will fail")

    # Polling (get_updates) + ekstra istekler (send_message vb.) için yeterli pool.
    # Varsayılan pool boyutu çok küçük olduğundan notify_stock gibi paralel
    # isteklerde "Pool timeout" hatası alınıyordu.
    _request = HTTPXRequest(
        connection_pool_size=16,
        pool_timeout=15.0,
        connect_timeout=10.0,
        read_timeout=20.0,
        write_timeout=10.0,
    )
    app = (
        Application.builder()
        .token(TOKEN)
        .request(_request)
        .get_updates_request(_request)
        .post_init(_capture_notify_loop)
        .build()
    )
    # Commands
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_command))
    app.add_handler(CommandHandler("myid", myid))
    app.add_handler(CommandHandler("approve", approve_command))
    app.add_handler(CommandHandler("removeaccess", removeaccess_command))
    app.add_handler(CommandHandler("maintenance", maintenance_command))
    app.add_handler(CommandHandler("broadcast", broadcast_command))
    app.add_handler(CommandHandler("approvedlist", approvedlist_command))
    app.add_handler(CommandHandler("messageuser", messageuser_command))
    app.add_handler(CommandHandler("waitlist", waitlist_command))
    app.add_handler(CommandHandler("notifywaitlist", notify_waitlist_command))

    # Callbacks & messages
    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    app.add_handler(ChatJoinRequestHandler(handle_join_request))

    # Jobs — threading-based (no job-queue dependency)
    def _run_job_thread(coro_func, interval, first_delay):
        import time as _time
        _time.sleep(first_delay)
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        while True:
            try:
                loop.run_until_complete(coro_func(None))
            except Exception as e:
                logger.error(f"Job error: {e}")
            _time.sleep(interval)

    t1 = threading.Thread(target=_run_job_thread, args=(check_activation_payments_job, 60, 30), daemon=True)
    t1.start()
    logger.info("Activation monitor started (every 60s)")

    t2 = threading.Thread(target=_run_job_thread, args=(check_deposits_expiry_job, 60, 45), daemon=True)
    t2.start()
    logger.info("Deposit expiry monitor started (every 60s)")

    # Bot commands menu
    async def set_commands(application):
        await application.bot.set_my_commands([
            BotCommand("start", "Open main menu"),
            BotCommand("help", "Help"),
        ])
    app.post_init = set_commands
    app.add_error_handler(error_handler)
    return app

# ─────────────────────────────────────────────────────────────────
# İç HTTP sunucu — Railway 1 (app.py) buraya webhook atar
# POST /internal/notify_stock  →  bot kanalına mesaj gönderir
# ─────────────────────────────────────────────────────────────────
async def _capture_notify_loop(application) -> None:
    """Application başlatıldığında çalışan event loop'u güvenilir şekilde yakalar."""
    global _notify_loop
    _notify_loop = asyncio.get_running_loop()
    logger.info("notify_stock: event loop yakalandı")

def _start_notify_server():
    """Flask HTTP sunucusunu ayrı bir thread'de başlatır."""
    from flask import Flask as _Flask, request as _req, jsonify as _jsonify
    import threading as _threading

    _flask_app = _Flask("notify_server")
    _flask_app.logger.disabled = True
    import logging as _logging
    _logging.getLogger("werkzeug").setLevel(_logging.ERROR)

    @_flask_app.route("/internal/notify_stock", methods=["POST"])
    def _notify_stock():
        data = _req.get_json(force=True, silent=True) or {}

        # Güvenlik kontrolü
        _secret = NOTIFY_BOT_SECRET.strip()
        if _secret:
            incoming = data.get("secret", "")
            if incoming != _secret:
                return _jsonify({"error": "unauthorized"}), 401

        chat_id = data.get("chat_id", "")
        text    = data.get("text", "")

        if not chat_id or not text:
            return _jsonify({"error": "chat_id ve text zorunlu"}), 400

        if _notify_bot_app is None:
            return _jsonify({"error": "bot henüz hazır değil"}), 503

        # Bot'un event loop'una mesajı gönder
        import asyncio as _asyncio

        async def _send():
            await _notify_bot_app.bot.send_message(
                chat_id=int(chat_id),
                text=text
            )

        try:
            if _notify_loop and _notify_loop.is_running():
                fut = _asyncio.run_coroutine_threadsafe(_send(), _notify_loop)
                fut.result(timeout=15)
            else:
                logger.warning("notify_stock: event loop henüz hazır değil, fallback deneniyor")
                _asyncio.run(_send())
            logger.info(f"notify_stock: mesaj gönderildi chat_id={chat_id}")
            return _jsonify({"success": True})
        except Exception as e:
            logger.warning(f"notify_stock send error: {e}")
            return _jsonify({"error": str(e)}), 500

    @_flask_app.route("/health", methods=["GET"])
    def _health():
        return _jsonify({"status": "ok", "service": "pgsm-bot-notify"})

    def _run():
        _flask_app.run(host="0.0.0.0", port=NOTIFY_HTTP_PORT, use_reloader=False)

    t = _threading.Thread(target=_run, daemon=True, name="notify-http-server")
    t.start()
    logger.info(f"notify_server started on port {NOTIFY_HTTP_PORT}")


def main() -> None:
    if not TOKEN:
        logger.critical("BOT_TOKEN not set")
        return
    if not ADMIN_CHAT_ID:
        logger.critical("ADMIN_CHAT_ID not set")
        return

    while True:
        try:
            logger.info(f"Starting {APP_VERSION}...")
            app = build_application()
            # Notify HTTP sunucusunu başlat (Railway 1'den webhook alır)
            global _notify_bot_app
            _notify_bot_app = app
            _start_notify_server()
            app.run_polling()
        except KeyboardInterrupt:
            print("Bot stopped.")
            close_sqlite_connection()
            break
        except Exception as e:
            logger.error(f"Bot crashed: {e}")
            traceback.print_exc()
            print("Restarting in 10 seconds...")
            time.sleep(10)

if __name__ == "__main__":
    main()
