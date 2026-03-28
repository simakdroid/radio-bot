from __future__ import annotations
from typing import List, Dict, Tuple, Optional
import asyncio
import logging
import os
import re
import sqlite3
import threading
from dataclasses import dataclass
from datetime import date, datetime, time, timedelta, timezone
from typing import Iterable

import requests
from dotenv import load_dotenv
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.ext import MessageHandler, filters
from telegram.error import NetworkError, TimedOut
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes

EIBI_URL = "http://www.eibispace.de/dx/eibi.txt"
README_URL = "http://www.eibispace.de/dx/README.TXT"
WEEKDAYS = ["Mo", "Tu", "We", "Th", "Fr", "Sa", "Su"]
ITU_RE = re.compile(r"^[A-Z]{1,4}$")
TIME_RE = re.compile(r"^\d{4}-\d{4}$")
FREQ_RE = re.compile(r"^\d+(?:\.\d+)?$")
MONTH_TOKEN_RE = re.compile(r"^(\d{1,2})([A-Z][a-z]{2})$")
NTH_WEEKDAY_RE = re.compile(r"^(\d)\.(Mo|Tu|We|Th|Fr|Sa|Su)$")
LAST_NUM_RE = re.compile(r"^Last([1-7])$")
LAST_WEEKDAY_RE = re.compile(r"^Last(Mo|Tu|We|Th|Fr|Sa|Su)$")
ALT_WEEKDAY_RE = re.compile(r"^alt(Mo|Tu|We|Th|Fr|Sa|Su)$")
UP_TO_DAY_RE = re.compile(r"^(Mo|Tu|We|Th|Fr|Sa|Su)-(\d{1,2})$")
MONTH_MAP = {
    "Jan": 1,
    "Feb": 2,
    "Mar": 3,
    "Apr": 4,
    "May": 5,
    "Jun": 6,
    "Jul": 7,
    "Aug": 8,
    "Sep": 9,
    "Oct": 10,
    "Nov": 11,
    "Dec": 12,
}
TELEGRAM_MESSAGE_LIMIT = 4000
CACHE_TTL_SECONDS = 24 * 60 * 60
_eibi_cache_lock = threading.Lock()
_eibi_cache_lines: list[str] | None = None
_eibi_cache_ts: datetime | None = None
DB_PATH_DEFAULT = os.path.join("data", "eibi.sqlite3")
_today_cache_lock = threading.Lock()
_today_cache_date: date | None = None
_today_cache_entries: list[Broadcast] | None = None
_db_refresh_lock = threading.Lock()
LANGUAGE_NAMES = {
    # Special codes
    "-TS": "Сигналы времени",
    "-CW": "Телеграф",
    "-TY": "Телетайп",
    "-MX": "Музыка",
    "-EC": "Empty Carrier",
    "-HF": "Станции авиационной связи",
    "Aud": "Проповедь Папы Римского",
    # Single-letter codes (most common)
    "A": "Арабский",
    "C": "Китайский",
    "D": "Немецкий",
    "E": "Английский",
    "F": "Французский",
    "G": "Немецкий",
    "H": "Хинди",
    "I": "Итальянский",
    "J": "Японский",
    "K": "Корейский",
    "P": "Португальский",
    "R": "Русский",
    "S": "Испанский",
    "T": "Турецкий",
    "U": "Украинский",
    # Two-letter codes
    "AF": "Afrikaans",
    "AM": "Amharic",
    "AR": "Армянский",
    "AZ": "Азербайджанский",
    "BA": "Башкирский",
    "BE": "Bengali",
    "BG": "Болгарский",
    "BI": "Bilen",
    "BJ": "Bhojpuri",
    "BM": "Bambara",
    "BN": "Burmese",
    "BR": "Burmese",
    "BS": "Bosnian",
    "BU": "Болгараский",
    "CA": "Cantonese",
    "CE": "Чешский",
    "CH": "Chin",
    "CO": "Corsican",
    "CR": "Creole",
    "CS": "Чешский",
    "CT": "Catalan",
    "CW": "Chewa",
    "CZ": "Чешский",
    "DA": "Датский",
    "DE": "Немецкий",
    "DI": "Dinka",
    "DR": "Dari",
    "DU": "Dusun",
    "DY": "Dyula",
    "DZ": "Dzongkha",
    "EC": "Эстонский",
    "EG": "Египетский арабский",
    "EO": "Эсперанто",
    "ES": "Эстонский",
    "ET": "Эстонский",
    "EU": "Basque",
    "FA": "Faroese",
    "FI": "Финский",
    "FJ": "Fijian",
    "FO": "Фарси",
    "FP": "Filipino",
    "FS": "Фарси",
    "FT": "Fiote",
    "FU": "Fulani",
    "FUJ": "FutaJalon",
    "GA": "Garhwali",
    "GE": "Грузинский",
    "GL": "Galician",
    "GR": "Греческий",
    "GU": "Gujarati",
    "GUA": "Guarani",
    "HA": "Hausa",
    "HAR": "Haryanvi",
    "HB": "Hebrew",
    "HD": "Hindko",
    "HI": "Хинди",
    "HK": "Hakka",
    "HM": "Hmong",
    "HO": "Ho",
    "HR": "Хорватский",
    "HU": "Венгерский",
    "HY": "Армянский",
    "HZ": "Hazaragi",
    "IB": "Iban",
    "IG": "Igbo",
    "IL": "Hebrew",
    "IN": "Индонезийский",
    "IS": "Исландский",
    "IT": "Итальянский",
    "JA": "Японский",
    "JV": "Javanese",
    "KA": "Karen",
    "KK": "Казахский",
    "KM": "Khmer",
    "KN": "Kannada",
    "KO": "Корейский",
    "KU": "Kurdish",
    "KY": "Кыргызский",
    "LA": "Lao",
    "LI": "Литовский",
    "LO": "Lao",
    "LT": "Литовский",
    "LV": "Латышский",
    "MA": "Мальтийский",
    "MC": "Македонский",
    "ME": "Черногорский",
    "MG": "Malagasy",
    "MI": "Маори",
    "MK": "Македонский",
    "ML": "Malayalam",
    "MN": "Монгольский",
    "MO": "Молдавский",
    "MR": "Marathi",
    "MS": "Малайский",
    "MT": "Мальтийский",
    "MY": "MМалайский",
    "NA": "Непальский",
    "NE": "Непальский",
    "NL": "Dutch",
    "NO": "Норвежский",
    "NS": "Норвежский",
    "OM": "Oromo",
    "OR": "Oriya",
    "PA": "Punjabi",
    "PE": "Persian",
    "PL": "Польский",
    "PS": "Pashto",
    "PT": "Португальский",
    "RM": "Румынский",
    "RO": "Румынский",
    "RU": "Русский",
    "SA": "Санскрит",
    "SB": "Сербский",
    "SD": "Sindhi",
    "SE": "Шведский",
    "SI": "Sinhala",
    "SK": "Словацкий",
    "SL": "Словенский",
    "SO": "Сомалийский",
    "SQ": "Албанский",
    "SR": "Сербский",
    "SU": "Swahili",
    "SV": "Шведский",
    "SW": "Swahili",
    "TA": "Tamil",
    "TE": "Telugu",
    "TG": "Таджикский",
    "TH": "Тайский",
    "TI": "Tigrinya",
    "TK": "Туркменский",
    "TL": "Tagalog",
    "TN": "Tongan",
    "TO": "Tongan",
    "TR": "Турецкий",
    "TT": "Татарский",
    "TW": "Taiwanese",
    "UG": "Уйгурский",
    "UK": "Украинский",
    "UR": "Урду",
    "UZ": "Узбекский",
    "VI": "Вьетнамский",
    "WO": "Wolof",
    "XH": "Xhosa",
    "YO": "Yoruba",
    "ZA": "Zhuang",
    "ZH": "Китайский",
    "ZU": "Zulu",
    # Three-letter codes (combinations)
    "A,F": "Арабо/французский",
    "M": "Мандарин (китайский)",
    "VN": "Вьетнамский",
    "BE": "Бенгальский",
    "HI": "Хинди",
}

# Словарь стран по ITU-кодам (для группировки станций по странам)
ITU_NAMES = {
    "ALB": "Албания",
    "ALS": "Аляска (США)",
    "ARM": "Армения",
    "AZE": "Азербайджан",
    "B": "Бразилия",
    "BD": "Бангладеш",
    "BEL": "Бельгия",
    "BG": "Болгария",
    "BHR": "Бахрейн",
    "BIH": "Босния и Герцеговина",
    "BRU": "Бруней",
    "CHN": "Китай",
    "CAM": "Камбоджа",
    "CAN": "Канада",
    "CHL": "Чили",
    "CL": "Шри-Ланка",
    "CNR": "Канарские о-ва",
    "CO": "Колумбия",
    "COD": "Демократическая республика Конго",
    "COG": "Конго",
    "CS": "Сербия и Черногория",
    "CVA": "Ватикан",
    "CYM": "Острова Кайман",
    "CZE": "Чехия",
    "D": "Германия",
    "DJI": "Джибути",
    "DOM": "Доминиканская республика",
    "E": "Испания",
    "EGY": "Египет",
    "EQA": "Эквадор",
    "ERI": "Эритрея",
    "EST": "Эстония",
    "ETH": "Эфиопия",
    "F": "Франция",
    "FIN": "Финляндия",
    "G": "Великобритания",
    "GEO": "Грузия",
    "GH": "Гана",
    "GNE": "Экваториальная Гвинея",
    "GR": "Греция",
    "GTM": "Гватемала",
    "H": "Венгрия",
    "HAW": "Гавайи",
    "HK": "Гонконг",
    "HR": "Хорватия",
    "I": "Италия",
    "IL": "Израиль",
    "IND": "Индия",
    "IR": "Иран",
    "IRQ": "Ирак",
    "ISL": "Исландия",
    "J": "Япония",
    "JOR": "Иордания",
    "K": "Кения",
    "KGZ": "Кыргызстан",
    "KHM": "Камбоджа",
    "KIR": "Кирибати",
    "KOR": "Южная Корея",
    "KRE": "КНДР",
    "KWT": "Кувейт",
    "KZ": "Казахстан",
    "L": "Литва",
    "LAO": "Лаос",
    "LBN": "Ливан",
    "LBR": "Либерия",
    "LBY": "Ливия",
    "LS": "Лесото",
    "LT": "Литва",
    "LU": "Люксембург",
    "LV": "Латвия",
    "MA": "Марокко",
    "MAC": "Макао",
    "MAD": "Мадагаскар",
    "MAU": "Маврикий",
    "MC": "Монако",
    "MD": "Молдова",
    "MDG": "Мадагаскар",
    "MEX": "Мексика",
    "MHL": "Маршалловы о-ва",
    "MK": "Северная Македония",
    "ML": "Мали",
    "MLT": "Мальта",
    "MNG": "Монголия",
    "MNT": "Черногория",
    "MOZ": "Мозамбик",
    "MR": "Мавритания",
    "MT": "Мальта",
    "MUS": "Маврикий",
    "MW": "Малави",
    "MYA": "Мьянма",
    "N": "Норвегия",
    "NA": "Намибия",
    "NCL": "Новая Каледония",
    "NG": "Нигерия",
    "NIC": "Никарагуа",
    "NL": "Нидерланды",
    "NZ": "Новая Зеландия",
    "P": "Португалия",
    "PA": "Панама",
    "PE": "Перу",
    "PHL": "Филиппины",
    "POL": "Польша",
    "PNG": "Папуа-Новая Гвинея",
    "PR": "Пуэрто-Рико",
    "PS": "Палестина",
    "PY": "Парагвай",
    "Q": "Катар",
    "R": "Россия",
    "RA": "Аргентина",
    "RB": "Ботсвана",
    "RC": "Тайвань",
    "RCA": "Австралия",
    "RCC": "Остров Рождества",
    "RCH": "Чили",
    "RG": "Габон",
    "RH": "Гаити",
    "RI": "Индонезия",
    "RL": "Ливан",
    "RM": "Мадагаскар",
    "ROU": "Румыния",
    "RUS": "Россия",
    "RS": "Сербия",
    "RU": "Россия",
    "RWA": "Руанда",
    "S": "Швеция",
    "SA": "Саудовская Аравия",
    "SD": "Судан",
    "SDA": "Шпицберген",
    "SG": "Сингапур",
    "SGP": "Сингапур",
    "SVK": "Словакия",
    "SLA": "Сьерра-Леоне",
    "SLM": "Соломоновы о-ва",
    "SM": "Сан-Марино",
    "SMO": "Самоа",
    "SN": "Сенегал",
    "SO": "Сомали",
    "SOL": "Соломоновы о-ва",
    "SP": "Испания",
    "SR": "Суринам",
    "SSD": "Южный Судан",
    "ST": "Сан-Томе и Принсипи",
    "SUI": "Швейцария",
    "SV": "Сальвадор",
    "SWZ": "Эсватини",
    "SY": "Сирия",
    "SYR": "Сирия",
    "T": "Таиланд",
    "TAD": "Таджикистан",
    "TG": "Того",
    "TH": "Таиланд",
    "TJK": "Таджикистан",
    "TL": "Тимор-Лесте",
    "TM": "Туркменистан",
    "TN": "Тунис",
    "TO": "Тонга",
    "TR": "Турция",
    "TT": "Тринидад и Тобаго",
    "TUN": "Тунис",
    "TUR": "Турция",
    "TUV": "Тувалу",
    "TWN": "Тайвань",
    "UA": "Украина",
    "UAE": "ОАЭ",
    "UGA": "Уганда",
    "UK": "Великобритания",
    "UN": "Международные организации",
    "UR": "Уругвай",
    "USA": "Соединенные Штаты Америки",
    "UZB": "Узбекистан",
    "V": "Ватикан",
    "VAN": "Вануату",
    "VE": "Венесуэла",
    "VTN": "Вьетнам",
    "VU": "Вануату",
    "W": "Западное Самоа",
    "WS": "Самоа",
    "YEM": "Йемен",
    "YV": "Венесуэла",
    "Z": "Замбия",
    "ZAN": "Зимбабве",
    "ZB": "Замбия",
    "ZWE": "Зимбабве",
}


def format_itu_label(itu: str) -> str:
    """Возвращает название страны по ITU-коду или сам код, если название неизвестно."""
    return ITU_NAMES.get(itu, itu)


@dataclass(frozen=True)
class Broadcast:
    frequency: str
    time_utc: str
    days: str
    itu: str
    station: str
    lang: str
    target: str
    remarks: str


def is_header_or_empty(line: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return True
    if stripped.startswith("BC ") or stripped.startswith("http://"):
        return True
    if "FREQUENCY VERSION" in stripped:
        return True
    if stripped.startswith("Valid ") or stripped.startswith("Last update:"):
        return True
    if stripped.startswith("kHz Time(UTC) Days"):
        return True
    if set(stripped) == {"="}:
        return True
    return False


def last_day_of_month(input_date: date) -> int:
    if input_date.month == 12:
        next_month = date(input_date.year + 1, 1, 1)
    else:
        next_month = date(input_date.year, input_date.month + 1, 1)
    return (next_month - timedelta(days=1)).day


def parse_simple_weekday_set(days: str) -> set[str] | None:
    days = days.strip()
    if not days:
        return set(WEEKDAYS)

    if re.fullmatch(r"[1-7]+", days):
        return {WEEKDAYS[int(ch) - 1] for ch in days}

    if "-" in days and all(part in WEEKDAYS for part in days.split("-", 1)):
        start, end = days.split("-", 1)
        i_start = WEEKDAYS.index(start)
        i_end = WEEKDAYS.index(end)
        if i_start <= i_end:
            return set(WEEKDAYS[i_start : i_end + 1])
        return set(WEEKDAYS[i_start:] + WEEKDAYS[: i_end + 1])

    parts = re.split(r"[,\s]+", days)
    listed = {p for p in parts if p in WEEKDAYS}
    if listed:
        return listed

    return None


def is_active_on_date(days: str, on_date: date) -> bool:
    days = days.strip()
    weekday_name = WEEKDAYS[on_date.weekday()]
    weekday_num = on_date.weekday() + 1  # 1=Monday ... 7=Sunday

    simple = parse_simple_weekday_set(days)
    if simple is not None:
        return weekday_name in simple

    nth_match = NTH_WEEKDAY_RE.fullmatch(days)
    if nth_match:
        nth = int(nth_match.group(1))
        target_weekday = nth_match.group(2)
        if weekday_name != target_weekday:
            return False
        ordinal = ((on_date.day - 1) // 7) + 1
        return ordinal == nth

    last_num_match = LAST_NUM_RE.fullmatch(days)
    if last_num_match:
        target_num = int(last_num_match.group(1))
        if weekday_num != target_num:
            return False
        return on_date.day + 7 > last_day_of_month(on_date)

    last_name_match = LAST_WEEKDAY_RE.fullmatch(days)
    if last_name_match:
        target_weekday = last_name_match.group(1)
        if weekday_name != target_weekday:
            return False
        return on_date.day + 7 > last_day_of_month(on_date)

    alt_weekday_match = ALT_WEEKDAY_RE.fullmatch(days)
    if alt_weekday_match:
        # "altFr" means alternating Fridays; treat as Friday schedule.
        return weekday_name == alt_weekday_match.group(1)

    up_to_day_match = UP_TO_DAY_RE.fullmatch(days)
    if up_to_day_match:
        from_weekday = up_to_day_match.group(1)
        day_limit = int(up_to_day_match.group(2))
        return weekday_name == from_weekday and on_date.day <= day_limit

    month_token_match = MONTH_TOKEN_RE.fullmatch(days)
    if month_token_match:
        token_day = int(month_token_match.group(1))
        token_month = MONTH_MAP.get(month_token_match.group(2))
        return token_month == on_date.month and token_day == on_date.day

    # Rare meta-markers ("Ram", "Haj", "irr", "test", "tent", "alt", etc.)
    # are intentionally not auto-included in strict mode.
    return False


def parse_line(line: str) -> Broadcast | None:
    if is_header_or_empty(line):
        return None

    parts = line.split()
    if len(parts) < 7:
        return None
    if not FREQ_RE.match(parts[0]) or not TIME_RE.match(parts[1]):
        return None

    frequency = parts[0]
    time_utc = parts[1]

    third = parts[2]
    if ITU_RE.match(third):
        days = ""
        itu = third
        rest = parts[3:]
    else:
        days = third
        if len(parts) < 8:
            return None
        itu = parts[3]
        rest = parts[4:]

    if len(rest) < 4:
        return None

    lang = rest[-3]
    target = rest[-2]
    remarks = rest[-1]
    station = " ".join(rest[:-3]).strip()
    if not station:
        return None

    return Broadcast(
        frequency=frequency,
        time_utc=time_utc,
        days=days,
        itu=itu,
        station=station,
        lang=lang,
        target=target,
        remarks=remarks,
    )


def fetch_eibi_lines() -> Iterable[str]:
    global _eibi_cache_lines, _eibi_cache_ts
    now = datetime.now(timezone.utc)
    with _eibi_cache_lock:
        if _eibi_cache_lines is not None and _eibi_cache_ts is not None:
            age = (now - _eibi_cache_ts).total_seconds()
            if age < CACHE_TTL_SECONDS:
                return list(_eibi_cache_lines)

    response = requests.get(EIBI_URL, timeout=60)
    response.raise_for_status()
    lines = response.text.splitlines()
    with _eibi_cache_lock:
        _eibi_cache_lines = lines
        _eibi_cache_ts = now
    return list(lines)


def init_db(conn: sqlite3.Connection) -> None:
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS broadcasts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            frequency TEXT NOT NULL,
            time_utc TEXT NOT NULL,
            days TEXT NOT NULL,
            itu TEXT NOT NULL,
            station TEXT NOT NULL,
            lang TEXT NOT NULL,
            target TEXT NOT NULL,
            remarks TEXT NOT NULL
        )
        """
    )
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS metadata (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_broadcasts_station ON broadcasts(station)")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_broadcasts_lang ON broadcasts(lang)")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_broadcasts_itu ON broadcasts(itu)")
    conn.commit()


def ensure_db_parent_dir(db_path: str) -> None:
    parent_dir = os.path.dirname(db_path)
    if parent_dir:
        os.makedirs(parent_dir, exist_ok=True)


def clear_today_cache() -> None:
    global _today_cache_date, _today_cache_entries
    with _today_cache_lock:
        _today_cache_date = None
        _today_cache_entries = None


def get_last_refresh_date(conn: sqlite3.Connection) -> date | None:
    row = conn.execute("SELECT value FROM metadata WHERE key = 'last_refresh_utc_date'").fetchone()
    if not row:
        return None
    try:
        return datetime.strptime(row[0], "%Y-%m-%d").date()
    except ValueError:
        return None


def set_last_refresh_date(conn: sqlite3.Connection, day: date) -> None:
    conn.execute(
        """
        INSERT INTO metadata(key, value) VALUES('last_refresh_utc_date', ?)
        ON CONFLICT(key) DO UPDATE SET value = excluded.value
        """,
        (day.strftime("%Y-%m-%d"),),
    )
    conn.commit()


def has_broadcast_rows(conn: sqlite3.Connection) -> bool:
    row = conn.execute("SELECT 1 FROM broadcasts LIMIT 1").fetchone()
    return row is not None


def is_russian_aero_station(item: Broadcast) -> bool:
    """Проверяет, является ли станция русскоязычной с 'Aero' в названии (регистронезависимо)."""
    return item.lang == "R" and "AERO" in item.station.upper()


def refresh_db_from_source(db_path: str, now_utc: datetime) -> int:
    ensure_db_parent_dir(db_path)
    lines = fetch_eibi_lines()
    parsed = [item for line in lines if (item := parse_line(line)) is not None]

    # Исключаем русскоязычные станции с "Aero" в названии
    original_count = len(parsed)
    parsed = [item for item in parsed if not is_russian_aero_station(item)]
    excluded = original_count - len(parsed)
    if excluded:
        logging.info("Excluded %d Russian Aero stations.", excluded)

    conn = sqlite3.connect(db_path)
    try:
        init_db(conn)
        conn.execute("DELETE FROM broadcasts")
        conn.executemany(
            """
            INSERT INTO broadcasts (
                frequency, time_utc, days, itu, station, lang, target, remarks
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            [
                (
                    item.frequency,
                    item.time_utc,
                    item.days,
                    item.itu,
                    item.station,
                    item.lang,
                    item.target,
                    item.remarks,
                )
                for item in parsed
            ],
        )
        conn.commit()
        set_last_refresh_date(conn, now_utc.date())
    finally:
        conn.close()

    clear_today_cache()
    logging.info("Database refreshed from source. Rows: %d", len(parsed))
    return len(parsed)


def ensure_db_fresh_for_today(db_path: str, now_utc: datetime, allow_stale: bool = True) -> bool:
    ensure_db_parent_dir(db_path)
    conn = sqlite3.connect(db_path)
    try:
        init_db(conn)
        last_refresh = get_last_refresh_date(conn)
        has_rows = has_broadcast_rows(conn)
    finally:
        conn.close()

    if last_refresh == now_utc.date():
        return True

    # Avoid duplicate long refreshes when several handlers start simultaneously.
    if not _db_refresh_lock.acquire(blocking=False):
        return allow_stale and has_rows

    try:
        refresh_db_from_source(db_path, now_utc)
        return True
    except (requests.RequestException, sqlite3.Error):
        if allow_stale and has_rows:
            logging.warning("Using stale DB data because refresh failed.")
            return False
        raise
    finally:
        _db_refresh_lock.release()


def load_broadcasts_from_db(db_path: str) -> list[Broadcast]:
    ensure_db_parent_dir(db_path)
    conn = sqlite3.connect(db_path)
    try:
        init_db(conn)
        rows = conn.execute(
            """
            SELECT frequency, time_utc, days, itu, station, lang, target, remarks
            FROM broadcasts
            """
        ).fetchall()
    finally:
        conn.close()

    return [
        Broadcast(
            frequency=row[0],
            time_utc=row[1],
            days=row[2],
            itu=row[3],
            station=row[4],
            lang=row[5],
            target=row[6],
            remarks=row[7],
        )
        for row in rows
    ]


def get_broadcasts_for_today(now_utc: datetime, db_path: str) -> list[Broadcast]:
    global _today_cache_date, _today_cache_entries
    today = now_utc.date()
    with _today_cache_lock:
        if _today_cache_date == today and _today_cache_entries is not None:
            return list(_today_cache_entries)

    all_entries = load_broadcasts_from_db(db_path)
    entries: list[Broadcast] = []
    for item in all_entries:
        if is_active_on_date(item.days, now_utc.date()):
            entries.append(item)

    with _today_cache_lock:
        _today_cache_date = today
        _today_cache_entries = entries
    return entries


def group_stations_by_lang(entries: list[Broadcast]) -> dict[str, list[tuple[tuple[str, str], list[Broadcast]]]]:
    """Group all stations by their language (including multilingual stations)."""
    grouped_by_lang: dict[str, list[tuple[tuple[str, str], list[Broadcast]]]] = {}
    for item in entries:
        key = (item.station, item.itu)
        lang = item.lang
        # Объединяем все записи станции для каждого языка
        station_list = grouped_by_lang.setdefault(lang, [])
        # Ищем существующую станцию в группе
        for i, (existing_key, existing_items) in enumerate(station_list):
            if existing_key == key:
                existing_items.append(item)
                break
        else:
            station_list.append((key, [item]))
    return grouped_by_lang


def build_message(now_utc: datetime, entries: list[Broadcast]) -> str:
    date_str = now_utc.strftime("%Y-%m-%d")
    header = (
        f"Список станций на {date_str} (UTC)\n"
        f"Источник: {EIBI_URL}\n"
        f"Описание формата: {README_URL}\n"
    )
    if not entries:
        return header + "\nСегодня активных записей не найдено."

    grouped_by_lang = group_stations_by_lang(entries)
    if not grouped_by_lang:
        return header + "\nНе найдено станций."

    lines: list[str] = []
    for lang in sorted(grouped_by_lang.keys()):
        lines.append(f"{format_lang_label(lang)}:")
        for (station, itu), station_entries in sorted(grouped_by_lang[lang], key=lambda x: x[0][0].lower()):
            # Группируем частоты по времени вещания
            freq_by_time: dict[str, list[str]] = {}
            for e in station_entries:
                freq_by_time.setdefault(e.time_utc, []).append(e.frequency)
            
            # Выводим: станцию, потом частоты и время (по порядку от 00:00)
            lines.append(f"  ★ {station} ({itu}):")
            for time_utc, freqs in sorted(freq_by_time.items()):
                freqs_str = ", ".join(sorted(freqs, key=lambda f: float(f)))
                time_formatted = format_time_utc(time_utc)
                lines.append(f"    • {freqs_str}kHz {time_formatted}")
        lines.append("")

    body = "\n".join(lines).rstrip()
    total = sum(len(items) for items in grouped_by_lang.values())
    message = (
        f"{header}\n"
        f"Найдено станций: {total}\n"
        f"Языков: {len(grouped_by_lang)}\n\n"
        f"{body}"
    )
    return message


def build_language_specific_message(
    now_utc: datetime,
    entries: list[Broadcast],
    lang: str,
) -> str:
    date_str = now_utc.strftime("%Y-%m-%d")
    header = (
        f"Список станций на {date_str} (UTC)\n"
        f"Язык: {format_lang_label(lang)}\n"
        f"Источник: {EIBI_URL}\n"
    )
    # Фильтруем все записи для выбранного языка
    lang_entries = [e for e in entries if e.lang == lang]
    if not lang_entries:
        return header + "\nДля выбранного языка сегодня ничего не найдено."

    # Группируем по станциям
    stations_dict: dict[tuple[str, str], list[Broadcast]] = {}
    for e in lang_entries:
        key = (e.station, e.itu)
        stations_dict.setdefault(key, []).append(e)

    # Группируем по стране (ITU): {itu: [(station, itu), [entries]]}
    by_country: dict[str, list[tuple[tuple[str, str], list[Broadcast]]]] = {}
    for station_key, station_entries in stations_dict.items():
        itu = station_key[1]
        by_country.setdefault(itu, []).append((station_key, station_entries))

    # Сортируем станции внутри каждой страны по названию
    for itu in by_country:
        by_country[itu].sort(key=lambda x: x[0][0].lower())

    # Сортируем страны по названию ITU-кода
    sorted_countries = sorted(by_country.keys())

    lines: list[str] = []
    for itu in sorted_countries:
        lines.append(f"{format_itu_label(itu)}:")  # Заголовок страны
        for (station, _itu), station_entries in by_country[itu]:
            # Группируем частоты по времени вещания
            freq_by_time: dict[str, list[str]] = {}
            for e in station_entries:
                freq_by_time.setdefault(e.time_utc, []).append(e.frequency)
            
            # Выводим: станцию, потом частоты и время (по порядку от 00:00)
            lines.append(f"  ★ {station}:")
            for time_utc, freqs in sorted(freq_by_time.items()):
                freqs_str = ", ".join(sorted(freqs, key=lambda f: float(f)))
                time_formatted = format_time_utc(time_utc)
                lines.append(f"    • {freqs_str}kHz {time_formatted}")
        lines.append("")  # Пустая строка между странами

    message = f"{header}\nНайдено станций: {len(stations_dict)}\n\n" + "\n".join(lines).rstrip()
    return message


def build_current_language_message(
    now_utc: datetime,
    entries: list[Broadcast],
    lang: str,
    current_hour: int,
) -> str:
    """Построить сообщение для станций, вещающих в текущий час."""
    date_str = now_utc.strftime("%Y-%m-%d")
    header = (
        f"Станции на {date_str} (UTC)\n"
        f"Язык: {format_lang_label(lang)}\n"
        f"Текущий час: {current_hour}:00 UTC\n"
    )
    # Фильтруем записи для выбранного языка
    lang_entries = [e for e in entries if e.lang == lang]
    if not lang_entries:
        return header + f"\nДля выбранного языка в {current_hour}:00 UTC ничего не найдено."

    # Группируем по станциям
    stations_dict: dict[tuple[str, str], list[Broadcast]] = {}
    for e in lang_entries:
        key = (e.station, e.itu)
        stations_dict.setdefault(key, []).append(e)

    # Группируем по стране (ITU): {itu: [(station, itu), [entries]]}
    by_country: dict[str, list[tuple[tuple[str, str], list[Broadcast]]]] = {}
    for station_key, station_entries in stations_dict.items():
        itu = station_key[1]
        by_country.setdefault(itu, []).append((station_key, station_entries))

    # Сортируем станции внутри каждой страны по названию
    for itu in by_country:
        by_country[itu].sort(key=lambda x: x[0][0].lower())

    # Сортируем страны по названию ITU-кода
    sorted_countries = sorted(by_country.keys())

    lines: list[str] = []
    for itu in sorted_countries:
        lines.append(f"{format_itu_label(itu)}:")  # Заголовок страны
        for (station, _itu), station_entries in by_country[itu]:
            # Группируем частоты по времени вещания
            freq_by_time: dict[str, list[str]] = {}
            for e in station_entries:
                freq_by_time.setdefault(e.time_utc, []).append(e.frequency)
            
            lines.append(f"  ★ {station}:")
            for time_utc, freqs in sorted(freq_by_time.items()):
                freqs_str = ", ".join(sorted(freqs, key=lambda f: float(f)))
                time_formatted = format_time_utc(time_utc)
                lines.append(f"    • {freqs_str}kHz {time_formatted}")
        lines.append("")  # Пустая строка между странами

    message = f"{header}\nНайдено станций: {len(stations_dict)}\n\n" + "\n".join(lines).rstrip()
    return message


def split_message(text: str, limit: int = TELEGRAM_MESSAGE_LIMIT) -> list[str]:
    if len(text) <= limit:
        return [text]

    lines = text.splitlines()
    chunks: list[str] = []
    current = ""
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Если текущая строка - начало станции (★), проверяем, помещается ли вся станция
        if line.startswith("  ★ "):
            station_lines = [line]
            j = i + 1
            # Собираем все строки этой станции (частоты)
            while j < len(lines) and lines[j].startswith("    • "):
                station_lines.append(lines[j])
                j += 1
            
            station_text = "\n".join(station_lines)
            candidate = f"{current}\n{station_text}" if current else station_text
            
            # Если станция целиком не помещается в текущую часть
            if len(candidate) > limit:
                # Если есть текущий контент - сохраняем его
                if current:
                    chunks.append(current)
                    current = ""
                # Если одна станция больше лимита - разбиваем её
                if len(station_text) > limit:
                    # Разбиваем станцию построчно
                    for sl in station_lines:
                        if len(current) + len(sl) + 1 > limit:
                            chunks.append(current)
                            current = ""
                        current = f"{current}\n{sl}" if current else sl
                else:
                    current = station_text
                i = j
                continue
        
        candidate = f"{current}\n{line}" if current else line
        if len(candidate) <= limit:
            current = candidate
            i += 1
            continue

        if current:
            chunks.append(current)
            current = ""

        if len(line) <= limit:
            current = line
            i += 1
            continue

        start = 0
        while start < len(line):
            end = min(start + limit, len(line))
            chunks.append(line[start:end])
            start = end
        i += 1

    if current:
        chunks.append(current)
    return chunks if chunks else [text]


async def send_long_message(bot, chat_id: str | int, text: str) -> None:
    chunks = split_message(text)
    total = len(chunks)
    for idx, chunk in enumerate(chunks, start=1):
        if total > 1:
            chunk = f"({idx}/{total})\n{chunk}"
        await bot.send_message(chat_id=chat_id, text=chunk)


def unique_station_count(entries: list[Broadcast]) -> int:
    return len({(e.station, e.itu) for e in entries})


def format_time_utc(time_str: str) -> str:
    """Преобразует время из формата 0000-0100 в 00:00 - 01:00."""
    try:
        start, end = time_str.split("-")
        return f"{start[:2]}:{start[2:]} - {end[:2]}:{end[2:]}"
    except (ValueError, IndexError):
        return time_str


def format_lang_label(lang: str) -> str:
    return f"{lang} ({LANGUAGE_NAMES[lang]})" if lang in LANGUAGE_NAMES else lang


def is_special_lang_code(lang: str) -> bool:
    """Check if language code is a special non-language code."""
    return lang.startswith("-")


def build_language_keyboard(
    grouped_by_lang: dict[str, list[tuple[tuple[str, str], list[Broadcast]]]],
    min_stations: int = 10,
) -> InlineKeyboardMarkup:
    # Фильтруем языки: специальные коды всегда включаем, остальные - по порогу
    lang_counts = sorted(
        (
            (lang, len(items))
            for lang, items in grouped_by_lang.items()
            if is_special_lang_code(lang) or len(items) >= min_stations
        ),
        key=lambda x: x[0]
    )
    keyboard_rows: list[list[InlineKeyboardButton]] = []
    row: list[InlineKeyboardButton] = []
    for idx, (lang, count) in enumerate(lang_counts, start=1):
        row.append(InlineKeyboardButton(f"{format_lang_label(lang)} ({count})", callback_data=f"lang:{lang}"))
        if idx % 4 == 0:
            keyboard_rows.append(row)
            row = []
    if row:
        keyboard_rows.append(row)
    return InlineKeyboardMarkup(keyboard_rows)


async def send_daily_report(bot, chat_id: str, db_path: str) -> None:
    now_utc = datetime.now(timezone.utc)
    ensure_db_fresh_for_today(db_path, now_utc, allow_stale=True)
    entries = get_broadcasts_for_today(now_utc, db_path)
    message = build_message(now_utc, entries)
    await send_long_message(bot, chat_id, message)
    logging.info("Daily report sent. Unique stations: %d", unique_station_count(entries))


async def now_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    progress_message = await update.message.reply_text("Проверяю локальную базу и обновления...")
    now_utc = datetime.now(timezone.utc)
    db_path = context.application.bot_data["db_path"]
    try:
        fresh_today = ensure_db_fresh_for_today(db_path, now_utc, allow_stale=True)
        entries = get_broadcasts_for_today(now_utc, db_path)
    except requests.RequestException:
        await progress_message.edit_text(
            "Не удалось обновить базу из eibispace.de. Попробуйте снова чуть позже."
        )
        return
    except sqlite3.Error:
        await progress_message.edit_text("Ошибка SQLite базы данных. Проверьте путь к базе и права доступа.")
        return

    if not entries:
        await progress_message.edit_text("Сегодня не найдено активных станций.")
        return

    grouped_by_lang = group_stations_by_lang(entries)
    # Save snapshot per chat to avoid reparsing on every button click.
    context.chat_data["last_now_utc"] = now_utc
    context.chat_data["last_entries"] = entries

    await progress_message.edit_text(
        "Выберите язык вещания на сегодня (UTC):"
        if fresh_today
        else "Выберите язык вещания на сегодня (UTC).\n(Показаны последние доступные данные из локальной базы.)",
        reply_markup=build_language_keyboard(grouped_by_lang),
    )
    logging.info("/now used by chat %s. Languages offered: %d", update.effective_chat.id, len(grouped_by_lang))


async def refresh_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    progress_message = await update.message.reply_text("Обновляю базу из eibispace.de...")
    now_utc = datetime.now(timezone.utc)
    db_path = context.application.bot_data["db_path"]
    try:
        rows = refresh_db_from_source(db_path, now_utc)
    except requests.RequestException:
        await progress_message.edit_text("Не удалось скачать eibi.txt. Попробуйте снова чуть позже.")
        return
    except sqlite3.Error:
        await progress_message.edit_text("Ошибка SQLite базы данных. Проверьте путь к базе и права доступа.")
        return

    await progress_message.edit_text(
        f"База обновлена: {rows} записей. Дата UTC: {now_utc.strftime('%Y-%m-%d')}."
    )


async def language_pick_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    data = query.data or ""
    cached_now_utc: datetime | None = context.chat_data.get("last_now_utc")
    cached_entries: list[Broadcast] | None = context.chat_data.get("last_entries")
    current_hour: int | None = context.chat_data.get("last_current_hour")
    
    # Определяем режим: /now (все станции) или /current (только вещающие сейчас)
    is_current_mode = current_hour is not None
    
    if cached_now_utc is None or cached_entries is None:
        await query.edit_message_text("Сессия истекла. Отправьте /now еще раз.")
        return

    if data == "lang_back":
        if not cached_entries:
            await query.edit_message_text("Сегодня не найдено станций.")
            return

        grouped_by_lang = group_stations_by_lang(cached_entries)
        if is_current_mode:
            prompt = f"Выберите язык вещания (станции, вещающие в {current_hour}:00 UTC):"
        else:
            prompt = "Выберите язык вещания на сегодня (UTC):"
        await query.edit_message_text(
            prompt,
            reply_markup=build_language_keyboard(grouped_by_lang),
        )
        return
    
    if not data.startswith("lang:"):
        return
    lang = data.split(":", 1)[1]
    
    if is_current_mode:
        message = build_current_language_message(cached_now_utc, cached_entries, lang, current_hour)
    else:
        message = build_language_specific_message(cached_now_utc, cached_entries, lang)
    
    chunks = split_message(message)
    total = len(chunks)
    first_chunk = chunks[0]
    if total > 1:
        first_chunk = f"(1/{total})\n{first_chunk}"
    await query.edit_message_text(
        first_chunk,
        reply_markup=InlineKeyboardMarkup(
            [[InlineKeyboardButton("Назад к языкам", callback_data="lang_back")]]
        ),
    )
    if query.message:
        for idx, extra_chunk in enumerate(chunks[1:], start=2):
            if total > 1:
                extra_chunk = f"({idx}/{total})\n{extra_chunk}"
            await context.bot.send_message(chat_id=query.message.chat_id, text=extra_chunk)
    logging.info("Language selected by chat %s: %s (mode=%s)", 
                 query.message.chat_id if query.message else "unknown", 
                 lang, 
                 "current" if is_current_mode else "daily")


async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        "Доступные команды:\n"
        "/now — выбрать язык и получить список станций на сегодня (UTC).\n"
        "/current — станции, вещающие в текущий час UTC.\n"
        "/datetime — показать текущие дату и время UTC.\n"
        "/freq — найти станции по частоте (бот спросит частоту).\n"
        "/refresh — принудительно обновить локальную SQLite базу."
    )


async def datetime_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Показать текущие дату и время UTC."""
    now_utc = datetime.now(timezone.utc)
    await update.message.reply_text(
        f"Текущее время UTC:\n{now_utc.strftime('%Y-%m-%d %H:%M:%S')} UTC"
    )


def is_broadcasting_now(entry: Broadcast, current_hour: int) -> bool:
    """Проверяет, вещает ли станция в текущий час."""
    try:
        start_str, end_str = entry.time_utc.split("-")
        start_hour = int(start_str[:2])
        end_hour = int(end_str[:2])
        
        # Если вещание переходит через полночь
        if end_hour < start_hour:
            return current_hour >= start_hour or current_hour < end_hour
        else:
            return start_hour <= current_hour < end_hour
    except (ValueError, IndexError):
        return False


async def current_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Показать станции, вещающие в текущий час UTC (с выбором языка)."""
    progress_message = await update.message.reply_text("Загружаю станции...")
    
    now_utc = datetime.now(timezone.utc)
    current_hour = now_utc.hour
    db_path = context.application.bot_data["db_path"]
    
    try:
        entries = get_broadcasts_for_today(now_utc, db_path)
    except Exception:
        await progress_message.edit_text("Ошибка загрузки базы. Попробуйте позже.")
        return

    # Фильтруем станции, вещающие в текущий час
    broadcasting_now = [e for e in entries if is_broadcasting_now(e, current_hour)]
    
    if not broadcasting_now:
        await progress_message.edit_text(
            f"В текущий час ({current_hour}:00 UTC) нет активных станций."
        )
        return
    
    # Группируем по языкам
    grouped_by_lang = group_stations_by_lang(broadcasting_now)
    
    # Сохраняем данные для callback
    context.chat_data["last_now_utc"] = now_utc
    context.chat_data["last_entries"] = broadcasting_now
    context.chat_data["last_current_hour"] = current_hour
    
    await progress_message.edit_text(
        f"Выберите язык вещания (станции, вещающие в {current_hour}:00 UTC):",
        reply_markup=build_language_keyboard(grouped_by_lang),
    )
    logging.info("/current used by chat %s, hour=%d, languages=%d", update.effective_chat.id, current_hour, len(grouped_by_lang))


async def freq_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Начало поиска по частоте - запрашиваем частоту."""
    # Устанавливаем флаг ожидания ввода частоты
    context.user_data["awaiting_freq"] = True
    await update.message.reply_text(
        "Введите частоту в кГц (например: 6170 или 15245.2):\n"
        "Для отмены нажмите /cancel"
    )


async def handle_freq_input(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Обработка ввода частоты (если пользователь в режиме ожидания)."""
    # Проверяем, ожидаем ли мы ввод частоты от этого пользователя
    if not context.user_data.get("awaiting_freq"):
        return  # Не в режиме ожидания, игнорируем
    
    # Сбрасываем флаг
    context.user_data["awaiting_freq"] = False
    
    freq_arg = update.message.text.replace(",", ".")
    
    # Проверка на отмену
    if freq_arg.lower() == "/cancel":
        await update.message.reply_text("Отменено.")
        return
    
    # Проверка на команду
    if freq_arg.startswith("/"):
        await update.message.reply_text("Введите частоту (число), для отмены нажмите /cancel")
        context.user_data["awaiting_freq"] = True  # Снова ожидаем ввод
        return
    
    # Проверка формата
    try:
        freq = float(freq_arg)
    except ValueError:
        await update.message.reply_text(
            "Неверный формат частоты. Введите число, например: 6170"
        )
        context.user_data["awaiting_freq"] = True  # Снова ожидаем ввод
        return

    db_path = context.application.bot_data["db_path"]
    now_utc = datetime.now(timezone.utc)

    # Загружаем записи за сегодня
    entries = get_broadcasts_for_today(now_utc, db_path)

    # Ищем станции на указанной частоте
    matching = [e for e in entries if e.frequency == freq_arg or e.frequency == str(freq)]

    if not matching:
        await update.message.reply_text(f"На частоте {freq} кГц сегодня ничего не найдено.")
        return

    # Группируем по станциям
    stations_dict: dict[tuple[str, str], list[Broadcast]] = {}
    for e in matching:
        key = (e.station, e.itu)
        stations_dict.setdefault(key, []).append(e)

    sorted_stations = sorted(stations_dict.items(), key=lambda x: x[0][0].lower())

    lines = [f"Станции на частоте {freq} кГц сегодня:\n"]
    for (station, itu), station_entries in sorted_stations:
        lang = station_entries[0].lang
        lang_label = format_lang_label(lang)
        # Группируем частоты по времени вещания
        freq_by_time: dict[str, list[str]] = {}
        for e in station_entries:
            freq_by_time.setdefault(e.time_utc, []).append(e.frequency)
        
        lines.append(f"  ★ {station} ({itu}) — {lang_label}:")
        for time_utc, freqs in sorted(freq_by_time.items()):
            freqs_str = ", ".join(sorted(freqs, key=lambda f: float(f)))
            time_formatted = format_time_utc(time_utc)
            lines.append(f"    • {freqs_str}kHz {time_formatted}")

    message = "\n".join(lines)
    await update.message.reply_text(message)
    logging.info("/freq used by chat %s: freq=%s, found=%d", update.effective_chat.id, freq, len(stations_dict))


async def scheduled_report_callback(context: ContextTypes.DEFAULT_TYPE) -> None:
    chat_id = context.job.chat_id
    db_path = context.application.bot_data["db_path"]
    logging.info("Starting scheduled daily report to %s", chat_id)
    await send_daily_report(context.bot, str(chat_id), db_path)


async def scheduled_refresh_callback(context: ContextTypes.DEFAULT_TYPE) -> None:
    db_path = context.application.bot_data["db_path"]
    now_utc = datetime.now(timezone.utc)
    try:
        rows = refresh_db_from_source(db_path, now_utc)
        logging.info("Scheduled DB refresh at 23:55 UTC completed. Rows: %d", rows)
    except (requests.RequestException, sqlite3.Error) as exc:
        logging.warning("Scheduled refresh failed: %s", exc)


async def scheduled_notify_callback(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Отправить уведомление об обновлении базы."""
    chat_id = context.job.chat_id
    now_utc = datetime.now(timezone.utc)
    db_path = context.application.bot_data["db_path"]
    
    try:
        await context.bot.send_message(
            chat_id=chat_id,
            text=f"База данных EiBi обновлена.\nДата: {now_utc.strftime('%Y-%m-%d')}\nВремя UTC: {now_utc.strftime('%H:%M')}\n\nИспользуйте /now для просмотра станций."
        )
        logging.info("Notification sent to chat %s", chat_id)
    except Exception as exc:
        logging.warning("Failed to send notification: %s", exc)


async def main() -> None:
    load_dotenv()
    token = os.getenv("TELEGRAM_BOT_TOKEN")
    chat_id = os.getenv("TELEGRAM_CHAT_ID")
    db_path = os.getenv("EIBI_DB_PATH", DB_PATH_DEFAULT)
    if not token or not chat_id:
        raise RuntimeError("Set TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID in .env")

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )

    # Increased HTTP timeouts for slow connections to Telegram API.
    app = (
        Application.builder()
        .token(token)
        .connect_timeout(30.0)
        .read_timeout(60.0)
        .write_timeout(60.0)
        .pool_timeout(30.0)
        .get_updates_connect_timeout(30.0)
        .get_updates_read_timeout(90.0)
        .get_updates_write_timeout(60.0)
        .get_updates_pool_timeout(30.0)
        .build()
    )
    app.bot_data["db_path"] = db_path
    app.bot_data["chat_id"] = chat_id
    app.add_handler(CommandHandler("start", start_command))
    app.add_handler(CommandHandler("now", now_command))
    app.add_handler(CommandHandler("datetime", datetime_command))
    app.add_handler(CommandHandler("current", current_command))
    app.add_handler(CommandHandler("refresh", refresh_command))
    app.add_handler(CallbackQueryHandler(language_pick_callback, pattern=r"^lang(?::|_back$)"))

    # Обработчик для команды /freq
    app.add_handler(CommandHandler("freq", freq_command))
    # Обработчик для ввода частоты (проверяет флаг в user_data)
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_freq_input))

    # Проверяем инициализацию job_queue
    if app.job_queue is None:
        logging.error("Job queue is not initialized!")
    else:
        # В 23:55 - обновление базы
        app.job_queue.run_daily(
            scheduled_refresh_callback,
            time=time(hour=23, minute=55, tzinfo=timezone.utc),
            days=(0, 1, 2, 3, 4, 5, 6),
            name="daily_eibi_refresh",
        )
        # В 00:00 - отправка уведомления об обновлении
        app.job_queue.run_daily(
            scheduled_notify_callback,
            time=time(hour=0, minute=0, tzinfo=timezone.utc),
            days=(0, 1, 2, 3, 4, 5, 6),
            chat_id=chat_id,
            name="daily_eibi_notify",
        )
        logging.info("Scheduled tasks: daily_eibi_refresh at 23:55 UTC, daily_eibi_notify at 00:00 UTC")

    logging.info("Bot started. Press Ctrl+C to stop.")

    # Telegram API can be temporarily unavailable from local network/VPN/proxy.
    # Retry startup instead of crashing the whole process on transient timeouts.
    while True:
        try:
            await app.initialize()
            await app.start()
            # Регистрируем команды для автодополнения по /
            await app.bot.set_my_commands([
                BotCommand("start", "Показать доступные команды"),
                BotCommand("now", "Выбрать язык и получить станции на сегодня"),
                BotCommand("current", "Станции, вещающие в текущий час"),
                BotCommand("datetime", "Показать текущее время UTC"),
                BotCommand("freq", "Найти станции по частоте"),
                BotCommand("refresh", "Обновить базу данных"),
            ])
            await app.updater.start_polling(
                bootstrap_retries=-1,
                timeout=60,
                read_timeout=90,
                write_timeout=60,
                connect_timeout=30,
                pool_timeout=30,
            )
            break
        except (TimedOut, NetworkError) as exc:
            logging.warning("Telegram connection failed on startup: %s. Retrying in 10 seconds...", exc)
            await asyncio.sleep(10)

    try:
        await asyncio.Event().wait()
    finally:
        await app.updater.stop()
        await app.stop()
        await app.shutdown()


if __name__ == "__main__":
    asyncio.run(main())
