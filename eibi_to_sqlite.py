import argparse
import os
import re
import sqlite3
from dataclasses import dataclass

import requests

EIBI_URL = "http://www.eibispace.de/dx/eibi.txt"
DB_PATH_DEFAULT = os.path.join("data", "eibi.sqlite3")
ITU_RE = re.compile(r"^[A-Z]{1,4}$")
TIME_RE = re.compile(r"^\d{4}-\d{4}$")
FREQ_RE = re.compile(r"^\d+(?:\.\d+)?$")


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


def fetch_lines(url: str) -> list[str]:
    response = requests.get(url, timeout=60)
    response.raise_for_status()
    return response.text.splitlines()


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
    conn.execute("CREATE INDEX IF NOT EXISTS idx_broadcasts_station ON broadcasts(station)")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_broadcasts_lang ON broadcasts(lang)")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_broadcasts_itu ON broadcasts(itu)")


def ensure_db_parent_dir(db_path: str) -> None:
    parent_dir = os.path.dirname(db_path)
    if parent_dir:
        os.makedirs(parent_dir, exist_ok=True)


def save_broadcasts(conn: sqlite3.Connection, items: list[Broadcast], replace: bool) -> None:
    if replace:
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
            for item in items
        ],
    )
    conn.commit()


def run(db_path: str, url: str, replace: bool) -> tuple[int, int]:
    ensure_db_parent_dir(db_path)
    lines = fetch_lines(url)
    parsed = [item for line in lines if (item := parse_line(line)) is not None]

    conn = sqlite3.connect(db_path)
    try:
        init_db(conn)
        save_broadcasts(conn, parsed, replace=replace)
    finally:
        conn.close()

    return len(lines), len(parsed)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Download eibi.txt and store parsed broadcasts in SQLite."
    )
    parser.add_argument("--db", default=DB_PATH_DEFAULT, help="Path to SQLite database file.")
    parser.add_argument("--url", default=EIBI_URL, help="Source URL for eibi data.")
    parser.add_argument(
        "--append",
        action="store_true",
        help="Append records instead of replacing existing rows.",
    )
    args = parser.parse_args()

    total_lines, total_parsed = run(
        db_path=args.db,
        url=args.url,
        replace=not args.append,
    )
    print(
        f"Done. Lines read: {total_lines}, rows parsed: {total_parsed}, database: {args.db}"
    )


if __name__ == "__main__":
    main()
