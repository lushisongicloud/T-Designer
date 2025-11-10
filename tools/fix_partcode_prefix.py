#!/usr/bin/env python3
"""
Prefix Equipment.PartCode with 'D' when it starts with a digit.

Usage:
    python tools/fix_partcode_prefix.py --db ref/LdMainData.db
"""

from __future__ import annotations

import argparse
import re
import sqlite3
from pathlib import Path


DIGIT_PREFIX = re.compile(r"^\s*\d")


def fix_partcodes(db_path: Path) -> int:
    if not db_path.exists():
        raise FileNotFoundError(f"Database not found: {db_path}")

    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        cur = conn.cursor()
        cur.execute(
            "SELECT Equipment_ID, PartCode "
            "FROM Equipment "
            "WHERE PartCode IS NOT NULL AND TRIM(PartCode) != ''"
        )
        rows = cur.fetchall()

        updates = []
        for row in rows:
            partcode = row["PartCode"]
            if DIGIT_PREFIX.match(partcode):
                new_code = f"D{partcode.lstrip()}"
                updates.append((new_code, row["Equipment_ID"]))

        if updates:
            cur.executemany(
                "UPDATE Equipment SET PartCode = ? WHERE Equipment_ID = ?",
                updates,
            )
            conn.commit()
        return len(updates)
    finally:
        conn.close()


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Prefix Equipment.PartCode with 'D' when it starts with a digit."
    )
    parser.add_argument(
        "--db",
        type=Path,
        default=Path("ref/LdMainData.db"),
        help="Path to SQLite database (default: ref/LdMainData.db)",
    )
    args = parser.parse_args()

    updated = fix_partcodes(args.db)
    print(f"Updated {updated} Equipment rows.")


if __name__ == "__main__":
    main()
