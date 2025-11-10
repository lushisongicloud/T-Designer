#!/usr/bin/env python3

"""
Dump the function description XML for a given model name from Model.db.

Usage:
    python scripts/dump_function_xml.py QBT

Writes <name>_function.xml in the current directory.
"""

import argparse
import sqlite3
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description="Dump functionDescription XML from Model.db")
    parser.add_argument("name", help="Model name, e.g. QBT")
    parser.add_argument("--db", default="Model.db", help="Path to Model.db (default: %(default)s)")
    args = parser.parse_args()

    db_path = Path(args.db)
    if not db_path.exists():
        raise SystemExit(f"Database not found: {db_path}")

    conn = sqlite3.connect(str(db_path))
    cur = conn.cursor()
    cur.execute("SELECT functionDescription FROM Model WHERE name=?", (args.name,))
    row = cur.fetchone()
    conn.close()

    if not row:
        raise SystemExit(f"No model named {args.name} found in {db_path}")

    output_path = Path(f"{args.name}_function.xml")
    output_path.write_text(row[0], encoding="utf-8")
    print(f"Wrote {output_path}")


if __name__ == "__main__":
    main()

