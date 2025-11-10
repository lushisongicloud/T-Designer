#!/usr/bin/env python3
"""
Replace restricted characters in selected columns of LdMainData.db.
"""

import argparse
import sqlite3
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Tuple

REPLACEMENTS: Tuple[Tuple[str, str], ...] = (
    ("'", "*"),
    ("’", "~"),
    ("、", "_"),
    ('"', "#"),
    ("\\", "-"),
    ("|", "-"),
)

ROWID_ALIAS = "__rowid__"


@dataclass(frozen=True)
class TableSpec:
    table: str
    columns: Tuple[str, ...]
    unique_key: Tuple[str, ...] = ()


TABLE_SPECS: Tuple[TableSpec, ...] = (
    TableSpec("EquipmentTemplate", ("ConnNum",)),
    TableSpec(
        "port_config",
        ("function_block", "port_name"),
        unique_key=("container_id", "function_block", "port_name"),
    ),
    TableSpec("TermInfo", ("TermNum",)),
)


def sanitize_text(value: str) -> str:
    result = value
    for old, new in REPLACEMENTS:
        if old in result:
            result = result.replace(old, new)
    return result


def select_columns(spec: TableSpec) -> List[str]:
    merged: Dict[str, None] = {}
    for name in (*spec.columns, *spec.unique_key):
        merged.setdefault(name, None)
    return list(merged.keys())


def build_key(
    row: sqlite3.Row, spec: TableSpec, sanitized_values: Dict[str, Any]
) -> Tuple:
    if not spec.unique_key:
        return ()
    key_parts: List[str] = []
    for column in spec.unique_key:
        key_parts.append(
            sanitized_values[column] if column in sanitized_values else row[column]
        )
    return tuple(key_parts)


def process_table(conn: sqlite3.Connection, spec: TableSpec) -> Tuple[int, int]:
    select_cols = select_columns(spec)
    if not select_cols:
        raise ValueError(f"No columns defined for table {spec.table}")

    query = (
        f"SELECT rowid AS {ROWID_ALIAS}, " + ", ".join(select_cols) + f" FROM {spec.table}"
    )

    cursor = conn.execute(query)
    rows_scanned = 0
    updates: List[Tuple] = []
    key_map: Dict[Tuple, List[int]] = {}

    for row in cursor:
        rows_scanned += 1
        sanitized_values: Dict[str, Any] = {}
        changed = False

        for column in spec.columns:
            value = row[column]
            if isinstance(value, str):
                sanitized = sanitize_text(value)
            else:
                sanitized = value

            sanitized_values[column] = sanitized
            if sanitized != value:
                changed = True

        if spec.unique_key:
            key = build_key(row, spec, sanitized_values)
            key_map.setdefault(key, []).append(row[ROWID_ALIAS])

        if changed:
            update_tuple = tuple(sanitized_values[col] for col in spec.columns)
            updates.append(update_tuple + (row[ROWID_ALIAS],))

    if spec.unique_key:
        collision_count = 0
        samples: List[str] = []
        for key, rowids in key_map.items():
            if len(rowids) > 1:
                collision_count += 1
                if len(samples) < 5:
                    samples.append(f"  key={key} rowids={tuple(rowids)}")
        if collision_count:
            sample_text = "\n".join(samples) if samples else "  (no sample rows)"
            raise RuntimeError(
                f"{spec.table}: {collision_count} sanitized key(s) would violate "
                f"the unique constraint.\n{sample_text}"
            )

    if updates:
        set_clause = ", ".join(f"{column} = ?" for column in spec.columns)
        sql = f"UPDATE {spec.table} SET {set_clause} WHERE rowid = ?"
        conn.executemany(sql, updates)

    rows_modified = len(updates)
    return rows_scanned, rows_modified


def run_cleaner(db_path: Path, dry_run: bool) -> None:
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    try:
        total_scanned = 0
        total_modified = 0
        for spec in TABLE_SPECS:
            scanned, modified = process_table(conn, spec)
            total_scanned += scanned
            total_modified += modified
            print(
                f"{spec.table}: scanned {scanned} rows, modified {modified}"
            )

        if dry_run:
            conn.rollback()
            print("Dry-run complete, no changes committed.")
        else:
            conn.commit()
            print(
                f"Cleaning finished. Total scanned: {total_scanned}, "
                f"total modified: {total_modified}"
            )
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Clean specific columns in LdMainData.db."
    )
    parser.add_argument(
        "--db",
        type=Path,
        default=Path("ref") / "LdMainData.db",
        help="Path to the target SQLite database (default: ref/LdMainData.db).",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Scan and report changes without modifying the database.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    db_path = args.db
    if not db_path.exists():
        raise FileNotFoundError(f"Database not found: {db_path}")
    run_cleaner(db_path, args.dry_run)


if __name__ == "__main__":
    main()
