#!/usr/bin/env python3
"""Project database migration tool for T-Designer × T-Solver integration.

Usage examples:
  python tools/db_migrate_project.py upgrade --database MyProjects/DemoSystem/DemoSystem.db
  python tools/db_migrate_project.py downgrade --database MyProjects/DemoSystem/DemoSystem.db
"""

import argparse
import sqlite3
import sys
from pathlib import Path
from typing import Iterable

MIGRATION_ID = "20241029_solver_integration_phase1"

CREATE_TABLE_STATEMENTS = [
    """
    CREATE TABLE IF NOT EXISTS component_smt (
        component_smt_id INTEGER PRIMARY KEY AUTOINCREMENT,
        equipment_id INTEGER,
        container_id INTEGER,
        model_scope TEXT NOT NULL DEFAULT 'component',
        revision_tag TEXT,
        smt_text TEXT NOT NULL,
        port_signature TEXT,
        syntax_status TEXT NOT NULL DEFAULT 'unknown',
        syntax_message TEXT,
        metadata_json TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS port_config (
        port_config_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        function_block TEXT NOT NULL,
        port_name TEXT NOT NULL,
        port_type TEXT NOT NULL,
        direction TEXT NOT NULL DEFAULT 'bidirectional',
        variable_profile TEXT NOT NULL DEFAULT 'default',
        variables_json TEXT NOT NULL,
        connect_macro TEXT,
        custom_metadata TEXT,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS port_connect_macro (
        macro_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        macro_name TEXT NOT NULL,
        domain TEXT NOT NULL,
        arity INTEGER NOT NULL,
        expansion_template TEXT NOT NULL,
        description TEXT,
        metadata_json TEXT,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS system_smt (
        system_smt_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL UNIQUE,
        def_block TEXT NOT NULL,
        connect_block TEXT NOT NULL,
        raw_block TEXT,
        options_json TEXT,
        checksum TEXT,
        generated_by TEXT,
        generated_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS function_document (
        function_document_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        xml_text TEXT NOT NULL,
        format_version TEXT NOT NULL DEFAULT '1.0',
        checksum TEXT,
        source_hint TEXT,
        metadata_json TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS dmatrix_meta (
        dmatrix_meta_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        result_json TEXT NOT NULL,
        options_json TEXT NOT NULL,
        state_json TEXT,
        csv_path TEXT,
        checksum TEXT,
        is_active INTEGER NOT NULL DEFAULT 1,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS schema_migrations (
        migration_id TEXT PRIMARY KEY,
        applied_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
    )
    """,
]

CREATE_INDEX_STATEMENTS = [
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_component_smt_equipment ON component_smt(equipment_id) WHERE equipment_id IS NOT NULL",
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_component_smt_container_scope ON component_smt(container_id, model_scope) WHERE container_id IS NOT NULL",
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_port_config_unique ON port_config(container_id, function_block, port_name)",
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_connect_macro_unique ON port_connect_macro(container_id, macro_name)",
    "CREATE UNIQUE INDEX IF NOT EXISTS idx_function_document_container ON function_document(container_id)",
    "CREATE INDEX IF NOT EXISTS idx_dmatrix_container ON dmatrix_meta(container_id, is_active)",
]

DROP_INDEX_STATEMENTS = [
    "DROP INDEX IF EXISTS idx_dmatrix_container",
    "DROP INDEX IF EXISTS idx_function_document_container",
    "DROP INDEX IF EXISTS idx_connect_macro_unique",
    "DROP INDEX IF EXISTS idx_port_config_unique",
    "DROP INDEX IF EXISTS idx_component_smt_container_scope",
    "DROP INDEX IF EXISTS idx_component_smt_equipment",
]

DROP_TABLE_STATEMENTS = [
    "DROP TABLE IF EXISTS dmatrix_meta",
    "DROP TABLE IF EXISTS function_document",
    "DROP TABLE IF EXISTS system_smt",
    "DROP TABLE IF EXISTS port_connect_macro",
    "DROP TABLE IF EXISTS port_config",
    "DROP TABLE IF EXISTS component_smt",
]


def execute_many(conn: sqlite3.Connection, statements: Iterable[str]) -> None:
    cursor = conn.cursor()
    for sql in statements:
        cursor.execute(sql)
    conn.commit()


def has_migration(conn: sqlite3.Connection) -> bool:
    cursor = conn.cursor()
    cursor.execute(
        "SELECT name FROM sqlite_master WHERE type='table' AND name='schema_migrations'"
    )
    if cursor.fetchone() is None:
        return False
    cursor.execute(
        "SELECT 1 FROM schema_migrations WHERE migration_id = ? LIMIT 1",
        (MIGRATION_ID,),
    )
    return cursor.fetchone() is not None


def record_migration(conn: sqlite3.Connection) -> None:
    conn.execute(
        "INSERT OR IGNORE INTO schema_migrations(migration_id) VALUES (?)",
        (MIGRATION_ID,),
    )
    conn.commit()


def remove_migration_record(conn: sqlite3.Connection) -> None:
    conn.execute(
        "DELETE FROM schema_migrations WHERE migration_id = ?",
        (MIGRATION_ID,),
    )
    conn.commit()


def upgrade(conn: sqlite3.Connection) -> None:
    if has_migration(conn):
        print(f"Migration {MIGRATION_ID} already applied.")
        return
    execute_many(conn, CREATE_TABLE_STATEMENTS)
    execute_many(conn, CREATE_INDEX_STATEMENTS)
    record_migration(conn)
    print(f"Migration {MIGRATION_ID} applied.")


def downgrade(conn: sqlite3.Connection) -> None:
    if not has_migration(conn):
        print(f"Migration {MIGRATION_ID} not found; nothing to rollback.")
        return
    execute_many(conn, DROP_INDEX_STATEMENTS)
    execute_many(conn, DROP_TABLE_STATEMENTS)
    remove_migration_record(conn)
    print(f"Migration {MIGRATION_ID} rolled back.")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Manage project database schema migrations.",
    )
    parser.add_argument(
        "command",
        choices=["upgrade", "downgrade"],
        help="Operation to execute",
    )
    parser.add_argument(
        "--database",
        "-d",
        required=True,
        help="Path to the SQLite project database",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    db_path = Path(args.database)
    if not db_path.exists():
        print(f"Database not found: {db_path}", file=sys.stderr)
        return 1
    conn = sqlite3.connect(db_path)
    try:
        if args.command == "upgrade":
            upgrade(conn)
        elif args.command == "downgrade":
            downgrade(conn)
    finally:
        conn.close()
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
