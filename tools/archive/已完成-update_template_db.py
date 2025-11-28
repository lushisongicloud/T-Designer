# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Update the project template database so it contains the unified schema and seed data
mirrored from ref/Model.db. The script is idempotent and safe to re-run.
"""

import sqlite3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT_DB = ROOT / "templete" / "project.db"
MODEL_DB = ROOT / "ref" / "Model.db"


DDL_STATEMENTS = [
    # Legacy compatibility tables (containers JSON storage)
    """
    CREATE TABLE IF NOT EXISTS containers (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        type INTEGER NOT NULL,
        parent_id INTEGER,
        order_index INTEGER DEFAULT 0,
        analysis_depth INTEGER DEFAULT 0,
        interface_json TEXT,
        behavior_smt TEXT,
        fault_modes_json TEXT,
        tests_json TEXT,
        analysis_json TEXT,
        equipment_id INTEGER,
        equipment_type TEXT,
        equipment_name TEXT,
        UNIQUE(name, parent_id),
        FOREIGN KEY(parent_id) REFERENCES containers(id) ON DELETE CASCADE
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_containers_parent ON containers(parent_id, order_index)",
    """
    CREATE TABLE IF NOT EXISTS equipment_containers (
        equipment_id INTEGER PRIMARY KEY,
        container_id INTEGER NOT NULL,
        FOREIGN KEY(container_id) REFERENCES containers(id) ON DELETE CASCADE
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_eq_containers_container ON equipment_containers(container_id)",
    # Unified container hierarchy and behaviour tables
    """
    CREATE TABLE IF NOT EXISTS container (
        container_id INTEGER PRIMARY KEY AUTOINCREMENT,
        project_structure_id INTEGER NOT NULL,
        name TEXT NOT NULL,
        level TEXT NOT NULL,
        source_equipment_id INTEGER,
        auto_generated INTEGER NOT NULL DEFAULT 0,
        description TEXT,
        fault_analysis_depth TEXT,
        inherits_from_container_id INTEGER,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY(project_structure_id) REFERENCES ProjectStructure(ProjectStructure_ID),
        FOREIGN KEY(source_equipment_id) REFERENCES Equipment(Equipment_ID),
        FOREIGN KEY(inherits_from_container_id) REFERENCES container(container_id)
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_container_project ON container(project_structure_id)",
    "CREATE INDEX IF NOT EXISTS idx_container_equipment ON container(source_equipment_id)",
    """
    CREATE TABLE IF NOT EXISTS container_hierarchy (
        parent_id INTEGER NOT NULL,
        child_id INTEGER NOT NULL,
        relation_type TEXT DEFAULT 'contains',
        PRIMARY KEY (parent_id, child_id),
        FOREIGN KEY(parent_id) REFERENCES container(container_id) ON DELETE CASCADE,
        FOREIGN KEY(child_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS container_component (
        container_id INTEGER NOT NULL,
        equipment_id INTEGER NOT NULL,
        role TEXT,
        PRIMARY KEY (container_id, equipment_id),
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE,
        FOREIGN KEY(equipment_id) REFERENCES Equipment(Equipment_ID) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS container_interface (
        interface_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        name TEXT NOT NULL,
        direction TEXT NOT NULL,
        signal_category TEXT NOT NULL,
        signal_subtype TEXT,
        physical_domain TEXT,
        default_unit TEXT,
        description TEXT,
        inherits_interface_id INTEGER,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE,
        FOREIGN KEY(inherits_interface_id) REFERENCES container_interface(interface_id)
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_container_interface_container ON container_interface(container_id)",
    """
    CREATE TABLE IF NOT EXISTS container_interface_binding (
        binding_id INTEGER PRIMARY KEY AUTOINCREMENT,
        interface_id INTEGER NOT NULL,
        equipment_id INTEGER,
        terminal_id INTEGER,
        connect_line_id INTEGER,
        binding_role TEXT,
        FOREIGN KEY(interface_id) REFERENCES container_interface(interface_id) ON DELETE CASCADE,
        FOREIGN KEY(equipment_id) REFERENCES Equipment(Equipment_ID),
        FOREIGN KEY(terminal_id) REFERENCES Terminal(Terminal_ID),
        FOREIGN KEY(connect_line_id) REFERENCES ConnectLine(ConnectLine_ID)
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS container_state (
        state_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        name TEXT NOT NULL,
        state_type TEXT NOT NULL,
        derived_from_children INTEGER NOT NULL DEFAULT 0,
        probability REAL,
        rationale TEXT,
        analysis_scope TEXT,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_container_state_container ON container_state(container_id)",
    """
    CREATE TABLE IF NOT EXISTS container_state_behavior (
        behavior_id INTEGER PRIMARY KEY AUTOINCREMENT,
        state_id INTEGER NOT NULL,
        representation TEXT NOT NULL,
        expression TEXT NOT NULL,
        notes TEXT,
        FOREIGN KEY(state_id) REFERENCES container_state(state_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS container_state_interface (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        state_id INTEGER NOT NULL,
        interface_id INTEGER NOT NULL,
        constraint TEXT,
        FOREIGN KEY(state_id) REFERENCES container_state(state_id) ON DELETE CASCADE,
        FOREIGN KEY(interface_id) REFERENCES container_interface(interface_id) ON DELETE CASCADE
    )
    """,
    # Functional definition tables
    """
    CREATE TABLE IF NOT EXISTS function_definition (
        function_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        parent_function_id INTEGER,
        name TEXT NOT NULL,
        description TEXT,
        requirement TEXT,
        expected_output TEXT,
        detection_rule TEXT,
        auto_generated INTEGER NOT NULL DEFAULT 0,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE,
        FOREIGN KEY(parent_function_id) REFERENCES function_definition(function_id) ON DELETE SET NULL
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_function_container ON function_definition(container_id)",
    """
    CREATE TABLE IF NOT EXISTS function_io (
        io_id INTEGER PRIMARY KEY AUTOINCREMENT,
        function_id INTEGER NOT NULL,
        io_type TEXT NOT NULL,
        name TEXT NOT NULL,
        interface_id INTEGER,
        default_value TEXT,
        expression TEXT,
        description TEXT,
        FOREIGN KEY(function_id) REFERENCES function_definition(function_id) ON DELETE CASCADE,
        FOREIGN KEY(interface_id) REFERENCES container_interface(interface_id)
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS function_dependency (
        function_id INTEGER NOT NULL,
        depends_on_function_id INTEGER NOT NULL,
        dependency_type TEXT DEFAULT 'requires',
        PRIMARY KEY (function_id, depends_on_function_id),
        FOREIGN KEY(function_id) REFERENCES function_definition(function_id) ON DELETE CASCADE,
        FOREIGN KEY(depends_on_function_id) REFERENCES function_definition(function_id) ON DELETE CASCADE
    )
    """,
    # Testability schema
    """
    CREATE TABLE IF NOT EXISTS test_definition (
        test_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER,
        function_id INTEGER,
        related_state_id INTEGER,
        test_type TEXT NOT NULL,
        name TEXT NOT NULL,
        description TEXT,
        auto_generated INTEGER NOT NULL DEFAULT 1,
        interface_id INTEGER,
        signal_category TEXT,
        expected_result TEXT,
        complexity INTEGER,
        estimated_duration REAL,
        estimated_cost REAL,
        FOREIGN KEY(container_id) REFERENCES container(container_id),
        FOREIGN KEY(function_id) REFERENCES function_definition(function_id),
        FOREIGN KEY(related_state_id) REFERENCES container_state(state_id),
        FOREIGN KEY(interface_id) REFERENCES container_interface(interface_id)
    )
    """,
    "CREATE INDEX IF NOT EXISTS idx_test_definition_container ON test_definition(container_id)",
    """
    CREATE TABLE IF NOT EXISTS test_fault_coverage (
        test_id INTEGER NOT NULL,
        state_id INTEGER NOT NULL,
        coverage_type TEXT NOT NULL,
        confidence REAL,
        PRIMARY KEY (test_id, state_id, coverage_type),
        FOREIGN KEY(test_id) REFERENCES test_definition(test_id) ON DELETE CASCADE,
        FOREIGN KEY(state_id) REFERENCES container_state(state_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS test_constraint (
        constraint_id INTEGER PRIMARY KEY AUTOINCREMENT,
        test_id INTEGER NOT NULL,
        constraint_type TEXT NOT NULL,
        value TEXT,
        unit TEXT,
        FOREIGN KEY(test_id) REFERENCES test_definition(test_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS analysis_requirement (
        requirement_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        metric TEXT NOT NULL,
        target_value REAL NOT NULL,
        unit TEXT DEFAULT 'ratio',
        notes TEXT,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS analysis_constraint (
        constraint_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        constraint_type TEXT NOT NULL,
        value TEXT,
        unit TEXT,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS test_plan_candidate (
        candidate_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        name TEXT NOT NULL,
        description TEXT,
        total_cost REAL,
        total_duration REAL,
        selection_notes TEXT,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS test_plan_candidate_item (
        candidate_id INTEGER NOT NULL,
        test_id INTEGER NOT NULL,
        PRIMARY KEY (candidate_id, test_id),
        FOREIGN KEY(candidate_id) REFERENCES test_plan_candidate(candidate_id) ON DELETE CASCADE,
        FOREIGN KEY(test_id) REFERENCES test_definition(test_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS diagnosis_tree (
        tree_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        name TEXT,
        description TEXT,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS diagnosis_tree_node (
        node_id INTEGER PRIMARY KEY AUTOINCREMENT,
        tree_id INTEGER NOT NULL,
        parent_node_id INTEGER,
        test_id INTEGER,
        state_id INTEGER,
        outcome TEXT,
        comment TEXT,
        FOREIGN KEY(tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
        FOREIGN KEY(parent_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE,
        FOREIGN KEY(test_id) REFERENCES test_definition(test_id),
        FOREIGN KEY(state_id) REFERENCES container_state(state_id)
    )
    """,
    # Model tables (from ref/Model.db)
    """
    CREATE TABLE IF NOT EXISTS components (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        type TEXT NOT NULL,
        mark TEXT NOT NULL UNIQUE,
        parameter TEXT,
        variable TEXT,
        description TEXT,
        failuremode TEXT,
        struct TEXT
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS parameters (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        componentId INTEGER NOT NULL,
        name TEXT NOT NULL,
        defaultValue TEXT NOT NULL,
        FOREIGN KEY(componentId) REFERENCES components(id) ON DELETE CASCADE
    )
    """,
    """
    CREATE TABLE IF NOT EXISTS models (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL UNIQUE,
        systemDescription TEXT,
        testDiscription TEXT,
        connectNodes TEXT,
        functionDescription TEXT
    )
    """,
]


def ensure_schema(conn: sqlite3.Connection) -> None:
    conn.execute("PRAGMA foreign_keys = ON")
    for statement in DDL_STATEMENTS:
        conn.execute(statement)


def copy_table(source: sqlite3.Connection, target: sqlite3.Connection, table: str) -> None:
    src_cur = source.execute(f"SELECT * FROM {table}")
    rows = src_cur.fetchall()
    if not rows:
        return
    column_names = [desc[0] for desc in src_cur.description]
    placeholders = ",".join(["?"] * len(column_names))
    columns = ",".join(column_names)
    tgt_cur = target.execute(f"SELECT COUNT(*) FROM {table}")
    if tgt_cur.fetchone()[0] > 0:
        return
    target.executemany(
        f"INSERT INTO {table} ({columns}) VALUES ({placeholders})",
        rows,
    )


def main() -> None:
    if not PROJECT_DB.exists():
        raise SystemExit(f"project template not found: {PROJECT_DB}")
    if not MODEL_DB.exists():
        raise SystemExit(f"reference Model.db not found: {MODEL_DB}")

    with sqlite3.connect(PROJECT_DB) as target, sqlite3.connect(MODEL_DB) as source:
        ensure_schema(target)
        target.execute("BEGIN")
        for table in ("components", "parameters", "models"):
            copy_table(source, target, table)
        target.commit()


if __name__ == "__main__":
    main()
