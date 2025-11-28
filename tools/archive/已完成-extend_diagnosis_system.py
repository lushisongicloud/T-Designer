# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
诊断系统数据库扩展脚本（Python版本）
用途：安全地扩展数据库表，检查列是否存在后再添加

Author: AI Assistant
Date: 2025-11-10
"""

import sqlite3
import sys
import os


def check_column_exists(cursor, table_name, column_name):
    """检查表中是否存在指定列"""
    cursor.execute(f"PRAGMA table_info({table_name})")
    columns = [row[1] for row in cursor.fetchall()]
    return column_name in columns


def add_column_if_not_exists(cursor, table_name, column_name, column_def):
    """如果列不存在则添加"""
    if not check_column_exists(cursor, table_name, column_name):
        try:
            sql = f"ALTER TABLE {table_name} ADD COLUMN {column_name} {column_def}"
            cursor.execute(sql)
            print(f"  ✓ 添加列: {table_name}.{column_name}")
            return True
        except sqlite3.Error as e:
            print(f"  ✗ 添加列失败: {table_name}.{column_name} - {e}")
            return False
    else:
        print(f"  - 列已存在: {table_name}.{column_name}")
        return False


def extend_diagnosis_tree_node(cursor):
    """扩展 diagnosis_tree_node 表"""
    print("\n[1] 扩展 diagnosis_tree_node 表...")
    
    columns_to_add = [
        ("skip_count", "INTEGER DEFAULT 0"),
        ("skip_reason", "TEXT"),
        ("alternative_tests", "TEXT"),
        ("cost_estimate", "REAL DEFAULT 0.0"),
        ("duration_estimate", "REAL DEFAULT 0.0"),
        ("detectable_faults", "TEXT"),
        ("isolatable_faults", "TEXT"),
    ]
    
    added_count = 0
    for col_name, col_def in columns_to_add:
        if add_column_if_not_exists(cursor, "diagnosis_tree_node", col_name, col_def):
            added_count += 1
    
    print(f"✓ diagnosis_tree_node 表扩展完成，新增 {added_count} 列")


def create_diagnosis_session_table(cursor):
    """创建 diagnosis_session 表"""
    print("\n[2] 创建 diagnosis_session 表...")
    
    sql = """
    CREATE TABLE IF NOT EXISTS diagnosis_session (
        session_id INTEGER PRIMARY KEY AUTOINCREMENT,
        tree_id INTEGER NOT NULL,
        function_id INTEGER,
        start_time TEXT NOT NULL,
        end_time TEXT,
        session_state TEXT NOT NULL CHECK(session_state IN ('NotStarted', 'InProgress', 'Completed', 'Failed', 'Cancelled')),
        fault_node_id INTEGER,
        total_steps INTEGER DEFAULT 0,
        total_duration REAL DEFAULT 0.0,
        user_id TEXT,
        session_notes TEXT,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
        FOREIGN KEY (fault_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE SET NULL
    )
    """
    
    try:
        cursor.execute(sql)
        print("  ✓ 表创建成功: diagnosis_session")
    except sqlite3.Error as e:
        print(f"  - 表可能已存在: diagnosis_session ({e})")
    
    # 创建索引
    indexes = [
        ("idx_diagnosis_session_tree_id", "diagnosis_session", "tree_id"),
        ("idx_diagnosis_session_state", "diagnosis_session", "session_state"),
        ("idx_diagnosis_session_start_time", "diagnosis_session", "start_time"),
    ]
    
    for idx_name, table_name, column in indexes:
        try:
            cursor.execute(f"CREATE INDEX IF NOT EXISTS {idx_name} ON {table_name}({column})")
            print(f"  ✓ 索引创建成功: {idx_name}")
        except sqlite3.Error as e:
            print(f"  - 索引可能已存在: {idx_name}")


def create_diagnosis_step_history_table(cursor):
    """创建 diagnosis_step_history 表"""
    print("\n[3] 创建 diagnosis_step_history 表...")
    
    sql = """
    CREATE TABLE IF NOT EXISTS diagnosis_step_history (
        step_id INTEGER PRIMARY KEY AUTOINCREMENT,
        session_id INTEGER NOT NULL,
        step_number INTEGER NOT NULL,
        node_id INTEGER NOT NULL,
        test_outcome TEXT NOT NULL CHECK(test_outcome IN ('Unknown', 'Pass', 'Fail', 'Skip')),
        timestamp TEXT NOT NULL,
        user_comment TEXT,
        duration REAL DEFAULT 0.0,
        can_rollback INTEGER DEFAULT 1 CHECK(can_rollback IN (0, 1)),
        previous_step_id INTEGER,
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (session_id) REFERENCES diagnosis_session(session_id) ON DELETE CASCADE,
        FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE,
        FOREIGN KEY (previous_step_id) REFERENCES diagnosis_step_history(step_id) ON DELETE SET NULL
    )
    """
    
    try:
        cursor.execute(sql)
        print("  ✓ 表创建成功: diagnosis_step_history")
    except sqlite3.Error as e:
        print(f"  - 表可能已存在: diagnosis_step_history ({e})")
    
    # 创建索引
    indexes = [
        ("idx_diagnosis_step_session_id", "diagnosis_step_history", "session_id"),
        ("idx_diagnosis_step_node_id", "diagnosis_step_history", "node_id"),
        ("idx_diagnosis_step_timestamp", "diagnosis_step_history", "timestamp"),
    ]
    
    for idx_name, table_name, column in indexes:
        try:
            cursor.execute(f"CREATE INDEX IF NOT EXISTS {idx_name} ON {table_name}({column})")
            print(f"  ✓ 索引创建成功: {idx_name}")
        except sqlite3.Error as e:
            print(f"  - 索引可能已存在: {idx_name}")


def create_test_recommendation_pool_table(cursor):
    """创建 test_recommendation_pool 表"""
    print("\n[4] 创建 test_recommendation_pool 表...")
    
    sql = """
    CREATE TABLE IF NOT EXISTS test_recommendation_pool (
        recommendation_id INTEGER PRIMARY KEY AUTOINCREMENT,
        tree_id INTEGER NOT NULL,
        node_id INTEGER NOT NULL,
        alternative_node_ids TEXT,
        recommendation_score REAL DEFAULT 0.0,
        recommendation_reason TEXT,
        is_active INTEGER DEFAULT 1 CHECK(is_active IN (0, 1)),
        created_at TEXT DEFAULT CURRENT_TIMESTAMP,
        updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
        FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE
    )
    """
    
    try:
        cursor.execute(sql)
        print("  ✓ 表创建成功: test_recommendation_pool")
    except sqlite3.Error as e:
        print(f"  - 表可能已存在: test_recommendation_pool ({e})")
    
    # 创建索引
    indexes = [
        ("idx_test_recommendation_tree_id", "test_recommendation_pool", "tree_id"),
        ("idx_test_recommendation_node_id", "test_recommendation_pool", "node_id"),
    ]
    
    for idx_name, table_name, column in indexes:
        try:
            cursor.execute(f"CREATE INDEX IF NOT EXISTS {idx_name} ON {table_name}({column})")
            print(f"  ✓ 索引创建成功: {idx_name}")
        except sqlite3.Error as e:
            print(f"  - 索引可能已存在: {idx_name}")


def create_views(cursor):
    """创建统计视图"""
    print("\n[5] 创建统计视图...")
    
    # 测试执行统计视图
    try:
        cursor.execute("""
            CREATE VIEW IF NOT EXISTS v_test_execution_stats AS
            SELECT 
                n.node_id,
                n.tree_id,
                n.test_description,
                COUNT(DISTINCT h.session_id) as execution_count,
                SUM(CASE WHEN h.test_outcome = 'Pass' THEN 1 ELSE 0 END) as pass_count,
                SUM(CASE WHEN h.test_outcome = 'Fail' THEN 1 ELSE 0 END) as fail_count,
                SUM(CASE WHEN h.test_outcome = 'Skip' THEN 1 ELSE 0 END) as skip_count,
                AVG(h.duration) as avg_duration,
                MAX(h.timestamp) as last_executed
            FROM diagnosis_tree_node n
            LEFT JOIN diagnosis_step_history h ON n.node_id = h.node_id
            WHERE n.node_type = 'Test'
            GROUP BY n.node_id
        """)
        print("  ✓ 视图创建成功: v_test_execution_stats")
    except sqlite3.Error as e:
        print(f"  - 视图可能已存在: v_test_execution_stats ({e})")
    
    # 诊断会话统计视图
    try:
        cursor.execute("""
            CREATE VIEW IF NOT EXISTS v_diagnosis_session_stats AS
            SELECT 
                s.tree_id,
                COUNT(*) as total_sessions,
                SUM(CASE WHEN s.session_state = 'Completed' THEN 1 ELSE 0 END) as completed_sessions,
                SUM(CASE WHEN s.session_state = 'Failed' THEN 1 ELSE 0 END) as failed_sessions,
                AVG(s.total_steps) as avg_steps,
                AVG(s.total_duration) as avg_duration
            FROM diagnosis_session s
            GROUP BY s.tree_id
        """)
        print("  ✓ 视图创建成功: v_diagnosis_session_stats")
    except sqlite3.Error as e:
        print(f"  - 视图可能已存在: v_diagnosis_session_stats ({e})")


def verify_extensions(cursor):
    """验证扩展结果"""
    print("\n[6] 验证扩展结果...")
    
    # 检查 diagnosis_tree_node 新增字段
    cursor.execute("PRAGMA table_info(diagnosis_tree_node)")
    columns = [row[1] for row in cursor.fetchall()]
    
    new_columns = ["skip_count", "skip_reason", "alternative_tests", 
                   "cost_estimate", "duration_estimate", "detectable_faults", "isolatable_faults"]
    
    missing_columns = [col for col in new_columns if col not in columns]
    
    if missing_columns:
        print(f"  警告：以下列未能添加: {', '.join(missing_columns)}")
    else:
        print(f"  ✓ diagnosis_tree_node 表所有新列都已添加")
    
    # 检查新表
    cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name LIKE 'diagnosis_%'")
    tables = [row[0] for row in cursor.fetchall()]
    
    required_tables = ["diagnosis_session", "diagnosis_step_history", "test_recommendation_pool"]
    missing_tables = [t for t in required_tables if t not in tables]
    
    if missing_tables:
        print(f"  警告：以下表未能创建: {', '.join(missing_tables)}")
    else:
        print(f"  ✓ 所有新表都已创建")
    
    # 检查视图
    cursor.execute("SELECT name FROM sqlite_master WHERE type='view' AND name LIKE 'v_%'")
    views = [row[0] for row in cursor.fetchall()]
    
    required_views = ["v_test_execution_stats", "v_diagnosis_session_stats"]
    missing_views = [v for v in required_views if v not in views]
    
    if missing_views:
        print(f"  警告：以下视图未能创建: {', '.join(missing_views)}")
    else:
        print(f"  ✓ 所有视图都已创建")


def main():
    """主函数"""
    # 数据库文件路径
    db_paths = [
        "集中油源动力系统.db",
        "project.db"
    ]
    
    print("=" * 60)
    print("诊断系统数据库扩展工具")
    print("=" * 60)
    
    for db_path in db_paths:
        if not os.path.exists(db_path):
            print(f"\n跳过：{db_path}（文件不存在）")
            continue
        
        print(f"\n处理数据库：{db_path}")
        print("-" * 60)
        
        try:
            conn = sqlite3.connect(db_path)
            cursor = conn.cursor()
            
            # 扩展表
            extend_diagnosis_tree_node(cursor)
            create_diagnosis_session_table(cursor)
            create_diagnosis_step_history_table(cursor)
            create_test_recommendation_pool_table(cursor)
            create_views(cursor)
            
            # 提交更改
            conn.commit()
            
            # 验证结果
            verify_extensions(cursor)
            
            print(f"\n✓ 数据库 {db_path} 扩展完成")
            
        except sqlite3.Error as e:
            print(f"\n✗ 数据库扩展失败: {e}")
            return 1
        finally:
            if conn:
                conn.close()
    
    print("\n" + "=" * 60)
    print("所有数据库扩展完成")
    print("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(main())
