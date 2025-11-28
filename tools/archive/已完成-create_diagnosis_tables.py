# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""为双电机拖曳收放装置数据库创建诊断相关表"""
import sqlite3
import sys

def create_diagnosis_tables(db_path):
    """创建诊断相关表"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 创建 diagnosis_tree 表
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS diagnosis_tree (
        tree_id INTEGER PRIMARY KEY AUTOINCREMENT,
        container_id INTEGER NOT NULL,
        name TEXT,
        description TEXT,
        function_id INTEGER,
        root_node_id INTEGER,
        created_time TEXT DEFAULT CURRENT_TIMESTAMP,
        auto_generated INTEGER DEFAULT 1,
        FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE
    )
    """)
    
    # 创建 diagnosis_tree_node 表
    cursor.execute("""
    CREATE TABLE IF NOT EXISTS diagnosis_tree_node (
        node_id INTEGER PRIMARY KEY AUTOINCREMENT,
        tree_id INTEGER NOT NULL,
        parent_node_id INTEGER,
        test_id INTEGER,
        state_id INTEGER,
        outcome TEXT,
        comment TEXT,
        node_type TEXT DEFAULT 'test',
        test_description TEXT,
        expected_result TEXT,
        fault_hypothesis TEXT,
        isolation_level INTEGER DEFAULT 0,
        test_priority REAL DEFAULT 0.5,
        FOREIGN KEY(tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
        FOREIGN KEY(parent_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE,
        FOREIGN KEY(test_id) REFERENCES test_definition(test_id),
        FOREIGN KEY(state_id) REFERENCES container_state(state_id)
    )
    """)
    
    conn.commit()
    conn.close()
    print(f"✅ 成功为数据库 {db_path} 创建诊断相关表")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("用法: python create_diagnosis_tables.py <数据库路径>")
        sys.exit(1)
    
    create_diagnosis_tables(sys.argv[1])
