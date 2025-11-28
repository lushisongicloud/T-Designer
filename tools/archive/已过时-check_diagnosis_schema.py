# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""检查诊断相关表的结构"""
import sqlite3

db_path = "templete/project.db"
conn = sqlite3.connect(db_path)
cursor = conn.cursor()

# 检查 diagnosis_tree 表
print("\n" + "=" * 80)
print("diagnosis_tree 表结构:")
print("=" * 80)
cursor.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='diagnosis_tree'")
result = cursor.fetchone()
if result:
    print(result[0])
    print("\n列信息:")
    cursor.execute("PRAGMA table_info(diagnosis_tree)")
    for row in cursor.fetchall():
        print(f"  {row[1]:20} {row[2]:15} {'PRIMARY KEY' if row[5] else ''}")

# 检查 diagnosis_tree_node 表
print("\n" + "=" * 80)
print("diagnosis_tree_node 表结构:")
print("=" * 80)
cursor.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='diagnosis_tree_node'")
result = cursor.fetchone()
if result:
    print(result[0])
    print("\n列信息:")
    cursor.execute("PRAGMA table_info(diagnosis_tree_node)")
    for row in cursor.fetchall():
        print(f"  {row[1]:20} {row[2]:15} {'PRIMARY KEY' if row[5] else ''}")

conn.close()
