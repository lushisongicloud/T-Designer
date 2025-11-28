# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""检查数据库中的所有表"""
import sqlite3
import sys

if len(sys.argv) != 2:
    print("用法: python check_tables.py <数据库路径>")
    sys.exit(1)

db_path = sys.argv[1]
conn = sqlite3.connect(db_path)
cursor = conn.cursor()

# 获取所有表名
cursor.execute("SELECT name FROM sqlite_master WHERE type='table'")
tables = cursor.fetchall()

print(f"\n数据库 {db_path} 中的所有表:")
print("=" * 80)
for table in tables:
    print(f"  - {table[0]}")

conn.close()
