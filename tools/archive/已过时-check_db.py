# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

import sqlite3

# 检查项目数据库中的 port_config 表
db_path = r'd:\SynologyDrive\Project\T_DESIGNER\templete\project.db'
conn = sqlite3.connect(db_path)
cursor = conn.cursor()

# 获取表结构
cursor.execute("SELECT sql FROM sqlite_master WHERE type='table' AND name='port_config'")
result = cursor.fetchone()
if result:
    print("port_config 表结构:")
    print(result[0])
    print("\n" + "="*80 + "\n")
    
    # 获取列信息
    cursor.execute("PRAGMA table_info(port_config)")
    columns = cursor.fetchall()
    print("列信息:")
    for col in columns:
        print(f"  {col[1]:20s} {col[2]:15s} {'NOT NULL' if col[3] else ''} {'PRIMARY KEY' if col[5] else ''}")
else:
    print("port_config 表不存在")

conn.close()
