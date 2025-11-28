# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

import sqlite3

db_path = r'd:\SynologyDrive\Project\T_DESIGNER\templete\project.db'
conn = sqlite3.connect(db_path)
cursor = conn.cursor()

# 检查 port_connect_macro 表是否存在
cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='port_connect_macro'")
result = cursor.fetchone()
if result:
    print("port_connect_macro 表存在")
    cursor.execute("SELECT * FROM port_connect_macro LIMIT 5")
    rows = cursor.fetchall()
    if rows:
        print(f"表中有 {len(rows)} 条记录（显示前5条）:")
        for row in rows:
            print(row)
    else:
        print("表为空")
    
    # 显示表结构
    cursor.execute("PRAGMA table_info(port_connect_macro)")
    columns = cursor.fetchall()
    print("\n表结构:")
    for col in columns:
        print(f"  {col[1]:20s} {col[2]:15s}")
else:
    print("port_connect_macro 表不存在，需要创建")

conn.close()
