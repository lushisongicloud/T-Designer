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
