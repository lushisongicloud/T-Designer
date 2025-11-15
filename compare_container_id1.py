import sqlite3

db1 = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
db2 = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\双电机拖曳收放装置\双电机拖曳收放装置.db"

for db_path, db_name in [(db1, "集中油源动力系统"), (db2, "双电机拖曳收放装置")]:
    print(f"\n{'='*60}")
    print(f"数据库: {db_name}")
    print('='*60)
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 检查 container_id=1
    cursor.execute("SELECT container_id, name, level FROM container WHERE container_id=1")
    row = cursor.fetchone()
    if row:
        print(f"✓ container_id=1 存在: name='{row[1]}', level='{row[2]}'")
    else:
        print("❌ container_id=1 不存在!")
        
        # 显示前5条
        cursor.execute("SELECT container_id, name, level FROM container ORDER BY container_id LIMIT 5")
        print("\n前5条记录:")
        for r in cursor.fetchall():
            print(f"  container_id={r[0]}, name={r[1]}, level={r[2]}")
    
    conn.close()
