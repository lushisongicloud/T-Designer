import sqlite3

db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\双电机拖曳收放装置\双电机拖曳收放装置.db"

print(f"检查数据库: {db_path}\n")

try:
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 检查 container 表是否存在
    cursor.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='container'")
    if not cursor.fetchone():
        print("❌ container 表不存在!")
        conn.close()
        exit(1)
    print("✓ container 表存在")
    
    # 检查表结构
    cursor.execute("PRAGMA table_info(container)")
    columns = cursor.fetchall()
    print(f"\ncontainer 表结构 ({len(columns)} 列):")
    for col in columns:
        print(f"  - {col[1]} ({col[2]})")
    
    # 查询 container_id = 1 的记录
    print("\n查询 container_id=1:")
    cursor.execute("SELECT * FROM container WHERE container_id=1")
    row = cursor.fetchone()
    
    if row:
        print("✓ 找到记录:")
        col_names = [desc[0] for desc in cursor.description]
        for i, col_name in enumerate(col_names):
            value = row[i]
            if isinstance(value, str) and len(value) > 100:
                value = value[:100] + "..."
            print(f"  {col_name} = {value}")
    else:
        print("❌ 未找到 container_id=1 的记录!")
        
        # 显示前5条记录
        print("\n显示前5条 container 记录:")
        cursor.execute("SELECT container_id, name, level FROM container ORDER BY container_id LIMIT 5")
        for row in cursor.fetchall():
            print(f"  container_id={row[0]}, name={row[1]}, level={row[2]}")
    
    # 统计总数
    cursor.execute("SELECT COUNT(*) FROM container")
    total = cursor.fetchone()[0]
    print(f"\ncontainer 表总记录数: {total}")
    
    conn.close()
    
except Exception as e:
    print(f"❌ 错误: {e}")
