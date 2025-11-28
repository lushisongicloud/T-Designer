# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

import sqlite3

db1 = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
db2 = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\双电机拖曳收放装置\双电机拖曳收放装置.db"

for db_path, db_name in [(db1, "集中油源动力系统"), (db2, "双电机拖曳收放装置")]:
    print(f"\n{'='*60}")
    print(f"数据库: {db_name}")
    print('='*60)
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 查找 level='system' 的容器
    cursor.execute("SELECT container_id, name, level FROM container WHERE level='system' ORDER BY container_id")
    rows = cursor.fetchall()
    if rows:
        print(f"找到 {len(rows)} 个系统级容器:")
        for r in rows:
            print(f"  container_id={r[0]}, name='{r[1]}'")
    else:
        print("未找到 level='system' 的容器")
        
        # 显示所有不同的 level 值
        cursor.execute("SELECT DISTINCT level FROM container ORDER BY level")
        levels = [r[0] for r in cursor.fetchall()]
        print(f"数据库中的 level 值: {levels}")
        
        # 如果有其他层级,显示最顶层的
        if levels:
            cursor.execute(f"SELECT container_id, name, level FROM container WHERE level=? ORDER BY container_id LIMIT 3", (levels[0],))
            print(f"\n'{levels[0]}' 层级的前3条记录:")
            for r in cursor.fetchall():
                print(f"  container_id={r[0]}, name='{r[1]}'")
    
    conn.close()
