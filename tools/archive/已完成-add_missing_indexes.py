# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

import sqlite3

# 为第二个数据库添加缺失的索引
db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\双电机拖曳收放装置\双电机拖曳收放装置.db"

print(f"为数据库添加索引: {db_path}")

try:
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 检查当前索引
    cursor.execute("""
        SELECT name FROM sqlite_master 
        WHERE type='index' AND tbl_name='diagnosis_tree'
    """)
    existing_indexes = [row[0] for row in cursor.fetchall()]
    print(f"现有索引: {existing_indexes}")
    
    # 添加索引
    indexes_to_create = [
        ("idx_diagnosis_tree_function_id", "diagnosis_tree", "function_id"),
        ("idx_diagnosis_tree_container_id", "diagnosis_tree", "container_id")
    ]
    
    for idx_name, table_name, column_name in indexes_to_create:
        if idx_name not in existing_indexes:
            sql = f"CREATE INDEX {idx_name} ON {table_name}({column_name})"
            print(f"创建索引: {sql}")
            cursor.execute(sql)
        else:
            print(f"索引 {idx_name} 已存在,跳过")
    
    conn.commit()
    
    # 验证
    cursor.execute("""
        SELECT name FROM sqlite_master 
        WHERE type='index' AND tbl_name='diagnosis_tree'
    """)
    final_indexes = [row[0] for row in cursor.fetchall()]
    print(f"\n最终索引: {final_indexes}")
    
    conn.close()
    print("\n✅ 索引添加成功!")
    
except Exception as e:
    print(f"\n❌ 错误: {e}")
