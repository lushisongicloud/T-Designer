import sqlite3

db_path = r'd:\SynologyDrive\Project\T_DESIGNER\templete\project.db'
conn = sqlite3.connect(db_path)
cursor = conn.cursor()

# 测试UPDATE语句
update_sql = """UPDATE port_config SET port_type = ?, direction = ?, variable_profile = ?, 
                      variables_json = ?, connect_macro = ?, updated_at = CURRENT_TIMESTAMP 
                      WHERE port_config_id = ?"""

# 打印占位符数量
print(f"占位符数量: {update_sql.count('?')}")
print(f"SQL: {update_sql}")

# 测试INSERT语句
insert_sql = """INSERT INTO port_config (container_id, function_block, port_name, port_type, 
                      direction, variable_profile, variables_json, connect_macro) 
                      VALUES (?, ?, ?, ?, ?, ?, ?, ?)"""
print(f"\nINSERT占位符数量: {insert_sql.count('?')}")
print(f"SQL: {insert_sql}")

conn.close()
