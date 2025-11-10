import sqlite3

conn = sqlite3.connect('MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db')
c = conn.cursor()

print("=== 功能7（排缆左移功能）的节点数据 ===")
c.execute('SELECT node_id, node_type, test_description, expected_result, fault_hypothesis FROM diagnosis_tree_node WHERE tree_id=7 ORDER BY node_id LIMIT 15')
for r in c.fetchall():
    print(f'Node {r[0]} [{r[1]}]: test="{r[2]}", expected="{r[3]}", fault="{r[4]}"')

conn.close()
