# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

import sqlite3

conn = sqlite3.connect('MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db')
c = conn.cursor()

print("=== 功能7（排缆左移功能）的节点数据 ===")
c.execute('SELECT node_id, node_type, test_description, expected_result, fault_hypothesis FROM diagnosis_tree_node WHERE tree_id=7 ORDER BY node_id LIMIT 15')
for r in c.fetchall():
    print(f'Node {r[0]} [{r[1]}]: test="{r[2]}", expected="{r[3]}", fault="{r[4]}"')

conn.close()
