# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python
# -*- coding: utf-8 -*-
import sqlite3

conn = sqlite3.connect('MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db')
cursor = conn.cursor()
cursor.execute('''
    SELECT node_id, parent_node_id, node_type, outcome, test_description 
    FROM diagnosis_tree_node 
    WHERE node_id IN (499, 500, 501, 502)
    ORDER BY node_id
''')

print("节点499-502关系:")
for row in cursor.fetchall():
    node_id, parent, ntype, outcome, desc = row
    print(f"节点{node_id}: parent={parent}, type={ntype:10}, outcome={outcome:7}, desc={desc[:40] if desc else ''}")

conn.close()
