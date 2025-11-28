# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
验证诊断树数据的详细信息
"""

import sqlite3

db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"

conn = sqlite3.connect(db_path)
cursor = conn.cursor()

print("="*80)
print("诊断树数据验证")
print("="*80)

# 查看第1棵树的详细结构
print("\n功能1: 液压泵站启动功能 - 诊断树结构:")
cursor.execute("""
    SELECT node_id, parent_node_id, node_type, 
           SUBSTR(test_description, 1, 30) as test_desc,
           SUBSTR(fault_hypothesis, 1, 40) as fault_desc,
           pass_button_text, fail_button_text
    FROM diagnosis_tree_node
    WHERE tree_id = 1
    ORDER BY node_id
""")

for row in cursor.fetchall():
    node_id, parent_id, node_type, test_desc, fault_desc, pass_text, fail_text = row
    if node_type == "Branch":
        print(f"  [{node_id:3d}] Branch (parent: {parent_id})")
    elif node_type == "Test":
        print(f"  [{node_id:3d}] Test: {test_desc}... (parent: {parent_id})")
    else:  # Fault
        print(f"  [{node_id:3d}] Fault: {fault_desc}... (parent: {parent_id})")

# 检查一些测试节点的详细内容
print("\n\n示例测试节点详细内容 (节点2):")
cursor.execute("""
    SELECT test_description, expected_result, pass_button_text, fail_button_text
    FROM diagnosis_tree_node
    WHERE node_id = 2
""")
row = cursor.fetchone()
if row:
    print(f"  测试描述: {row[0]}")
    print(f"  预期结果: {row[1]}")
    print(f"  通过按钮: {row[2]}")
    print(f"  失败按钮: {row[3]}")

# 检查故障节点的类型分布（功能1）
print("\n\n功能1的故障类型:")
cursor.execute("""
    SELECT fault_hypothesis
    FROM diagnosis_tree_node
    WHERE tree_id = 1 AND node_type = 'Fault'
    ORDER BY node_id
""")
for i, row in enumerate(cursor.fetchall(), 1):
    fault = row[0]
    if "器件故障" in fault:
        fault_type = "器件"
    elif "连接故障" in fault:
        fault_type = "连接"
    elif "软件故障" in fault:
        fault_type = "软件"
    elif "系统正常" in fault:
        fault_type = "正常"
    else:
        fault_type = "其他"
    print(f"  {i}. [{fault_type}] {fault[:60]}")

# 检查所有功能的名称
print("\n\n所有诊断功能:")
cursor.execute("""
    SELECT f.FunctionID, f.FunctionName, 
           COUNT(DISTINCT dtn.node_id) as node_count,
           SUM(CASE WHEN dtn.node_type='Test' THEN 1 ELSE 0 END) as test_count
    FROM Function f
    LEFT JOIN diagnosis_tree dt ON f.FunctionID = dt.function_id
    LEFT JOIN diagnosis_tree_node dtn ON dt.tree_id = dtn.tree_id
    WHERE f.FunctionID BETWEEN 1 AND 10
    GROUP BY f.FunctionID
    ORDER BY f.FunctionID
""")

for row in cursor.fetchall():
    func_id, func_name, nodes, tests = row
    print(f"  功能{func_id}: {func_name} ({tests}个测试, {nodes}个节点)")

conn.close()
print("\n" + "="*80)
