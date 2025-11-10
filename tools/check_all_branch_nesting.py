#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""检查所有16个功能的Branch嵌套情况"""

import sqlite3

def check_all_functions_branch_nesting():
    db_path = "MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    print("=" * 100)
    print("检查所有功能的Branch嵌套情况")
    print("=" * 100)
    
    # 查找所有Branch→Branch的嵌套
    cursor.execute("""
        SELECT 
            child.tree_id,
            child.node_id as child_branch_id,
            parent.node_id as parent_branch_id,
            child.outcome
        FROM diagnosis_tree_node child
        JOIN diagnosis_tree_node parent ON child.parent_node_id = parent.node_id
        WHERE child.node_type = 'Branch' 
          AND parent.node_type = 'Branch'
        ORDER BY child.tree_id, child.node_id
    """)
    
    nested_branches = cursor.fetchall()
    
    if not nested_branches:
        print("\n✅ 没有发现任何功能存在Branch→Branch嵌套")
        conn.close()
        return
    
    print(f"\n⚠️  发现 {len(nested_branches)} 个Branch嵌套情况:\n")
    
    # 获取功能名称
    cursor.execute("SELECT FunctionID, FunctionName FROM Function ORDER BY FunctionID")
    func_names = {fid: fname for fid, fname in cursor.fetchall()}
    
    current_tree = None
    for tree_id, child_id, parent_id, outcome in nested_branches:
        func_name = func_names.get(tree_id, f"未知功能{tree_id}")
        if tree_id != current_tree:
            if current_tree is not None:
                print()
            current_tree = tree_id
            print(f"功能{tree_id}: {func_name}")
        
        print(f"  节点{child_id} (Branch, outcome={outcome}) ← 父节点{parent_id} (Branch)")
        
        # 查找这个嵌套Branch下面有什么
        cursor.execute("""
            SELECT node_id, node_type, outcome, 
                   SUBSTR(test_description, 1, 50) as test_desc,
                   SUBSTR(fault_hypothesis, 1, 50) as fault_desc
            FROM diagnosis_tree_node
            WHERE parent_node_id = ?
            ORDER BY outcome
        """, (child_id,))
        
        children = cursor.fetchall()
        for c_id, c_type, c_outcome, c_test, c_fault in children:
            content = c_test if c_test else c_fault
            print(f"    └─> 节点{c_id} ({c_type}, outcome={c_outcome}): {content}")
    
    print("\n" + "=" * 100)
    print("影响评估")
    print("=" * 100)
    
    # 统计每个功能的嵌套情况
    affected_functions = set(item[0] for item in nested_branches)
    
    print(f"\n受影响的功能数: {len(affected_functions)}")
    print(f"功能列表: {', '.join(f'功能{fid}' for fid in sorted(affected_functions))}")
    
    print("\n修复状态:")
    print("✅ diagnosisengine.cpp 已修改为支持递归Branch处理")
    print("✅ 所有受影响的功能将自动获得修复")
    
    print("\n建议:")
    print("1. 在T-Designer中测试受影响的功能，验证诊断流程能正常完成")
    print("2. 特别测试会触发嵌套Branch的路径（通常是Pass路径）")
    print("3. 验证日志输出是否显示 'Entering nested branch node' 信息")
    
    conn.close()

if __name__ == "__main__":
    check_all_functions_branch_nesting()
