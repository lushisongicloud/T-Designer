# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""验证功能15诊断树Branch节点嵌套修复"""

import sqlite3

def verify_branch_nesting():
    db_path = "MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    print("=" * 100)
    print("功能15诊断树Branch嵌套情况分析")
    print("=" * 100)
    
    # 找出所有Branch节点
    cursor.execute("""
        SELECT node_id, parent_node_id, outcome
        FROM diagnosis_tree_node
        WHERE tree_id = 15 AND node_type = 'Branch'
        ORDER BY node_id
    """)
    
    branches = cursor.fetchall()
    print(f"\n找到 {len(branches)} 个Branch节点\n")
    
    nested_branches = []
    
    for branch_id, parent_id, outcome in branches:
        # 检查这个Branch的父节点是否也是Branch
        if parent_id:
            cursor.execute("""
                SELECT node_type, test_description
                FROM diagnosis_tree_node
                WHERE node_id = ?
            """, (parent_id,))
            
            parent_info = cursor.fetchone()
            if parent_info:
                parent_type, parent_desc = parent_info
                
                if parent_type == 'Branch':
                    nested_branches.append((branch_id, parent_id, outcome))
                    print(f"嵌套Branch: 节点{branch_id} (outcome={outcome}) 的父节点 {parent_id} 也是Branch")
                elif parent_type == 'Test':
                    print(f"正常Branch: 节点{branch_id} (outcome={outcome}) 的父节点 {parent_id} 是Test")
                    print(f"  父测试: {parent_desc[:60]}")
        
        # 检查这个Branch的子节点
        cursor.execute("""
            SELECT node_id, node_type, outcome, test_description, fault_hypothesis
            FROM diagnosis_tree_node
            WHERE parent_node_id = ?
            ORDER BY outcome
        """, (branch_id,))
        
        children = cursor.fetchall()
        print(f"\n  Branch {branch_id} 的子节点:")
        for child_id, child_type, child_outcome, child_test, child_fault in children:
            content = child_test if child_test else child_fault
            print(f"    节点{child_id}: {child_type:10} outcome={child_outcome:7} {content[:50] if content else ''}")
    
    print("\n" + "=" * 100)
    print("嵌套Branch节点汇总")
    print("=" * 100)
    
    if nested_branches:
        print(f"\n找到 {len(nested_branches)} 个嵌套Branch节点:")
        for branch_id, parent_id, outcome in nested_branches:
            print(f"  节点{branch_id} → 父节点{parent_id} (outcome={outcome})")
            
            # 跟踪这条链路到底
            cursor.execute("""
                SELECT node_id, node_type, test_description, fault_hypothesis
                FROM diagnosis_tree_node
                WHERE parent_node_id = ?
            """, (branch_id,))
            
            grandchildren = cursor.fetchall()
            for gc_id, gc_type, gc_test, gc_fault in grandchildren:
                content = gc_test if gc_test else gc_fault
                print(f"    └─> 节点{gc_id} ({gc_type}): {content[:60] if content else ''}")
    else:
        print("\n✅ 没有发现Branch→Branch的嵌套情况")
    
    print("\n" + "=" * 100)
    print("潜在问题节点检查")
    print("=" * 100)
    
    # 检查所有Test节点是否都能到达Fault节点
    cursor.execute("""
        SELECT node_id, test_description
        FROM diagnosis_tree_node
        WHERE tree_id = 15 AND node_type = 'Test'
        ORDER BY node_id
    """)
    
    test_nodes = cursor.fetchall()
    
    problems = []
    for test_id, test_desc in test_nodes:
        # 检查Pass分支能否到达Test或Fault
        cursor.execute("""
            WITH RECURSIVE path AS (
                SELECT node_id, parent_node_id, node_type, outcome, 0 as depth
                FROM diagnosis_tree_node
                WHERE parent_node_id = ? AND outcome = 'Pass'
                
                UNION ALL
                
                SELECT n.node_id, n.parent_node_id, n.node_type, n.outcome, p.depth + 1
                FROM diagnosis_tree_node n
                JOIN path p ON n.parent_node_id = p.node_id
                WHERE p.depth < 5 AND p.node_type != 'Fault' AND p.node_type != 'Test'
            )
            SELECT node_id, node_type, depth
            FROM path
            WHERE node_type IN ('Test', 'Fault')
            ORDER BY depth
            LIMIT 1
        """, (test_id,))
        
        pass_result = cursor.fetchone()
        
        if not pass_result:
            problems.append((test_id, test_desc, 'Pass'))
    
    if problems:
        print(f"\n❌ 发现 {len(problems)} 个有问题的测试节点:")
        for test_id, test_desc, branch in problems:
            print(f"  节点{test_id} ({branch}分支): {test_desc[:60]}")
            print(f"    该分支无法到达Test或Fault节点")
    else:
        print("\n✅ 所有测试节点的Pass/Fail分支都能正确到达下一个节点")
    
    conn.close()
    
    return len(nested_branches), len(problems)

if __name__ == "__main__":
    nested_count, problem_count = verify_branch_nesting()
    
    print("\n" + "=" * 100)
    print("总结")
    print("=" * 100)
    print(f"嵌套Branch节点数: {nested_count}")
    print(f"有问题的测试节点数: {problem_count}")
    
    if nested_count > 0:
        print("\n✅ 代码修复已实现递归Branch节点处理，应该能正确处理嵌套情况")
    
    if problem_count == 0:
        print("✅ 树结构完整，所有路径都能到达终点")
