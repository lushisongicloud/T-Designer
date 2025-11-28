# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""检查功能15节点499的子节点配置问题"""

import sqlite3
import sys

def check_node_499():
    db_path = "MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"
    
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        print("=" * 120)
        print("检查节点497-505的详细信息")
        print("=" * 120)
        
        cursor.execute("""
            SELECT node_id, tree_id, parent_node_id, node_type, 
                   test_description, expected_result, outcome, comment
            FROM diagnosis_tree_node 
            WHERE node_id BETWEEN 497 AND 505
            ORDER BY node_id
        """)
        
        rows = cursor.fetchall()
        for row in rows:
            node_id, tree_id, parent_id, node_type, test_desc, expected, outcome, comment = row
            print(f"\n节点 {node_id}:")
            print(f"  树ID: {tree_id}, 父节点: {parent_id}, 类型: {node_type}")
            print(f"  测试描述: {test_desc}")
            print(f"  预期结果: {expected}")
            print(f"  结果: {outcome}")
            print(f"  备注: {comment}")
        
        print("\n" + "=" * 120)
        print("检查节点499的子节点")
        print("=" * 120)
        
        cursor.execute("""
            SELECT node_id, node_type, outcome, test_description, fault_hypothesis
            FROM diagnosis_tree_node 
            WHERE parent_node_id = 499
            ORDER BY outcome
        """)
        
        children = cursor.fetchall()
        print(f"\n节点499的子节点数量: {len(children)}")
        
        if children:
            for child in children:
                child_id, child_type, child_outcome, child_test, child_fault = child
                print(f"\n  子节点 {child_id}:")
                print(f"    类型: {child_type}")
                print(f"    结果: {child_outcome}")
                print(f"    测试描述: {child_test}")
                print(f"    故障假设: {child_fault}")
        else:
            print("\n  ❌ 节点499没有子节点！这是问题所在。")
        
        print("\n" + "=" * 120)
        print("检查整个功能15的树结构")
        print("=" * 120)
        
        cursor.execute("""
            SELECT node_id, parent_node_id, node_type, outcome, 
                   SUBSTR(test_description, 1, 40) as test_desc_short,
                   SUBSTR(fault_hypothesis, 1, 40) as fault_short
            FROM diagnosis_tree_node 
            WHERE tree_id = 15
            ORDER BY node_id
        """)
        
        all_nodes = cursor.fetchall()
        print(f"\n功能15总节点数: {len(all_nodes)}")
        print("\n节点层级结构:")
        print("node_id | parent | type       | outcome | 描述/故障")
        print("-" * 100)
        
        for node in all_nodes:
            node_id, parent, ntype, outcome, desc, fault = node
            content = desc if desc else fault
            parent_str = str(parent) if parent else "ROOT"
            print(f"{node_id:7} | {parent_str:6} | {ntype:10} | {outcome:7} | {content}")
        
        print("\n" + "=" * 120)
        print("分析诊断树完整性")
        print("=" * 120)
        
        # 检查每个测试节点是否有Pass和Fail分支
        cursor.execute("""
            SELECT node_id, test_description
            FROM diagnosis_tree_node 
            WHERE tree_id = 15 AND node_type = 'Test'
            ORDER BY node_id
        """)
        
        test_nodes = cursor.fetchall()
        print(f"\n测试节点数量: {len(test_nodes)}")
        
        incomplete_tests = []
        for test_id, test_desc in test_nodes:
            cursor.execute("""
                SELECT outcome
                FROM diagnosis_tree_node 
                WHERE parent_node_id = ? AND node_type = 'Branch'
                ORDER BY outcome
            """, (test_id,))
            
            branches = cursor.fetchall()
            if len(branches) < 2:
                incomplete_tests.append((test_id, test_desc, [b[0] for b in branches]))
        
        if incomplete_tests:
            print("\n❌ 发现不完整的测试节点:")
            for test_id, test_desc, branches in incomplete_tests:
                print(f"  节点 {test_id}: {test_desc[:50]}")
                print(f"    当前分支: {branches}")
                print(f"    缺失: {'Fail' if 'Pass' in branches else 'Pass'}")
        else:
            print("\n✅ 所有测试节点都有Pass和Fail分支")
        
        # 检查Branch节点是否有子节点
        cursor.execute("""
            SELECT node_id, outcome, parent_node_id
            FROM diagnosis_tree_node 
            WHERE tree_id = 15 AND node_type = 'Branch'
            ORDER BY node_id
        """)
        
        branch_nodes = cursor.fetchall()
        print(f"\n分支节点数量: {len(branch_nodes)}")
        
        incomplete_branches = []
        for branch_id, outcome, parent in branch_nodes:
            cursor.execute("""
                SELECT COUNT(*)
                FROM diagnosis_tree_node 
                WHERE parent_node_id = ?
            """, (branch_id,))
            
            child_count = cursor.fetchone()[0]
            if child_count == 0:
                incomplete_branches.append((branch_id, outcome, parent))
        
        if incomplete_branches:
            print("\n❌ 发现没有子节点的分支节点:")
            for branch_id, outcome, parent in incomplete_branches:
                # 获取父节点信息
                cursor.execute("""
                    SELECT node_type, test_description
                    FROM diagnosis_tree_node 
                    WHERE node_id = ?
                """, (parent,))
                parent_info = cursor.fetchone()
                parent_type, parent_desc = parent_info if parent_info else ("Unknown", "")
                
                print(f"  节点 {branch_id} (结果: {outcome}):")
                print(f"    父节点: {parent} ({parent_type})")
                print(f"    父节点描述: {parent_desc[:60]}")
        else:
            print("\n✅ 所有分支节点都有子节点")
        
        conn.close()
        
        return len(incomplete_branches) == 0
        
    except Exception as e:
        print(f"❌ 错误: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = check_node_499()
    sys.exit(0 if success else 1)
