#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""在UI中测试功能9的完整诊断流程"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def test_diagnosis_flow():
    """模拟诊断流程"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    tree_id = 9
    
    print("="*80)
    print("功能9: 左侧制动器控制功能 - 诊断流程模拟")
    print("="*80)
    
    # 获取根节点
    cursor.execute("SELECT root_node_id FROM diagnosis_tree WHERE tree_id = ?", (tree_id,))
    current_node_id = cursor.fetchone()[0]
    
    step = 0
    
    while True:
        # 获取当前节点
        cursor.execute("""
            SELECT node_id, node_type, test_description, expected_result, 
                   fault_hypothesis, outcome
            FROM diagnosis_tree_node 
            WHERE node_id = ?
        """, (current_node_id,))
        
        node = cursor.fetchone()
        if not node:
            break
        
        node_id, node_type, test_desc, expected, fault, outcome = node
        
        if node_type == "Branch":
            # 分支节点，继续到子节点
            cursor.execute("""
                SELECT node_id FROM diagnosis_tree_node 
                WHERE parent_node_id = ? 
                LIMIT 1
            """, (node_id,))
            child = cursor.fetchone()
            if child:
                current_node_id = child[0]
            else:
                break
        
        elif node_type == "Test":
            step += 1
            print(f"\n【步骤{step}】测试")
            print(f"  测试内容: {test_desc}")
            print(f"  预期结果: {expected}")
            print(f"  选择结果: [Pass] / [Fail]")
            
            # 模拟选择Pass继续
            cursor.execute("""
                SELECT node_id FROM diagnosis_tree_node 
                WHERE parent_node_id = ? AND outcome = 'Pass'
            """, (node_id,))
            child = cursor.fetchone()
            if child:
                current_node_id = child[0]
            else:
                break
        
        elif node_type == "Fault":
            if "系统正常" in fault:
                print(f"\n✅ 诊断结论: {fault}")
            else:
                print(f"\n❌ 故障诊断: {fault}")
            break
    
    print(f"\n诊断完成，共执行{step}步测试")
    print("="*80)
    
    conn.close()

if __name__ == "__main__":
    test_diagnosis_flow()
