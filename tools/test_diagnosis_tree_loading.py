#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
测试诊断树数据加载
"""

import sqlite3
import sys

def test_diagnosis_tree_loading(db_path):
    """测试诊断树加载逻辑"""
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    print("=" * 60)
    print("诊断树数据检查")
    print("=" * 60)
    
    # 1. 检查诊断树表
    cursor.execute("SELECT tree_id, function_id, name, root_node_id FROM diagnosis_tree")
    trees = cursor.fetchall()
    print(f"\n找到 {len(trees)} 个诊断树:")
    for tree in trees:
        tree_id, func_id, name, root_node_id = tree
        print(f"  Tree ID: {tree_id}, Function ID: {func_id}, Name: {name}, Root: {root_node_id}")
    
    if not trees:
        print("❌ 错误：没有找到诊断树数据！")
        return False
    
    # 2. 对每个树测试加载流程
    for tree_id, func_id, name, root_node_id in trees:
        print(f"\n{'='*60}")
        print(f"测试树 {tree_id}: {name}")
        print(f"{'='*60}")
        
        # 2.1 检查根节点
        if not root_node_id:
            print(f"❌ 树 {tree_id} 没有根节点！")
            continue
        
        cursor.execute("SELECT * FROM diagnosis_tree_node WHERE node_id = ?", (root_node_id,))
        root_node = cursor.fetchone()
        if not root_node:
            print(f"❌ 根节点 {root_node_id} 不存在！")
            continue
        
        col_names = [desc[0] for desc in cursor.description]
        root_dict = dict(zip(col_names, root_node))
        
        print(f"\n根节点 (node_id={root_dict['node_id']}):")
        print(f"  类型: {root_dict['node_type']}")
        print(f"  描述: {root_dict.get('test_description', 'N/A')}")
        print(f"  outcome: {root_dict['outcome']}")
        
        # 2.2 如果根节点是Branch，找第一个Test子节点
        current_node = root_dict
        if current_node['node_type'] == 'Branch':
            cursor.execute("""
                SELECT * FROM diagnosis_tree_node 
                WHERE parent_node_id = ? AND node_type = 'Test'
                LIMIT 1
            """, (current_node['node_id'],))
            test_node = cursor.fetchone()
            if test_node:
                current_node = dict(zip(col_names, test_node))
                print(f"\n✓ 找到第一个测试节点 (node_id={current_node['node_id']}):")
                print(f"  描述: {current_node['test_description']}")
            else:
                print(f"❌ 根节点是Branch但没有Test子节点！")
                continue
        
        # 2.3 检查测试节点的子节点
        test_node_id = current_node['node_id']
        cursor.execute("""
            SELECT node_id, node_type, outcome, test_description, fault_hypothesis
            FROM diagnosis_tree_node
            WHERE parent_node_id = ?
        """, (test_node_id,))
        children = cursor.fetchall()
        
        print(f"\n测试节点 {test_node_id} 有 {len(children)} 个子节点:")
        for child in children:
            child_id, child_type, child_outcome, child_test_desc, child_fault = child
            if child_type == 'Fault':
                print(f"  - [{child_outcome}] Fault: {child_fault}")
            elif child_type == 'Branch':
                print(f"  - [{child_outcome}] Branch (继续)")
            else:
                print(f"  - [{child_outcome}] Test: {child_test_desc}")
        
        # 2.4 模拟测试流程
        print(f"\n模拟测试流程:")
        print(f"  当前测试: {current_node['test_description']}")
        print(f"  按钮文本: [{current_node['pass_button_text']}] / [{current_node['fail_button_text']}]")
        
        # 假设用户点击"Pass"
        outcome_to_test = 'Pass'
        cursor.execute("""
            SELECT node_id, node_type, test_description, fault_hypothesis
            FROM diagnosis_tree_node
            WHERE parent_node_id = ? AND outcome = ?
        """, (test_node_id, outcome_to_test))
        next_node = cursor.fetchone()
        
        if next_node:
            next_id, next_type, next_test, next_fault = next_node
            print(f"  ✓ 用户点击 [{outcome_to_test}] -> 找到下一个节点:")
            if next_type == 'Fault':
                print(f"    故障定位: {next_fault}")
            elif next_type == 'Branch':
                print(f"    进入分支，需要继续查找测试节点")
            else:
                print(f"    下一个测试: {next_test}")
        else:
            print(f"  ❌ 用户点击 [{outcome_to_test}] -> 找不到匹配的子节点！")
            print(f"     可能的问题：outcome字段值不匹配")
        
        # 假设用户点击"Fail"
        outcome_to_test = 'Fail'
        cursor.execute("""
            SELECT node_id, node_type, test_description, fault_hypothesis
            FROM diagnosis_tree_node
            WHERE parent_node_id = ? AND outcome = ?
        """, (test_node_id, outcome_to_test))
        next_node = cursor.fetchone()
        
        if next_node:
            next_id, next_type, next_test, next_fault = next_node
            print(f"  ✓ 用户点击 [{outcome_to_test}] -> 找到下一个节点:")
            if next_type == 'Fault':
                print(f"    故障定位: {next_fault}")
            elif next_type == 'Branch':
                print(f"    进入分支，需要继续查找测试节点")
            else:
                print(f"    下一个测试: {next_test}")
        else:
            print(f"  ❌ 用户点击 [{outcome_to_test}] -> 找不到匹配的子节点！")
            print(f"     可能的问题：outcome字段值不匹配")
    
    conn.close()
    print(f"\n{'='*60}")
    print("测试完成")
    print(f"{'='*60}\n")
    return True

if __name__ == "__main__":
    db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
    test_diagnosis_tree_loading(db_path)
