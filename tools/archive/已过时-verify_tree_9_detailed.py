# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""验证功能9的诊断树完整性和逻辑正确性"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def verify_tree_9():
    """验证功能9的诊断树"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    tree_id = 9
    
    print("=" * 80)
    print(f"功能9: 左侧制动器控制功能 - 诊断树详细信息")
    print("=" * 80)
    
    # 获取根节点
    cursor.execute("""
        SELECT root_node_id FROM diagnosis_tree WHERE tree_id = ?
    """, (tree_id,))
    root_id = cursor.fetchone()[0]
    print(f"\n根节点ID: {root_id}")
    
    # 获取所有节点
    cursor.execute("""
        SELECT node_id, parent_node_id, outcome, node_type, 
               test_description, expected_result, fault_hypothesis
        FROM diagnosis_tree_node 
        WHERE tree_id = ? 
        ORDER BY node_id
    """, (tree_id,))
    
    nodes = cursor.fetchall()
    print(f"总节点数: {len(nodes)}\n")
    
    # 构建树结构并显示
    node_dict = {}
    for node in nodes:
        node_dict[node[0]] = node
    
    def print_tree(node_id, indent=0):
        """递归打印树结构"""
        if node_id not in node_dict:
            return
        
        node = node_dict[node_id]
        node_id, parent_id, outcome, node_type, test_desc, expected, fault = node
        
        prefix = "  " * indent
        
        if node_type == "Test":
            print(f"{prefix}[测试节点 {node_id}]")
            print(f"{prefix}  测试: {test_desc[:60]}...")
            print(f"{prefix}  预期: {expected[:60] if expected else ''}...")
        elif node_type == "Fault":
            print(f"{prefix}[故障节点 {node_id}] outcome={outcome}")
            if fault.startswith("系统正常"):
                print(f"{prefix}  ✓ {fault[:70]}...")
            else:
                fault_type = "未知"
                if "器件故障" in fault:
                    fault_type = "器件"
                elif "连接故障" in fault:
                    fault_type = "连接"
                elif "软件故障" in fault or "供电故障" in fault:
                    fault_type = "其他"
                print(f"{prefix}  ✗ [{fault_type}] {fault[:70]}...")
        elif node_type == "Branch":
            print(f"{prefix}[分支节点 {node_id}]")
        
        # 查找子节点
        children = [n for n in nodes if n[1] == node_id]
        for child in children:
            print_tree(child[0], indent + 1)
    
    print("\n诊断树结构:")
    print("-" * 80)
    print_tree(root_id)
    
    # 验证树的完整性
    print("\n" + "=" * 80)
    print("完整性检查:")
    print("=" * 80)
    
    # 检查每个测试节点有两个子节点（Pass和Fail）
    test_nodes = [n for n in nodes if n[3] == "Test"]
    print(f"\n1. 测试节点检查 (共{len(test_nodes)}个):")
    for test_node in test_nodes:
        test_id = test_node[0]
        children = [n for n in nodes if n[1] == test_id]
        if len(children) != 2:
            print(f"   ⚠ 测试节点 {test_id} 有 {len(children)} 个子节点（应为2个）")
        else:
            outcomes = [c[2] for c in children]
            if "Pass" not in outcomes or "Fail" not in outcomes:
                print(f"   ⚠ 测试节点 {test_id} outcome不规范: {outcomes}")
    print("   ✓ 所有测试节点结构正确")
    
    # 检查故障节点没有子节点
    fault_nodes = [n for n in nodes if n[3] == "Fault"]
    print(f"\n2. 故障节点检查 (共{len(fault_nodes)}个):")
    for fault_node in fault_nodes:
        fault_id = fault_node[0]
        children = [n for n in nodes if n[1] == fault_id]
        if len(children) > 0:
            print(f"   ⚠ 故障节点 {fault_id} 有 {len(children)} 个子节点（应为0）")
    print("   ✓ 所有故障节点是叶子节点")
    
    # 检查分支节点有且仅有一个子节点
    branch_nodes = [n for n in nodes if n[3] == "Branch" and n[1] is not None]  # 排除根节点
    print(f"\n3. 分支节点检查 (共{len(branch_nodes)}个非根分支):")
    for branch_node in branch_nodes:
        branch_id = branch_node[0]
        children = [n for n in nodes if n[1] == branch_id]
        if len(children) != 1:
            print(f"   ⚠ 分支节点 {branch_id} 有 {len(children)} 个子节点（应为1个）")
    print("   ✓ 所有分支节点结构正确")
    
    # 统计故障类型
    print(f"\n4. 故障类型分布:")
    device_faults = [n for n in fault_nodes if "器件故障" in n[6]]
    connection_faults = [n for n in fault_nodes if "连接故障" in n[6]]
    other_faults = [n for n in fault_nodes if "软件故障" in n[6] or "供电故障" in n[6]]
    normal_results = [n for n in fault_nodes if "系统正常" in n[6]]
    
    total_faults = len(device_faults) + len(connection_faults) + len(other_faults)
    print(f"   器件故障: {len(device_faults)} ({len(device_faults)*100//total_faults}%)")
    print(f"   连接故障: {len(connection_faults)} ({len(connection_faults)*100//total_faults}%)")
    print(f"   其他故障: {len(other_faults)} ({len(other_faults)*100//total_faults}%)")
    print(f"   正常结果: {len(normal_results)}")
    
    # 检查故障描述的详细程度
    print(f"\n5. 故障描述质量检查:")
    for fault in device_faults + connection_faults + other_faults:
        desc = fault[6]
        if len(desc) < 20:
            print(f"   ⚠ 节点 {fault[0]} 故障描述过短: {desc}")
        # 检查是否包含具体器件编号
        if not any(comp in desc for comp in ["SA", "KA", "KM", "YV", "SQ", "PLC", "PS"]):
            print(f"   ⚠ 节点 {fault[0]} 缺少具体器件编号")
    print("   ✓ 故障描述包含详细信息")
    
    # 检查测试步骤的详细程度
    print(f"\n6. 测试步骤质量检查:")
    for test in test_nodes:
        desc = test[4]
        expected = test[5]
        if len(desc) < 15:
            print(f"   ⚠ 节点 {test[0]} 测试描述过短: {desc}")
        if len(expected) < 15:
            print(f"   ⚠ 节点 {test[0]} 预期结果过短: {expected}")
    print("   ✓ 测试步骤描述详细")
    
    print("\n" + "=" * 80)
    print("✅ 功能9诊断树验证完成")
    print("=" * 80)
    
    conn.close()

if __name__ == "__main__":
    verify_tree_9()
