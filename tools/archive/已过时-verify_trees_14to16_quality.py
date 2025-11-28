# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""全面验证功能14-16的诊断树质量"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def verify_trees_14_to_16():
    """验证功能14-16的所有诊断树"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    print("=" * 100)
    print("功能14-16诊断树质量验证报告")
    print("=" * 100)
    
    function_names = {
        14: "应急停机功能",
        15: "导引机构展开功能",
        16: "拖体入水检测功能"
    }
    
    all_stats = []
    
    for tree_id in range(14, 17):
        print(f"\n{'='*100}")
        print(f"功能{tree_id}: {function_names[tree_id]}")
        print(f"{'='*100}")
        
        # 获取所有节点
        cursor.execute("""
            SELECT node_id, parent_node_id, outcome, node_type, 
                   test_description, expected_result, fault_hypothesis
            FROM diagnosis_tree_node 
            WHERE tree_id = ? 
            ORDER BY node_id
        """, (tree_id,))
        nodes = cursor.fetchall()
        
        # 分类统计
        test_nodes = [n for n in nodes if n[3] == "Test"]
        fault_nodes = [n for n in nodes if n[3] == "Fault"]
        branch_nodes = [n for n in nodes if n[3] == "Branch"]
        
        device_faults = [n for n in fault_nodes if "器件故障" in n[6]]
        connection_faults = [n for n in fault_nodes if "连接故障" in n[6]]
        other_faults = [n for n in fault_nodes if "软件故障" in n[6] or "供电故障" in n[6]]
        normal_results = [n for n in fault_nodes if "系统正常" in n[6]]
        
        print(f"\n[节点统计]")
        print(f"   总节点数: {len(nodes)}")
        print(f"   测试节点: {len(test_nodes)} 步")
        print(f"   故障节点: {len(fault_nodes)} 个 (含{len(normal_results)}个正常结果)")
        print(f"   分支节点: {len(branch_nodes)} 个")
        
        total_faults = len(device_faults) + len(connection_faults) + len(other_faults)
        if total_faults > 0:
            print(f"\n[故障分布]")
            print(f"   器件故障: {len(device_faults)} 个 ({len(device_faults)*100//total_faults}%)")
            print(f"   连接故障: {len(connection_faults)} 个 ({len(connection_faults)*100//total_faults}%)")
            print(f"   其他故障: {len(other_faults)} 个 ({len(other_faults)*100//total_faults}%)")
        
        # 检查树结构完整性
        print(f"\n[结构检查]")
        issues = []
        
        for test in test_nodes:
            children = [n for n in nodes if n[1] == test[0]]
            if len(children) != 2:
                issues.append(f"测试节点{test[0]}子节点数={len(children)}，应为2")
        
        for fault in fault_nodes:
            children = [n for n in nodes if n[1] == fault[0]]
            if len(children) > 0:
                issues.append(f"故障节点{fault[0]}不应有子节点")
        
        if issues:
            for issue in issues:
                print(f"   ⚠ {issue}")
        else:
            print(f"   ✓ 树结构完整，所有测试节点有Pass/Fail分支")
            print(f"   ✓ 所有故障节点是叶子节点")
        
        # 检查测试步骤详细度
        print(f"\n[测试步骤质量]")
        avg_len = sum(len(t[4]) for t in test_nodes)//len(test_nodes) if test_nodes else 0
        print(f"   ✓ 平均测试描述长度: {avg_len}字")
        
        # 检查具体测量值
        value_keywords = ["±", "V", "A", "MPa", "°", "Ω", "ms", "s", "mm", "m", "%", "Hz", "N·m"]
        detailed_tests = [t for t in test_nodes if any(kw in t[4] or kw in t[5] for kw in value_keywords)]
        print(f"   ✓ {len(detailed_tests)}/{len(test_nodes)} 个测试包含具体数值/单位")
        
        # 故障描述质量
        print(f"\n[故障描述质量]")
        avg_fault_len = sum(len(f[6]) for f in fault_nodes if '系统正常' not in f[6])//total_faults if total_faults else 0
        print(f"   ✓ 平均故障描述长度: {avg_fault_len}字")
        
        # 检查器件编号
        component_keywords = ["PS0", "PLC", "SA", "KA", "KM", "YV", "SQ", "HP", "CY", "SV", "HL", "SB", "TB", "XT", "JB", "HB", "SF", "AI", "AO", "DI", "L_", "M", "HA", "QF", "RA", "SG"]
        faults_with_components = [f for f in fault_nodes if any(kw in f[6] for kw in component_keywords) and "系统正常" not in f[6]]
        print(f"   ✓ {len(faults_with_components)}/{total_faults} 个故障包含具体器件/线路编号")
        
        # 测试步骤示例
        print(f"\n[测试步骤示例] (前2步):")
        for i, test in enumerate(test_nodes[:2], 1):
            print(f"   步骤{i}: {test[4][:60]}...")
            print(f"          {test[5][:60]}...")
        
        # 故障示例
        print(f"\n[故障类型示例]:")
        if device_faults:
            print(f"   [器件] {device_faults[0][6][:80]}...")
        if connection_faults:
            print(f"   [连接] {connection_faults[0][6][:80]}...")
        if other_faults:
            print(f"   [其他] {other_faults[0][6][:80]}...")
        
        all_stats.append({
            'tree_id': tree_id,
            'name': function_names[tree_id],
            'tests': len(test_nodes),
            'faults': total_faults,
            'device': len(device_faults),
            'connection': len(connection_faults),
            'other': len(other_faults),
            'issues': len(issues)
        })
    
    # 总体统计
    print(f"\n{'='*100}")
    print("总体统计")
    print(f"{'='*100}")
    
    total_tests = sum(s['tests'] for s in all_stats)
    total_faults = sum(s['faults'] for s in all_stats)
    total_device = sum(s['device'] for s in all_stats)
    total_connection = sum(s['connection'] for s in all_stats)
    total_other = sum(s['other'] for s in all_stats)
    total_issues = sum(s['issues'] for s in all_stats)
    
    print(f"\n功能14-16汇总:")
    print(f"   总测试步骤: {total_tests} 步 (平均 {total_tests/3:.1f} 步/功能)")
    print(f"   总故障节点: {total_faults} 个")
    print(f"\n故障分布:")
    print(f"   器件故障: {total_device} 个 ({total_device*100//total_faults}%)")
    print(f"   连接故障: {total_connection} 个 ({total_connection*100//total_faults}%)")
    print(f"   其他故障: {total_other} 个 ({total_other*100//total_faults}%)")
    print(f"\n质量评估:")
    if total_issues == 0:
        print(f"   ✅ 所有诊断树结构完整，无逻辑错误")
    
    if abs(total_device - total_connection) <= total_faults * 0.1:
        print(f"   ✅ 故障分布均衡（器件vs连接差距<10%）")
    
    if total_tests >= 30:
        print(f"   ✅ 测试步骤充分（{total_tests}步 ≥ 30步）")
    
    print(f"\n{'='*100}")
    print("✅ 验证完成！")
    print(f"{'='*100}")
    
    conn.close()

if __name__ == "__main__":
    verify_trees_14_to_16()
