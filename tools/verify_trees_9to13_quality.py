#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""全面验证功能9-13的诊断树质量"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def verify_all_trees():
    """验证功能9-13的所有诊断树"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    print("=" * 100)
    print("功能9-13诊断树质量验证报告")
    print("=" * 100)
    
    function_names = {
        9: "左侧制动器控制功能",
        10: "右侧制动器控制功能",
        11: "缆绳张力平衡功能",
        12: "过载保护功能",
        13: "限位保护功能"
    }
    
    all_stats = []
    
    for tree_id in range(9, 14):
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
        other_faults = [n for n in fault_nodes if "软件故障" in n[6] or "供电故障" in n[6] or "综合故障" in n[6]]
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
        
        # 检查测试节点
        for test in test_nodes:
            children = [n for n in nodes if n[1] == test[0]]
            if len(children) != 2:
                issues.append(f"测试节点{test[0]}子节点数={len(children)}，应为2")
            else:
                outcomes = [c[2] for c in children]
                if "Pass" not in outcomes or "Fail" not in outcomes:
                    issues.append(f"测试节点{test[0]} outcome不规范")
        
        # 检查故障节点
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
        short_tests = [t for t in test_nodes if len(t[4]) < 15 or len(t[5]) < 15]
        if short_tests:
            print(f"   ⚠ 有{len(short_tests)}个测试描述过短")
        else:
            print(f"   ✓ 所有测试步骤描述详细（平均{sum(len(t[4]) for t in test_nodes)//len(test_nodes)}字）")
        
        # 检查是否包含具体的测试值和测量方法
        detail_keywords = ["万用表", "测量", "观察", "检查", "应为", "±", "范围", "状态"]
        detailed_tests = [t for t in test_nodes if any(kw in t[4] or kw in t[5] for kw in detail_keywords)]
        print(f"   ✓ {len(detailed_tests)}/{len(test_nodes)} 个测试包含具体测量方法或数值")
        
        # 检查故障描述详细度
        print(f"\n[故障描述质量]")
        short_faults = [f for f in fault_nodes if len(f[6]) < 20 and "系统正常" not in f[6]]
        if short_faults:
            print(f"   ⚠ 有{len(short_faults)}个故障描述过短")
        else:
            print(f"   ✓ 所有故障描述详细（平均{sum(len(f[6]) for f in fault_nodes if '系统正常' not in f[6])//total_faults}字）")
        
        # 检查是否包含具体器件编号
        component_keywords = ["PS0", "PLC", "SA", "KA", "KM", "YV", "SQ", "HP", "CY", "SV", "HL", "SB", "TB", "XT", "JB", "HB", "FB", "SF", "AI", "AO", "DI", "L_"]
        faults_with_components = [f for f in fault_nodes if any(kw in f[6] for kw in component_keywords) and "系统正常" not in f[6]]
        print(f"   ✓ {len(faults_with_components)}/{total_faults} 个故障包含具体器件/线路编号")
        
        # 示例输出
        print(f"\n[测试步骤示例] (前3步):")
        for i, test in enumerate(test_nodes[:3], 1):
            print(f"   步骤{i}: {test[4][:50]}...")
            print(f"          {test[5][:50]}...")
        
        print(f"\n[故障类型示例] (各类型1个):")
        if device_faults:
            print(f"   [器件] {device_faults[0][6][:70]}...")
        if connection_faults:
            print(f"   [连接] {connection_faults[0][6][:70]}...")
        if other_faults:
            print(f"   [其他] {other_faults[0][6][:70]}...")
        
        # 汇总统计
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
    
    print(f"\n功能9-13汇总:")
    print(f"   总测试步骤: {total_tests} 步 (平均 {total_tests/5:.1f} 步/功能)")
    print(f"   总故障节点: {total_faults} 个")
    print(f"\n故障分布:")
    print(f"   器件故障: {total_device} 个 ({total_device*100//total_faults}%)")
    print(f"   连接故障: {total_connection} 个 ({total_connection*100//total_faults}%)")
    print(f"   其他故障: {total_other} 个 ({total_other*100//total_faults}%)")
    print(f"\n质量评估:")
    if total_issues == 0:
        print(f"   ✅ 所有诊断树结构完整，无逻辑错误")
    else:
        print(f"   ⚠ 发现 {total_issues} 个结构问题")
    
    if abs(total_device - total_connection) <= total_faults * 0.1:
        print(f"   ✅ 故障分布均衡（器件vs连接差距<10%）")
    else:
        print(f"   ⚠ 故障分布需调整（建议器件和连接各占约50%）")
    
    if total_tests >= 50:
        print(f"   ✅ 测试步骤充分（{total_tests}步 ≥ 50步）")
    
    print(f"\n{'='*100}")
    print("✅ 验证完成！")
    print(f"{'='*100}")
    
    conn.close()

if __name__ == "__main__":
    verify_all_trees()
