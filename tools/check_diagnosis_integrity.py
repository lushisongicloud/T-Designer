#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""快速验证诊断功能数据完整性"""

import sqlite3
import sys

def check_diagnosis_data(db_path):
    """检查诊断数据完整性"""
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    print("="*70)
    print("诊断系统数据完整性检查")
    print("="*70)
    
    issues = []
    
    # 检查1: 功能数量
    cursor.execute("SELECT COUNT(*) FROM Function WHERE FunctionID BETWEEN 1 AND 10")
    func_count = cursor.fetchone()[0]
    if func_count == 10:
        print(f"✓ 功能数量: {func_count}")
    else:
        print(f"✗ 功能数量异常: {func_count} (应该是10)")
        issues.append("功能数量不足")
    
    # 检查2: 诊断树数量
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree")
    tree_count = cursor.fetchone()[0]
    if tree_count == 10:
        print(f"✓ 诊断树数量: {tree_count}")
    else:
        print(f"✗ 诊断树数量异常: {tree_count} (应该是10)")
        issues.append("诊断树数量不足")
    
    # 检查3: root_node_id有效性
    cursor.execute("""
        SELECT dt.tree_id, dt.root_node_id, dtn.node_type
        FROM diagnosis_tree dt
        LEFT JOIN diagnosis_tree_node dtn ON dt.root_node_id = dtn.node_id
        WHERE dt.tree_id BETWEEN 1 AND 10
        ORDER BY dt.tree_id
    """)
    
    root_issues = []
    for row in cursor.fetchall():
        tree_id, root_id, node_type = row
        if node_type != "Branch":
            root_issues.append(f"树{tree_id}: root={root_id}, type={node_type}")
    
    if not root_issues:
        print(f"✓ root_node_id检查: 所有根节点都是Branch类型")
    else:
        print(f"✗ root_node_id检查失败:")
        for issue in root_issues:
            print(f"  - {issue}")
        issues.append("root_node_id错误")
    
    # 检查4: 孤立节点
    cursor.execute("""
        SELECT COUNT(*) FROM diagnosis_tree_node dtn
        WHERE dtn.parent_node_id IS NOT NULL
        AND NOT EXISTS (
            SELECT 1 FROM diagnosis_tree_node parent
            WHERE parent.node_id = dtn.parent_node_id
            AND parent.tree_id = dtn.tree_id
        )
    """)
    orphan_count = cursor.fetchone()[0]
    if orphan_count == 0:
        print(f"✓ 孤立节点检查: 无孤立节点")
    else:
        print(f"✗ 发现{orphan_count}个孤立节点")
        issues.append(f"{orphan_count}个孤立节点")
    
    # 检查5: 节点类型分布
    cursor.execute("""
        SELECT 
            node_type,
            COUNT(*) as count
        FROM diagnosis_tree_node
        GROUP BY node_type
        ORDER BY node_type
    """)
    
    print(f"\n节点类型分布:")
    for row in cursor.fetchall():
        node_type, count = row
        print(f"  {node_type}: {count}个")
    
    # 检查6: Test节点必填字段
    cursor.execute("""
        SELECT node_id, tree_id
        FROM diagnosis_tree_node
        WHERE node_type = 'Test'
        AND (test_description IS NULL OR test_description = ''
             OR expected_result IS NULL OR expected_result = '')
    """)
    
    test_issues = cursor.fetchall()
    if not test_issues:
        print(f"\n✓ Test节点必填字段: 完整")
    else:
        print(f"\n✗ {len(test_issues)}个Test节点缺少必填字段:")
        for node_id, tree_id in test_issues:
            print(f"  - 树{tree_id}节点{node_id}")
        issues.append(f"{len(test_issues)}个Test节点数据不完整")
    
    # 检查7: Fault节点必填字段
    cursor.execute("""
        SELECT node_id, tree_id
        FROM diagnosis_tree_node
        WHERE node_type = 'Fault'
        AND (fault_hypothesis IS NULL OR fault_hypothesis = '')
    """)
    
    fault_issues = cursor.fetchall()
    if not fault_issues:
        print(f"✓ Fault节点必填字段: 完整")
    else:
        print(f"✗ {len(fault_issues)}个Fault节点缺少故障假设:")
        for node_id, tree_id in fault_issues:
            print(f"  - 树{tree_id}节点{node_id}")
        issues.append(f"{len(fault_issues)}个Fault节点数据不完整")
    
    # 检查8: outcome与parent_node关系
    cursor.execute("""
        SELECT dtn.node_id, dtn.tree_id, dtn.outcome, parent.node_type
        FROM diagnosis_tree_node dtn
        JOIN diagnosis_tree_node parent ON dtn.parent_node_id = parent.node_id
        WHERE dtn.outcome IN ('Pass', 'Fail')
        AND parent.node_type NOT IN ('Test', 'Branch')
    """)
    
    outcome_issues = cursor.fetchall()
    if not outcome_issues:
        print(f"✓ outcome字段关系: 正确")
    else:
        print(f"✗ {len(outcome_issues)}个节点outcome字段异常:")
        for node_id, tree_id, outcome, parent_type in outcome_issues:
            print(f"  - 树{tree_id}节点{node_id}: outcome={outcome}, parent_type={parent_type}")
        issues.append(f"{len(outcome_issues)}个节点outcome错误")
    
    # 总结
    print("\n" + "="*70)
    if not issues:
        print("✅ 数据完整性检查通过!")
        conn.close()
        return 0
    else:
        print(f"❌ 发现 {len(issues)} 个问题:")
        for i, issue in enumerate(issues, 1):
            print(f"  {i}. {issue}")
        conn.close()
        return 1

def main():
    db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
    
    try:
        return check_diagnosis_data(db_path)
    except Exception as e:
        print(f"\n❌ 检查过程出错: {e}")
        import traceback
        traceback.print_exc()
        return 1

if __name__ == "__main__":
    sys.exit(main())
