# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为双电机拖曳收放装置生成16个完整诊断功能
每个功能平均11步测试，故障分布: 50%器件/45%连接/10%其他
"""

import sqlite3
import sys

# 数据库路径
db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def clear_existing_data(cursor):
    """清除现有的诊断数据"""
    print("清除现有诊断数据...")
    cursor.execute("DELETE FROM diagnosis_tree_node")
    cursor.execute("DELETE FROM diagnosis_tree")
    cursor.execute("DELETE FROM Function WHERE FunctionID BETWEEN 1 AND 16")
    print("✓ 清除完成")

def create_functions(cursor):
    """创建16个功能定义"""
    print("\n创建功能定义...")
    
    functions = [
        (1, "左电机正转收缆功能", "KM01,KM03,KA01", "SA101.转速,KM01.状态", "左电机正常正转收缆"),
        (2, "右电机正转收缆功能", "KM02,KM04,KA02", "SA102.转速,KM02.状态", "右电机正常正转收缆"),
        (3, "左电机反转放缆功能", "KM05,KM07,KA03", "SA101.转速,KM05.状态", "左电机正常反转放缆"),
        (4, "右电机反转放缆功能", "KM06,KM08,KA04", "SA102.转速,KM06.状态", "右电机正常反转放缆"),
        (5, "双电机同步收缆功能", "KM01,KM02,PLC01", "SA101.转速,SA102.转速", "双电机同步收缆无偏差"),
        (6, "双电机同步放缆功能", "KM05,KM06,PLC01", "SA101.转速,SA102.转速", "双电机同步放缆无偏差"),
        (7, "排缆左移功能", "KM10,YV01,SQ01", "SA110.位置", "排缆机构正常左移"),
        (8, "排缆右移功能", "KM11,YV02,SQ02", "SA110.位置", "排缆机构正常右移"),
        (9, "左侧制动器控制功能", "YV10,SQ10,KA10", "SA120.张力", "左侧制动器正常工作"),
        (10, "右侧制动器控制功能", "YV11,SQ11,KA11", "SA121.张力", "右侧制动器正常工作"),
        (11, "缆绳张力平衡功能", "PLC01,SA120,SA121", "SA120.张力,SA121.张力", "双侧张力平衡控制"),
        (12, "过载保护功能", "KA20,SA103,SA104", "SA103.电流,SA104.电流", "电机过载时保护动作"),
        (13, "限位保护功能", "SQ20,SQ21,PLC01", "SQ20.状态,SQ21.状态", "到达限位时停机保护"),
        (14, "应急停机功能", "SQ30,KM01-08", "所有接触器状态", "紧急情况快速停机"),
        (15, "导引机构展开功能", "YV20,SQ40,KA30", "SQ40.状态", "导引机构正常展开"),
        (16, "拖体入水检测功能", "SA130,PLC01", "SA130.水压", "拖体入水状态检测")
    ]
    
    for func_id, name, execs, cmd_vals, remark in functions:
        cursor.execute("""
            INSERT INTO Function (FunctionID, FunctionName, ExecsList, CmdValList, Remark)
            VALUES (?, ?, ?, ?, ?)
        """, (func_id, name, execs, cmd_vals, remark))
    
    print(f"✓ 创建了 {len(functions)} 个功能定义")

def insert_nodes(cursor, nodes):
    """插入节点数据"""
    for node_data in nodes:
        data = node_data[:13]
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, data)

# 这里继续包含之前生成的完整功能1-5...
# (为节省篇幅，我会在后续消息中补充)

def verify_data(cursor):
    """验证生成的数据"""
    print("\n验证生成的数据...")
    
    cursor.execute("SELECT COUNT(*) FROM Function WHERE FunctionID BETWEEN 1 AND 16")
    func_count = cursor.fetchone()[0]
    print(f"✓ 功能数量: {func_count}")
    
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree")
    tree_count = cursor.fetchone()[0]
    print(f"✓ 诊断树数量: {tree_count}")
    
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree_node")
    total_nodes = cursor.fetchone()[0]
    print(f"✓ 节点总数: {total_nodes}")
    
    cursor.execute("""
        SELECT node_type, COUNT(*) 
        FROM diagnosis_tree_node 
        GROUP BY node_type
    """)
    for node_type, count in cursor.fetchall():
        print(f"  - {node_type}: {count}个")
    
    cursor.execute("""
        SELECT 
            CASE 
                WHEN fault_hypothesis LIKE '%器件故障%' THEN '器件故障'
                WHEN fault_hypothesis LIKE '%连接故障%' THEN '连接故障'
                WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' THEN '其他故障'
                WHEN fault_hypothesis LIKE '%系统正常%' THEN '正常'
                ELSE '未分类'
            END as fault_category,
            COUNT(*) as count
        FROM diagnosis_tree_node
        WHERE node_type = 'Fault'
        GROUP BY fault_category
    """)
    print("\n故障分布:")
    total_faults = 0
    for category, count in cursor.fetchall():
        if category != '正常':
            total_faults += count
        print(f"  - {category}: {count}个")
    
    cursor.execute("""
        SELECT tree_id, COUNT(*) 
        FROM diagnosis_tree_node 
        WHERE node_type = 'Test'
        GROUP BY tree_id
        ORDER BY tree_id
    """)
    print("\n各功能测试步数:")
    total_tests = 0
    for tree_id, count in cursor.fetchall():
        total_tests += count
        print(f"  - 功能{tree_id}: {count}步")
    print(f"平均测试步数: {total_tests/16:.1f}步")

def main():
    """主函数"""
    print("=" * 60)
    print("为双电机拖曳收放装置生成16个完整诊断功能")
    print("=" * 60)
    
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        clear_existing_data(cursor)
        create_functions(cursor)
        
        # 导入所有诊断树创建函数
        from generate_winch_trees_part1 import (
            create_diagnosis_tree_1, create_diagnosis_tree_2, 
            create_diagnosis_tree_3, create_diagnosis_tree_4,
            create_diagnosis_tree_5
        )
        from generate_winch_trees_part2 import (
            create_diagnosis_tree_6, create_diagnosis_tree_7,
            create_diagnosis_tree_8, create_diagnosis_tree_9,
            create_diagnosis_tree_10
        )
        from generate_winch_trees_part3 import (
            create_diagnosis_tree_11, create_diagnosis_tree_12,
            create_diagnosis_tree_13, create_diagnosis_tree_14,
            create_diagnosis_tree_15, create_diagnosis_tree_16
        )
        
        # 创建所有诊断树
        for i in range(1, 17):
            func_name = f"create_diagnosis_tree_{i}"
            eval(func_name)(cursor, insert_nodes)
        
        verify_data(cursor)
        
        conn.commit()
        conn.close()
        
        print("\n" + "=" * 60)
        print("✅ 成功生成16个完整诊断功能和诊断树")
        print("=" * 60)
        
    except Exception as e:
        print(f"\n❌ 错误: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
