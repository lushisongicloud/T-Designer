# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
调整功能9-13的故障分布，使器件故障和连接故障各占约50%
"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def adjust_fault_distribution(cursor):
    """调整故障类型分布"""
    
    # 功能9：将节点284（传感器故障）改为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：张力传感器SA120信号线L_SA120断线、屏蔽层接地不良、接线端子松动或传感器安装基座螺栓松动导致信号漂移'
        WHERE node_id = 284
    """)
    
    # 功能10：将节点318（传感器故障）改为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：张力传感器SA121信号线L_SA121断线、屏蔽层接地不良、接线端子松动或传感器安装基座螺栓松动导致信号漂移'
        WHERE node_id = 318
    """)
    
    # 功能11：将节点365（机械传动故障）改为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：传感器SA120或SA121机械传动部件（滑轮、导向轮、支架）连接松动、传感器安装螺栓松动或机械传动链条松脱'
        WHERE node_id = 365
    """)
    
    # 功能11：将节点374（综合故障）拆分为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：左右侧机械传动系统不对称、传感器安装位置偏差、传动链条张紧度不一致或反馈信号线路存在干扰'
        WHERE node_id = 374
    """)
    
    # 功能12：将节点387（传感器故障）改为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：电流传感器SA104穿芯线松动、屏蔽线接地失效、接线端子接触不良或传感器安装位置不当'
        WHERE node_id = 387
    """)
    
    # 功能12：将节点405（HMI故障）改为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：PLC与HMI通讯线路L_HMI故障、通讯协议配置错误、报警指示灯HL20线路断线或复位按钮SB20线路接触不良'
        WHERE node_id = 405
    """)
    
    # 功能13：将节点412（DI模块故障）改为连接故障
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：DI01模块与PLC背板接触不良、模块供电线路L_DI01断线或模块接地端子松动'
        WHERE node_id = 412
    """)
    
    # 功能13：将节点433（PLC程序故障）改为连接故障  
    cursor.execute("""
        UPDATE diagnosis_tree_node 
        SET fault_hypothesis = '连接故障：下限位保护硬件连锁链路L_LOCK2断线、安全继电器KA31线路故障或紧急停机回路接线错误'
        WHERE node_id = 433
    """)
    
    print("✓ 调整功能9: 节点284 (供电→连接)")
    print("✓ 调整功能10: 节点318 (传感器→连接)")
    print("✓ 调整功能11: 节点365 (机械→连接), 节点374 (综合→连接)")
    print("✓ 调整功能12: 节点387 (传感器→连接), 节点405 (HMI→连接)")
    print("✓ 调整功能13: 节点412 (模块→连接), 节点433 (软件→连接)")

def verify_new_distribution(cursor):
    """验证调整后的分布"""
    print("\n" + "="*80)
    print("调整后的故障分布:")
    print("="*80)
    
    for tree_id in range(9, 14):
        cursor.execute("""
            SELECT 
                SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
                SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
                SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' OR fault_hypothesis LIKE '%综合故障%' THEN 1 ELSE 0 END) as other,
                SUM(CASE WHEN fault_hypothesis LIKE '%系统正常%' THEN 1 ELSE 0 END) as normal
            FROM diagnosis_tree_node 
            WHERE tree_id = ? AND node_type = 'Fault'
        """, (tree_id,))
        
        stats = cursor.fetchone()
        total = stats[0] + stats[1] + stats[2]
        
        print(f"\n功能{tree_id}:")
        print(f"  器件: {stats[0]} ({stats[0]*100//total if total>0 else 0}%)")
        print(f"  连接: {stats[1]} ({stats[1]*100//total if total>0 else 0}%)")
        print(f"  其他: {stats[2]} ({stats[2]*100//total if total>0 else 0}%)")
        print(f"  正常: {stats[3]}")
    
    # 总体统计
    cursor.execute("""
        SELECT 
            SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
            SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
            SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' OR fault_hypothesis LIKE '%综合故障%' THEN 1 ELSE 0 END) as other
        FROM diagnosis_tree_node 
        WHERE tree_id BETWEEN 9 AND 13 AND node_type = 'Fault' AND fault_hypothesis NOT LIKE '%系统正常%'
    """)
    
    total_stats = cursor.fetchone()
    total = sum(total_stats)
    
    print(f"\n总计 (功能9-13):")
    print(f"  器件: {total_stats[0]} ({total_stats[0]*100//total}%)")
    print(f"  连接: {total_stats[1]} ({total_stats[1]*100//total}%)")
    print(f"  其他: {total_stats[2]} ({total_stats[2]*100//total}%)")
    print(f"  总故障数: {total}")

def main():
    """主函数"""
    print("="*80)
    print("调整功能9-13的故障分布")
    print("="*80)
    print("\n目标：器件故障约50%，连接故障约45%，其他故障约10%\n")
    
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        adjust_fault_distribution(cursor)
        verify_new_distribution(cursor)
        
        conn.commit()
        conn.close()
        
        print("\n" + "="*80)
        print("✅ 故障分布调整完成")
        print("="*80)
        
    except Exception as e:
        print(f"\n❌ 错误: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0

if __name__ == "__main__":
    import sys
    sys.exit(main())
