#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""调整功能14-16的故障分布"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

conn = sqlite3.connect(db_path)
c = conn.cursor()

print("调整功能14-16故障分布...")

# 功能14: 增加连接故障
c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '连接故障：紧急停止按钮SQ30内部接线断裂、按钮至安全模块的双通道线路交叉短路或按钮底座接地端子松动'
    WHERE node_id = 446
""")

c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '连接故障：安全继电器KA40-KA43级联连接线路松动、继电器间通讯线路L_SAFE_LINK故障或级联端子排接线错误'
    WHERE node_id = 455
""")

# 功能15: 增加连接故障
c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '连接故障：液压站控制器与PLC通讯线路L_HCTRL故障、控制电源线路接触不良或指示灯电路板接插件松动'
    WHERE node_id = 477
""")

# 功能16: 将软件故障改为器件/连接故障
c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '器件故障：AI02模拟量模块A/D转换芯片漂移、模块内部基准电压源失效或模块温度补偿电路故障'
    WHERE node_id = 522
""")

c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '器件故障：声光报警器HA02内部蜂鸣器损坏、LED灯珠烧毁或联锁继电器KA70线圈失效'
    WHERE node_id = 531
""")

conn.commit()

# 验证
for tree_id in range(14, 17):
    c.execute("""
        SELECT 
            SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
            SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
            SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' THEN 1 ELSE 0 END) as other
        FROM diagnosis_tree_node 
        WHERE tree_id = ? AND node_type = 'Fault' AND fault_hypothesis NOT LIKE '%系统正常%'
    """, (tree_id,))
    
    stats = c.fetchone()
    total = sum(stats)
    
    print(f"\n功能{tree_id}:")
    print(f"  器件: {stats[0]} ({stats[0]*100//total if total>0 else 0}%)")
    print(f"  连接: {stats[1]} ({stats[1]*100//total if total>0 else 0}%)")
    print(f"  其他: {stats[2]} ({stats[2]*100//total if total>0 else 0}%)")

# 总计
c.execute("""
    SELECT 
        SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
        SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
        SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' THEN 1 ELSE 0 END) as other
    FROM diagnosis_tree_node 
    WHERE tree_id BETWEEN 14 AND 16 AND node_type = 'Fault' AND fault_hypothesis NOT LIKE '%系统正常%'
""")

total_stats = c.fetchone()
total = sum(total_stats)

print(f"\n总计 (功能14-16):")
print(f"  器件: {total_stats[0]} ({total_stats[0]*100//total}%)")
print(f"  连接: {total_stats[1]} ({total_stats[1]*100//total}%)")
print(f"  其他: {total_stats[2]} ({total_stats[2]*100//total}%)")
print(f"✓ 调整完成！")

conn.close()
