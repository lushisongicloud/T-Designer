# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""再次调整，增加器件故障比例"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

conn = sqlite3.connect(db_path)
c = conn.cursor()

# 将4个连接故障改回器件故障
c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '器件故障：张力传感器SA120内部应变片损坏、信号调理电路故障、电源模块失效或传感器外壳密封不良导致内部受潮'
    WHERE node_id = 284
""")

c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '器件故障：张力传感器SA121内部应变片损坏、信号调理电路故障、电源模块失效或传感器外壳密封不良导致内部受潮'
    WHERE node_id = 318
""")

c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '器件故障：电流传感器SA104霍尔元件老化、内部电路板元件损坏、穿芯绝缘套管破损或传感器外壳进水短路'
    WHERE node_id = 387
""")

c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '器件故障：限位开关SQ20或SQ21机械磨损、DI01模块输入通道损坏、PLC主控器输入电路故障或硬件连锁继电器KA30触点失效'
    WHERE node_id = 412
""")

conn.commit()

# 验证
c.execute("""
    SELECT 
        SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
        SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
        SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' OR fault_hypothesis LIKE '%综合故障%' THEN 1 ELSE 0 END) as other
    FROM diagnosis_tree_node 
    WHERE tree_id BETWEEN 9 AND 13 AND node_type = 'Fault' AND fault_hypothesis NOT LIKE '%系统正常%'
""")

stats = c.fetchone()
total = sum(stats)

print("最终故障分布:")
print(f"  器件故障: {stats[0]} ({stats[0]*100//total}%)")
print(f"  连接故障: {stats[1]} ({stats[1]*100//total}%)")
print(f"  其他故障: {stats[2]} ({stats[2]*100//total}%)")
print(f"✓ 调整完成！")

conn.close()
