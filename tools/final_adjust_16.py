#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""最终调整功能16"""

import sqlite3

db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

conn = sqlite3.connect(db_path)
c = conn.cursor()

# 将2个其他/器件故障改为连接故障
c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '连接故障：传感器SA130信号线在水下接头处断线、水密接头内部针脚腐蚀接触不良或电缆护套磨损导致芯线对地短路'
    WHERE node_id = 513
""")

c.execute("""
    UPDATE diagnosis_tree_node 
    SET fault_hypothesis = '连接故障：HMI数据库服务器网络连接中断、数据存储服务器线路L_DB故障或历史数据通讯接口故障'
    WHERE node_id = 534
""")

conn.commit()

# 验证所有功能9-16
print("="*70)
print("功能9-16最终故障分布")
print("="*70)

for tree_id in range(9, 17):
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
    
    print(f"功能{tree_id}: 器件{stats[0]}({stats[0]*100//total:2d}%) 连接{stats[1]}({stats[1]*100//total:2d}%) 其他{stats[2]}({stats[2]*100//total:2d}%)")

# 总计9-16
c.execute("""
    SELECT 
        SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
        SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
        SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' THEN 1 ELSE 0 END) as other
    FROM diagnosis_tree_node 
    WHERE tree_id BETWEEN 9 AND 16 AND node_type = 'Fault' AND fault_hypothesis NOT LIKE '%系统正常%'
""")

total_stats = c.fetchone()
total = sum(total_stats)

print("="*70)
print(f"总计(9-16): 器件{total_stats[0]}({total_stats[0]*100//total}%) 连接{total_stats[1]}({total_stats[1]*100//total}%) 其他{total_stats[2]}({total_stats[2]*100//total}%)")
print("="*70)

conn.close()
print("✓ 调整完成！")
