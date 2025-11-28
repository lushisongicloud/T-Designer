# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
测试RepairInfo字段的保存和加载格式
验证TModelHelper::parseRepairInfo和serializeRepairInfo的正确性
"""

import sqlite3
import sys

def test_repairinfo_format():
    """测试RepairInfo数据格式"""
    
    # 测试数据：旧格式（从数据库中读取的）
    old_format = "故障模式名a￤0.1￤￤￤￤故障模式名c￤0.2￤￤￤￤故障模式名f￤0.3￤￤￤￤故障模式名k￤0.4￤￤"
    
    print("=== 旧格式数据 ===")
    print(f"原始字符串: {old_format}")
    print(f"长度: {len(old_format)}")
    print()
    
    # 解析旧格式
    records = old_format.split("￤￤")
    print(f"记录数量: {len(records)}")
    print()
    
    for i, record in enumerate(records):
        if not record.strip():
            continue
        fields = record.split("￤")
        print(f"记录 {i+1}:")
        print(f"  故障模式: '{fields[0] if len(fields) > 0 else ''}'")
        print(f"  故障概率: '{fields[1] if len(fields) > 1 else ''}'")
        print(f"  解决方案: '{fields[2] if len(fields) > 2 else ''}'")
        print(f"  所需资源: '{fields[3] if len(fields) > 3 else ''}'")
        print()
    
    # 测试新格式
    print("=== 新格式数据（应该保存的格式）===")
    new_format = "电机开路￤0.05￤更换电机￤电机×1￤￤电机短路￤0.02￤检修绕组￤维修工时×2h"
    print(f"新格式字符串: {new_format}")
    print()
    
    records = new_format.split("￤￤")
    print(f"记录数量: {len(records)}")
    print()
    
    for i, record in enumerate(records):
        if not record.strip():
            continue
        fields = record.split("￤")
        print(f"记录 {i+1}:")
        print(f"  故障模式: '{fields[0] if len(fields) > 0 else ''}'")
        print(f"  故障概率: '{fields[1] if len(fields) > 1 else ''}'")
        print(f"  解决方案: '{fields[2] if len(fields) > 2 else ''}'")
        print(f"  所需资源: '{fields[3] if len(fields) > 3 else ''}'")
        print()

def check_database_repairinfo(db_path):
    """检查数据库中的RepairInfo字段"""
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        print(f"\n=== 检查数据库: {db_path} ===\n")
        
        # 查询有RepairInfo的记录
        cursor.execute("""
            SELECT Equipment_ID, Name, RepairInfo 
            FROM Equipment 
            WHERE RepairInfo IS NOT NULL AND RepairInfo != '' 
            LIMIT 5
        """)
        
        rows = cursor.fetchall()
        print(f"找到 {len(rows)} 条包含RepairInfo的记录:\n")
        
        for equipment_id, name, repair_info in rows:
            print(f"元件ID: {equipment_id}")
            print(f"元件名称: {name}")
            print(f"RepairInfo长度: {len(repair_info)}")
            print(f"RepairInfo内容: {repair_info[:200]}...")
            
            # 解析并显示
            records = repair_info.split("￤￤")
            valid_records = [r for r in records if r.strip()]
            print(f"记录数: {len(valid_records)}")
            
            for i, record in enumerate(valid_records[:3]):  # 只显示前3条
                fields = record.split("￤")
                if len(fields) >= 4:
                    print(f"  记录{i+1}: 故障={fields[0]}, 概率={fields[1]}, 方案={fields[2]}, 资源={fields[3]}")
            print()
        
        conn.close()
        
    except sqlite3.Error as e:
        print(f"数据库错误: {e}")
    except Exception as e:
        print(f"错误: {e}")

if __name__ == "__main__":
    print("RepairInfo格式测试工具\n")
    print("=" * 60)
    
    # 测试格式解析
    test_repairinfo_format()
    
    # 检查数据库
    if len(sys.argv) > 1:
        db_path = sys.argv[1]
    else:
        db_path = "ref/LdMainData.db"
    
    check_database_repairinfo(db_path)
    
    print("\n" + "=" * 60)
    print("测试完成！")
