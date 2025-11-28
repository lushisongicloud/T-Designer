# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
生成10个完整的液压系统诊断功能
每个功能都包含完整的诊断树，逻辑严谨，数据格式正确
"""

import sqlite3
import sys

def clear_existing_data(cursor):
    """清除现有的诊断数据"""
    print("清除现有诊断数据...")
    cursor.execute("DELETE FROM diagnosis_tree_node")
    cursor.execute("DELETE FROM diagnosis_tree")
    cursor.execute("DELETE FROM Function WHERE FunctionID BETWEEN 1 AND 10")
    print("✓ 清除完成")

def create_functions(cursor):
    """创建10个功能定义"""
    print("\n创建功能定义...")
    
    functions = [
        (1, "液压泵站启动功能", "M1,M2", "P1.压力,KA1.状态", "液压泵站正常启动并建立压力"),
        (2, "压力控制功能", "KV1,KV2", "P1.压力,P2.压力", "系统压力维持在设定范围"),
        (3, "液压油质量监测功能", "FS1", "FS1.颗粒度,FS1.含水量", "液压油质量符合标准"),
        (4, "电机过载保护功能", "M1,FR1", "FR1.状态,I1.电流", "电机过载时自动保护"),
        (5, "油温控制功能", "TC1,FAN1", "T1.温度", "油温维持在正常范围"),
        (6, "液位监测报警功能", "LS1,LS2", "LS1.液位,LS2.液位", "液位异常时及时报警"),
        (7, "泵组切换功能", "M1,M2,KA2", "M1.运行,M2.运行", "主备泵自动切换"),
        (8, "压力卸荷功能", "KV3,P1", "P1.压力,KV3.状态", "空载时自动卸荷节能"),
        (9, "滤芯堵塞监测功能", "DP1,DP2", "DP1.压差,DP2.压差", "滤芯堵塞时及时更换"),
        (10, "应急停机功能", "SB1,KM1", "KM1.状态", "紧急情况快速停机")
    ]
    
    for func_id, name, execs, cmd_vals, remark in functions:
        cursor.execute("""
            INSERT INTO Function (FunctionID, FunctionName, ExecsList, CmdValList, Remark)
            VALUES (?, ?, ?, ?, ?)
        """, (func_id, name, execs, cmd_vals, remark))
    
    print(f"✓ 创建了 {len(functions)} 个功能定义")

def create_diagnosis_tree_1(cursor):
    """功能1: 液压泵站启动功能 - 复杂度：高"""
    tree_id = 1
    function_id = 1
    container_id = 1
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "液压泵站启动功能诊断树", "诊断液压泵站无法启动或启动异常的故障", 1))
    
    nodes = [
        # 格式: (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment, node_type, test_description, expected_result, fault_hypothesis, isolation_level, test_priority, pass_button_text, fail_button_text)
        # 根节点
        (1, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "是", "否"),
        
        # 第一层：电源检查
        (2, tree_id, 1, None, None, "Unknown", None, "Test", "测试AC220V供电是否正常", "万用表测试主电源，电压应在198-242V", "", 0, 0.9, "电压符合", "电压不符合"),
        (3, tree_id, 2, None, None, "Fail", None, "Fault", "", "", "供电系统故障：电源滤波器或配电系统异常", 95, 0.9, "", ""),
        (4, tree_id, 2, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第二层：控制电源
        (5, tree_id, 4, None, None, "Unknown", None, "Test", "测试控制电源输出是否正常", "测试DC24V控制电源，电压应在21.6-26.4V", "", 0, 0.8, "输出正常", "输出异常"),
        (6, tree_id, 5, None, None, "Fail", None, "Fault", "", "", "控制电源模块故障", 90, 0.8, "", ""),
        (7, tree_id, 5, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第三层：PLC检查
        (8, tree_id, 7, None, None, "Unknown", None, "Test", "检查PLC1（主控）运行指示灯及通讯状态", "运行灯应常亮，通讯灯闪烁", "", 0, 0.7, "指示正常", "指示异常"),
        (9, tree_id, 8, None, None, "Fail", None, "Fault", "", "", "PLC主控器故障或程序异常", 85, 0.7, "", ""),
        (10, tree_id, 8, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第四层：启动信号
        (11, tree_id, 10, None, None, "Unknown", None, "Test", "通过本地操作单元发送泵站启动命令，检查电机启动信号输出", "PLC输出端应有24V信号", "", 0, 0.6, "信号正常", "信号异常"),
        (12, tree_id, 11, None, None, "Fail", None, "Fault", "", "", "PLC输出模块故障或软启动器未收到信号", 80, 0.6, "", ""),
        (13, tree_id, 11, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第五层：电机启动
        (14, tree_id, 13, None, None, "Unknown", None, "Test", "检查电机M1是否启动运行", "电机应正常运转，听声音是否异常", "", 0, 0.5, "运行正常", "运行异常"),
        (15, tree_id, 14, None, None, "Fail", None, "Fault", "", "", "电机故障、软启动器故障或接触器故障", 75, 0.5, "", ""),
        (16, tree_id, 14, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第六层：压力建立
        (17, tree_id, 16, None, None, "Unknown", None, "Test", "观察压力表P1，5秒内压力是否上升到设定值", "压力应上升至10-12MPa", "", 0, 0.4, "压力正常", "压力异常"),
        (18, tree_id, 17, None, None, "Fail", None, "Fault", "", "", "液压泵故障、溢流阀未关闭或系统严重泄漏", 70, 0.4, "", ""),
        (19, tree_id, 17, None, None, "Pass", None, "Fault", "", "", "系统正常，启动成功", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = 1 WHERE tree_id = ?", (tree_id,))
    print(f"✓ 创建功能1诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_2(cursor):
    """功能2: 压力控制功能 - 复杂度：中"""
    tree_id = 2
    function_id = 2
    container_id = 2
    node_id_start = 20
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "压力控制功能诊断树", "诊断系统压力无法维持或压力异常的故障", node_id_start))
    
    nodes = [
        # 根节点
        (20, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 压力传感器检查
        (21, tree_id, 20, None, None, "Unknown", None, "Test", "检查压力传感器P1读数是否准确", "对比机械压力表，误差应小于±0.5MPa", "", 0, 0.9, "读数准确", "读数偏差"),
        (22, tree_id, 21, None, None, "Fail", None, "Fault", "", "", "压力传感器故障或信号线路故障", 90, 0.9, "", ""),
        (23, tree_id, 21, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 压力设定检查
        (24, tree_id, 23, None, None, "Unknown", None, "Test", "检查PLC中压力设定值是否正确", "上限12MPa，下限10MPa", "", 0, 0.8, "设定正确", "设定错误"),
        (25, tree_id, 24, None, None, "Fail", None, "Fault", "", "", "PLC参数设置错误", 95, 0.8, "", ""),
        (26, tree_id, 24, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 溢流阀检查
        (27, tree_id, 26, None, None, "Unknown", None, "Test", "手动调节溢流阀，观察压力是否变化", "顺时针旋转压力应上升", "", 0, 0.7, "调节有效", "调节无效"),
        (28, tree_id, 27, None, None, "Fail", None, "Fault", "", "", "溢流阀卡滞或损坏", 85, 0.7, "", ""),
        (29, tree_id, 27, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 比例阀检查
        (30, tree_id, 29, None, None, "Unknown", None, "Test", "检查比例阀KV1控制信号是否正常", "PLC输出4-20mA信号", "", 0, 0.6, "信号正常", "信号异常"),
        (31, tree_id, 30, None, None, "Fail", None, "Fault", "", "", "PLC输出模块故障或比例阀线圈故障", 80, 0.6, "", ""),
        (32, tree_id, 30, None, None, "Pass", None, "Fault", "", "", "系统正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能2诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_3(cursor):
    """功能3: 液压油质量监测功能 - 复杂度：中"""
    tree_id = 3
    function_id = 3
    container_id = 3
    node_id_start = 33
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "液压油质量监测诊断树", "诊断油质监测异常或报警的故障", node_id_start))
    
    nodes = [
        (33, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (34, tree_id, 33, None, None, "Unknown", None, "Test", "检查油质传感器FS1电源是否正常", "传感器指示灯应亮", "", 0, 0.9, "电源正常", "电源异常"),
        (35, tree_id, 34, None, None, "Fail", None, "Fault", "", "", "传感器电源故障或接线松动", 90, 0.9, "", ""),
        (36, tree_id, 34, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (37, tree_id, 36, None, None, "Unknown", None, "Test", "检查传感器通讯是否正常", "PLC应能读取到传感器数据", "", 0, 0.8, "通讯正常", "通讯故障"),
        (38, tree_id, 37, None, None, "Fail", None, "Fault", "", "", "通讯线路故障或传感器损坏", 85, 0.8, "", ""),
        (39, tree_id, 37, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (40, tree_id, 39, None, None, "Unknown", None, "Test", "取样检测，对比实际油质与传感器读数", "颗粒度等级应一致", "", 0, 0.7, "读数准确", "读数偏差"),
        (41, tree_id, 40, None, None, "Fail", None, "Fault", "", "", "传感器精度下降，需要校准或更换", 80, 0.7, "", ""),
        (42, tree_id, 40, None, None, "Pass", None, "Fault", "", "", "传感器工作正常，油质确实超标", 95, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能3诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_4(cursor):
    """功能4: 电机过载保护功能"""
    tree_id = 4
    function_id = 4
    container_id = 4
    node_id_start = 43
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "电机过载保护功能诊断树", "诊断电机过载保护不动作或误动作的故障", node_id_start))
    
    nodes = [
        (43, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (44, tree_id, 43, None, None, "Unknown", None, "Test", "检查热继电器FR1整定值是否匹配电机额定电流", "整定值应为电机额定电流的1.1-1.15倍", "", 0, 0.9, "整定合理", "整定不当"),
        (45, tree_id, 44, None, None, "Fail", None, "Fault", "", "", "热继电器整定值设置错误", 95, 0.9, "", ""),
        (46, tree_id, 44, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (47, tree_id, 46, None, None, "Unknown", None, "Test", "手动按下FR1复位按钮，观察是否复位", "应能听到复位声音", "", 0, 0.8, "可以复位", "无法复位"),
        (48, tree_id, 47, None, None, "Fail", None, "Fault", "", "", "热继电器机械故障", 90, 0.8, "", ""),
        (49, tree_id, 47, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (50, tree_id, 49, None, None, "Unknown", None, "Test", "测量电机实际运行电流是否正常", "不应超过额定电流的110%", "", 0, 0.7, "电流正常", "电流过大"),
        (51, tree_id, 50, None, None, "Fail", None, "Fault", "", "", "电机负载过大或电机本身故障", 85, 0.7, "", ""),
        (52, tree_id, 50, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (53, tree_id, 52, None, None, "Unknown", None, "Test", "检查FR1常闭触点是否正常", "万用表测试常闭触点应导通", "", 0, 0.6, "触点正常", "触点故障"),
        (54, tree_id, 53, None, None, "Fail", None, "Fault", "", "", "FR1辅助触点故障", 80, 0.6, "", ""),
        (55, tree_id, 53, None, None, "Pass", None, "Fault", "", "", "保护功能正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能4诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_5(cursor):
    """功能5: 油温控制功能"""
    tree_id = 5
    function_id = 5
    container_id = 5
    node_id_start = 56
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "油温控制功能诊断树", "诊断油温过高或温控系统故障", node_id_start))
    
    nodes = [
        (56, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (57, tree_id, 56, None, None, "Unknown", None, "Test", "检查温度传感器T1读数是否准确", "对比温度计，误差应小于±2℃", "", 0, 0.9, "读数准确", "读数偏差"),
        (58, tree_id, 57, None, None, "Fail", None, "Fault", "", "", "温度传感器故障", 90, 0.9, "", ""),
        (59, tree_id, 57, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (60, tree_id, 59, None, None, "Unknown", None, "Test", "检查温控器TC1设定值", "启动温度55℃，停止温度50℃", "", 0, 0.8, "设定正确", "设定错误"),
        (61, tree_id, 60, None, None, "Fail", None, "Fault", "", "", "温控器参数设置错误", 95, 0.8, "", ""),
        (62, tree_id, 60, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (63, tree_id, 62, None, None, "Unknown", None, "Test", "手动启动风扇FAN1，观察是否运转", "风扇应正常运转", "", 0, 0.7, "运转正常", "不运转"),
        (64, tree_id, 63, None, None, "Fail", None, "Fault", "", "", "风扇电机故障或接触器故障", 85, 0.7, "", ""),
        (65, tree_id, 63, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (66, tree_id, 65, None, None, "Unknown", None, "Test", "检查冷却器散热片是否堵塞", "散热片应清洁无油污", "", 0, 0.6, "清洁良好", "严重堵塞"),
        (67, tree_id, 66, None, None, "Fail", None, "Fault", "", "", "冷却器散热片堵塞，需清洗", 80, 0.6, "", ""),
        (68, tree_id, 66, None, None, "Pass", None, "Fault", "", "", "温控系统正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能5诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_6(cursor):
    """功能6: 液位监测报警功能"""
    tree_id = 6
    function_id = 6
    container_id = 6
    node_id_start = 69
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "液位监测报警功能诊断树", "诊断液位监测不报警或误报警的故障", node_id_start))
    
    nodes = [
        (69, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (70, tree_id, 69, None, None, "Unknown", None, "Test", "检查液位开关LS1电源是否正常", "开关应有24V供电", "", 0, 0.9, "电源正常", "电源异常"),
        (71, tree_id, 70, None, None, "Fail", None, "Fault", "", "", "液位开关电源故障", 90, 0.9, "", ""),
        (72, tree_id, 70, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (73, tree_id, 72, None, None, "Unknown", None, "Test", "手动模拟液位变化，观察LS1是否动作", "浮子上升应闭合，下降应断开", "", 0, 0.8, "动作正常", "不动作"),
        (74, tree_id, 73, None, None, "Fail", None, "Fault", "", "", "液位开关机械卡滞或损坏", 85, 0.8, "", ""),
        (75, tree_id, 73, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (76, tree_id, 75, None, None, "Unknown", None, "Test", "检查PLC是否接收到液位信号", "PLC输入点应有信号变化", "", 0, 0.7, "信号正常", "无信号"),
        (77, tree_id, 76, None, None, "Fail", None, "Fault", "", "", "PLC输入模块故障或线路断线", 80, 0.7, "", ""),
        (78, tree_id, 76, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (79, tree_id, 78, None, None, "Unknown", None, "Test", "检查报警灯和蜂鸣器是否工作", "手动触发应有声光报警", "", 0, 0.6, "报警正常", "报警失效"),
        (80, tree_id, 79, None, None, "Fail", None, "Fault", "", "", "报警装置故障", 75, 0.6, "", ""),
        (81, tree_id, 79, None, None, "Pass", None, "Fault", "", "", "液位监测系统正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能6诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_7(cursor):
    """功能7: 泵组切换功能"""
    tree_id = 7
    function_id = 7
    container_id = 7
    node_id_start = 82
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "泵组切换功能诊断树", "诊断主备泵无法切换的故障", node_id_start))
    
    nodes = [
        (82, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (83, tree_id, 82, None, None, "Unknown", None, "Test", "检查切换条件是否满足", "主泵运行时间超过设定值或故障", "", 0, 0.9, "条件满足", "条件未满足"),
        (84, tree_id, 83, None, None, "Fail", None, "Fault", "", "", "PLC切换逻辑参数设置错误", 90, 0.9, "", ""),
        (85, tree_id, 83, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (86, tree_id, 85, None, None, "Unknown", None, "Test", "检查备用泵M2是否处于就绪状态", "M2热继电器应复位，无故障", "", 0, 0.8, "就绪状态", "未就绪"),
        (87, tree_id, 86, None, None, "Fail", None, "Fault", "", "", "备用泵存在故障或未复位", 85, 0.8, "", ""),
        (88, tree_id, 86, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (89, tree_id, 88, None, None, "Unknown", None, "Test", "手动触发切换，检查PLC输出是否正常", "M1停止信号，M2启动信号", "", 0, 0.7, "输出正常", "输出异常"),
        (90, tree_id, 89, None, None, "Fail", None, "Fault", "", "", "PLC输出模块故障", 80, 0.7, "", ""),
        (91, tree_id, 89, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (92, tree_id, 91, None, None, "Unknown", None, "Test", "检查切换接触器KA2是否动作", "KA2应吸合，指示灯亮", "", 0, 0.6, "动作正常", "不动作"),
        (93, tree_id, 92, None, None, "Fail", None, "Fault", "", "", "切换接触器KA2故障或线圈烧损", 75, 0.6, "", ""),
        (94, tree_id, 92, None, None, "Pass", None, "Fault", "", "", "切换功能正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能7诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_8(cursor):
    """功能8: 压力卸荷功能"""
    tree_id = 8
    function_id = 8
    container_id = 8
    node_id_start = 95
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "压力卸荷功能诊断树", "诊断空载时不卸荷导致能耗高的故障", node_id_start))
    
    nodes = [
        (95, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (96, tree_id, 95, None, None, "Unknown", None, "Test", "检查卸荷条件是否满足", "压力达到上限且无负载动作", "", 0, 0.9, "条件满足", "条件未满足"),
        (97, tree_id, 96, None, None, "Fail", None, "Fault", "", "", "PLC卸荷逻辑错误或传感器故障", 88, 0.9, "", ""),
        (98, tree_id, 96, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (99, tree_id, 98, None, None, "Unknown", None, "Test", "检查卸荷电磁阀KV3是否得电", "PLC输出端应有24V信号", "", 0, 0.8, "得电正常", "未得电"),
        (100, tree_id, 99, None, None, "Fail", None, "Fault", "", "", "PLC输出模块故障", 85, 0.8, "", ""),
        (101, tree_id, 99, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (102, tree_id, 101, None, None, "Unknown", None, "Test", "手动给KV3通电，观察压力是否下降", "压力应快速降至0.5MPa以下", "", 0, 0.7, "压力下降", "压力不降"),
        (103, tree_id, 102, None, None, "Fail", None, "Fault", "", "", "卸荷阀KV3阀芯卡滞或损坏", 82, 0.7, "", ""),
        (104, tree_id, 102, None, None, "Pass", None, "Fault", "", "", "卸荷功能正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能8诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_9(cursor):
    """功能9: 滤芯堵塞监测功能"""
    tree_id = 9
    function_id = 9
    container_id = 9
    node_id_start = 105
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "滤芯堵塞监测功能诊断树", "诊断滤芯堵塞不报警的故障", node_id_start))
    
    nodes = [
        (105, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (106, tree_id, 105, None, None, "Unknown", None, "Test", "检查压差传感器DP1电源是否正常", "传感器应有24V供电", "", 0, 0.9, "电源正常", "电源异常"),
        (107, tree_id, 106, None, None, "Fail", None, "Fault", "", "", "压差传感器电源故障", 88, 0.9, "", ""),
        (108, tree_id, 106, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (109, tree_id, 108, None, None, "Unknown", None, "Test", "检查DP1读数是否合理", "正常应小于0.3MPa", "", 0, 0.8, "读数合理", "读数异常"),
        (110, tree_id, 109, None, None, "Fail", None, "Fault", "", "", "压差传感器故障或堵塞", 85, 0.8, "", ""),
        (111, tree_id, 109, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (112, tree_id, 111, None, None, "Unknown", None, "Test", "检查PLC中压差报警阈值设置", "应设置为0.4MPa", "", 0, 0.7, "设置正确", "设置错误"),
        (113, tree_id, 112, None, None, "Fail", None, "Fault", "", "", "PLC参数设置错误", 92, 0.7, "", ""),
        (114, tree_id, 112, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (115, tree_id, 114, None, None, "Unknown", None, "Test", "模拟高压差，检查是否报警", "压差超0.4MPa应报警", "", 0, 0.6, "正常报警", "不报警"),
        (116, tree_id, 115, None, None, "Fail", None, "Fault", "", "", "PLC报警逻辑错误或报警装置故障", 80, 0.6, "", ""),
        (117, tree_id, 115, None, None, "Pass", None, "Fault", "", "", "监测功能正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能9诊断树: {len(nodes)}个节点")

def create_diagnosis_tree_10(cursor):
    """功能10: 应急停机功能"""
    tree_id = 10
    function_id = 10
    container_id = 10
    node_id_start = 118
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "应急停机功能诊断树", "诊断紧急停止按钮失效的故障", node_id_start))
    
    nodes = [
        (118, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (119, tree_id, 118, None, None, "Unknown", None, "Test", "检查急停按钮SB1常闭触点是否正常", "未按下时应导通", "", 0, 0.9, "触点正常", "触点异常"),
        (120, tree_id, 119, None, None, "Fail", None, "Fault", "", "", "急停按钮触点故障或接线松动", 90, 0.9, "", ""),
        (121, tree_id, 119, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (122, tree_id, 121, None, None, "Unknown", None, "Test", "按下SB1，检查PLC是否接收到停止信号", "PLC输入点应变化", "", 0, 0.8, "信号正常", "无信号"),
        (123, tree_id, 122, None, None, "Fail", None, "Fault", "", "", "PLC输入模块故障或线路断线", 85, 0.8, "", ""),
        (124, tree_id, 122, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (125, tree_id, 124, None, None, "Unknown", None, "Test", "检查PLC急停程序逻辑", "接收信号后应立即切断所有输出", "", 0, 0.7, "逻辑正确", "逻辑错误"),
        (126, tree_id, 125, None, None, "Fail", None, "Fault", "", "", "PLC程序错误", 88, 0.7, "", ""),
        (127, tree_id, 125, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (128, tree_id, 127, None, None, "Unknown", None, "Test", "检查主接触器KM1是否能断电", "KM1应立即释放", "", 0, 0.6, "能断电", "不能断电"),
        (129, tree_id, 128, None, None, "Fail", None, "Fault", "", "", "接触器KM1粘连或机械卡滞", 82, 0.6, "", ""),
        (130, tree_id, 128, None, None, "Pass", None, "Fault", "", "", "应急停机功能正常", 100, 1.0, "", ""),
    ]
    
    for node_data in nodes:
        cursor.execute("""
            INSERT INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority, pass_button_text, fail_button_text)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, node_data)
    
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 创建功能10诊断树: {len(nodes)}个节点")

def verify_data(cursor):
    """验证生成的数据"""
    print("\n" + "="*60)
    print("数据验证")
    print("="*60)
    
    # 统计功能
    cursor.execute("SELECT COUNT(*) FROM Function WHERE FunctionID BETWEEN 1 AND 10")
    func_count = cursor.fetchone()[0]
    print(f"✓ 功能数量: {func_count}")
    
    # 统计诊断树
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree WHERE tree_id BETWEEN 1 AND 10")
    tree_count = cursor.fetchone()[0]
    print(f"✓ 诊断树数量: {tree_count}")
    
    # 统计节点
    cursor.execute("""
        SELECT tree_id, 
               COUNT(*) as total,
               SUM(CASE WHEN node_type='Test' THEN 1 ELSE 0 END) as tests,
               SUM(CASE WHEN node_type='Fault' THEN 1 ELSE 0 END) as faults,
               SUM(CASE WHEN node_type='Branch' THEN 1 ELSE 0 END) as branches
        FROM diagnosis_tree_node 
        WHERE tree_id BETWEEN 1 AND 10
        GROUP BY tree_id
        ORDER BY tree_id
    """)
    
    print(f"\n各诊断树节点统计:")
    print(f"{'树ID':<6} {'总节点':<8} {'测试':<6} {'故障':<6} {'分支':<6}")
    print("-" * 40)
    
    total_nodes = 0
    total_tests = 0
    total_faults = 0
    total_branches = 0
    
    for row in cursor.fetchall():
        tree_id, total, tests, faults, branches = row
        print(f"{tree_id:<6} {total:<8} {tests:<6} {faults:<6} {branches:<6}")
        total_nodes += total
        total_tests += tests
        total_faults += faults
        total_branches += branches
    
    print("-" * 40)
    print(f"{'总计':<6} {total_nodes:<8} {total_tests:<6} {total_faults:<6} {total_branches:<6}")
    
    # 验证root_node_id
    print(f"\n验证root_node_id:")
    cursor.execute("""
        SELECT dt.tree_id, dt.root_node_id, dtn.node_type
        FROM diagnosis_tree dt
        LEFT JOIN diagnosis_tree_node dtn ON dt.root_node_id = dtn.node_id
        WHERE dt.tree_id BETWEEN 1 AND 10
        ORDER BY dt.tree_id
    """)
    
    for row in cursor.fetchall():
        tree_id, root_id, node_type = row
        status = "✓" if node_type == "Branch" else "✗"
        print(f"  {status} 树{tree_id}: root_node_id={root_id}, 类型={node_type}")
    
    print("\n" + "="*60)

def main():
    db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
    
    print("="*60)
    print("生成10个液压系统诊断功能")
    print("="*60)
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    try:
        # 清除旧数据
        clear_existing_data(cursor)
        
        # 创建功能定义
        create_functions(cursor)
        
        # 创建10个诊断树
        create_diagnosis_tree_1(cursor)
        create_diagnosis_tree_2(cursor)
        create_diagnosis_tree_3(cursor)
        create_diagnosis_tree_4(cursor)
        create_diagnosis_tree_5(cursor)
        create_diagnosis_tree_6(cursor)
        create_diagnosis_tree_7(cursor)
        create_diagnosis_tree_8(cursor)
        create_diagnosis_tree_9(cursor)
        create_diagnosis_tree_10(cursor)
        
        # 提交事务
        conn.commit()
        print("\n✓ 所有数据已提交到数据库")
        
        # 验证数据
        verify_data(cursor)
        
        print(f"\n✅ 完成！数据库已更新: {db_path}")
        
    except Exception as e:
        conn.rollback()
        print(f"\n❌ 错误: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    finally:
        conn.close()
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
