#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
生成改进版的10个液压系统诊断功能
- 平均测试长度约10步
- 器件故障与连接故障各占一半
- 少数软件配置错误
- 符合工程实践的诊断逻辑
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
        (1, "液压泵站启动功能", "KM01,KM02,YV101", "SA101.压力,KA01.状态", "液压泵站正常启动并建立压力"),
        (2, "压力控制功能", "BT101,BT102,YV102", "SA101.压力,SA102.压力", "系统压力维持在设定范围"),
        (3, "液压油质量监测功能", "SA131,SA132", "SA131.颗粒度,SA132.含水量", "液压油质量符合标准"),
        (4, "电机过载保护功能", "KM01,KA02", "SA103.电流,KA02.状态", "电机过载时自动保护"),
        (5, "油温控制功能", "SA121,KM05,YV103", "SA121.温度", "油温维持在正常范围"),
        (6, "液位监测报警功能", "SQ101,SQ102,SA110", "SA110.液位", "液位异常时及时报警"),
        (7, "泵组切换功能", "KM01,KM02,KA10", "SA101.压力,KA10.状态", "主备泵自动切换"),
        (8, "压力卸荷功能", "YV105,BT105", "SA101.压力,YV105.状态", "空载时自动卸荷节能"),
        (9, "滤芯堵塞监测功能", "SA111,SA112,SQ110", "SA111.压差,SA112.压差", "滤芯堵塞时及时更换"),
        (10, "应急停机功能", "QF01,KM01,KA15", "KM01.状态", "紧急情况快速停机")
    ]
    
    for func_id, name, execs, cmd_vals, remark in functions:
        cursor.execute("""
            INSERT INTO Function (FunctionID, FunctionName, ExecsList, CmdValList, Remark)
            VALUES (?, ?, ?, ?, ?)
        """, (func_id, name, execs, cmd_vals, remark))
    
    print(f"✓ 创建了 {len(functions)} 个功能定义")

def create_diagnosis_tree_1(cursor):
    """功能1: 液压泵站启动功能 - 约10步测试"""
    tree_id = 1
    function_id = 1
    container_id = 1
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "液压泵站启动功能诊断树", "诊断液压泵站无法启动或启动异常的故障", 1))
    
    nodes = [
        # 根节点
        (1, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第1层：电源滤波器检查
        (2, tree_id, 1, None, None, "Unknown", None, "Test", "检查电源滤波器PF01输入端AC220V电压", "使用万用表测量，电压应为AC 220V±10%", "", 0, 0.95, "电压正常", "电压异常"),
        (3, tree_id, 2, None, None, "Fail", None, "Fault", "", "", "供电系统故障：上级配电柜断路器跳闸或电源滤波器损坏", 95, 0.95, "", ""),
        (4, tree_id, 2, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第2层：控制电源检查
        (5, tree_id, 4, None, None, "Unknown", None, "Test", "测量控制电源模块输出DC24V电压", "电压应在21.6-26.4V范围", "", 0, 0.9, "电压正常", "电压异常"),
        (6, tree_id, 5, None, None, "Fail", None, "Fault", "", "", "器件故障：控制电源模块损坏", 90, 0.9, "", ""),
        (7, tree_id, 5, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第3层：PLC主控器检查
        (8, tree_id, 7, None, None, "Unknown", None, "Test", "检查PLC01主控器运行状态指示灯", "RUN灯应常亮，ERR灯应熄灭", "", 0, 0.85, "指示正常", "指示异常"),
        (9, tree_id, 8, None, None, "Fail", None, "Fault", "", "", "器件故障：PLC01主控器故障或程序丢失", 88, 0.85, "", ""),
        (10, tree_id, 8, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第4层：PLC通讯检查
        (11, tree_id, 10, None, None, "Unknown", None, "Test", "检查PLC01与本地操作单元通讯状态", "操作界面应能显示系统状态", "", 0, 0.8, "通讯正常", "通讯故障"),
        (12, tree_id, 11, None, None, "Fail", None, "Fault", "", "", "连接故障：PLC01与本地操作单元通讯线缆松动或损坏", 85, 0.8, "", ""),
        (13, tree_id, 11, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第5层：启动命令发送检查
        (14, tree_id, 13, None, None, "Unknown", None, "Test", "通过本地操作单元发送泵站启动命令，检查PLC01输出点Q0.0状态", "Q0.0应输出24V信号", "", 0, 0.75, "有输出", "无输出"),
        (15, tree_id, 14, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01程序逻辑错误或参数配置错误", 82, 0.75, "", ""),
        (16, tree_id, 14, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第6层：接触器KM01线圈检查
        (17, tree_id, 16, None, None, "Unknown", None, "Test", "测量接触器KM01线圈端电压", "应有AC220V电压", "", 0, 0.7, "有电压", "无电压"),
        (18, tree_id, 17, None, None, "Fail", None, "Fault", "", "", "连接故障：PLC01输出到KM01线圈的线路断线或继电器KA01触点故障", 80, 0.7, "", ""),
        (19, tree_id, 17, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第7层：接触器KM01吸合检查
        (20, tree_id, 19, None, None, "Unknown", None, "Test", "观察接触器KM01是否吸合", "应听到吸合声音，指示灯亮", "", 0, 0.65, "已吸合", "未吸合"),
        (21, tree_id, 20, None, None, "Fail", None, "Fault", "", "", "器件故障：接触器KM01线圈烧损或机械卡滞", 78, 0.65, "", ""),
        (22, tree_id, 20, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第8层：电机供电检查
        (23, tree_id, 22, None, None, "Unknown", None, "Test", "测量电机M1三相供电电压", "三相电压应平衡，为AC380V±10%", "", 0, 0.6, "电压正常", "电压异常"),
        (24, tree_id, 23, None, None, "Fail", None, "Fault", "", "", "连接故障：电机M1供电线路缺相或接触不良", 75, 0.6, "", ""),
        (25, tree_id, 23, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第9层：电机运行检查
        (26, tree_id, 25, None, None, "Unknown", None, "Test", "观察电机M1是否启动运转", "电机应正常运转，声音平稳", "", 0, 0.55, "运转正常", "不运转"),
        (27, tree_id, 26, None, None, "Fail", None, "Fault", "", "", "器件故障：电机M1绕组烧损或轴承卡死", 72, 0.55, "", ""),
        (28, tree_id, 26, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第10层：压力建立检查
        (29, tree_id, 28, None, None, "Unknown", None, "Test", "观察压力传感器SA101读数，10秒内压力是否上升", "压力应上升至10-12MPa", "", 0, 0.5, "压力上升", "压力不升"),
        (30, tree_id, 29, None, None, "Fail", None, "Fault", "", "", "器件故障：液压泵损坏或溢流阀YV101卡在开启位置", 70, 0.5, "", ""),
        (31, tree_id, 29, None, None, "Pass", None, "Fault", "", "", "系统正常：液压泵站启动成功，压力建立正常", 100, 1.0, "", ""),
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
    """功能2: 压力控制功能 - 约10步测试"""
    tree_id = 2
    function_id = 2
    container_id = 2
    node_id_start = 32
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "压力控制功能诊断树", "诊断系统压力无法维持或波动异常的故障", node_id_start))
    
    nodes = [
        (32, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第1层：压力传感器供电
        (33, tree_id, 32, None, None, "Unknown", None, "Test", "检查压力传感器SA101供电电压", "应为DC24V±10%", "", 0, 0.95, "电压正常", "电压异常"),
        (34, tree_id, 33, None, None, "Fail", None, "Fault", "", "", "连接故障：SA101供电线路断线或接触不良", 92, 0.95, "", ""),
        (35, tree_id, 33, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第2层：传感器读数校验
        (36, tree_id, 35, None, None, "Unknown", None, "Test", "对比SA101读数与机械压力表读数", "误差应小于±0.5MPa", "", 0, 0.9, "读数准确", "读数偏差大"),
        (37, tree_id, 36, None, None, "Fail", None, "Fault", "", "", "器件故障：压力传感器SA101精度漂移或损坏", 90, 0.9, "", ""),
        (38, tree_id, 36, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第3层：PLC模拟量输入
        (39, tree_id, 38, None, None, "Unknown", None, "Test", "检查PLC01模拟量输入通道AI0读数", "应与SA101输出电流值匹配（4-20mA）", "", 0, 0.85, "读数正常", "读数异常"),
        (40, tree_id, 39, None, None, "Fail", None, "Fault", "", "", "连接故障：SA101到PLC01的信号线屏蔽层接地不良或断线", 88, 0.85, "", ""),
        (41, tree_id, 39, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第4层：压力设定值检查
        (42, tree_id, 41, None, None, "Unknown", None, "Test", "检查PLC01中压力控制参数设定", "上限12MPa，下限10MPa，是否正确", "", 0, 0.8, "设定正确", "设定错误"),
        (43, tree_id, 42, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01压力控制参数设置错误", 95, 0.8, "", ""),
        (44, tree_id, 42, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第5层：比例阀供电检查
        (45, tree_id, 44, None, None, "Unknown", None, "Test", "检查比例阀BT101驱动模块供电", "应为DC24V", "", 0, 0.75, "供电正常", "供电异常"),
        (46, tree_id, 45, None, None, "Fail", None, "Fault", "", "", "连接故障：比例阀驱动模块供电线路断线", 85, 0.75, "", ""),
        (47, tree_id, 45, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第6层：PLC输出信号检查
        (48, tree_id, 47, None, None, "Unknown", None, "Test", "测量PLC01模拟量输出AO0电流", "应为4-20mA范围", "", 0, 0.7, "信号正常", "信号异常"),
        (49, tree_id, 48, None, None, "Fail", None, "Fault", "", "", "器件故障：PLC01模拟量输出模块损坏", 82, 0.7, "", ""),
        (50, tree_id, 48, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第7层：比例阀线圈检查
        (51, tree_id, 50, None, None, "Unknown", None, "Test", "测量比例阀BT101线圈电阻", "应为8-15Ω", "", 0, 0.65, "电阻正常", "电阻异常"),
        (52, tree_id, 51, None, None, "Fail", None, "Fault", "", "", "器件故障：比例阀BT101线圈烧损", 80, 0.65, "", ""),
        (53, tree_id, 51, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第8层：比例阀动作检查
        (54, tree_id, 53, None, None, "Unknown", None, "Test", "手动改变PLC输出值，观察压力变化", "压力应随输出值变化", "", 0, 0.6, "压力可调", "压力不变"),
        (55, tree_id, 54, None, None, "Fail", None, "Fault", "", "", "器件故障：比例阀BT101阀芯卡滞", 78, 0.6, "", ""),
        (56, tree_id, 54, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第9层：溢流阀检查
        (57, tree_id, 56, None, None, "Unknown", None, "Test", "手动调节溢流阀YV102调节旋钮", "压力应能在8-14MPa范围调节", "", 0, 0.55, "可调节", "不可调"),
        (58, tree_id, 57, None, None, "Fail", None, "Fault", "", "", "器件故障：溢流阀YV102主阀芯卡滞或弹簧失效", 75, 0.55, "", ""),
        (59, tree_id, 57, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第10层：系统稳定性测试
        (60, tree_id, 59, None, None, "Unknown", None, "Test", "观察系统空载运行10分钟，压力波动范围", "压力波动应小于±0.3MPa", "", 0, 0.5, "稳定", "波动大"),
        (61, tree_id, 60, None, None, "Fail", None, "Fault", "", "", "连接故障：液压管路连接处泄漏或空气混入系统", 72, 0.5, "", ""),
        (62, tree_id, 60, None, None, "Pass", None, "Fault", "", "", "系统正常：压力控制功能正常", 100, 1.0, "", ""),
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
    """功能3: 液压油质量监测功能 - 约10步测试"""
    tree_id = 3
    function_id = 3
    container_id = 3
    node_id_start = 63
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "液压油质量监测诊断树", "诊断油质监测异常或报警的故障", node_id_start))
    
    nodes = [
        (63, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第1层：传感器供电
        (64, tree_id, 63, None, None, "Unknown", None, "Test", "检查污染度传感器SA131供电", "应为DC24V", "", 0, 0.95, "供电正常", "供电异常"),
        (65, tree_id, 64, None, None, "Fail", None, "Fault", "", "", "连接故障：SA131供电线路断线", 92, 0.95, "", ""),
        (66, tree_id, 64, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第2层：传感器自检
        (67, tree_id, 66, None, None, "Unknown", None, "Test", "检查SA131自检指示灯状态", "绿灯常亮表示正常", "", 0, 0.9, "自检通过", "自检失败"),
        (68, tree_id, 67, None, None, "Fail", None, "Fault", "", "", "器件故障：污染度传感器SA131内部故障", 90, 0.9, "", ""),
        (69, tree_id, 67, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第3层：通讯线路检查
        (70, tree_id, 69, None, None, "Unknown", None, "Test", "检查SA131到PLC01的RS485通讯线路连接", "A、B线应正确连接且无短路", "", 0, 0.85, "连接正确", "连接异常"),
        (71, tree_id, 70, None, None, "Fail", None, "Fault", "", "", "连接故障：RS485通讯线接反或接触不良", 88, 0.85, "", ""),
        (72, tree_id, 70, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第4层：通讯参数检查
        (73, tree_id, 72, None, None, "Unknown", None, "Test", "检查PLC01中SA131通讯参数配置", "波特率9600、地址01、无校验", "", 0, 0.8, "参数正确", "参数错误"),
        (74, tree_id, 73, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01通讯参数配置错误", 95, 0.8, "", ""),
        (75, tree_id, 73, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第5层：PLC通讯测试
        (76, tree_id, 75, None, None, "Unknown", None, "Test", "通过PLC监控界面查看SA131数据更新", "数据应实时更新", "", 0, 0.75, "数据更新", "无数据"),
        (77, tree_id, 76, None, None, "Fail", None, "Fault", "", "", "连接故障：RS485终端电阻未接或通讯线屏蔽层接地不良", 85, 0.75, "", ""),
        (78, tree_id, 76, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第6层：水分传感器检查
        (79, tree_id, 78, None, None, "Unknown", None, "Test", "检查水分传感器SA132供电和通讯", "供电24V，通讯正常", "", 0, 0.7, "正常", "异常"),
        (80, tree_id, 79, None, None, "Fail", None, "Fault", "", "", "器件故障：水分传感器SA132损坏或连接故障", 82, 0.7, "", ""),
        (81, tree_id, 79, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第7层：传感器校准状态
        (82, tree_id, 81, None, None, "Unknown", None, "Test", "检查传感器上次校准日期", "应在6个月内", "", 0, 0.65, "在有效期", "已过期"),
        (83, tree_id, 82, None, None, "Fail", None, "Fault", "", "", "软件故障：传感器校准过期，读数不可靠", 90, 0.65, "", ""),
        (84, tree_id, 82, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第8层：取样对比测试
        (85, tree_id, 84, None, None, "Unknown", None, "Test", "取油样送实验室检测，对比传感器读数", "污染度等级误差≤1级", "", 0, 0.6, "读数准确", "读数偏差"),
        (86, tree_id, 85, None, None, "Fail", None, "Fault", "", "", "器件故障：传感器精度下降，需重新校准或更换", 80, 0.6, "", ""),
        (87, tree_id, 85, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第9层：报警阈值检查
        (88, tree_id, 87, None, None, "Unknown", None, "Test", "检查PLC01中油质报警阈值设置", "污染度≥NAS9级、含水量≥100ppm", "", 0, 0.55, "阈值正确", "阈值错误"),
        (89, tree_id, 88, None, None, "Fail", None, "Fault", "", "", "软件故障：报警阈值设置不当", 92, 0.55, "", ""),
        (90, tree_id, 88, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 第10层：实际油质确认
        (91, tree_id, 90, None, None, "Unknown", None, "Test", "根据实验室检测结果确认油质状态", "是否真的超标", "", 0, 0.5, "油质合格", "油质超标"),
        (92, tree_id, 91, None, None, "Fail", None, "Fault", "", "", "系统正常：传感器工作正常，油质确实超标，需更换液压油", 98, 0.5, "", ""),
        (93, tree_id, 91, None, None, "Pass", None, "Fault", "", "", "系统正常：监测功能正常，油质合格", 100, 1.0, "", ""),
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
    """功能4: 电机过载保护功能 - 约10步测试"""
    tree_id = 4
    function_id = 4
    container_id = 4
    node_id_start = 94
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "电机过载保护功能诊断树", "诊断电机过载保护不动作或误动作的故障", node_id_start))
    
    nodes = [
        (94, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        # 继续添加10步左右的测试，器件故障与连接故障各半
        (95, tree_id, 94, None, None, "Unknown", None, "Test", "检查电流传感器SA103供电电压", "应为DC24V", "", 0, 0.95, "电压正常", "电压异常"),
        (96, tree_id, 95, None, None, "Fail", None, "Fault", "", "", "连接故障：SA103供电线路断线或熔断器烧断", 92, 0.95, "", ""),
        (97, tree_id, 95, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (98, tree_id, 97, None, None, "Unknown", None, "Test", "检查SA103穿芯线缆是否正确穿过传感器", "三相线缆应全部穿过且方向一致", "", 0, 0.9, "安装正确", "安装错误"),
        (99, tree_id, 98, None, None, "Fail", None, "Fault", "", "", "连接故障：电流传感器安装位置错误或穿芯线未穿过", 90, 0.9, "", ""),
        (100, tree_id, 98, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (101, tree_id, 100, None, None, "Unknown", None, "Test", "测量SA103输出电流信号", "应为4-20mA对应0-额定电流", "", 0, 0.85, "信号正常", "信号异常"),
        (102, tree_id, 101, None, None, "Fail", None, "Fault", "", "", "器件故障：电流传感器SA103损坏", 88, 0.85, "", ""),
        (103, tree_id, 101, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (104, tree_id, 103, None, None, "Unknown", None, "Test", "检查PLC01模拟量输入AI1读数", "应与SA103输出匹配", "", 0, 0.8, "读数正常", "读数异常"),
        (105, tree_id, 104, None, None, "Fail", None, "Fault", "", "", "连接故障：SA103到PLC01信号线断线或屏蔽不良", 85, 0.8, "", ""),
        (106, tree_id, 104, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (107, tree_id, 106, None, None, "Unknown", None, "Test", "检查PLC01过载保护参数设置", "阈值应为电机额定电流的110%", "", 0, 0.75, "参数正确", "参数错误"),
        (108, tree_id, 107, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01过载保护参数设置错误", 95, 0.75, "", ""),
        (109, tree_id, 107, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (110, tree_id, 109, None, None, "Unknown", None, "Test", "检查继电器KA02线圈供电", "PLC输出点应能输出24V", "", 0, 0.7, "供电正常", "无供电"),
        (111, tree_id, 110, None, None, "Fail", None, "Fault", "", "", "器件故障：PLC01输出模块损坏", 82, 0.7, "", ""),
        (112, tree_id, 110, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (113, tree_id, 112, None, None, "Unknown", None, "Test", "模拟过载信号，检查KA02是否动作", "继电器应吸合", "", 0, 0.65, "动作正常", "不动作"),
        (114, tree_id, 113, None, None, "Fail", None, "Fault", "", "", "器件故障：继电器KA02线圈烧损或触点粘连", 80, 0.65, "", ""),
        (115, tree_id, 113, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (116, tree_id, 115, None, None, "Unknown", None, "Test", "检查KA02常闭触点串联在KM01控制回路中", "断电时触点应断开", "", 0, 0.6, "连接正确", "连接错误"),
        (117, tree_id, 116, None, None, "Fail", None, "Fault", "", "", "连接故障：保护回路接线错误", 78, 0.6, "", ""),
        (118, tree_id, 116, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (119, tree_id, 118, None, None, "Unknown", None, "Test", "过载时检查KM01是否能正常断电", "KM01应立即释放", "", 0, 0.55, "能断电", "不断电"),
        (120, tree_id, 119, None, None, "Fail", None, "Fault", "", "", "器件故障：接触器KM01主触点粘连", 75, 0.55, "", ""),
        (121, tree_id, 119, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (122, tree_id, 121, None, None, "Unknown", None, "Test", "测试实际电机运行电流", "是否确实超过额定值110%", "", 0, 0.5, "电流正常", "电流过大"),
        (123, tree_id, 122, None, None, "Fail", None, "Fault", "", "", "系统正常：电机负载过大或电机绕组故障，保护功能正确动作", 98, 0.5, "", ""),
        (124, tree_id, 122, None, None, "Pass", None, "Fault", "", "", "系统正常：过载保护功能正常", 100, 1.0, "", ""),
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
    """功能5: 油温控制功能 - 约10步测试"""
    tree_id = 5
    function_id = 5
    container_id = 5
    node_id_start = 125
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "油温控制功能诊断树", "诊断油温过高或温控系统故障", node_id_start))
    
    nodes = [
        (125, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (126, tree_id, 125, None, None, "Unknown", None, "Test", "检查温度传感器SA121供电", "应为DC24V", "", 0, 0.95, "供电正常", "供电异常"),
        (127, tree_id, 126, None, None, "Fail", None, "Fault", "", "", "连接故障：SA121供电线断线", 92, 0.95, "", ""),
        (128, tree_id, 126, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (129, tree_id, 128, None, None, "Unknown", None, "Test", "检查SA121探头是否浸入油箱", "探头应完全浸入液压油中", "", 0, 0.9, "安装正确", "安装错误"),
        (130, tree_id, 129, None, None, "Fail", None, "Fault", "", "", "连接故障：温度传感器安装位置不当", 90, 0.9, "", ""),
        (131, tree_id, 129, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (132, tree_id, 131, None, None, "Unknown", None, "Test", "对比SA121读数与温度计实测值", "误差应小于±2℃", "", 0, 0.85, "读数准确", "读数偏差"),
        (133, tree_id, 132, None, None, "Fail", None, "Fault", "", "", "器件故障：温度传感器SA121损坏", 88, 0.85, "", ""),
        (134, tree_id, 132, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (135, tree_id, 134, None, None, "Unknown", None, "Test", "检查PLC01温控参数设置", "启动55℃，停止50℃", "", 0, 0.8, "参数正确", "参数错误"),
        (136, tree_id, 135, None, None, "Fail", None, "Fault", "", "", "软件故障：温控参数设置不合理", 95, 0.8, "", ""),
        (137, tree_id, 135, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (138, tree_id, 137, None, None, "Unknown", None, "Test", "温度超55℃时检查PLC输出Q1.0", "应输出24V控制风扇", "", 0, 0.75, "有输出", "无输出"),
        (139, tree_id, 138, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01温控程序逻辑错误", 92, 0.75, "", ""),
        (140, tree_id, 138, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (141, tree_id, 140, None, None, "Unknown", None, "Test", "检查接触器KM05线圈是否得电", "应有AC220V", "", 0, 0.7, "有电压", "无电压"),
        (142, tree_id, 141, None, None, "Fail", None, "Fault", "", "", "连接故障：PLC输出到KM05的线路断线或中间继电器故障", 85, 0.7, "", ""),
        (143, tree_id, 141, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (144, tree_id, 143, None, None, "Unknown", None, "Test", "观察风扇电机是否启动", "风扇应运转", "", 0, 0.65, "运转正常", "不运转"),
        (145, tree_id, 144, None, None, "Fail", None, "Fault", "", "", "器件故障：风扇电机损坏或KM05触点烧蚀", 82, 0.65, "", ""),
        (146, tree_id, 144, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (147, tree_id, 146, None, None, "Unknown", None, "Test", "检查冷却器散热片清洁状况", "散热片应无油污堵塞", "", 0, 0.6, "清洁良好", "堵塞严重"),
        (148, tree_id, 147, None, None, "Fail", None, "Fault", "", "", "连接故障：冷却器散热片堵塞，散热效率下降", 80, 0.6, "", ""),
        (149, tree_id, 147, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (150, tree_id, 149, None, None, "Unknown", None, "Test", "检查冷却器水路是否通畅", "水流应顺畅，无气堵", "", 0, 0.55, "水路通畅", "水路堵塞"),
        (151, tree_id, 150, None, None, "Fail", None, "Fault", "", "", "连接故障：冷却水管路堵塞或水泵故障", 78, 0.55, "", ""),
        (152, tree_id, 150, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (153, tree_id, 152, None, None, "Unknown", None, "Test", "测试系统连续运行温度变化", "温度应能降至50℃以下", "", 0, 0.5, "温度下降", "温度居高"),
        (154, tree_id, 153, None, None, "Fail", None, "Fault", "", "", "器件故障：冷却器换热效率下降，需清洗或更换", 75, 0.5, "", ""),
        (155, tree_id, 153, None, None, "Pass", None, "Fault", "", "", "系统正常：温控功能正常", 100, 1.0, "", ""),
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
    """功能6: 液位监测报警功能 - 约10步测试"""
    tree_id = 6
    function_id = 6
    container_id = 6
    node_id_start = 156
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "液位监测报警诊断树", "诊断液位监测不准或报警失效的故障", node_id_start))
    
    nodes = [
        (156, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (157, tree_id, 156, None, None, "Unknown", None, "Test", "检查液位开关SQ101供电", "应为DC24V", "", 0, 0.95, "供电正常", "供电异常"),
        (158, tree_id, 157, None, None, "Fail", None, "Fault", "", "", "连接故障：SQ101供电线路断线", 92, 0.95, "", ""),
        (159, tree_id, 157, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (160, tree_id, 159, None, None, "Unknown", None, "Test", "观察SQ101浮球动作是否灵活", "浮球应随液位升降自由移动", "", 0, 0.9, "动作灵活", "卡滞"),
        (161, tree_id, 160, None, None, "Fail", None, "Fault", "", "", "器件故障：液位开关SQ101浮球卡死或机械损坏", 90, 0.9, "", ""),
        (162, tree_id, 160, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (163, tree_id, 162, None, None, "Unknown", None, "Test", "手动提拉浮球，测试触点通断", "触点应可靠通断", "", 0, 0.85, "触点正常", "触点故障"),
        (164, tree_id, 163, None, None, "Fail", None, "Fault", "", "", "器件故障：SQ101触点烧蚀或弹簧失效", 88, 0.85, "", ""),
        (165, tree_id, 163, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (166, tree_id, 165, None, None, "Unknown", None, "Test", "检查SQ101到PLC01的信号线连接", "应无断线或短路", "", 0, 0.8, "连接良好", "连接异常"),
        (167, tree_id, 166, None, None, "Fail", None, "Fault", "", "", "连接故障：信号线断线或接头松动", 85, 0.8, "", ""),
        (168, tree_id, 166, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (169, tree_id, 168, None, None, "Unknown", None, "Test", "检查PLC01输入点I1.0状态", "应随SQ101变化", "", 0, 0.75, "状态正常", "无响应"),
        (170, tree_id, 169, None, None, "Fail", None, "Fault", "", "", "器件故障：PLC01输入模块损坏", 82, 0.75, "", ""),
        (171, tree_id, 169, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (172, tree_id, 171, None, None, "Unknown", None, "Test", "检查模拟量液位传感器SA110供电", "应为DC24V", "", 0, 0.7, "供电正常", "供电异常"),
        (173, tree_id, 172, None, None, "Fail", None, "Fault", "", "", "连接故障：SA110供电线路断线", 80, 0.7, "", ""),
        (174, tree_id, 172, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (175, tree_id, 174, None, None, "Unknown", None, "Test", "对比SA110读数与油标尺实测值", "误差应小于±5mm", "", 0, 0.65, "读数准确", "读数偏差"),
        (176, tree_id, 175, None, None, "Fail", None, "Fault", "", "", "器件故障：液位传感器SA110精度漂移", 78, 0.65, "", ""),
        (177, tree_id, 175, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (178, tree_id, 177, None, None, "Unknown", None, "Test", "检查PLC01液位报警阈值设置", "低液位60%，高液位90%", "", 0, 0.6, "阈值正确", "阈值错误"),
        (179, tree_id, 178, None, None, "Fail", None, "Fault", "", "", "软件故障：报警阈值设置不合理", 95, 0.6, "", ""),
        (180, tree_id, 178, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (181, tree_id, 180, None, None, "Unknown", None, "Test", "液位异常时检查PLC报警输出Q2.0", "应输出报警信号", "", 0, 0.55, "有输出", "无输出"),
        (182, tree_id, 181, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01报警逻辑程序错误", 92, 0.55, "", ""),
        (183, tree_id, 181, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (184, tree_id, 183, None, None, "Unknown", None, "Test", "检查报警灯和蜂鸣器是否动作", "应声光报警", "", 0, 0.5, "报警正常", "无报警"),
        (185, tree_id, 184, None, None, "Fail", None, "Fault", "", "", "连接故障：报警输出线路断线或报警装置损坏", 75, 0.5, "", ""),
        (186, tree_id, 184, None, None, "Pass", None, "Fault", "", "", "系统正常：液位监测报警功能正常", 100, 1.0, "", ""),
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
    """功能7: 泵组切换功能 - 约11步测试"""
    tree_id = 7
    function_id = 7
    container_id = 7
    node_id_start = 187
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "泵组切换功能诊断树", "诊断主备泵无法切换或切换异常的故障", node_id_start))
    
    nodes = [
        (187, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (188, tree_id, 187, None, None, "Unknown", None, "Test", "检查压力传感器SA101读数是否准确", "对比机械压力表", "", 0, 0.95, "读数准确", "读数偏差"),
        (189, tree_id, 188, None, None, "Fail", None, "Fault", "", "", "器件故障：压力传感器SA101损坏或漂移", 92, 0.95, "", ""),
        (190, tree_id, 188, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (191, tree_id, 190, None, None, "Unknown", None, "Test", "检查PLC01切换条件参数设置", "主泵故障或压力低于8MPa启动备泵", "", 0, 0.9, "参数正确", "参数错误"),
        (192, tree_id, 191, None, None, "Fail", None, "Fault", "", "", "软件故障：切换逻辑参数设置错误", 95, 0.9, "", ""),
        (193, tree_id, 191, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (194, tree_id, 193, None, None, "Unknown", None, "Test", "模拟主泵KM01故障，检查PLC是否检测到", "故障信号应被识别", "", 0, 0.85, "检测到", "未检测"),
        (195, tree_id, 194, None, None, "Fail", None, "Fault", "", "", "连接故障：KM01辅助触点到PLC的反馈线断线", 88, 0.85, "", ""),
        (196, tree_id, 194, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (197, tree_id, 196, None, None, "Unknown", None, "Test", "检查切换控制继电器KA10供电", "应有DC24V控制电源", "", 0, 0.8, "供电正常", "无供电"),
        (198, tree_id, 197, None, None, "Fail", None, "Fault", "", "", "连接故障：KA10供电线路断线或熔断器烧断", 85, 0.8, "", ""),
        (199, tree_id, 197, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (200, tree_id, 199, None, None, "Unknown", None, "Test", "主泵故障时检查PLC输出Q1.2状态", "应输出切换信号", "", 0, 0.75, "有输出", "无输出"),
        (201, tree_id, 200, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01切换程序逻辑错误", 92, 0.75, "", ""),
        (202, tree_id, 200, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (203, tree_id, 202, None, None, "Unknown", None, "Test", "检查KA10线圈是否得电吸合", "继电器应动作", "", 0, 0.7, "已吸合", "未吸合"),
        (204, tree_id, 203, None, None, "Fail", None, "Fault", "", "", "器件故障：继电器KA10线圈烧损或卡滞", 82, 0.7, "", ""),
        (205, tree_id, 203, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (206, tree_id, 205, None, None, "Unknown", None, "Test", "检查KA10常开触点是否接通KM02控制回路", "触点应闭合", "", 0, 0.65, "接通", "断开"),
        (207, tree_id, 206, None, None, "Fail", None, "Fault", "", "", "器件故障：KA10触点烧蚀或接触不良", 80, 0.65, "", ""),
        (208, tree_id, 206, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (209, tree_id, 208, None, None, "Unknown", None, "Test", "检查备泵接触器KM02线圈供电", "应有AC220V", "", 0, 0.6, "有电压", "无电压"),
        (210, tree_id, 209, None, None, "Fail", None, "Fault", "", "", "连接故障：KM02控制回路接线松动或断线", 78, 0.6, "", ""),
        (211, tree_id, 209, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (212, tree_id, 211, None, None, "Unknown", None, "Test", "观察KM02是否吸合启动备泵", "KM02应吸合", "", 0, 0.55, "已吸合", "未吸合"),
        (213, tree_id, 212, None, None, "Fail", None, "Fault", "", "", "器件故障：接触器KM02线圈损坏或机械故障", 75, 0.55, "", ""),
        (214, tree_id, 212, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (215, tree_id, 214, None, None, "Unknown", None, "Test", "观察备泵电机M2是否启动运行", "电机应正常运转", "", 0, 0.5, "运转正常", "不运转"),
        (216, tree_id, 215, None, None, "Fail", None, "Fault", "", "", "器件故障：备泵电机M2损坏或供电缺相", 72, 0.5, "", ""),
        (217, tree_id, 215, None, None, "Pass", None, "Fault", "", "", "系统正常：泵组切换功能正常", 100, 1.0, "", ""),
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
    """功能8: 压力卸荷功能 - 约10步测试"""
    tree_id = 8
    function_id = 8
    container_id = 8
    node_id_start = 218
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "压力卸荷功能诊断树", "诊断空载卸荷不动作或卸荷阀故障", node_id_start))
    
    nodes = [
        (218, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (219, tree_id, 218, None, None, "Unknown", None, "Test", "检查系统是否满足卸荷条件", "无负载需求持续30秒以上", "", 0, 0.95, "满足条件", "不满足"),
        (220, tree_id, 219, None, None, "Fail", None, "Fault", "", "", "软件故障：卸荷延时参数设置过长", 95, 0.95, "", ""),
        (221, tree_id, 219, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (222, tree_id, 221, None, None, "Unknown", None, "Test", "检查PLC01卸荷逻辑是否执行", "计时器应超时", "", 0, 0.9, "逻辑正常", "逻辑异常"),
        (223, tree_id, 222, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01卸荷程序逻辑错误", 92, 0.9, "", ""),
        (224, tree_id, 222, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (225, tree_id, 224, None, None, "Unknown", None, "Test", "检查PLC输出Q2.5卸荷信号", "应输出DC24V", "", 0, 0.85, "有输出", "无输出"),
        (226, tree_id, 225, None, None, "Fail", None, "Fault", "", "", "器件故障：PLC01输出模块Q2.5损坏", 88, 0.85, "", ""),
        (227, tree_id, 225, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (228, tree_id, 227, None, None, "Unknown", None, "Test", "检查卸荷阀YV105电磁铁供电", "应有DC24V", "", 0, 0.8, "有电压", "无电压"),
        (229, tree_id, 228, None, None, "Fail", None, "Fault", "", "", "连接故障：PLC到YV105的线路断线或接头松动", 85, 0.8, "", ""),
        (230, tree_id, 228, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (231, tree_id, 230, None, None, "Unknown", None, "Test", "测量YV105电磁铁线圈电阻", "应为20-40Ω", "", 0, 0.75, "电阻正常", "电阻异常"),
        (232, tree_id, 231, None, None, "Fail", None, "Fault", "", "", "器件故障：卸荷阀YV105电磁铁线圈烧损", 82, 0.75, "", ""),
        (233, tree_id, 231, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (234, tree_id, 233, None, None, "Unknown", None, "Test", "通电时手摸YV105应感觉到振动", "电磁铁应动作", "", 0, 0.7, "有动作", "无动作"),
        (235, tree_id, 234, None, None, "Fail", None, "Fault", "", "", "器件故障：YV105电磁铁铁芯卡滞", 80, 0.7, "", ""),
        (236, tree_id, 234, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (237, tree_id, 236, None, None, "Unknown", None, "Test", "观察压力表压力是否下降", "压力应降至1MPa以下", "", 0, 0.65, "压力下降", "压力不降"),
        (238, tree_id, 237, None, None, "Fail", None, "Fault", "", "", "器件故障：卸荷阀YV105阀芯卡滞无法打开", 78, 0.65, "", ""),
        (239, tree_id, 237, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (240, tree_id, 239, None, None, "Unknown", None, "Test", "检查比例阀BT105是否同时切换到低压模式", "输出电流应降至最小", "", 0, 0.6, "已切换", "未切换"),
        (241, tree_id, 240, None, None, "Fail", None, "Fault", "", "", "软件故障：比例阀控制程序与卸荷逻辑未联动", 90, 0.6, "", ""),
        (242, tree_id, 240, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (243, tree_id, 242, None, None, "Unknown", None, "Test", "测量卸荷状态电机电流", "应下降至空载电流", "", 0, 0.55, "电流正常", "电流偏高"),
        (244, tree_id, 243, None, None, "Fail", None, "Fault", "", "", "连接故障：卸荷阀回油管路堵塞导致卸荷不彻底", 75, 0.55, "", ""),
        (245, tree_id, 243, None, None, "Pass", None, "Fault", "", "", "系统正常：压力卸荷功能正常", 100, 1.0, "", ""),
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
    """功能9: 滤芯堵塞监测功能 - 约10步测试"""
    tree_id = 9
    function_id = 9
    container_id = 9
    node_id_start = 246
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "滤芯堵塞监测诊断树", "诊断滤芯堵塞检测异常或报警失效", node_id_start))
    
    nodes = [
        (246, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (247, tree_id, 246, None, None, "Unknown", None, "Test", "检查差压传感器SA111供电", "应为DC24V", "", 0, 0.95, "供电正常", "供电异常"),
        (248, tree_id, 247, None, None, "Fail", None, "Fault", "", "", "连接故障：SA111供电线路断线或熔断器烧断", 92, 0.95, "", ""),
        (249, tree_id, 247, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (250, tree_id, 249, None, None, "Unknown", None, "Test", "检查SA111高低压测压管连接", "应分别接在滤芯前后", "", 0, 0.9, "连接正确", "连接错误"),
        (251, tree_id, 250, None, None, "Fail", None, "Fault", "", "", "连接故障：测压管接反或接头漏气", 90, 0.9, "", ""),
        (252, tree_id, 250, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (253, tree_id, 252, None, None, "Unknown", None, "Test", "检查测压管路是否畅通", "无堵塞、无气泡", "", 0, 0.85, "管路畅通", "管路堵塞"),
        (254, tree_id, 253, None, None, "Fail", None, "Fault", "", "", "连接故障：测压管路堵塞或有空气", 88, 0.85, "", ""),
        (255, tree_id, 253, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (256, tree_id, 255, None, None, "Unknown", None, "Test", "系统运行时测量SA111输出电流", "应为4-20mA对应0-1MPa差压", "", 0, 0.8, "信号正常", "信号异常"),
        (257, tree_id, 256, None, None, "Fail", None, "Fault", "", "", "器件故障：差压传感器SA111损坏", 85, 0.8, "", ""),
        (258, tree_id, 256, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (259, tree_id, 258, None, None, "Unknown", None, "Test", "检查PLC01模拟量输入AI2读数", "应与SA111输出匹配", "", 0, 0.75, "读数正常", "读数异常"),
        (260, tree_id, 259, None, None, "Fail", None, "Fault", "", "", "连接故障：SA111到PLC信号线断线或屏蔽不良", 82, 0.75, "", ""),
        (261, tree_id, 259, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (262, tree_id, 261, None, None, "Unknown", None, "Test", "检查滤芯堵塞报警阈值设置", "差压≥0.4MPa报警", "", 0, 0.7, "阈值正确", "阈值错误"),
        (263, tree_id, 262, None, None, "Fail", None, "Fault", "", "", "软件故障：报警阈值设置过高", 95, 0.7, "", ""),
        (264, tree_id, 262, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (265, tree_id, 264, None, None, "Unknown", None, "Test", "差压超标时检查PLC报警输出Q2.8", "应输出报警信号", "", 0, 0.65, "有输出", "无输出"),
        (266, tree_id, 265, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01报警程序逻辑错误", 92, 0.65, "", ""),
        (267, tree_id, 265, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (268, tree_id, 267, None, None, "Unknown", None, "Test", "检查滤芯指示器SQ110状态", "红色指示器应弹出", "", 0, 0.6, "指示正常", "无指示"),
        (269, tree_id, 268, None, None, "Fail", None, "Fault", "", "", "器件故障：机械差压指示器SQ110卡滞", 80, 0.6, "", ""),
        (270, tree_id, 268, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (271, tree_id, 270, None, None, "Unknown", None, "Test", "拆检滤芯实际状态", "确认是否真的堵塞", "", 0, 0.55, "滤芯清洁", "滤芯堵塞"),
        (272, tree_id, 271, None, None, "Fail", None, "Fault", "", "", "系统正常：监测功能正常，滤芯确实堵塞需更换", 98, 0.55, "", ""),
        (273, tree_id, 271, None, None, "Pass", None, "Fault", "", "", "系统正常：滤芯监测功能正常，滤芯状态良好", 100, 1.0, "", ""),
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
    """功能10: 应急停机功能 - 约11步测试"""
    tree_id = 10
    function_id = 10
    container_id = 10
    node_id_start = 274
    
    cursor.execute("""
        INSERT INTO diagnosis_tree (tree_id, container_id, function_id, name, description, root_node_id)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (tree_id, container_id, function_id, "应急停机功能诊断树", "诊断紧急停止功能失效或动作异常", node_id_start))
    
    nodes = [
        (274, tree_id, None, None, None, "Unknown", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (275, tree_id, 274, None, None, "Unknown", None, "Test", "检查急停按钮SQ120的NC触点状态", "正常时应闭合", "", 0, 0.95, "触点闭合", "触点断开"),
        (276, tree_id, 275, None, None, "Fail", None, "Fault", "", "", "器件故障：急停按钮SQ120自锁未复位或触点损坏", 92, 0.95, "", ""),
        (277, tree_id, 275, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (278, tree_id, 277, None, None, "Unknown", None, "Test", "按下急停按钮，测量触点状态", "NC触点应立即断开", "", 0, 0.9, "动作正常", "不动作"),
        (279, tree_id, 278, None, None, "Fail", None, "Fault", "", "", "器件故障：急停按钮SQ120机械卡滞或触点粘连", 90, 0.9, "", ""),
        (280, tree_id, 278, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (281, tree_id, 280, None, None, "Unknown", None, "Test", "检查急停回路接线", "NC触点应串联在控制回路中", "", 0, 0.85, "接线正确", "接线错误"),
        (282, tree_id, 281, None, None, "Fail", None, "Fault", "", "", "连接故障：急停回路旁路或接线错误", 95, 0.85, "", ""),
        (283, tree_id, 281, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (284, tree_id, 283, None, None, "Unknown", None, "Test", "急停时检查PLC01输入I0.0状态", "应从1变为0", "", 0, 0.8, "状态正常", "无变化"),
        (285, tree_id, 284, None, None, "Fail", None, "Fault", "", "", "连接故障：SQ120到PLC的信号线断线或短路", 88, 0.8, "", ""),
        (286, tree_id, 284, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (287, tree_id, 286, None, None, "Unknown", None, "Test", "检查PLC01急停响应程序", "应最高优先级执行", "", 0, 0.75, "优先级正确", "优先级低"),
        (288, tree_id, 287, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01急停程序优先级设置错误", 95, 0.75, "", ""),
        (289, tree_id, 287, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (290, tree_id, 289, None, None, "Unknown", None, "Test", "急停时检查所有接触器输出", "KM01/02应立即断电", "", 0, 0.7, "全部断电", "仍有输出"),
        (291, tree_id, 290, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01输出复位逻辑错误", 92, 0.7, "", ""),
        (292, tree_id, 290, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (293, tree_id, 292, None, None, "Unknown", None, "Test", "检查接触器KM01/KM02是否释放", "应听到释放声音", "", 0, 0.65, "已释放", "未释放"),
        (294, tree_id, 293, None, None, "Fail", None, "Fault", "", "", "器件故障：接触器主触点或辅助触点粘连", 85, 0.65, "", ""),
        (295, tree_id, 293, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (296, tree_id, 295, None, None, "Unknown", None, "Test", "观察电机是否停止运转", "应立即停机", "", 0, 0.6, "已停机", "仍运转"),
        (297, tree_id, 296, None, None, "Fail", None, "Fault", "", "", "器件故障：电机惯性过大或接触器主触点粘连", 82, 0.6, "", ""),
        (298, tree_id, 296, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (299, tree_id, 298, None, None, "Unknown", None, "Test", "检查断路器QF01是否可手动/自动断开", "应能可靠断开", "", 0, 0.55, "可断开", "无法断开"),
        (300, tree_id, 299, None, None, "Fail", None, "Fault", "", "", "器件故障：断路器QF01脱扣机构故障", 80, 0.55, "", ""),
        (301, tree_id, 299, None, None, "Pass", None, "Branch", "", "", "", 0, 0.5, "", ""),
        
        (302, tree_id, 301, None, None, "Unknown", None, "Test", "检查急停复位后系统能否正常启动", "复位后应能重新启动", "", 0, 0.5, "可启动", "无法启动"),
        (303, tree_id, 302, None, None, "Fail", None, "Fault", "", "", "软件故障：PLC01急停复位逻辑缺失或联锁错误", 90, 0.5, "", ""),
        (304, tree_id, 302, None, None, "Pass", None, "Fault", "", "", "系统正常：应急停机功能正常", 100, 1.0, "", ""),
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
    
    cursor.execute("SELECT COUNT(*) FROM Function WHERE FunctionID BETWEEN 1 AND 10")
    func_count = cursor.fetchone()[0]
    print(f"✓ 功能数量: {func_count}")
    
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree WHERE tree_id BETWEEN 1 AND 10")
    tree_count = cursor.fetchone()[0]
    print(f"✓ 诊断树数量: {tree_count}")
    
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
    total_tests = 0
    total_faults = 0
    for row in cursor.fetchall():
        tree_id, total, tests, faults, branches = row
        total_tests += tests
        total_faults += faults
        print(f"  树{tree_id}: {total}节点 ({tests}测试 + {faults}故障 + {branches}分支)")
    
    print(f"\n总体统计:")
    print(f"  测试节点总数: {total_tests} (平均每树: {total_tests/10:.1f})")
    print(f"  故障节点总数: {total_faults}")
    
    # 统计故障类型分布
    cursor.execute("""
        SELECT 
            SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device_faults,
            SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection_faults,
            SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' THEN 1 ELSE 0 END) as software_faults,
            COUNT(*) as total_faults
        FROM diagnosis_tree_node 
        WHERE node_type='Fault' AND tree_id BETWEEN 1 AND 10
            AND fault_hypothesis NOT LIKE '%系统正常%'
    """)
    device, connection, software, total = cursor.fetchone()
    print(f"\n故障类型分布:")
    print(f"  器件故障: {device} ({device/total*100:.1f}%)")
    print(f"  连接故障: {connection} ({connection/total*100:.1f}%)")
    print(f"  软件故障: {software} ({software/total*100:.1f}%)")

def main():
    db_path = r"D:\SynologyDrive\Project\T_DESIGNER\MyProjects\集中油源动力系统\集中油源动力系统.db"
    
    print("="*60)
    print("生成改进版10个液压系统诊断功能")
    print("="*60)
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    try:
        clear_existing_data(cursor)
        create_functions(cursor)
        
        # 创建所有10个诊断树
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
        
        conn.commit()
        print("\n✓ 所有数据已提交到数据库")
        
        verify_data(cursor)
        
        print(f"\n✅ 完成！")
        
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
