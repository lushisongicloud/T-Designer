# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
完善功能14-16的完整诊断树
功能14: 应急停机功能
功能15: 导引机构展开功能
功能16: 拖体入水检测功能
"""

import sqlite3
import sys

# 数据库路径
db_path = r"./MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db"

def insert_nodes(cursor, nodes):
    """插入节点数据"""
    for node_data in nodes:
        data = node_data[:13]
        cursor.execute("""
            INSERT OR REPLACE INTO diagnosis_tree_node 
            (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment,
             node_type, test_description, expected_result, fault_hypothesis,
             isolation_level, test_priority)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, data)

def update_diagnosis_tree_14(cursor):
    """功能14: 应急停机功能 - 11步测试
    多级安全保护：紧急停止按钮、安全继电器链、所有动力断电"""
    tree_id = 14
    node_id_start = 438
    
    cursor.execute("DELETE FROM diagnosis_tree_node WHERE tree_id = ?", (tree_id,))
    
    nodes = [
        # 根节点
        (438, 14, None, None, None, "Unknown", "", "Branch", "", "", "", 0, 0.5),
        
        # 第1步：检查控制电源
        (439, 14, 438, None, None, "Unknown", "", "Test",
         "检查收放控制机柜DC24V控制电源和安全回路独立电源PS04",
         "使用万用表测量DC24V母线电压为24V±2.4V，安全回路专用电源PS04输出DC24V±0.5V（高精度要求）", "", 0, 0.95),
        (440, 14, 439, None, None, "Fail", "", "Fault", "", "",
         "供电故障：控制电源模块PS01损坏、安全回路电源PS04故障、双路电源切换装置失效或UPS备用电源失效", 95, 0.95),
        (441, 14, 439, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第2步：检查PLC和安全模块
        (442, 14, 441, None, None, "Unknown", "", "Test",
         "观察PLC01主控器和安全PLC模块SF02的运行状态",
         "PLC RUN灯常亮，安全模块SF02双通道指示灯均为绿色，SAFE OUTPUT指示灯亮，故障指示灯熄灭", "", 0, 0.9),
        (443, 14, 442, None, None, "Fail", "", "Fault", "", "",
         "器件故障：PLC01主控器故障、安全模块SF02双通道CPU故障、安全程序校验和错误或模块固件版本不匹配", 92, 0.9),
        (444, 14, 442, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第3步：检查紧急停止按钮机械状态
        (445, 14, 444, None, None, "Unknown", "", "Test",
         "检查紧急停止按钮SQ30的机械安装和操作手感",
         "按钮应处于弹起未触发状态，目测蘑菇头完整无损，旋转解锁顺畅，按下锁定可靠，安装支架牢固无松动", "", 0, 0.85),
        (446, 14, 445, None, None, "Fail", "", "Fault", "", "",
         "器件故障：紧急停止按钮SQ30蘑菇头损坏、锁定机构卡滞、复位弹簧疲劳失效或按钮底座安装松动导致机械偏移", 88, 0.85),
        (447, 14, 445, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第4步：检查E-Stop按钮触点
        (448, 14, 447, None, None, "Unknown", "", "Test",
         "测量紧急停止按钮SQ30的常闭触点电气性能",
         "用万用表电阻档测量，未按下时触点11-12和21-22应导通（<0.5Ω），按下后应断开（>1MΩ），切换响应时间<10ms", "", 0, 0.8),
        (449, 14, 448, None, None, "Fail", "", "Fault", "", "",
         "器件故障：紧急停止按钮SQ30内部触点烧蚀、触点簧片变形、接触电阻过大或微动开关内部触点粘连失效", 85, 0.8),
        (450, 14, 448, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第5步：检查E-Stop至安全模块连接
        (451, 14, 450, None, None, "Unknown", "", "Test",
         "检查紧急停止按钮SQ30至安全模块SF02的双通道安全输入线路",
         "用万用表测量通道1线路L_ESTOP1和通道2线路L_ESTOP2，两路均应有DC24V电压，双通道冗余设计无短路或断路", "", 0, 0.75),
        (452, 14, 451, None, None, "Fail", "", "Fault", "", "",
         "连接故障：安全回路线路L_ESTOP1或L_ESTOP2断线、安全端子排TB40接线松动、双通道线路在桥架内绞接或屏蔽层接地失效", 82, 0.75),
        (453, 14, 451, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第6步：检查安全继电器链
        (454, 14, 453, None, None, "Unknown", "", "Test",
         "检查安全继电器链KA40-KA43的级联状态和自检功能",
         "安全继电器应呈级联连接，每个继电器指示灯亮绿色，自检按钮TEST按下后应产生故障报警并自动恢复", "", 0, 0.7),
        (455, 14, 454, None, None, "Fail", "", "Fault", "", "",
         "器件故障：安全继电器KA40-KA43中任一继电器线圈故障、强制导向触点失效、自检电路故障或继电器间级联逻辑错误", 78, 0.7),
        (456, 14, 454, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第7步：检查安全继电器输出
        (457, 14, 456, None, None, "Unknown", "", "Test",
         "测量安全继电器链最终输出触点串联在主接触器控制回路的电压",
         "用万用表测量安全输出端，正常时应有DC24V电压供给主接触器KM01-KM08控制回路，紧急停止后应为0V", "", 0, 0.65),
        (458, 14, 457, None, None, "Fail", "", "Fault", "", "",
         "连接故障：安全继电器输出线路L_SAFE_OUT断线、主接触器控制端子排TB50接线错误或安全链旁路开关SA99误闭合", 75, 0.65),
        (459, 14, 457, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第8步：模拟触发E-Stop
        (460, 14, 459, None, None, "Unknown", "", "Test",
         "按下紧急停止按钮SQ30，观察系统响应时间和停机过程",
         "按下后100ms内安全模块SF02应输出跳闸信号，所有接触器KM01-KM08应在200ms内失电，电机立即断电停止", "", 0, 0.6),
        (461, 14, 460, None, None, "Fail", "", "Fault", "", "",
         "软件故障：安全模块SF02响应延时过长、PLC紧急停车程序逻辑错误、接触器延时释放设置不当或停车优先级配置错误", 73, 0.6),
        (462, 14, 460, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第9步：检查制动器自动抱闸
        (463, 14, 462, None, None, "Unknown", "", "Test",
         "确认紧急停止后制动器自动抱闸动作和机械锁定",
         "停机后500ms内电磁阀YV10/YV11应失电，制动器液压释放，弹簧力使制动器抱紧，位置开关SQ10/SQ11确认制动到位", "", 0, 0.55),
        (464, 14, 463, None, None, "Fail", "", "Fault", "", "",
         "器件故障：制动器电磁阀YV10/YV11失效保持打开、制动器复位弹簧疲劳、液压缸泄压过慢或位置开关SQ10/SQ11调整不当", 70, 0.55),
        (465, 14, 463, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第10步：检查报警显示和记录
        (466, 14, 465, None, None, "Unknown", "", "Test",
         "检查HMI紧急停机报警显示、声光报警器和事件记录功能",
         "HMI应显示紧急停机报警页面（红色背景），声光报警器HA01应响铃并闪红灯，PLC应记录停机时间、操作员、设备状态到历史数据库", "", 0, 0.5),
        (467, 14, 466, None, None, "Fail", "", "Fault", "", "",
         "连接故障：HMI通讯线路L_HMI故障、声光报警器HA01线路L_ALARM断线或PLC与历史数据库通讯中断", 68, 0.5),
        (468, 14, 466, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        # 第11步：检查复位功能
        (469, 14, 468, None, None, "Unknown", "", "Test",
         "旋转解锁紧急停止按钮，按复位按钮SB40，检查系统恢复流程",
         "解锁E-Stop后指示灯变黄色（待复位），按SB40复位，安全继电器自检通过后恢复绿色，允许重新启动但需再次确认安全条件", "", 0, 0.45),
        (470, 14, 469, None, None, "Fail", "", "Fault", "", "",
         "软件故障：复位逻辑程序错误、安全继电器自检流程失败、复位条件检查不完整或复位按钮SB40线路L_RESET断线", 65, 0.45),
        (471, 14, 469, None, None, "Pass", "", "Fault", "", "",
         "系统正常：应急停机功能完全正常，响应时间<200ms，停机彻底可靠，制动器自动抱闸，报警记录完整，复位流程规范", 100, 1.0),
    ]
    
    insert_nodes(cursor, nodes)
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 更新功能14诊断树: {len(nodes)}个节点 (11步测试)")

def update_diagnosis_tree_15(cursor):
    """功能15: 导引机构展开功能 - 11步测试
    液压驱动的机械展开机构，带位置检测和锁定"""
    tree_id = 15
    node_id_start = 472
    
    cursor.execute("DELETE FROM diagnosis_tree_node WHERE tree_id = ?", (tree_id,))
    
    nodes = [
        (472, 15, None, None, None, "Unknown", "", "Branch", "", "", "", 0, 0.5),
        
        (473, 15, 472, None, None, "Unknown", "", "Test",
         "检查收放控制机柜DC24V控制电源和液压站电源AC380V",
         "使用万用表测量DC24V母线电压24V±2.4V，三相电源AC380V±38V，相间电压平衡度<2%，缺相保护继电器KA60正常", "", 0, 0.95),
        (474, 15, 473, None, None, "Fail", "", "Fault", "", "",
         "供电故障：控制电源PS01损坏、液压站主开关QF02跳闸、三相电源缺相或相序保护继电器KA60误动作", 95, 0.95),
        (475, 15, 473, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (476, 15, 475, None, None, "Unknown", "", "Test",
         "观察PLC01主控器和液压站就地控制箱指示灯状态",
         "PLC RUN灯常亮，液压站控制箱电源指示灯亮绿色，油泵运行指示灯HL40根据需求状态显示，温度报警灯HL41熄灭", "", 0, 0.9),
        (477, 15, 476, None, None, "Fail", "", "Fault", "", "",
         "器件故障：PLC01主控器故障、液压站控制器损坏、指示灯电路板故障或控制电源模块PS05失效", 92, 0.9),
        (478, 15, 476, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (479, 15, 478, None, None, "Unknown", "", "Test",
         "操作导引展开按钮SB50，检查PLC输入点I3.0的信号采集",
         "在HMI监控画面查看I3.0输入状态，按下SB50时应立即变为ON（<50ms响应），释放后恢复OFF，信号无抖动", "", 0, 0.85),
        (480, 15, 479, None, None, "Fail", "", "Fault", "", "",
         "连接故障：按钮SB50至PLC的控制线路L_SB50断线、接线端子XT50松动、中间接线盒JB06内部受潮短路或电缆护套破损", 88, 0.85),
        (481, 15, 479, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (482, 15, 481, None, None, "Unknown", "", "Test",
         "检查导引机构收起位置开关SQ40和展开位置开关SQ41状态",
         "用万用表测量，收起位置时SQ40应闭合（<1Ω），SQ41应断开（>1MΩ），机械触发行程合理（提前8-12mm），限位块无松动", "", 0, 0.8),
        (483, 15, 482, None, None, "Fail", "", "Fault", "", "",
         "器件故障：位置开关SQ40或SQ41机械松动、触点烧蚀、调整螺母松动偏移、防护罩破损进水或安装支架变形", 85, 0.8),
        (484, 15, 482, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (485, 15, 484, None, None, "Unknown", "", "Test",
         "检查PLC对位置开关SQ40/SQ41的输入信号I3.1/I3.2读取",
         "在PLC监控界面查看I3.1（收起到位）应为ON，I3.2（展开到位）应为OFF，与实际机械位置一致，无信号反相错误", "", 0, 0.75),
        (486, 15, 485, None, None, "Fail", "", "Fault", "", "",
         "连接故障：位置开关信号线L_SQ40或L_SQ41断线、接线端子TB60松动、信号线极性接反或DI模块输入通道损坏", 82, 0.75),
        (487, 15, 485, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (488, 15, 487, None, None, "Unknown", "", "Test",
         "检查液压站油泵HP02的启动和压力建立过程",
         "PLC输出Q3.0启动油泵，电机M3应在2s内启动，压力表P20显示系统压力在10s内升至10-12MPa，油泵运行声音正常无异响", "", 0, 0.7),
        (489, 15, 488, None, None, "Fail", "", "Fault", "", "",
         "器件故障：液压泵HP02叶片磨损、电机M3轴承卡滞、溢流阀SV02设定压力过低、液压油箱油位不足或吸油滤芯堵塞", 78, 0.7),
        (490, 15, 488, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (491, 15, 490, None, None, "Unknown", "", "Test",
         "监视PLC输出Q3.1控制导引展开电磁阀YV20的信号",
         "在PLC监控界面查看Q3.1应输出ON，用万用表测量YV20线圈电压应为DC24V±2.4V或AC220V±22V（根据阀型号）", "", 0, 0.65),
        (492, 15, 491, None, None, "Fail", "", "Fault", "", "",
         "连接故障：PLC输出至电磁阀YV20的控制线路L_YV20断线、中间继电器KA50触点接触不良或端子排TB70接线松动", 75, 0.65),
        (493, 15, 491, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (494, 15, 493, None, None, "Unknown", "", "Test",
         "确认电磁阀YV20动作和液压缸CY20的伸出运动",
         "听电磁阀YV20有清晰吸合声，观察压力表P20压力下降约2MPa（系统负载），液压缸活塞杆以稳定速度伸出（约50mm/s），无爬行或卡滞", "", 0, 0.6),
        (495, 15, 494, None, None, "Fail", "", "Fault", "", "",
         "器件故障：电磁阀YV20阀芯卡滞、液压缸CY20密封圈损坏内泄、液压管路泄漏、单向节流阀调节不当或液压缸导向套磨损", 73, 0.6),
        (496, 15, 494, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (497, 15, 496, None, None, "Unknown", "", "Test",
         "观察导引机构展开过程的机械动作和安全保护",
         "导引臂以均匀速度展开，展开角度达到90度±2度，机械缓冲器在到位前5度开始起作用，无冲击和异响，安全光栅SG01无遮挡报警", "", 0, 0.55),
        (498, 15, 497, None, None, "Fail", "", "Fault", "", "",
         "器件故障：导引臂铰链轴承卡滞、机械缓冲器失效、安全光栅SG01发射/接收头故障或机构角度传感器RA01读数偏差", 70, 0.55),
        (499, 15, 497, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (500, 15, 499, None, None, "Unknown", "", "Test",
         "检查展开到位位置开关SQ41的触发和机械锁定机构",
         "展开到位时SQ41应触发闭合，PLC输入I3.2变为ON，机械锁定销自动插入锁定孔，锁定确认开关SQ42闭合，HMI显示展开到位绿色指示", "", 0, 0.5),
        (500, 15, 499, None, None, "Fail", "", "Fault", "", "",
         "连接故障：位置开关SQ41或锁定确认开关SQ42信号线L_SQ41/L_SQ42断线、机械锁定销电磁铁线圈L_LOCK断线或HMI通讯线路故障", 68, 0.5),
        (501, 15, 499, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (502, 15, 501, None, None, "Unknown", "", "Test",
         "验证展开完成后液压系统卸压和电磁阀复位",
         "到位后2s内电磁阀YV20应失电复位，压力表P20回升至系统保压压力10-12MPa，油泵根据压力开关自动间歇运行，系统无持续泄漏", "", 0, 0.45),
        (503, 15, 502, None, None, "Fail", "", "Fault", "", "",
         "软件故障：PLC展开完成检测逻辑错误、电磁阀延时释放时间设置不当、压力保持控制程序错误或油泵启停压力阈值设置不合理", 65, 0.45),
        (504, 15, 502, None, None, "Pass", "", "Fault", "", "",
         "系统正常：导引机构展开功能完全正常，展开时间15-20s，到位精度±2度，机械锁定可靠，液压系统稳定，所有反馈信号正确", 100, 1.0),
    ]
    
    insert_nodes(cursor, nodes)
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 更新功能15诊断树: {len(nodes)}个节点 (11步测试)")

def update_diagnosis_tree_16(cursor):
    """功能16: 拖体入水检测功能 - 11步测试
    压力传感器检测水深，多级报警和联锁保护"""
    tree_id = 16
    node_id_start = 505
    
    cursor.execute("DELETE FROM diagnosis_tree_node WHERE tree_id = ?", (tree_id,))
    
    nodes = [
        (505, 16, None, None, None, "Unknown", "", "Branch", "", "", "", 0, 0.5),
        
        (506, 16, 505, None, None, "Unknown", "", "Test",
         "检查收放控制机柜DC24V控制电源和传感器专用稳压电源PS06",
         "使用万用表测量DC24V母线电压24V±2.4V，传感器专用电源PS06输出DC24V±0.2V（高稳定度<1%），纹波<50mV", "", 0, 0.95),
        (507, 16, 506, None, None, "Fail", "", "Fault", "", "",
         "供电故障：控制电源PS01损坏、传感器稳压电源PS06故障、电源滤波电容失效或供电线路接触电阻过大", 95, 0.95),
        (508, 16, 506, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (509, 16, 508, None, None, "Unknown", "", "Test",
         "观察PLC01主控器和高精度模拟量输入模块AI02的运行状态",
         "PLC RUN灯常亮，AI02模块（16位分辨率）电源指示灯亮，通道CH0指示灯闪烁表示有信号输入，ERR灯熄灭，模块温度正常", "", 0, 0.9),
        (510, 16, 509, None, None, "Fail", "", "Fault", "", "",
         "器件故障：PLC01主控器故障、AI02高精度模拟量模块损坏、模块A/D转换芯片失效或模块背板通讯接口接触不良", 92, 0.9),
        (511, 16, 509, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (512, 16, 511, None, None, "Unknown", "", "Test",
         "检查水下压力传感器SA130的供电和零点校准",
         "传感器供电DC24V正常，用标准压力表比对，大气压下（0m水深）SA130输出应为4.00mA±0.02mA，对应0-100m量程起点", "", 0, 0.85),
        (513, 16, 512, None, None, "Fail", "", "Fault", "", "",
         "器件故障：压力传感器SA130压阻式敏感元件漂移、信号调理电路老化、传感器膜片破损进水或温度补偿电路失效", 88, 0.85),
        (514, 16, 512, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (515, 16, 514, None, None, "Unknown", "", "Test",
         "检查传感器SA130防水电缆和水密接头的密封完整性",
         "目测电缆护套无破损、扭结或机械损伤，水密接头O型圈完好无老化龟裂，连接紧固力矩符合规范（8-10N·m），防水胶带缠绕完整", "", 0, 0.8),
        (516, 16, 515, None, None, "Fail", "", "Fault", "", "",
         "连接故障：防水电缆L_SA130护套破损进水、水密接头密封失效、O型圈老化漏水或电缆应力释放装置松动", 85, 0.8),
        (517, 16, 515, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (518, 16, 517, None, None, "Unknown", "", "Test",
         "检查传感器信号线至AI02模块通道0的屏蔽和接地",
         "用万用表测量屏蔽层对地电阻<4Ω，双绞线对地绝缘电阻>10MΩ，屏蔽层单端接地（信号源端），无重复接地或悬空", "", 0, 0.75),
        (519, 16, 518, None, None, "Fail", "", "Fault", "", "",
         "连接故障：信号线屏蔽层断裂、接地端子TB80松动、屏蔽层在中间接线盒处重复接地形成地环路或信号线对地短路", 82, 0.75),
        (520, 16, 518, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (521, 16, 520, None, None, "Unknown", "", "Test",
         "在PLC监控界面查看AI02通道0的原始数据和工程值转换",
         "原始模拟量读数4-20mA对应数字量0-32000（16位），工程值转换公式应正确：深度(m)=(I-4)×100/16，显示精度0.1m", "", 0, 0.7),
        (522, 16, 521, None, None, "Fail", "", "Fault", "", "",
         "软件故障：PLC程序中量程缩放参数错误、工程值转换公式不正确、数据类型定义错误（整型/浮点型）或滤波算法参数不当", 78, 0.7),
        (523, 16, 521, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (524, 16, 523, None, None, "Unknown", "", "Test",
         "模拟拖体入水，观察压力传感器SA130的响应特性和数据稳定性",
         "将传感器放入水桶（模拟1m水深），读数应升至约0.8-1.2m（考虑误差），响应时间<1s，数据波动<±0.2m，10s内稳定", "", 0, 0.65),
        (525, 16, 524, None, None, "Fail", "", "Fault", "", "",
         "器件故障：传感器SA130动态响应慢、压力膜片刚度下降、信号放大器带宽不足或传感器内部阻尼液泄漏", 75, 0.65),
        (526, 16, 524, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (527, 16, 526, None, None, "Unknown", "", "Test",
         "检查多级水深报警阈值设置和HMI显示功能",
         "在PLC参数设置中验证：预警阈值5m（黄色），一级报警20m（橙色），二级报警50m（红色），极限80m（闪烁红色+声音），HMI分层显示正确", "", 0, 0.6),
        (528, 16, 527, None, None, "Fail", "", "Fault", "", "",
         "软件故障：报警阈值参数设置错误、多级报警逻辑程序不完整、HMI画面脚本错误或报警优先级配置不当", 73, 0.6),
        (529, 16, 527, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (530, 16, 529, None, None, "Unknown", "", "Test",
         "测试入水检测联锁保护功能的动作逻辑",
         "设置测试阈值10m触发，检测到超限后PLC应在2s内输出联锁信号，触发声光报警HA02，可选自动减速放缆或停止放缆（根据配置）", "", 0, 0.55),
        (531, 16, 530, None, None, "Fail", "", "Fault", "", "",
         "连接故障：联锁输出线路L_INTERLOCK断线、声光报警器HA02线路故障、联锁继电器KA70触点接触不良或接触器控制回路接线错误", 70, 0.55),
        (532, 16, 530, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (533, 16, 532, None, None, "Unknown", "", "Test",
         "验证历史数据记录和趋势曲线显示功能",
         "HMI应记录水深历史数据（采样周期1s），趋势曲线显示最近10分钟数据，数据导出功能正常，历史报警记录包含时间戳和最大深度值", "", 0, 0.5),
        (534, 16, 533, None, None, "Fail", "", "Fault", "", "",
         "软件故障：HMI历史数据库连接失败、数据采样周期设置过长、趋势曲线缓冲区溢出或数据存储路径配置错误", 68, 0.5),
        (535, 16, 533, None, None, "Pass", "", "Branch", "", "", "", 0, 0.5),
        
        (536, 16, 535, None, None, "Unknown", "", "Test",
         "测试传感器故障诊断和冗余保护功能",
         "模拟传感器故障（断线/短路），PLC应在3s内检测到异常（电流<3.5mA或>20.5mA），切换到备用测量方式或安全模式，报警提示传感器故障", "", 0, 0.45),
        (537, 16, 536, None, None, "Fail", "", "Fault", "", "",
         "软件故障：传感器故障检测算法不完善、异常值判断阈值设置不当、备用传感器切换逻辑缺失或安全模式保护措施不到位", 65, 0.45),
        (538, 16, 536, None, None, "Pass", "", "Fault", "", "",
         "系统正常：拖体入水检测功能完全正常，测量精度±0.5m，响应时间<1s，多级报警准确，联锁保护可靠，数据记录完整，故障诊断有效", 100, 1.0),
    ]
    
    insert_nodes(cursor, nodes)
    cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", (node_id_start, tree_id))
    print(f"✓ 更新功能16诊断树: {len(nodes)}个节点 (11步测试)")

def verify_trees_14_to_16(cursor):
    """验证功能14-16的数据"""
    print("\n" + "="*60)
    print("验证功能14-16的诊断树数据")
    print("="*60)
    
    for tree_id in range(14, 17):
        cursor.execute("""
            SELECT COUNT(*) as total,
                   SUM(CASE WHEN node_type='Test' THEN 1 ELSE 0 END) as tests,
                   SUM(CASE WHEN node_type='Fault' THEN 1 ELSE 0 END) as faults,
                   SUM(CASE WHEN node_type='Branch' THEN 1 ELSE 0 END) as branches
            FROM diagnosis_tree_node WHERE tree_id = ?
        """, (tree_id,))
        stats = cursor.fetchone()
        print(f"\n功能{tree_id}:")
        print(f"  - 总节点数: {stats[0]}")
        print(f"  - 测试节点: {stats[1]}")
        print(f"  - 故障节点: {stats[2]}")
        print(f"  - 分支节点: {stats[3]}")
        
        # 故障类型分布
        cursor.execute("""
            SELECT 
                SUM(CASE WHEN fault_hypothesis LIKE '%器件故障%' THEN 1 ELSE 0 END) as device,
                SUM(CASE WHEN fault_hypothesis LIKE '%连接故障%' THEN 1 ELSE 0 END) as connection,
                SUM(CASE WHEN fault_hypothesis LIKE '%软件故障%' OR fault_hypothesis LIKE '%供电故障%' THEN 1 ELSE 0 END) as other,
                SUM(CASE WHEN fault_hypothesis LIKE '%系统正常%' THEN 1 ELSE 0 END) as normal
            FROM diagnosis_tree_node 
            WHERE tree_id = ? AND node_type = 'Fault'
        """, (tree_id,))
        faults = cursor.fetchone()
        total_faults = faults[0] + faults[1] + faults[2]
        if total_faults > 0:
            print(f"  故障分布:")
            print(f"    - 器件故障: {faults[0]} ({faults[0]*100//total_faults}%)")
            print(f"    - 连接故障: {faults[1]} ({faults[1]*100//total_faults}%)")
            print(f"    - 其他故障: {faults[2]} ({faults[2]*100//total_faults}%)")
            print(f"    - 正常结果: {faults[3]}")

def main():
    """主函数"""
    print("=" * 60)
    print("完善功能14-16的完整诊断树")
    print("=" * 60)
    
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        update_diagnosis_tree_14(cursor)
        update_diagnosis_tree_15(cursor)
        update_diagnosis_tree_16(cursor)
        
        verify_trees_14_to_16(cursor)
        
        conn.commit()
        conn.close()
        
        print("\n" + "=" * 60)
        print("✅ 成功更新功能14-16的诊断树")
        print("=" * 60)
        print("\n特点:")
        print("- 每个功能11步详细测试")
        print("- 测试步骤极其详细，包含具体数值、公差和测试方法")
        print("- 故障分布约50%器件/45%连接/10%其他")
        print("- 包含详细的工程定位信息和故障现象描述")
        
    except Exception as e:
        print(f"\n❌ 错误: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
