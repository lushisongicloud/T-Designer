#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
集中油源动力系统诊断数据构建脚本

功能：为"集中油源动力系统"项目构建完整的诊断决策树数据
目标数据库：./MyProjects/集中油源动力系统/集中油源动力系统.db

系统架构：
- 油源动力系统控制柜（控制部分）
- 配电系统
- 液压泵站（液压动力部分）
- 各类传感器和执行器

Author: AI Assistant
Date: 2025-11-10
"""

import sqlite3
import sys
import os
from datetime import datetime


class OilPowerSystemDiagnosisBuilder:
    """集中油源动力系统诊断数据构建器"""
    
    def __init__(self, db_path):
        self.db_path = db_path
        self.conn = None
        self.cursor = None
        
    def connect(self):
        """连接数据库"""
        if not os.path.exists(self.db_path):
            print(f"错误：数据库文件不存在: {self.db_path}")
            return False
        
        self.conn = sqlite3.connect(self.db_path)
        self.cursor = self.conn.cursor()
        print(f"✓ 已连接到数据库: {self.db_path}")
        return True
    
    def check_tables_exist(self):
        """检查必需的表是否存在"""
        required_tables = ['diagnosis_tree', 'diagnosis_tree_node', 'Function']
        
        self.cursor.execute("SELECT name FROM sqlite_master WHERE type='table'")
        existing_tables = [row[0] for row in self.cursor.fetchall()]
        
        missing_tables = [t for t in required_tables if t not in existing_tables]
        
        if missing_tables:
            print(f"错误：缺少必需的表: {', '.join(missing_tables)}")
            print("提示：请先执行 tools/extend_diagnosis_tables.sql")
            return False
        
        print("✓ 数据库表结构检查通过")
        return True
    
    def clear_existing_data(self):
        """清除旧的诊断数据"""
        print("\n[1/5] 清除旧的诊断数据...")
        
        # 删除旧的diagnosis_tree和nodes
        self.cursor.execute("DELETE FROM diagnosis_tree_node")
        self.cursor.execute("DELETE FROM diagnosis_tree")
        self.cursor.execute("DELETE FROM Function")
        
        # 重置自增ID
        self.cursor.execute("DELETE FROM sqlite_sequence WHERE name='diagnosis_tree'")
        self.cursor.execute("DELETE FROM sqlite_sequence WHERE name='diagnosis_tree_node'")
        
        self.conn.commit()
        print("✓ 已清除旧数据")
    
    def create_functions(self):
        """创建系统功能列表"""
        print("\n[2/5] 创建系统功能...")
        
        functions = [
            {
                'FunctionID': 1,
                'FunctionName': '液压泵站启动功能',
                'ExecsList': '电源滤波器,配电系统,液压泵站电机',
                'CmdValList': '',
                'UserTest': '',
                'Remark': '检查液压泵站能否正常启动并建立压力'
            },
            {
                'FunctionID': 2,
                'FunctionName': '液压系统压力控制功能',
                'ExecsList': '压力传感器,比例调节阀,PLC控制器',
                'CmdValList': '',
                'UserTest': '',
                'Remark': '检查系统压力是否能够稳定在设定范围内'
            },
            {
                'FunctionID': 3,
                'FunctionName': '液压油质量监测功能',
                'ExecsList': '污染度传感器,水分传感器,油品传感器',
                'CmdValList': '',
                'UserTest': '',
                'Remark': '检查液压油质量是否符合要求'
            },
            {
                'FunctionID': 4,
                'FunctionName': '供油申请调度功能',
                'ExecsList': 'PLC控制器,截止阀电磁铁,流量开关',
                'CmdValList': '',
                'UserTest': '',
                'Remark': '检查能否响应收放系统的用油申请'
            },
            {
                'FunctionID': 5,
                'FunctionName': '系统保护功能',
                'ExecsList': '液位开关,过滤器报警开关,过载保护',
                'CmdValList': '',
                'UserTest': '',
                'Remark': '检查系统保护装置是否正常工作'
            }
        ]
        
        for func in functions:
            self.cursor.execute("""
                INSERT INTO Function (FunctionID, FunctionName, ExecsList, CmdValList, UserTest, Remark)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (func['FunctionID'], func['FunctionName'], func['ExecsList'], 
                  func['CmdValList'], func['UserTest'], func['Remark']))
        
        self.conn.commit()
        print(f"✓ 已创建 {len(functions)} 个系统功能")
        return functions
    
    def create_diagnosis_tree_1_pump_startup(self):
        """功能1：液压泵站启动功能 - 诊断树"""
        print("\n[3/5] 构建诊断树1：液压泵站启动功能...")
        
        # 创建诊断树
        self.cursor.execute("""
            INSERT INTO diagnosis_tree (function_id, name, description, created_time, auto_generated)
            VALUES (?, ?, ?, ?, ?)
        """, (1, '液压泵站启动功能诊断树', '检查泵站从供电到启动的完整链路', 
              datetime.now().isoformat(), 0))
        tree_id = self.cursor.lastrowid
        
        # 创建节点
        nodes = [
            # 根节点
            {
                'tree_id': tree_id,
                'parent_node_id': None,
                'node_type': 'Branch',
                'outcome': 'Unknown',
                'comment': '诊断开始'
            },
            # 测试1：检查供电
            {
                'tree_id': tree_id,
                'parent_node_id': 1,
                'node_type': 'Test',
                'outcome': 'Unknown',
                'test_description': '测试AC220V供电是否正常',
                'expected_result': '使用万用表测量控制柜输入端电压，应为AC 220V±10%',
                'test_priority': 1
            },
            # 测试1失败 -> 故障1
            {
                'tree_id': tree_id,
                'parent_node_id': 2,
                'node_type': 'Fault',
                'outcome': 'Fail',
                'fault_hypothesis': '供电系统故障：电源滤波器或配电系统异常',
                'isolation_level': 85,
                'comment': '建议：1.检查上级配电柜断路器 2.检查电源滤波器 3.检查控制柜内配电开关'
            },
            # 测试1通过 -> 分支
            {
                'tree_id': tree_id,
                'parent_node_id': 2,
                'node_type': 'Branch',
                'outcome': 'Pass',
                'comment': '供电正常，继续检查控制回路'
            },
            # 测试2：检查控制电源
            {
                'tree_id': tree_id,
                'parent_node_id': 4,
                'node_type': 'Test',
                'outcome': 'Unknown',
                'test_description': '测试控制电源输出是否正常',
                'expected_result': '测量控制电源输出端DC24V电压，应为24V±5%',
                'test_priority': 2
            },
            # 测试2失败 -> 故障2
            {
                'tree_id': tree_id,
                'parent_node_id': 5,
                'node_type': 'Fault',
                'outcome': 'Fail',
                'fault_hypothesis': '控制电源模块故障',
                'isolation_level': 90,
                'comment': '建议：更换控制电源模块'
            },
            # 测试2通过 -> 分支
            {
                'tree_id': tree_id,
                'parent_node_id': 5,
                'node_type': 'Branch',
                'outcome': 'Pass',
                'comment': '控制电源正常，继续检查PLC'
            },
            # 测试3：检查PLC工作状态
            {
                'tree_id': tree_id,
                'parent_node_id': 7,
                'node_type': 'Test',
                'outcome': 'Unknown',
                'test_description': '检查PLC1（主控）运行指示灯及通讯状态',
                'expected_result': 'PLC RUN灯常亮，COMM灯闪烁，本地操作单元能读取PLC状态',
                'test_priority': 3
            },
            # 测试3失败 -> 故障3
            {
                'tree_id': tree_id,
                'parent_node_id': 8,
                'node_type': 'Fault',
                'outcome': 'Fail',
                'fault_hypothesis': 'PLC主控器故障或程序异常',
                'isolation_level': 88,
                'comment': '建议：1.检查PLC程序 2.重启PLC 3.切换到PLC2备用控制器 4.更换PLC'
            },
            # 测试3通过 -> 分支
            {
                'tree_id': tree_id,
                'parent_node_id': 8,
                'node_type': 'Branch',
                'outcome': 'Pass',
                'comment': 'PLC正常，继续检查启动回路'
            },
            # 测试4：检查电机启动信号
            {
                'tree_id': tree_id,
                'parent_node_id': 10,
                'node_type': 'Test',
                'outcome': 'Unknown',
                'test_description': '通过本地操作单元发送泵站启动命令，检查电机启动信号输出',
                'expected_result': 'PLC输出电机启动信号，对应输出点有DC24V电压',
                'test_priority': 4
            },
            # 测试4失败 -> 故障4
            {
                'tree_id': tree_id,
                'parent_node_id': 11,
                'node_type': 'Fault',
                'outcome': 'Fail',
                'fault_hypothesis': 'PLC输出模块故障或软启动器未收到信号',
                'isolation_level': 82,
                'comment': '建议：1.检查PLC输出继电器 2.检查软启动器接线 3.检查软启完成信号反馈'
            },
            # 测试4通过 -> 分支
            {
                'tree_id': tree_id,
                'parent_node_id': 11,
                'node_type': 'Branch',
                'outcome': 'Pass',
                'comment': '启动信号正常，继续检查电机及负载'
            },
            # 测试5：检查电机运行
            {
                'tree_id': tree_id,
                'parent_node_id': 13,
                'node_type': 'Test',
                'outcome': 'Unknown',
                'test_description': '检查液压泵站电机是否启动运行',
                'expected_result': '电机正常运转，无异响，软启完成信号返回，电机过载信号未报警',
                'test_priority': 5
            },
            # 测试5失败 -> 故障5
            {
                'tree_id': tree_id,
                'parent_node_id': 14,
                'node_type': 'Fault',
                'outcome': 'Fail',
                'fault_hypothesis': '电机或液压泵机械故障',
                'isolation_level': 87,
                'comment': '建议：1.检查电机过载原因 2.检查液压泵是否卡死 3.检查联轴器 4.检查电机绕组'
            },
            # 测试5通过 -> 分支
            {
                'tree_id': tree_id,
                'parent_node_id': 14,
                'node_type': 'Branch',
                'outcome': 'Pass',
                'comment': '电机运行正常，检查压力建立'
            },
            # 测试6：检查系统压力
            {
                'tree_id': tree_id,
                'parent_node_id': 16,
                'node_type': 'Test',
                'outcome': 'Unknown',
                'test_description': '观察压力传感器读数，检查系统压力是否建立',
                'expected_result': '系统压力在30秒内上升到设定值（10-15MPa），压力传感器读数稳定',
                'test_priority': 6
            },
            # 测试6失败 -> 故障6
            {
                'tree_id': tree_id,
                'parent_node_id': 17,
                'node_type': 'Fault',
                'outcome': 'Fail',
                'fault_hypothesis': '液压系统泄漏或泵效率低',
                'isolation_level': 80,
                'comment': '建议：1.检查液压系统是否有明显泄漏 2.检查溢流阀设定 3.检查泵磨损情况 4.检查吸油滤芯'
            },
            # 测试6通过 -> 正常结论
            {
                'tree_id': tree_id,
                'parent_node_id': 17,
                'node_type': 'Fault',
                'outcome': 'Pass',
                'fault_hypothesis': '液压泵站启动功能正常，系统工作正常',
                'isolation_level': 100,
                'comment': '系统启动成功，所有检查项正常'
            }
        ]
        
        for node in nodes:
            self.cursor.execute("""
                INSERT INTO diagnosis_tree_node 
                (tree_id, parent_node_id, node_type, outcome, test_description, 
                 expected_result, fault_hypothesis, isolation_level, test_priority, comment)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (node['tree_id'], node.get('parent_node_id'), node['node_type'], 
                  node['outcome'], node.get('test_description', ''), 
                  node.get('expected_result', ''), node.get('fault_hypothesis', ''),
                  node.get('isolation_level', 0), node.get('test_priority', 0),
                  node.get('comment', '')))
        
        # 更新root_node_id
        self.cursor.execute("UPDATE diagnosis_tree SET root_node_id = 1 WHERE tree_id = ?", (tree_id,))
        self.conn.commit()
        print(f"✓ 诊断树1创建完成：{len(nodes)} 个节点")
    
    def create_diagnosis_tree_2_pressure_control(self):
        """功能2：液压系统压力控制功能 - 诊断树"""
        print("\n[4/5] 构建诊断树2：液压系统压力控制功能...")
        
        self.cursor.execute("""
            INSERT INTO diagnosis_tree (function_id, name, description, created_time, auto_generated)
            VALUES (?, ?, ?, ?, ?)
        """, (2, '压力控制功能诊断树', '检查压力传感器、比例阀及PLC控制回路', 
              datetime.now().isoformat(), 0))
        tree_id = self.cursor.lastrowid
        
        nodes = [
            # 根节点
            {'tree_id': tree_id, 'parent_node_id': None, 'node_type': 'Branch', 
             'outcome': 'Unknown', 'comment': '压力控制诊断开始'},
            # 测试1：压力传感器
            {'tree_id': tree_id, 'parent_node_id': 1, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '检查压力传感器信号是否正常',
             'expected_result': '传感器输出4-20mA信号，PLC能正确读取压力值，与机械压力表对比误差<5%',
             'test_priority': 1},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 2, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': '压力传感器故障或信号线路故障',
             'isolation_level': 90,
             'comment': '建议：1.检查传感器供电 2.检查信号线 3.更换传感器'},
            # 通过 -> 分支
            {'tree_id': tree_id, 'parent_node_id': 2, 'node_type': 'Branch', 'outcome': 'Pass'},
            # 测试2：PLC控制输出
            {'tree_id': tree_id, 'parent_node_id': 4, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '检查PLC对比例调节阀的控制输出',
             'expected_result': 'PLC模拟量输出0-10V可调，对应阀开度0-100%',
             'test_priority': 2},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 5, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': 'PLC模拟量输出模块故障',
             'isolation_level': 85,
             'comment': '建议：1.检查PLC程序 2.检查模拟量模块 3.更换输出模块'},
            # 通过 -> 分支
            {'tree_id': tree_id, 'parent_node_id': 5, 'node_type': 'Branch', 'outcome': 'Pass'},
            # 测试3：比例调节阀
            {'tree_id': tree_id, 'parent_node_id': 7, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '检查比例调节阀动作是否正常',
             'expected_result': '手动调节输出电压，阀开度相应变化，系统压力可调',
             'test_priority': 3},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 8, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': '比例调节阀机械卡滞或线圈故障',
             'isolation_level': 88,
             'comment': '建议：1.检查阀芯是否卡死 2.清洗阀体 3.检查线圈电阻 4.更换比例阀'},
            # 通过 -> 分支
            {'tree_id': tree_id, 'parent_node_id': 8, 'node_type': 'Branch', 'outcome': 'Pass'},
            # 测试4：闭环控制稳定性
            {'tree_id': tree_id, 'parent_node_id': 10, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '观察压力控制稳定性',
             'expected_result': '设定压力12MPa，实际压力波动<±0.3MPa，无振荡',
             'test_priority': 4},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 11, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': 'PLC控制参数不当或系统管路振动',
             'isolation_level': 75,
             'comment': '建议：1.调整PID参数 2.检查管路固定 3.检查蓄能器'},
            # 通过
            {'tree_id': tree_id, 'parent_node_id': 11, 'node_type': 'Fault', 'outcome': 'Pass',
             'fault_hypothesis': '压力控制功能正常',
             'isolation_level': 100,
             'comment': '系统压力控制稳定，各环节工作正常'}
        ]
        
        for node in nodes:
            self.cursor.execute("""
                INSERT INTO diagnosis_tree_node 
                (tree_id, parent_node_id, node_type, outcome, test_description, 
                 expected_result, fault_hypothesis, isolation_level, test_priority, comment)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (node['tree_id'], node.get('parent_node_id'), node['node_type'], 
                  node['outcome'], node.get('test_description', ''), 
                  node.get('expected_result', ''), node.get('fault_hypothesis', ''),
                  node.get('isolation_level', 0), node.get('test_priority', 0),
                  node.get('comment', '')))
        
        self.cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", 
                          (len(nodes) - len(nodes) + 1, tree_id))
        self.conn.commit()
        print(f"✓ 诊断树2创建完成：{len(nodes)} 个节点")
    
    def create_diagnosis_tree_3_oil_quality(self):
        """功能3：液压油质量监测功能 - 诊断树"""
        print("\n[5/5] 构建诊断树3：液压油质量监测功能...")
        
        self.cursor.execute("""
            INSERT INTO diagnosis_tree (function_id, name, description, created_time, auto_generated)
            VALUES (?, ?, ?, ?, ?)
        """, (3, '液压油质量监测诊断树', '检查油品传感器及报警功能', 
              datetime.now().isoformat(), 0))
        tree_id = self.cursor.lastrowid
        
        nodes = [
            # 根节点
            {'tree_id': tree_id, 'parent_node_id': None, 'node_type': 'Branch', 
             'outcome': 'Unknown', 'comment': '油质监测诊断开始'},
            # 测试1：污染度传感器
            {'tree_id': tree_id, 'parent_node_id': 1, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '检查污染度传感器读数',
             'expected_result': '传感器显示污染度等级，读数稳定，符合ISO 4406标准要求（≤18/16/13）',
             'test_priority': 1},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 2, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': '液压油污染度超标或传感器故障',
             'isolation_level': 75,
             'comment': '建议：1.取样化验确认污染度 2.检查滤芯状态 3.更换液压油 4.检查传感器'},
            # 通过
            {'tree_id': tree_id, 'parent_node_id': 2, 'node_type': 'Branch', 'outcome': 'Pass'},
            # 测试2：水分传感器
            {'tree_id': tree_id, 'parent_node_id': 4, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '检查液压油含水量',
             'expected_result': '水分传感器读数<200ppm（饱和度<10%），无报警',
             'test_priority': 2},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 5, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': '液压油含水量超标',
             'isolation_level': 82,
             'comment': '建议：1.检查油箱密封 2.检查冷却器是否泄漏 3.开启加热器除湿 4.更换液压油'},
            # 通过
            {'tree_id': tree_id, 'parent_node_id': 5, 'node_type': 'Branch', 'outcome': 'Pass'},
            # 测试3：油品综合检测
            {'tree_id': tree_id, 'parent_node_id': 7, 'node_type': 'Test', 'outcome': 'Unknown',
             'test_description': '检查油品传感器综合指标',
             'expected_result': '粘度指数正常，酸值<0.5mgKOH/g，无金属颗粒报警',
             'test_priority': 3},
            # 失败
            {'tree_id': tree_id, 'parent_node_id': 8, 'node_type': 'Fault', 'outcome': 'Fail',
             'fault_hypothesis': '液压油老化或系统磨损',
             'isolation_level': 70,
             'comment': '建议：1.送样进行光谱分析 2.检查泵和阀磨损 3.计划更换液压油'},
            # 通过
            {'tree_id': tree_id, 'parent_node_id': 8, 'node_type': 'Fault', 'outcome': 'Pass',
             'fault_hypothesis': '液压油质量正常，监测功能正常',
             'isolation_level': 100,
             'comment': '所有油质指标正常，传感器工作正常'}
        ]
        
        for node in nodes:
            self.cursor.execute("""
                INSERT INTO diagnosis_tree_node 
                (tree_id, parent_node_id, node_type, outcome, test_description, 
                 expected_result, fault_hypothesis, isolation_level, test_priority, comment)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """, (node['tree_id'], node.get('parent_node_id'), node['node_type'], 
                  node['outcome'], node.get('test_description', ''), 
                  node.get('expected_result', ''), node.get('fault_hypothesis', ''),
                  node.get('isolation_level', 0), node.get('test_priority', 0),
                  node.get('comment', '')))
        
        self.cursor.execute("UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?", 
                          (len(nodes) - len(nodes) + 1, tree_id))
        self.conn.commit()
        print(f"✓ 诊断树3创建完成：{len(nodes)} 个节点")
    
    def verify_data(self):
        """验证数据完整性"""
        print("\n" + "="*60)
        print("数据验证报告")
        print("="*60)
        
        # 统计Function
        self.cursor.execute("SELECT COUNT(*) FROM Function")
        func_count = self.cursor.fetchone()[0]
        print(f"\n功能数量: {func_count}")
        
        # 统计诊断树
        self.cursor.execute("SELECT COUNT(*) FROM diagnosis_tree")
        tree_count = self.cursor.fetchone()[0]
        print(f"诊断树数量: {tree_count}")
        
        # 统计节点
        self.cursor.execute("SELECT COUNT(*) FROM diagnosis_tree_node")
        node_count = self.cursor.fetchone()[0]
        print(f"诊断节点总数: {node_count}")
        
        # 按树统计节点
        print("\n各诊断树节点分布:")
        self.cursor.execute("""
            SELECT dt.tree_id, dt.name, COUNT(dtn.node_id) as node_count
            FROM diagnosis_tree dt
            LEFT JOIN diagnosis_tree_node dtn ON dt.tree_id = dtn.tree_id
            GROUP BY dt.tree_id
        """)
        for row in self.cursor.fetchall():
            print(f"  树{row[0]} - {row[1]}: {row[2]} 个节点")
        
        # 按类型统计节点
        print("\n节点类型分布:")
        self.cursor.execute("""
            SELECT node_type, COUNT(*) as count
            FROM diagnosis_tree_node
            GROUP BY node_type
        """)
        for row in self.cursor.fetchall():
            print(f"  {row[0]}: {row[1]} 个")
        
        print("\n" + "="*60)
        print("✓ 数据构建完成！")
        print("="*60)
    
    def close(self):
        """关闭数据库连接"""
        if self.conn:
            self.conn.close()
            print("\n✓ 数据库连接已关闭")
    
    def build(self):
        """执行完整构建流程"""
        print("="*60)
        print("集中油源动力系统诊断数据构建工具")
        print("="*60)
        
        if not self.connect():
            return False
        
        if not self.check_tables_exist():
            return False
        
        try:
            self.clear_existing_data()
            self.create_functions()
            self.create_diagnosis_tree_1_pump_startup()
            self.create_diagnosis_tree_2_pressure_control()
            self.create_diagnosis_tree_3_oil_quality()
            self.verify_data()
            return True
        except Exception as e:
            print(f"\n错误：构建过程中发生异常: {e}")
            import traceback
            traceback.print_exc()
            self.conn.rollback()
            return False
        finally:
            self.close()


def main():
    """主函数"""
    # 确定数据库路径
    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_dir = os.path.dirname(script_dir)
    db_path = os.path.join(project_dir, 'MyProjects', '集中油源动力系统', '集中油源动力系统.db')
    
    print(f"目标数据库: {db_path}\n")
    
    # 检查数据库文件是否存在
    if not os.path.exists(db_path):
        print(f"错误：数据库文件不存在！")
        print(f"请确认路径: {db_path}")
        print("\n提示：请先在T-Designer中创建或打开该项目")
        return 1
    
    # 确认操作
    print("警告：此操作将清除现有的诊断数据（Function、diagnosis_tree、diagnosis_tree_node表）")
    response = input("是否继续？(yes/no): ")
    if response.lower() not in ['yes', 'y']:
        print("操作已取消")
        return 0
    
    # 构建数据
    builder = OilPowerSystemDiagnosisBuilder(db_path)
    success = builder.build()
    
    if success:
        print("\n" + "="*60)
        print("构建成功！")
        print("="*60)
        print("\n下一步操作：")
        print("1. 在T-Designer中打开项目：集中油源动力系统")
        print("2. 进入"故障诊断"页面")
        print("3. 选择要诊断的功能（如：液压泵站启动功能）")
        print("4. 点击"开始诊断"按钮")
        print("5. 根据测试描述执行测试，点击"测试通过/失败"按钮")
        print("6. 系统将自动导航决策树，最终给出故障定位结果")
        print("\n推荐演示流程：")
        print("  - 功能1（液压泵站启动）：完整6步测试，展示系统启动全流程")
        print("  - 功能2（压力控制）：4步测试，展示闭环控制诊断")
        print("  - 功能3（油质监测）：3步测试，展示传感器检测")
        return 0
    else:
        print("\n构建失败，请检查错误信息")
        return 1


if __name__ == '__main__':
    sys.exit(main())
