#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
故障诊断数据迁移脚本
从旧的Function表迁移到新的diagnosis_tree和diagnosis_tree_node表结构

运行方法:
    python migrate_diagnosis_data.py <project_db_path>

例如:
    python migrate_diagnosis_data.py "d:/path/to/project.db"
"""

import sqlite3
import sys
import os
from datetime import datetime

def connect_database(db_path):
    """连接数据库"""
    if not os.path.exists(db_path):
        print(f"错误: 数据库文件不存在: {db_path}")
        return None
    
    try:
        conn = sqlite3.connect(db_path)
        conn.row_factory = sqlite3.Row
        print(f"成功连接到数据库: {db_path}")
        return conn
    except Exception as e:
        print(f"连接数据库失败: {e}")
        return None

def check_old_table_exists(conn):
    """检查旧的Function表是否存在"""
    cursor = conn.cursor()
    cursor.execute("""
        SELECT name FROM sqlite_master 
        WHERE type='table' AND name='Function'
    """)
    result = cursor.fetchone()
    return result is not None

def check_new_tables_exist(conn):
    """检查新表是否存在且包含扩展字段"""
    cursor = conn.cursor()
    
    # 检查diagnosis_tree表
    cursor.execute("PRAGMA table_info(diagnosis_tree)")
    dt_columns = {row[1] for row in cursor.fetchall()}
    required_dt_cols = {'function_id', 'root_node_id', 'created_time', 'auto_generated'}
    
    if not required_dt_cols.issubset(dt_columns):
        print(f"错误: diagnosis_tree表缺少必需字段: {required_dt_cols - dt_columns}")
        return False
    
    # 检查diagnosis_tree_node表
    cursor.execute("PRAGMA table_info(diagnosis_tree_node)")
    dtn_columns = {row[1] for row in cursor.fetchall()}
    required_dtn_cols = {'node_type', 'test_description', 'expected_result', 
                         'fault_hypothesis', 'isolation_level', 'test_priority'}
    
    if not required_dtn_cols.issubset(dtn_columns):
        print(f"错误: diagnosis_tree_node表缺少必需字段: {required_dtn_cols - dtn_columns}")
        return False
    
    print("数据库表结构验证通过")
    return True

def get_functions(conn):
    """获取所有Function记录"""
    cursor = conn.cursor()
    cursor.execute("SELECT * FROM Function")
    functions = cursor.fetchall()
    print(f"找到 {len(functions)} 个待迁移的功能记录")
    return functions

def parse_execs_list(execs_str):
    """解析执行器列表字符串"""
    if not execs_str:
        return []
    
    # 去除空格并分割
    execs = [e.strip() for e in execs_str.split(',') if e.strip()]
    return execs

def create_diagnosis_tree(conn, function):
    """为一个功能创建诊断树记录"""
    cursor = conn.cursor()
    
    func_id = function['FunctionID']
    func_name = function['FunctionName']
    remark = function['Remark'] if function['Remark'] else ''
    
    # 插入diagnosis_tree记录
    cursor.execute("""
        INSERT INTO diagnosis_tree 
        (container_id, function_id, name, description, created_time, auto_generated)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (
        1,  # 默认container_id=1 (系统级)
        func_id,
        f"诊断树-{func_name}",
        remark,
        datetime.now().isoformat(),
        1  # auto_generated=1
    ))
    
    tree_id = cursor.lastrowid
    print(f"  创建诊断树: ID={tree_id}, 功能={func_name}")
    return tree_id

def create_linear_diagnosis_tree(conn, tree_id, function):
    """创建线性诊断树结构"""
    cursor = conn.cursor()
    
    execs_list = parse_execs_list(function['ExecsList'])
    
    if not execs_list:
        print("    警告: 执行器列表为空，创建空树")
        # 创建一个根节点
        cursor.execute("""
            INSERT INTO diagnosis_tree_node
            (tree_id, node_type, test_description)
            VALUES (?, ?, ?)
        """, (tree_id, 'branch', '开始诊断'))
        root_id = cursor.lastrowid
        
        # 更新tree的root_node_id
        cursor.execute("""
            UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?
        """, (root_id, tree_id))
        
        return root_id
    
    # 创建根节点
    cursor.execute("""
        INSERT INTO diagnosis_tree_node
        (tree_id, node_type, test_description)
        VALUES (?, ?, ?)
    """, (tree_id, 'branch', '开始诊断'))
    root_id = cursor.lastrowid
    
    print(f"    创建根节点: ID={root_id}")
    
    # 创建线性测试链
    parent_id = root_id
    
    for i, exec_name in enumerate(execs_list):
        # 创建测试节点
        test_desc = f"测试 {exec_name}"
        expected_result = "正常工作"
        priority = 1.0 - (i * 0.1)  # 优先级递减
        
        cursor.execute("""
            INSERT INTO diagnosis_tree_node
            (tree_id, parent_node_id, node_type, test_description, 
             expected_result, test_priority)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (tree_id, parent_id, 'test', test_desc, expected_result, priority))
        
        test_node_id = cursor.lastrowid
        print(f"      测试节点 {i+1}: ID={test_node_id}, {test_desc}")
        
        # 创建"失败"分支 -> 故障节点
        cursor.execute("""
            INSERT INTO diagnosis_tree_node
            (tree_id, parent_node_id, node_type, outcome, 
             fault_hypothesis, isolation_level)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (tree_id, test_node_id, 'fault', 'fail', 
              f"{exec_name} 故障", 2))
        
        fault_node_id = cursor.lastrowid
        print(f"        故障节点: ID={fault_node_id}, {exec_name} 故障")
        
        # 创建"通过"分支 -> 下一个测试或结束
        if i < len(execs_list) - 1:
            # 还有更多测试，创建分支节点
            cursor.execute("""
                INSERT INTO diagnosis_tree_node
                (tree_id, parent_node_id, node_type, outcome)
                VALUES (?, ?, ?, ?)
            """, (tree_id, test_node_id, 'branch', 'pass'))
            
            parent_id = cursor.lastrowid
            print(f"        分支节点: ID={parent_id}")
        else:
            # 最后一个测试，创建"通过"故障节点（表示所有测试都通过，可能是其他原因）
            cursor.execute("""
                INSERT INTO diagnosis_tree_node
                (tree_id, parent_node_id, node_type, outcome, 
                 fault_hypothesis, isolation_level)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (tree_id, test_node_id, 'fault', 'pass', 
                  "所有测试通过，可能是其他原因导致故障", 0))
            
            other_fault_id = cursor.lastrowid
            print(f"        其他故障节点: ID={other_fault_id}")
    
    # 更新tree的root_node_id
    cursor.execute("""
        UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?
    """, (root_id, tree_id))
    
    return root_id

def migrate_function(conn, function):
    """迁移单个功能"""
    func_id = function['FunctionID']
    func_name = function['FunctionName']
    
    print(f"\n迁移功能: ID={func_id}, 名称={func_name}")
    
    # 检查是否已经迁移过
    cursor = conn.cursor()
    cursor.execute("""
        SELECT tree_id FROM diagnosis_tree WHERE function_id = ?
    """, (func_id,))
    
    if cursor.fetchone():
        print(f"  跳过: 功能 {func_name} 已存在对应的诊断树")
        return False
    
    # 创建诊断树
    tree_id = create_diagnosis_tree(conn, function)
    
    # 创建诊断树结构
    root_id = create_linear_diagnosis_tree(conn, tree_id, function)
    
    print(f"  完成: 诊断树ID={tree_id}, 根节点ID={root_id}")
    return True

def verify_migration(conn):
    """验证迁移结果"""
    cursor = conn.cursor()
    
    # 统计Function表
    cursor.execute("SELECT COUNT(*) FROM Function")
    func_count = cursor.fetchone()[0]
    
    # 统计diagnosis_tree表
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree")
    tree_count = cursor.fetchone()[0]
    
    # 统计diagnosis_tree_node表
    cursor.execute("SELECT COUNT(*) FROM diagnosis_tree_node")
    node_count = cursor.fetchone()[0]
    
    print("\n=== 迁移结果统计 ===")
    print(f"原Function记录数: {func_count}")
    print(f"新diagnosis_tree记录数: {tree_count}")
    print(f"新diagnosis_tree_node记录数: {node_count}")
    
    # 显示一些示例
    print("\n=== 示例诊断树 ===")
    cursor.execute("""
        SELECT t.tree_id, t.name, t.function_id, 
               COUNT(n.node_id) as node_count
        FROM diagnosis_tree t
        LEFT JOIN diagnosis_tree_node n ON t.tree_id = n.tree_id
        GROUP BY t.tree_id
        LIMIT 5
    """)
    
    for row in cursor.fetchall():
        print(f"树ID={row[0]}, 名称={row[1]}, 功能ID={row[2]}, 节点数={row[3]}")

def main():
    """主函数"""
    print("=" * 60)
    print("故障诊断数据迁移脚本")
    print("=" * 60)
    
    if len(sys.argv) < 2:
        print("用法: python migrate_diagnosis_data.py <database_path>")
        print("示例: python migrate_diagnosis_data.py d:/project.db")
        sys.exit(1)
    
    db_path = sys.argv[1]
    
    # 连接数据库
    conn = connect_database(db_path)
    if not conn:
        sys.exit(1)
    
    try:
        # 检查表结构
        if not check_old_table_exists(conn):
            print("错误: 找不到Function表，可能不需要迁移")
            return
        
        if not check_new_tables_exist(conn):
            print("错误: 新表结构不完整，请先运行extend_diagnosis_tables.sql")
            return
        
        # 获取所有功能
        functions = get_functions(conn)
        
        if not functions:
            print("没有需要迁移的数据")
            return
        
        # 开始迁移
        migrated_count = 0
        skipped_count = 0
        
        for function in functions:
            if migrate_function(conn, function):
                migrated_count += 1
            else:
                skipped_count += 1
        
        # 提交事务
        conn.commit()
        print(f"\n迁移完成: 成功={migrated_count}, 跳过={skipped_count}")
        
        # 验证结果
        verify_migration(conn)
        
    except Exception as e:
        print(f"\n错误: {e}")
        import traceback
        traceback.print_exc()
        conn.rollback()
        sys.exit(1)
    
    finally:
        conn.close()
        print("\n数据库连接已关闭")

if __name__ == "__main__":
    main()
