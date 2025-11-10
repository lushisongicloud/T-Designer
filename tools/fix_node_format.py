#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""修复节点数据格式"""

import re

def main():
    file_path = r'd:\SynologyDrive\Project\T_DESIGNER\tools\generate_10_diagnosis_functions.py'
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 统计修复前的问题
    matches = re.findall(r'\(\d+, tree_id, (?:\d+|None), None, None, None, None,', content)
    print(f"发现需要修复的节点格式: {len(matches)}个")
    
    # 修复模式1: Test节点格式 - outcome在第6个位置
    content = re.sub(
        r'\((\d+), tree_id, (\d+|None), None, None, None, None, "Test", "Unknown",',
        r'(\1, tree_id, \2, None, None, "Unknown", None, "Test",',
        content
    )
    
    # 修复模式2: Fault节点格式
    content = re.sub(
        r'\((\d+), tree_id, (\d+), None, None, None, None, "Fault", "Fail",',
        r'(\1, tree_id, \2, None, None, "Fail", None, "Fault",',
        content
    )
    
    # 修复模式3: Branch节点格式(子节点)
    content = re.sub(
        r'\((\d+), tree_id, (\d+), None, None, None, None, "Branch", "Pass",',
        r'(\1, tree_id, \2, None, None, "Pass", None, "Branch",',
        content
    )
    
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print('✓ 节点格式修复完成')

if __name__ == '__main__':
    main()
