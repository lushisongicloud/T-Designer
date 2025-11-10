#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""继续修复剩余的节点格式问题"""

import re

def main():
    file_path = r'd:\SynologyDrive\Project\T_DESIGNER\tools\generate_10_diagnosis_functions.py'
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 修复根节点格式 (parent_node_id = None)
    content = re.sub(
        r'\((\d+), tree_id, None, None, None, None, None, "Branch", "Unknown",',
        r'(\1, tree_id, None, None, None, "Unknown", None, "Branch",',
        content
    )
    
    # 修复最后一个节点 Fault+Pass格式
    content = re.sub(
        r'\((\d+), tree_id, (\d+), None, None, None, None, "Fault", "Pass",',
        r'(\1, tree_id, \2, None, None, "Pass", None, "Fault",',
        content
    )
    
    # 统计还剩多少问题
    matches = re.findall(r'\(\d+, tree_id, (?:\d+|None), None, None, None, None,', content)
    print(f"剩余问题节点: {len(matches)}个")
    
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print('✓ 修复完成')

if __name__ == '__main__':
    main()
