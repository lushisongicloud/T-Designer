# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
测试新的RepairInfo格式
使用换行符作为记录分隔符，竖线|作为字段分隔符
"""

def escape_field(text):
    """转义字段内容"""
    if not text:
        return ""
    # 先转义反斜杠，再转义竖线
    text = text.replace("\\", "\\\\")
    text = text.replace("|", "\\|")
    return text

def unescape_field(text):
    """反转义字段内容"""
    if not text:
        return ""
    # 先反转义竖线，再反转义反斜杠
    text = text.replace("\\|", "|")
    text = text.replace("\\\\", "\\")
    return text

def serialize(records):
    """序列化记录列表"""
    lines = []
    for fault, prob, sol, res in records:
        line = "|".join([
            escape_field(fault),
            escape_field(prob),
            escape_field(sol),
            escape_field(res)
        ])
        lines.append(line)
    return "\n".join(lines)

def parse(data):
    """解析序列化数据"""
    if not data or not data.strip():
        return []
    
    records = []
    lines = data.split("\n")
    
    for i, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
        
        # 分割字段（考虑转义）
        fields = []
        current_field = ""
        escaped = False
        
        for char in line:
            if escaped:
                current_field += char
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == "|":
                fields.append(current_field)
                current_field = ""
            else:
                current_field += char
        
        # 添加最后一个字段
        fields.append(current_field)
        
        # 验证字段数量
        if len(fields) != 4:
            print(f"警告：第{i+1}行字段数量不正确（{len(fields)}个），跳过")
            continue
        
        fault, prob, sol, res = [unescape_field(f) for f in fields]
        
        if fault:  # 故障模式不能为空
            records.append((fault, prob, sol, res))
    
    return records

# 测试数据
test_cases = [
    ("电机开路", "0.05", "更换电机", "电机×1"),
    ("轴承损坏", "0.02", "更换轴承|检查润滑", "轴承×1"),  # 包含|
    ("线路故障", "0.01", "检查\\测试连接", "万用表"),  # 包含\
    ("传感器失效", "", "", ""),  # 空字段
    ("复杂故障", "0.001", "方案：A|B\\C", "资源：X|Y\\Z"),  # 复杂情况
]

print("=" * 60)
print("测试新格式\n")

print("1. 序列化测试:")
print("-" * 60)
serialized = serialize(test_cases)
print(f"序列化结果:\n{serialized}\n")
print(f"长度: {len(serialized)} 字符\n")

print("2. 反序列化测试:")
print("-" * 60)
parsed = parse(serialized)
print(f"解析出 {len(parsed)} 条记录:\n")

for i, (fault, prob, sol, res) in enumerate(parsed):
    print(f"记录 {i+1}:")
    print(f"  故障模式: {repr(fault)}")
    print(f"  故障概率: {repr(prob)}")
    print(f"  解决方案: {repr(sol)}")
    print(f"  所需资源: {repr(res)}")
    print()

print("3. 验证一致性:")
print("-" * 60)
if len(test_cases) == len(parsed):
    all_match = True
    for i, ((f1, p1, s1, r1), (f2, p2, s2, r2)) in enumerate(zip(test_cases, parsed)):
        if (f1, p1, s1, r1) != (f2, p2, s2, r2):
            print(f"✗ 记录 {i+1} 不匹配")
            all_match = False
    if all_match:
        print("✓ 所有记录完全一致")
else:
    print(f"✗ 记录数量不一致: {len(test_cases)} vs {len(parsed)}")

print("\n4. 测试旧格式检测:")
print("-" * 60)
old_format = "故障模式名a￤0.002￤￤￤￤故障模式名c￤0.003￤￤"
parsed_old = parse(old_format)
print(f"旧格式字符串: {repr(old_format)}")
print(f"解析结果: {parsed_old}")
if not parsed_old:
    print("✓ 旧格式被正确拒绝（返回空列表）")
else:
    print("✗ 旧格式意外解析成功")

print("\n" + "=" * 60)
