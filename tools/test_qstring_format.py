#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
模拟Qt QString的格式化行为
"""

# Python的str.format()应该和Qt的arg()行为类似
test_cases = [
    ("故障模式名a", "0.002", "", ""),
    ("故障模式名c", "0.003", "", ""),
    ("故障模式名f", "", "", ""),
    ("故障模式名k", "", "", ""),
]

print("测试QString('%1￤%2￤%3￤%4').arg()的行为:\n")

for fault, prob, sol, res in test_cases:
    # Python的格式化
    result = f"{fault}￤{prob}￤{sol}￤{res}"
    print(f"输入: fault={repr(fault)}, prob={repr(prob)}, sol={repr(sol)}, res={repr(res)}")
    print(f"输出: {repr(result)}")
    
    # 计算￤的数量
    count = result.count("￤")
    print(f"分隔符数量: {count}")
    
    # 分割测试
    fields = result.split("￤")
    print(f"分割后字段数: {len(fields)}")
    print()

print("\n" + "="*60)
print("拼接测试（使用￤￤作为记录分隔符）:\n")

records = []
for fault, prob, sol, res in test_cases:
    record = f"{fault}￤{prob}￤{sol}￤{res}"
    records.append(record)

joined = "￤￤".join(records)
print("拼接结果:")
print(repr(joined))
print()

print("分割测试:")
split_records = joined.split("￤￤")
print(f"分割后记录数: {len(split_records)}")
for i, rec in enumerate(split_records):
    print(f"  记录{i}: {repr(rec)}")
