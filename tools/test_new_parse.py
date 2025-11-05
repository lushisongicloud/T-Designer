#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
测试新的解析方案
"""

data = "故障模式名a￤0.002￤￤￤￤故障模式名c￤0.003￤￤￤￤故障模式名f￤￤￤￤￤故障模式名k￤￤￤"

print("原始数据:")
print(repr(data))
print()

# 按￤分割所有字段
all_fields = data.split("￤")
print(f"按 '￤' 分割后，得到 {len(all_fields)} 个字段:")
for i, field in enumerate(all_fields):
    print(f"  字段{i}: {repr(field)}")
print()

# 每4个字段为一条记录
print("按每4个字段一组解析:")
records = []
for i in range(0, len(all_fields) - 3, 4):
    fault = all_fields[i].strip()
    prob = all_fields[i + 1].strip()
    sol = all_fields[i + 2].strip()
    res = all_fields[i + 3].strip()
    
    print(f"记录{len(records)}: 故障={repr(fault)}, 概率={repr(prob)}, 方案={repr(sol)}, 资源={repr(res)}")
    
    if fault:
        records.append((fault, prob, sol, res))

print(f"\n成功解析 {len(records)} 条有效记录")
