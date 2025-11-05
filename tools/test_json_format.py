#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
测试新的JSON格式RepairInfo
"""

import json

print("=" * 70)
print("新的RepairInfo JSON格式测试")
print("=" * 70)
print()

# 测试数据（包含各种特殊字符）
test_data = [
    {
        "fault": "电机开路",
        "prob": "0.05",
        "solution": "更换电机\n检查接线\n测试运行",
        "resource": "电机×1\n万用表"
    },
    {
        "fault": "轴承|损坏",
        "prob": "0.02",
        "solution": "方案：A\\B\\C\n备选：D|E|F",
        "resource": "资源：X|Y|Z"
    },
    {
        "fault": "传感器\"失效\"",
        "prob": "0.01",
        "solution": "检查'线路'\n更换传感器",
        "resource": "传感器（型号:ABC-123）"
    },
    {
        "fault": "控制器故障",
        "prob": "",
        "solution": "",
        "resource": ""
    }
]

print("1. 测试数据:")
print("-" * 70)
for i, record in enumerate(test_data, 1):
    print(f"记录 {i}:")
    print(f"  故障模式: {repr(record['fault'])}")
    print(f"  故障概率: {repr(record['prob'])}")
    print(f"  解决方案: {repr(record['solution'])}")
    print(f"  所需资源: {repr(record['resource'])}")
    print()

print("2. JSON序列化:")
print("-" * 70)
json_compact = json.dumps(test_data, ensure_ascii=False, separators=(',', ':'))
print(f"紧凑格式（长度={len(json_compact)}）:")
print(json_compact)
print()

json_pretty = json.dumps(test_data, ensure_ascii=False, indent=2)
print("美化格式:")
print(json_pretty)
print()

print("3. JSON解析:")
print("-" * 70)
parsed_data = json.loads(json_compact)
print(f"成功解析 {len(parsed_data)} 条记录")
for i, record in enumerate(parsed_data, 1):
    print(f"记录 {i}: {record['fault']}")
print()

print("4. 数据一致性验证:")
print("-" * 70)
if test_data == parsed_data:
    print("✓ 序列化和反序列化后数据完全一致")
else:
    print("✗ 数据不一致!")
print()

print("5. 旧格式数据测试:")
print("-" * 70)
old_format_data = "故障模式名a￤0.002￤￤￤￤故障模式名c￤0.003￤￤"
print(f"旧格式数据: {repr(old_format_data)}")
try:
    json.loads(old_format_data)
    print("✗ 旧格式数据被错误解析为JSON")
except json.JSONDecodeError as e:
    print(f"✓ 旧格式数据解析失败（预期行为）: {e}")
print()

print("6. 空数据测试:")
print("-" * 70)
empty_json = "[]"
parsed_empty = json.loads(empty_json)
print(f"空数组: {empty_json}")
print(f"解析结果: {parsed_empty}")
print(f"✓ 空数据处理正常")
print()

print("=" * 70)
print("测试完成！")
print()
print("总结:")
print("- JSON格式可以完美处理换行、特殊字符、引号等")
print("- 紧凑格式节省空间")
print("- 旧格式数据会被识别为无效JSON并清空")
print("- 易于扩展（可以添加更多字段）")
print("=" * 70)
