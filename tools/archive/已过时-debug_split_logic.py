# 【分类依据】本脚本记录了具体的调试过程、一次性修复或临时性问题解决方案。
# 这些脚本已完成其历史使命，作为问题解决过程记录保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
测试RepairInfo的分割逻辑
"""

# 测试数据
data = "故障模式名a￤0.002￤￤￤￤故障模式名c￤0.003￤￤￤￤故障模式名f￤￤￤￤￤故障模式名k￤￤￤"

print("原始数据:")
print(repr(data))
print()

# 第一步：按 ￤￤ 分割
records = data.split("￤￤")
print(f"按 '￤￤' 分割后，得到 {len(records)} 条记录:")
for i, record in enumerate(records):
    print(f"  记录{i}: {repr(record)}")
print()

# 过滤空记录
non_empty_records = [r for r in records if r.strip()]
print(f"过滤空记录后，得到 {len(non_empty_records)} 条:")
for i, record in enumerate(non_empty_records):
    print(f"  记录{i}: {repr(record)}")
print()

# 第二步：每条记录按 ￤ 分割
print("解析每条记录的字段:")
for i, record in enumerate(non_empty_records):
    fields = record.split("￤")
    print(f"  记录{i} 有 {len(fields)} 个字段:")
    for j, field in enumerate(fields):
        print(f"    字段{j}: {repr(field)}")
    
    if len(fields) >= 4:
        print(f"    ✓ 满足条件 (>= 4 个字段)")
    else:
        print(f"    ✗ 不满足条件 (只有 {len(fields)} 个字段)")
    print()
