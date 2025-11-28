**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 性能调试说明

## 概述

为了诊断项目打开缓慢的问题，已在关键的加载函数中添加了详细的性能跟踪。这些调试信息将帮助我们精确定位性能瓶颈。

## 添加的性能跟踪工具

### PerformanceTimer 类

位置: `performancetimer.h`

这是一个轻量级的性能计时器类,主要功能:
- 自动记录函数开始和结束时间
- 支持在函数执行过程中记录多个检查点
- 析构时自动输出完整的性能报告
- 支持附加信息(如处理的数据量)

**使用示例:**
```cpp
void MyFunction() {
    PerformanceTimer timer("MyFunction");
    
    // 一些代码...
    timer.checkpoint("步骤1完成");
    
    // 更多代码...
    timer.checkpoint("步骤2完成", QString("处理了 %1 条记录").arg(count));
    
    // 析构时自动输出总时间和所有检查点
}
```

## 已添加性能跟踪的函数

### 1. LoadProject()
**位置:** `mainwindow_project.cpp:3601`

**跟踪点:**
- 初始化开始
- 数据库连接准备完成
- 数据库打开完成
- UI初始化完成
- LoadProjectPages 完成
- LoadProjectUnits 完成
- LoadProjectTerminals 完成
- LoadProjectLines 完成

**预期输出示例:**
```
>>> [性能分析] LoadProject 开始
... [性能分析] LoadProject -> 初始化开始: 5 毫秒
... [性能分析] LoadProject -> 数据库打开完成: 120 毫秒
... [性能分析] LoadProject -> LoadProjectPages 完成: 2500 毫秒
<<< [性能分析] LoadProject 完成，总耗时: 8000 毫秒
```

### 2. LoadProjectPages()
**位置:** `mainwindow_project.cpp:2103`

**跟踪点:**
- 展开状态保存完成 (显示展开节点数)
- 模型清空完成
- 根节点创建完成
- ProjectStructure查询开始
- ProjectStructure层次构建完成 (显示处理的结构数)
- Page表查询开始
- Page表处理完成 (显示处理的页面数)
- 树视图展开完成

**关键指标:**
- ProjectStructure 查询和处理时间
- Page 表查询和处理时间
- 树节点构建时间

### 3. LoadProjectUnits()
**位置:** `mainwindow_project.cpp:1804`

**跟踪点:**
- 展开状态保存完成
- 模型清空完成
- 根节点创建完成
- Equipment表查询开始
- Equipment表处理完成 (显示器件数和Symbol查询次数)
- LoadUnitTable 完成

**关键指标:**
- Equipment 表的记录数
- 每个 Equipment 触发的 Symbol 子查询次数
- 总查询次数 = Equipment数 × 平均Symbol数

### 4. LoadProjectTerminals()
**位置:** `mainwindow_project.cpp:1607`

**跟踪点:**
- 展开状态保存完成
- 模型清空完成
- 根节点创建完成
- TerminalStrip表查询开始
- TerminalStrip表处理完成 (显示端子排数和Terminal查询次数)

**关键指标:**
- TerminalStrip 表的记录数
- 每个 TerminalStrip 触发的 Terminal 子查询次数

### 5. LoadProjectLines()
**位置:** `mainwindow_project.cpp:1595`

**跟踪点:**
- LoadModelLineDT 完成
- LoadModelLineByUnits 完成

## 如何使用这些调试信息

### 步骤1: 启用调试输出

确保在运行程序时能看到 qDebug 输出。在 Qt Creator 中:
1. 运行程序 (Ctrl+R)
2. 查看"应用程序输出"窗口

### 步骤2: 打开一个大型项目

打开一个包含大量器件和连线的项目,例如 `MyProjects/集中油源动力系统/`

### 步骤3: 收集性能数据

程序会自动输出详细的性能日志,例如:

```
>>> [性能分析] LoadProject 开始
... [性能分析] LoadProject -> 数据库打开完成: 150 毫秒
>>> [性能分析] LoadProjectPages 开始
... [性能分析] LoadProjectPages -> 展开状态保存完成: 50 毫秒 (展开节点数: 15)
... [性能分析] LoadProjectPages -> ProjectStructure层次构建完成: 800 毫秒 (处理结构数: 120)
... [性能分析] LoadProjectPages -> Page表处理完成: 1200 毫秒 (处理页面数: 85)
<<< [性能分析] LoadProjectPages 完成，总耗时: 2150 毫秒
>>> [性能分析] LoadProjectUnits 开始
... [性能分析] LoadProjectUnits -> Equipment表处理完成: 3500 毫秒 (器件数: 250, Symbol查询次数: 250)
<<< [性能分析] LoadProjectUnits 完成，总耗时: 4000 毫秒
```

### 步骤4: 分析瓶颈

根据输出数据,找出耗时最长的部分:

**常见性能问题:**

1. **数据库查询过多 (N+1 问题)**
   - 症状: `Symbol查询次数` 等于或接近 `器件数`
   - 说明: 每个 Equipment 都单独查询一次 Symbol 表
   - 解决方案: 使用 JOIN 或一次性查询所有 Symbol

2. **树节点构建慢**
   - 症状: ProjectStructure 或 Page 表处理耗时长
   - 说明: 嵌套循环查找父节点效率低
   - 解决方案: 使用 Hash 表优化节点查找

3. **UI 更新频繁**
   - 症状: 树视图展开或模型操作耗时长
   - 解决方案: 批量更新,延迟渲染

## 性能优化建议

根据调试输出,可能的优化方向:

### 优化1: 减少数据库查询次数

**当前问题:**
```cpp
// 对每个 Equipment 执行一次查询
for each Equipment:
    SELECT * FROM Symbol WHERE Equipment_ID = ?
```

**优化方案:**
```cpp
// 一次性获取所有 Symbol
SELECT * FROM Symbol WHERE Equipment_ID IN (...)
// 或使用 JOIN
SELECT Equipment.*, Symbol.* 
FROM Equipment 
LEFT JOIN Symbol ON Equipment.Equipment_ID = Symbol.Equipment_ID
```

### 优化2: 使用索引优化树节点查找

**当前问题:**
```cpp
// 嵌套循环查找节点
for (int i = 0; i < ModelPages->item(0,0)->rowCount(); i++) {
    if (ModelPages->item(0,0)->child(i,0)->data(...) == target) {
        // 找到了
    }
}
```

**优化方案:**
```cpp
// 使用 QHash 快速查找
QHash<int, QStandardItem*> nodeCache;
QStandardItem* node = nodeCache.value(projectStructureId, nullptr);
```

### 优化3: 延迟加载 (Lazy Loading)

只加载可见的树节点,展开时再加载子节点。参考 `LAZY_LOADING_OPTIMIZATION.md` 中的方案。

## 预期结果

添加这些调试信息后,你应该能够:

1. **准确识别瓶颈**: 看到每个加载步骤的精确耗时
2. **量化问题规模**: 知道处理了多少条记录,执行了多少次查询
3. **对比优化效果**: 优化前后可以直接比较时间差异

## 后续步骤

1. 运行程序并收集性能日志
2. 将日志输出发送给开发团队或粘贴到问题报告中
3. 根据瓶颈制定优化计划
4. 实施优化后重新测试,对比改进效果

## 注意事项

- 性能计时器的开销很小(<1ms),不会显著影响程序运行
- 所有日志都通过 qDebug 输出,发布版本可以通过编译选项关闭
- 如果需要更详细的 SQL 查询日志,可以使用 `QueryPerformanceHelper::ScopedQueryLog`

## 示例:完整的性能分析输出

```
>>> [性能分析] LoadProject 开始
... [性能分析] LoadProject -> 初始化开始: 2 毫秒
... [性能分析] LoadProject -> 数据库打开完成: 135 毫秒
... [性能分析] LoadProject -> UI初始化完成: 5 毫秒

>>> [性能分析] LoadProjectPages 开始
... [性能分析] LoadProjectPages -> 展开状态保存完成: 45 毫秒 (展开节点数: 18)
... [性能分析] LoadProjectPages -> 模型清空完成: 12 毫秒
... [性能分析] LoadProjectPages -> 根节点创建完成: 3 毫秒
... [性能分析] LoadProjectPages -> ProjectStructure查询开始: 25 毫秒
... [性能分析] LoadProjectPages -> ProjectStructure层次构建完成: 850 毫秒 (处理结构数: 125)
... [性能分析] LoadProjectPages -> Page表查询开始: 15 毫秒
... [性能分析] LoadProjectPages -> Page表处理完成: 1350 毫秒 (处理页面数: 92)
... [性能分析] LoadProjectPages -> 树视图展开完成: 85 毫秒
<<< [性能分析] LoadProjectPages 完成，总耗时: 2385 毫秒

... [性能分析] LoadProject -> LoadProjectPages 完成: 2390 毫秒

>>> [性能分析] LoadProjectUnits 开始
... [性能分析] LoadProjectUnits -> 展开状态保存完成: 38 毫秒
... [性能分析] LoadProjectUnits -> 模型清空完成: 10 毫秒
... [性能分析] LoadProjectUnits -> 根节点创建完成: 2 毫秒
... [性能分析] LoadProjectUnits -> Equipment表查询开始: 12 毫秒
... [性能分析] LoadProjectUnits -> Equipment表处理完成: 4250 毫秒 (器件数: 280, Symbol查询次数: 280)
... [性能分析] LoadProjectUnits -> LoadUnitTable 完成: 320 毫秒
<<< [性能分析] LoadProjectUnits 完成，总耗时: 4632 毫秒

... [性能分析] LoadProject -> LoadProjectUnits 完成: 4635 毫秒

>>> [性能分析] LoadProjectTerminals 开始
... [性能分析] LoadProjectTerminals -> 展开状态保存完成: 25 毫秒
... [性能分析] LoadProjectTerminals -> 模型清空完成: 8 毫秒
... [性能分析] LoadProjectTerminals -> 根节点创建完成: 2 毫秒
... [性能分析] LoadProjectTerminals -> TerminalStrip表查询开始: 10 毫秒
... [性能分析] LoadProjectTerminals -> TerminalStrip表处理完成: 2100 毫秒 (端子排数: 45, Terminal查询次数: 45)
<<< [性能分析] LoadProjectTerminals 完成，总耗时: 2145 毫秒

... [性能分析] LoadProject -> LoadProjectTerminals 完成: 2148 毫秒

>>> [性能分析] LoadProjectLines 开始
... [性能分析] LoadProjectLines -> LoadModelLineDT 完成: 850 毫秒
... [性能分析] LoadProjectLines -> LoadModelLineByUnits 完成: 1200 毫秒
<<< [性能分析] LoadProjectLines 完成，总耗时: 2050 毫秒

... [性能分析] LoadProject -> LoadProjectLines 完成: 2053 毫秒

<<< [性能分析] LoadProject 完成，总耗时: 11356 毫秒
--- [性能分析] LoadProject 检查点详情:
    初始化开始: 2 毫秒 (累计: 2 毫秒)
    数据库打开完成: 135 毫秒 (累计: 137 毫秒)
    UI初始化完成: 5 毫秒 (累计: 142 毫秒)
    LoadProjectPages 完成: 2390 毫秒 (累计: 2532 毫秒)
    LoadProjectUnits 完成: 4635 毫秒 (累计: 7167 毫秒)
    LoadProjectTerminals 完成: 2148 毫秒 (累计: 9315 毫秒)
    LoadProjectLines 完成: 2053 毫秒 (累计: 11368 毫秒)
```

从这个输出可以清楚地看到:
- **LoadProjectUnits 是最大瓶颈** (4635ms, 占总时间的 40.8%)
- **原因**: 执行了 280 次 Symbol 查询 (每个 Equipment 一次)
- **优化方向**: 合并 Symbol 查询,减少数据库往返次数
