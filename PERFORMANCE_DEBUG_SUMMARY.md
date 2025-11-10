# 性能调试功能添加总结

## 已完成的工作

为了诊断项目打开缓慢的问题,已经在 T-Designer 中添加了全面的性能调试系统。

### 1. 创建的文件

#### performancetimer.h
一个轻量级的性能计时工具类,特点:
- **自动计时**: 构造时开始,析构时自动输出报告
- **检查点支持**: 可在函数执行过程中记录多个关键节点
- **附加信息**: 支持记录数据量等上下文信息
- **零侵入**: 使用 RAII 模式,无需手动管理

核心类:
- `PerformanceTimer`: 主计时器类
- `QueryPerformanceHelper`: 数据库查询性能辅助类
- 便捷宏: `PERF_TIMER()`, `PERF_CHECKPOINT()`

### 2. 修改的文件

#### mainwindow_project.cpp
在以下关键函数中添加了详细的性能跟踪:

1. **LoadProject()**
   - 数据库连接过程
   - 各子模块加载时间
   - 总耗时统计

2. **LoadProjectPages()**
   - 展开状态保存
   - ProjectStructure 层次构建
   - Page 表处理
   - 记录处理的页面数量

3. **LoadProjectUnits()**
   - Equipment 表查询
   - Symbol 子查询次数统计
   - 树节点构建时间

4. **LoadProjectTerminals()**
   - TerminalStrip 表查询
   - Terminal 子查询次数统计

5. **LoadProjectLines()**
   - LoadModelLineDT 耗时
   - LoadModelLineByUnits 耗时

#### T_DESIGNER.pro
添加了 `performancetimer.h` 到 HEADERS 列表

### 3. 创建的文档

#### PERFORMANCE_DEBUG_GUIDE.md
详细的使用指南,包含:
- 工具类使用说明
- 各函数的跟踪点列表
- 如何收集和分析性能数据
- 性能优化建议
- 完整的输出示例

## 性能问题诊断流程

### 当前可以诊断的问题

通过添加的调试信息,现在可以准确识别:

1. **数据库查询瓶颈**
   - 查询次数统计
   - 每个查询的耗时
   - N+1 查询问题

2. **树节点构建效率**
   - 节点查找时间
   - 嵌套循环开销
   - UI 更新开销

3. **数据加载顺序**
   - 哪个模块最慢
   - 各模块之间的依赖关系

### 典型性能日志输出

```
>>> [性能分析] LoadProject 开始
... [性能分析] LoadProject -> 数据库打开完成: 120 毫秒
>>> [性能分析] LoadProjectUnits 开始
... [性能分析] LoadProjectUnits -> Equipment表处理完成: 3500 毫秒 (器件数: 250, Symbol查询次数: 250)
<<< [性能分析] LoadProjectUnits 完成，总耗时: 4000 毫秒
... [性能分析] LoadProject -> LoadProjectUnits 完成: 4005 毫秒
<<< [性能分析] LoadProject 完成，总耗时: 8000 毫秒
```

从这个输出可以看出:
- **LoadProjectUnits 占用了 50% 的时间**
- **执行了 250 次独立的 Symbol 查询** (每个 Equipment 一次)
- **这是典型的 N+1 查询问题**

## 预期性能瓶颈分析

根据代码结构,预计会发现以下问题:

### 问题1: 数据库 N+1 查询

**症状:**
```
器件数: 300, Symbol查询次数: 300
端子排数: 50, Terminal查询次数: 50
```

**原因:**
```cpp
while(QueryEquipment.next()) {
    // 每个 Equipment 单独查询一次 Symbol
    SELECT * FROM Symbol WHERE Equipment_ID = ?
}
```

**影响:** 
- 300个器件 × 10ms/查询 = 3000ms
- 大型项目可能有数千个器件

**优化方案:**
```cpp
// 一次性查询所有 Symbol
SELECT * FROM Symbol WHERE Equipment_ID IN (1,2,3,...)
// 在内存中按 Equipment_ID 分组
```

### 问题2: 树节点查找效率低

**症状:**
```
ProjectStructure层次构建完成: 1200 毫秒 (处理结构数: 120)
```

**原因:**
- 嵌套循环查找父节点
- O(n²) 或 O(n³) 复杂度

**优化方案:**
```cpp
// 使用 QHash 索引
QHash<int, QStandardItem*> nodeIndex;
// O(1) 查找
QStandardItem* parent = nodeIndex.value(parentId);
```

### 问题3: UI 更新频繁

**症状:**
- 树视图频繁刷新
- 每次添加节点都触发 UI 重绘

**优化方案:**
```cpp
// 批量操作
ui->treeView->setUpdatesEnabled(false);
// ... 添加所有节点 ...
ui->treeView->setUpdatesEnabled(true);
```

## 下一步行动

### 1. 立即行动
1. **编译项目**: 确保新代码能正常编译
2. **运行测试**: 打开一个大型项目(如 `集中油源动力系统`)
3. **收集日志**: 复制完整的性能输出

### 2. 分析阶段
1. 识别最耗时的函数
2. 查看查询次数是否合理
3. 计算每个操作的平均耗时

### 3. 优化阶段
根据日志结果,按优先级实施:
- **高优先级**: 合并数据库查询 (预计节省 50-70% 时间)
- **中优先级**: 优化树节点查找算法
- **低优先级**: 延迟加载 (Lazy Loading)

## 编译和运行

### Windows (Qt Creator)

```batch
# 1. 清理旧的构建
Remove-Item -Recurse -Force build -ErrorAction SilentlyContinue

# 2. 创建构建目录
New-Item -ItemType Directory -Force build

# 3. 运行 qmake
cd build
& "D:/Qt/Qt5.12.9/5.12.9/msvc2017_64/bin/qmake.exe" ..\T_DESIGNER.pro

# 4. 编译
& "D:/Qt/Qt5.12.9/Tools/QtCreator/bin/jom.exe" -j 8

# 5. 运行
.\release\T_DESIGNER.exe
```

或者在 Qt Creator 中:
1. 打开 `T_DESIGNER.pro`
2. 按 Ctrl+B 编译
3. 按 Ctrl+R 运行
4. 查看"应用程序输出"窗口中的性能日志

### 查看调试输出

确保能看到 qDebug 输出:
- Qt Creator: "应用程序输出" 面板
- Visual Studio: "输出" 窗口
- 命令行: 输出会直接显示在控制台

## 性能基准参考

根据经验,理想的加载时间应该是:

| 项目规模 | 预期加载时间 | 当前问题 |
|---------|------------|---------|
| 小项目 (<50页) | < 1秒 | 可能 3-5秒 |
| 中项目 (50-200页) | 1-3秒 | 可能 10-30秒 |
| 大项目 (>200页) | 3-10秒 | 可能数分钟 |

如果实际时间远超预期,说明存在严重的性能问题。

## 技术细节

### 为什么使用 QElapsedTimer?

- 高精度: 毫秒级精度
- 跨平台: Windows/Linux/macOS 通用
- 单调递增: 不受系统时间调整影响

### 为什么使用 RAII 模式?

```cpp
PerformanceTimer timer("MyFunction");
// 即使函数提前返回或抛出异常
// 析构函数也会被调用,确保日志输出
```

这确保了:
- 无需手动调用 stop()
- 不会遗漏计时结束
- 代码更清晰

### 线程安全性

当前实现:
- ✅ 在单个线程中使用安全
- ⚠️ 不支持多线程并发计时
- ℹ️ 如需多线程支持,可添加 QMutex

## 常见问题

### Q: 性能计时器本身会影响性能吗?

A: 影响极小(<1ms)。QElapsedTimer 的开销非常低,checkpoint() 操作主要是记录时间和字符串拼接。

### Q: 发布版本需要移除这些代码吗?

A: 不强制要求。可以通过以下方式控制:
```cpp
#ifdef QT_DEBUG
    PerformanceTimer timer("LoadProject");
#endif
```

### Q: 如何只针对某个函数启用计时?

A: 只需注释掉或删除对应的 `PerformanceTimer` 对象创建语句。

### Q: 输出太多怎么办?

A: 可以:
1. 使用日志重定向到文件
2. 使用 `qInstallMessageHandler` 过滤输出
3. 调整 checkpoint 的粒度

## 总结

通过添加这套性能调试系统,我们现在可以:

✅ **精确定位瓶颈**: 知道哪个函数最慢  
✅ **量化性能问题**: 有具体的毫秒数  
✅ **统计数据量**: 知道处理了多少记录  
✅ **发现潜在问题**: 如 N+1 查询  
✅ **验证优化效果**: 优化前后直接对比  

这为后续的性能优化工作奠定了坚实的基础。

---

**文件清单:**
- ✅ `performancetimer.h` - 性能计时工具类
- ✅ `mainwindow_project.cpp` - 添加了性能跟踪代码
- ✅ `T_DESIGNER.pro` - 更新了头文件列表
- ✅ `PERFORMANCE_DEBUG_GUIDE.md` - 详细使用指南
- ✅ `PERFORMANCE_DEBUG_SUMMARY.md` - 本总结文档

**预计效果:**
添加这些调试信息后,打开项目时会看到详细的性能日志,能够清楚地识别出是 LoadProjectUnits、LoadProjectPages 还是其他模块导致了缓慢。
