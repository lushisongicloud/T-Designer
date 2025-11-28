**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 性能优化结果报告

## 优化概述

本次优化针对项目加载过程中的 N+1 查询问题进行了改进，通过引入 `ProjectDataCache` 批量数据加载机制，显著减少了数据库查询次数。

## 优化前性能数据

### 总体耗时
- **总加载时间**: 2906ms (约3秒)
- **主要瓶颈**: LoadModelLineByUnits (1150ms, 39.6%)

### 详细分解
```
[PerformanceTimer] LoadProject
  ├─ 初始化开始: 0ms
  ├─ 数据库连接准备完成: 1ms
  ├─ 数据库打开完成: 8ms
  ├─ 缓存加载完成: 3ms (新增)
  ├─ UI初始化完成: 0ms
  ├─ LoadProjectPages 完成: 10ms
  ├─ LoadProjectUnits 完成: 1194ms (41.1%)
  ├─ LoadProjectTerminals 完成: 3ms
  └─ LoadProjectLines 完成: 1686ms (58.0%)
      ├─ LoadModelLineDT: 437ms (15.0%)
      └─ LoadModelLineByUnits: 1150ms (39.6%)
```

### 数据库查询分析
- **LoadModelLineByUnits**: 960个连接 × ~6次查询 = ~5,760次查询
  - GetUnitTermimalGaocengAndPos 被调用960次
  - 每次调用执行约6条SQL查询
- **LoadModelLineDT**: 960个连接 × 1次Structure查询 = ~960次查询
- **LoadProjectUnits**: ~1,939次查询
- **总计**: 约 8,659 次数据库查询

## 优化方案

### 核心思路
将多次重复的小查询改为一次批量加载 + 内存缓存查找。

### 实现细节

#### 1. ProjectDataCache 类
```cpp
class ProjectDataCache {
public:
    bool loadAll(QSqlDatabase &db);
    bool getEquipmentLocation(int equipmentId, int &structureId, QString &structInt);
    bool getSymbolLocation(int symbolId, int &equipmentId, int &structureId, QString &structInt);
    QList<TermInfo> getTermInfos(int symbolId);
    QString getStatistics() const;
    
private:
    QHash<int, StructureInfo> m_structures;      // key: ProjectStructure_ID
    QHash<int, EquipmentInfo> m_equipments;      // key: Equipment_ID
    QHash<int, SymbolInfo> m_symbols;            // key: Symbol_ID
    QHash<int, QList<TermInfo>> m_termInfos;     // key: Symbol_ID
};
```

#### 2. 批量加载SQL
```sql
-- 一次性加载所有结构信息
SELECT ProjectStructure_ID, Structure_INT, Parent_ID FROM ProjectStructure

-- 一次性加载所有设备信息
SELECT Equipment_ID, DT, ProjectStructure_ID FROM Equipment

-- 一次性加载所有符号信息
SELECT Symbol_ID, Equipment_ID FROM Symbol

-- 一次性加载所有端子映射信息
SELECT Symbol_ID, ConnNum FROM Symb2TermInfo
```

#### 3. 缓存查询函数
```cpp
// 原函数: GetUnitTermimalGaocengAndPos (每次调用执行~6条SQL)
// 新函数: GetUnitTermimalGaocengAndPos_Cached (使用QHash O(1)查找)
```

## 优化后性能数据 (2025-11-12)

### 架构变更：Model/View 迁移

**主要变更**:
1. **EquipmentTreeModel**: 替代 QStandardItemModel，直接从 ProjectDataModel 获取数据
2. **ConnectionTreeModel**: 替代 QStandardItemModel，支持两种视图模式
3. **EquipmentTableModel**: 替代 QTableWidget，继承自 QAbstractTableModel
4. **ProjectDataModel**: 内存缓存层，提供 O(1) 数据访问

**性能监控**:
- ✅ LoadProjectUnits: 使用 PerformanceTimer 监控，目标 <1s
- ✅ LoadProjectLines: 使用 PerformanceTimer 监控，目标 <1s
- ✅ LoadProjectTerminals: 使用 PerformanceTimer 监控
- ✅ LoadProjectPages: 使用 PerformanceTimer 监控

**关键改进**:
```
// 原有架构: UI控件 ← QStandardItemModel ← 数据库查询 (N+1问题)
// 新架构: UI控件 ← QAbstractItemModel ← ProjectDataModel ← 内存缓存
```

**内存模型统计** (基于 ProjectDataModel):
- Structures: 高层/位置层次结构
- Equipments: 设备实例数据
- Symbols: 功能块数据
- Connections: 连线信息
- Pages: 图纸页面数据
- 所有数据预加载到内存，避免运行期查询

**过滤器实现**:
```cpp
// FilterUnit() 已适配新架构
void MainWindow::FilterUnit() {
    // 从UI控件读取过滤条件
    const QString gaocengFilter = ui->CbUnitGaoceng->currentText();
    const QString posFilter = ui->CbUnitPos->currentText();
    const QString keyword = ui->EdUnitTagSearch->text();

    // 应用到 EquipmentTreeModel
    m_equipmentTreeModel->applyFilter(...);
}
```
void GetUnitTermimalGaocengAndPos_Cached(
    ProjectDataCache* cache,
    int Category, int Symb_ID,
    QString &StrGaoceng, QString &StrPos
);
```

#### 4. 集成到 MainWindow
- 在 `LoadProject()` 中初始化缓存 (耗时3ms)
- 在 `LoadModelLineByUnits()` 中使用缓存查询
- 保留原有函数,通过 `m_useCacheOptimization` 开关控制

## 优化后预期效果

### 查询次数对比
| 函数 | 优化前查询次数 | 优化后查询次数 | 减少量 |
|------|---------------|---------------|--------|
| LoadModelLineByUnits | ~5,760 | 4 (批量加载) | -5,756 (99.9%) |
| 缓存初始化 | 0 | 4 | +4 |
| **总计** | ~8,659 | ~2,907 | **-5,752 (66.4%)** |

### 耗时预测
- **缓存加载**: 3ms (实测)
- **LoadModelLineByUnits**: 预计从 1150ms 降至 100-200ms
  - 数据库查询耗时: 1100ms → 0ms (使用缓存)
  - 数据处理耗时: 50ms (保持不变)
- **总加载时间**: 预计从 2906ms 降至 ~1000-1200ms

### 性能提升
- **查询减少**: 66.4% (5,752条查询)
- **LoadModelLineByUnits提速**: 约 85-90%
- **总体提速**: 预计 50-60%

## 下一步优化方向

根据当前性能分析,还有两个优化点:

### 1. LoadModelLineDT (437ms)
```cpp
// 当前: 每个连接查询一次Structure表
QSqlQuery QueryStructure(T_ProjectDatabase);
QueryStructure.exec(QString("select * from ProjectStructure where ProjectStructure_ID='%1'").arg(...));

// 优化: 使用缓存的getStructureById()
```

### 2. LoadProjectUnits 隐藏开销 (1194ms)
```cpp
// 怀疑 GetUnitSpurStrBySymbol_ID() 内部有大量查询
// 需要进一步分析该函数的查询模式
```

## 实施步骤

- [x] 创建 PerformanceTimer 类
- [x] 添加性能检测点,识别瓶颈
- [x] 设计 ProjectDataCache 类
- [x] 实现批量数据加载
- [x] 修复SQL列名错误
- [x] 实现缓存查询函数
- [x] 集成到 MainWindow 类
- [x] 编译通过
- [ ] 实际测试验证性能提升
- [ ] 优化 LoadModelLineDT
- [ ] 优化 LoadProjectUnits
- [ ] 最终性能对比报告

## 注意事项

### 安全措施
1. **功能开关**: 通过 `m_useCacheOptimization` 控制,可随时回退
2. **环境变量**: 设置 `T_DESIGNER_DISABLE_CACHE=1` 可禁用缓存
3. **保留原函数**: 所有原有函数保持不变,仅添加新的Cached版本
4. **渐进式改进**: 每次只优化一个函数,逐步验证

### 测试建议
1. 在实际项目上测试 (439个器件, 480个连接)
2. 对比优化前后的加载时间
3. 验证所有功能正常工作
4. 检查内存占用是否合理

## 代码影响范围

### 新增文件
- `projectdatacache.h` - 缓存类声明
- `projectdatacache.cpp` - 缓存类实现
- `performancetimer.h` - 性能计时工具

### 修改文件
- `mainwindow.h` - 已有 `m_projectCache` 成员变量
- `mainwindow.cpp` - 析构函数清理缓存
- `mainwindow_project.cpp` 
  - `LoadProject()` - 初始化缓存
  - `LoadModelLineByUnits()` - 使用缓存查询
- `common.h` - 添加 Cached 函数声明
- `common.cpp` - 实现 Cached 函数
- `T_DESIGNER.pro` - 添加新文件到编译

### 代码审查要点
- ✅ 所有原有函数保持不变
- ✅ 新函数名称清晰 (带 `_Cached` 后缀)
- ✅ 缓存失败时有降级处理
- ✅ 内存管理正确 (new/delete配对)
- ✅ 编译无警告/错误

## 技术债务

无新增技术债务。本次优化:
- 遵循现有代码风格
- 保持向后兼容
- 可完全回退
- 有清晰的性能指标

## 总结

通过引入 `ProjectDataCache` 批量数据加载机制:
- 将 ~5,760 次数据库小查询合并为 4 次批量查询
- 预计 `LoadModelLineByUnits` 从 1150ms 降至 100-200ms
- 预计总加载时间从 2906ms 降至 ~1000-1200ms
- **预期整体性能提升 50-60%**

下一步需要通过实际测试验证这些预期,并继续优化其他瓶颈函数。
