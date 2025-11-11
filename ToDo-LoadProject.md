# ToDo — LoadProject 性能改造

目标：修复 ProjectDataModel 加载失败、用 Qt Model/View 重构器件与连线界面的数据加载路径，将 `LoadProjectUnits`、`LoadProjectLines` 的耗时从分钟级降到秒级以内。

## 任务 1：恢复 ProjectDataModel 的连线支持 ✅
> 已完成：ConnectionData 与数据库列对齐，ConnectionManager 在缺失列时降级告警；LoadProject 依据 ProjectDataModel 结果重新启用缓存优化并加载 ProjectDataCache。
1. **梳理 JXB 字段差异**  
   - 对比 `projectdatamodel.h/.cpp` 的 `ConnectionData` 定义与数据库实际列（`Symb1_ID`、`Symb2_ID` 等）。  
   - 更新 `ConnectionManager::load()` 查询与 `ConnectionData` 字段命名，确保兼容缺失列时退化为警告而非终止。
2. **复用 ProjectDataModel 结果**  
   - `MainWindow::LoadProject()`：若 `ProjectDataModel::loadAll()` 失败，记录错误并继续旧逻辑；成功时开启 `m_useCacheOptimization` 并提供统一的 `getProjectDataModel()` 访问口。
3. **验证**  
   - 在测试项目（>4k 器件）上运行 `LoadProject()`，确认 ProjectDataModel 统计信息显示完整（含 Connections）。

## 任务 2：器件树改用 Model/View
1. **实现 `EquipmentTreeModel`**  
   - 基于 `ProjectDataModel` 构建 `项目 → 高层 → 位置 → 器件 → Symbol` 的 `QAbstractItemModel`，节点上只存 ID/类型，`data()` 内按需查询真实文本。
2. **实现过滤代理 `EquipmentTreeFilterProxy`**  
   - 支持高层、位置、页面、关键字四类条件；由 `FilterUnit()` 改为设置 proxy 参数。
3. **接入 UI**  
   - `LoadProjectUnits()` 创建/刷新模型，移除 `ModelUnits` + SQL 循环；`treeViewUnits` 绑定到 proxy，维持展开状态、双击行为等。  
   - 原 `FilterUnit()` 精简为 proxy setter。
4. **验证**  
   - 重新加载大项目，确认树视图秒级展开，过滤无 SQL 查询。

## 任务 3：器件列表改用 Table Model
1. **实现 `EquipmentTableModel`**  
   - 基于 `ProjectDataModel` 暴露列（序号、项目代号、型号、名称、数量、厂家、部件编号、备注）；数据由 `EquipmentData` 直接提供。  
2. **使用 `QSortFilterProxyModel` 做筛选/排序**  
   - 代理与树的过滤条件保持一致，支持列排序。  
3. **UI 替换**  
   - 用 `QTableView`（或对 `tableWidgetUnit` 做 `setModel`）取代逐格 `setItem`；取消 `LoadUnitTable()` 中的 SQL 查询。  
4. **验证**  
   - 载入+筛选+选择器件，保证行为与旧界面一致，性能提升显著。

## 任务 4：连线树 Model/View 化
1. **实现 `ConnectionTreeModel`**  
   - 结构为 `项目 → 高层 → 位置 → 连线`，显示文本 `ConnectionNumber (端口A → 端口B)`，端点信息通过 `ProjectDataModel::SymbolManager` 查询。  
2. **过滤代理**  
   - 线号关键字、线型、颜色等条件；用于替代 `LoadModelLineDT()` 的遍历+SQL。  
3. **接入 UI**  
   - `LoadModelLineDT()` 改为刷新模型，不再构造 `ModelLineDT`；保留展开状态与树的右键功能。  
4. **验证**  
   - 在 6k+ JXB 的项目上确保秒级刷新、过滤流畅。

## 任务 5：统一 ComboBox/搜索数据源
1. **使用 ProjectDataModel 的唯一列表接口**  
   - `PageManager::getUniqueGaocengList()`/`getUniquePosList()` 填充所有高层/位置下拉。  
2. **页面筛选联动**  
   - 根据页面选择获取所属结构，再驱动树/表 proxy 过滤。  
3. **删除旧的 SQL Helper**  
   - 移除 `GetProjectStructureStrByProjectStructureID` 等不再需要的频繁查询函数。

## 任务 6：回归测试与性能确认
1. **功能验证**：加载多项目，检查器件树/表、连线树、过滤、双击打开、导出等关键流程。  
2. **性能对比**：保留新的 `PerformanceTimer` 日志，确认 `LoadProjectUnits`、`LoadProjectLines` 耗时均 <1 s。  
3. **清理文档**：更新 `PERFORMANCE_OPTIMIZATION_RESULT.md`、`UI_DATA_ACCESS_ANALYSIS.md` 等报告，记录新的架构和测试结果。

## 任务 7：数据访问一致性审查
1. **排查 UI 直接取值**：审阅 `MainWindow` 及相关对话框（如 `buildTestReportMetrics()`、`FilterUnit()` 等），确认数据来源均为数据库/ProjectDataModel，而非直接读取 UI 控件内容。  
2. **整改发现的问题**：若存在 `ui->tableWidget…`、`treeView…->model()` 等被用作数据存储，改为调用 ProjectDataModel 或必要的缓存接口。  
3. **回归测试**：在修复点执行相关功能（测试报告、诊断、过滤等），确保数据正确且性能无回退。
