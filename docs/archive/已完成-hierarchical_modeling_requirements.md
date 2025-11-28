**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# T-Designer 分层建模与测试性扩展需求说明（修订版）

## 1. 背景与优先目标
- **优先级 P0**：
  1. 在现有 T-Designer 架构上实现“系统 → 子系统 → LRU → SRU → 模块 → 子模块 → 元件”的七层分层建模能力，使实体“元件”与新容器模型保持兼容，并支持 Z3 推理。
  2. 落地一版可执行的核心用户工作流程（元件管理 → 功能定义 → 分层建模 → 自动生成主要测试 → 测试性模型初步分析），同时为后续功能预留扩展接口。
- **中长期目标**：在 P0 稳定后逐步完善测试性指标分解、候选测试筛选、故障诊断决策树等高级能力，实现模型-分析一体化。

## 2. 名词约定
- **实体元件**：用户在图纸上插入的具体器件实例（如继电器 K1、电磁铁 YV1）。
- **容器（Container）**：表示某个层级的节点，封装子容器/元件并维护接口、功能行为、故障模式。
- **接口（Port）**：容器对外暴露的物理或逻辑交互点，包含名称、物理量类型、方向、量纲、约束等属性。
- **功能（Function）**：基于“所需输入 + 期望输出”定义的行为约束，可声明依赖关系。
- **功能行为（Behavior）**：容器的正常模式与故障模式的形式化描述，可由 SMT/T 语言表达。
- **状态（State）**：容器或元件当前模式。实体元件只能处于一种状态；聚合后的多子容器父节点只有 `normal` 与 `fault` 两种状态。
- **D 矩阵**：测试性模型，记录测试用例对故障模式的检测性与隔离性。

## 3. 分层模型需求
### 3.1 层级结构与约束
1. **层级定义**：系统 > 子系统 > LRU > SRU > 模块 > 子模块 > 元件。
2. **唯一所属**：每个容器（含元件层）在同层级中只能有一个父容器，禁止共享子树或形成环。
3. **元件约束**：实体元件仅在其同名元件层容器中出现一次，不得同时出现在多个容器中。
4. **层级跳跃**：允许父容器直接包含任意更低层级的容器，但必须严格高于被包含对象。示例：系统层可直接包含元件层或模块层。
5. **默认容器生成**：插入实体元件时自动创建同名元件层容器，将现有接口描述、功能行为、故障模式迁移至该容器。
6. **自动提升**：
   - 当系统仅含一个元件容器时，可自动生成系统层容器并继承其接口与行为；
   - 当加入新元件时，允许创建新的中间层（如子系统）将相关元件归类，原系统层引用新的上层容器。
7. **分析层级设置**：每个容器支持配置“故障模式分析层级”（`analysisDepth`），默认为自身层级；可下钻到更低层级参与分析，跳过聚合后的模式。

### 3.2 数据模型
1. **内存结构**：
   - 定义 `ContainerNode`：`id`, `displayName`, `level`, `parentId`, `childIds`, `analysisDepth`, `metadata`。
   - 子节点列表按顺序存储，支持层级拖拽与重排。
2. **接口描述（PortSchema）**：
   - 字段：`name`, `type`（电气/液压/机械/自定义）, `quantity`（电压/电流/油压/流量/速度/位移等）, `direction`（input/output/inout/internal）, `unit`, `bounds`（上下限或公式引用）, `signalId`, `mappedSymbol`, `sourceContainerId`。
   - 支持接口继承：记录来源容器 ID，便于追溯。
3. **功能行为（BehaviorSpec）**：
   - `normalMode` 与 `faultModes[]`，每个模式包含 `modeId`, `modeName`, `modeType`（normal/fault/commonFault/derivedFault）, `probability`, `constraints`, `sourceContainers[]`, `z3StateSymbol`。
   - 聚合父容器仅保留 `normal` 与 `fault`，未知模式由“非正常即故障”规则覆盖。
4. **状态互斥**：
   - 实体元件模式互斥，使用 `Σ state_i = 1` 约束；
   - 聚合父容器使用布尔状态 `state_parent`，`true` 表示 normal。
5. **连接关系**：
   - 维护 `ContainerConnection`，描述内部接口互连情况，用于识别内部接口与生成等式约束。

### 3.3 行为聚合与等价化简
1. **单子容器继承**：
   - 直接引用子容器的接口、行为、概率、状态集合；
   - 父容器 `analysisDepth` 继承子容器设置；
   - UI 中标记“继承模式”，可解除后自定义。
2. **多子容器聚合**：
   - **接口整合流程**：
     1. 收集所有子容器对外接口（`direction != internal`）。
     2. 根据连接拓扑识别内部接口，转换为父容器内部变量并标记 `internal`。
     3. 检查类型/量纲冲突并提示用户处理（重命名、映射或取消合并）。
     4. 输出父容器接口列表，记录来源集合。
   - **行为整合流程**：
     - 正常模式：`normal_parent = ∧ normal_child_i ∧ internal_connections`；
     - 故障模式：`fault_parent = ¬normal_parent`，并记录导致故障的子容器/模式集合；
     - 允许对指定子容器启用“枚举展开”生成派生容器（默认关闭，需手动触发）。
   - **概率整合**：
     - 默认独立假设：`P(parent.normal) = Π P(child.normal)`，`P(parent.fault) = 1 - P(parent.normal)`；
     - 若缺失概率，提供占位值并提示用户补充。
3. **分析层级控制**：
   - 计算测试性指标时，若 `analysisDepth` 小于子容器层级，则直接使用该层子容器的细粒度模式参与分析。
4. **Z3 化简支持**：
   - 使用容器路径前缀规范化变量命名，确保唯一；
   - 生成 SMT 片段：
     ```smt
     (declare-fun state_parent () Bool)
     (assert (= state_parent (and child1_normal child2_normal ...)))
     (assert (=> (not state_parent) (or child1_fault child2_fault ...)))
     ```
   - 对内部接口使用 `solve-eqs`、`elim-uncnstr` 消元，并调用 `simplify`, `ctx-solver-simplify` 获取等效表达式；
   - 缓存化简结果供 UI 展示与测试生成调用。

### 3.4 UI 需求（P0 范围）
1. **层级建模界面**：左侧树视图（支持拖拽、右键菜单），右侧属性面板显示容器信息与 `analysisDepth` 设置。
2. **接口管理**：属性面板提供接口列表（表格），支持新增/编辑/删除；显示来源容器与映射符号；内部接口默认隐藏。
3. **行为预览**：展示聚合后的 `normal`/`fault` SMT 片段与化简日志，支持导出；枚举展开入口预留但默认禁用。
4. **验证提示**：保存前执行一致性检查（层级合法性、接口唯一性、概率和、无孤立接口），失败时阻止保存并给出解决建议。

### 3.5 数据转换策略
- **元件级转换**：扫描现有工程中的实体元件，读取接口描述与 SMT/T 行为，生成元件容器数据并写入新表，同时记录转换日志与状态。
- **工程兼容**：在工程文件加入 `schema_version` 字段；首次打开旧工程时引导用户完成转换，可选择暂时保持旧模型只读。

## 4. 用户工作流程（含 P0 标记）
### 4.1 流程步骤
1. **元件导入（P0）**：沿用现有元件库操作，新增后台逻辑自动创建元件容器并在 UI 中提示成功。
2. **功能定义（P0）**：
   - 在功能管理界面提供输入端口选择器与输出表达式编辑器；
   - 支持声明依赖功能，系统自动补全间接输入；
   - 系统故障定义：输入满足要求但输出与期望不符。
3. **分层建模（P0）**：在层级建模界面搭建容器结构，查看自动聚合的接口、行为、概率，调整 `analysisDepth`。
4. **自动生成测试（P0）**：
   - **信号类测试**：根据接口类型生成测量模板，设定默认阈值；算法步骤：
     1. 从故障模式约束解析受影响变量；
     2. 匹配变量到接口；
     3. 构造 `normal ∧ test_condition ∧ fault_constraint`，若 Z3 返回 `unsat`，判定可检测该故障。
   - **功能类测试**：针对每个功能自动生成测试（设置输入、验证输出），依赖功能的输入自动注入；检测算法同上。
   - **故障模式测试**：每个元件默认生成“正常判别测试”；用户可选择特定故障生成专属测试；未知模式不单独生成，测试不通过且无法定位时归为“异常”。
5. **测试管理（P0）**：展示自动生成的测试列表，支持增删改查、批量操作，允许编辑复杂度、费用、时间、设备等属性。
6. **D 矩阵构建（P0）**：
   - 自动生成测试 vs. 故障矩阵，使用上述 Z3 判定填充检测性/隔离性标记；
   - 以稀疏结构存储并提供预览界面。
7. **指标分解（P1 预研）**：数据层预留目标与实际指标表，UI 提供占位入口，P0 不实现实际计算。
8. **候选测试筛选、指标预估、诊断决策树（P1+）**：定义接口但暂不实现，确保 D 矩阵数据结构可直接用于后续算法。

### 4.2 数据交互
- `FunctionSpec`：存储输入端口、输出约束、依赖关系、故障定义。
- `TestGeneratorService`：读取 `FunctionSpec`、容器接口与故障模式信息，生成测试并写入 `TestCase` 与 `DMatrix`。
- `DiagnosticMatrixBuilder`：提供 `getCoverageStats(containerId, analysisDepth)` 接口，为指标分解与决策树模块提供数据。
- 预留 `MetricTarget`, `MetricActual` 结构支撑后续指标分解。

## 5. Z3/SMT 描述与实现策略
### 5.1 现状概述
- 元件行为通过 SMT-LIB 描述，`z3solverthread` 负责求解。
- 现有流程以文本为主，自动聚合、化简难度大，需要结构化数据层辅助。

### 5.2 方案比较
| 方案 | 描述 | 优点 | 缺点 |
| --- | --- | --- | --- |
| **SMT 文本直编** | 继续人工或模板生成 SMT 文本 | 与现有流程兼容、迁移成本低 | 不利于聚合化简，维护困难，难以支持分析层级配置 |
| **结构化数据 + SMT 输出（推荐）** | 在 C++/Python 结构体中构建模型，最终生成 SMT 片段 | 易于组合、裁剪和化简；可复用现有 Z3 流程 | 需要实现生成器与数据同步机制 |
| **纯 z3py** | 在 Python 中使用 z3py 构建 AST | 操作灵活，易于做符号处理 | 需重写大量 C++/Qt 交互，风险较大 |

### 5.3 推荐策略
1. **P0 阶段**：
   - C++ 构建容器、接口、行为的数据结构；
   - 引入 `Z3Simplifier` 封装 Z3 化简操作，可与 Python 脚本协作；
   - 现有 SMT 文本作为输出格式，供后续求解与导出。
2. **P1 阶段**：
   - 引入共享的模型描述中间层（JSON/ProtoBuf），供 C++/Python 共享；
   - 在测试筛选等算法中使用 z3py 直接操作 AST。
3. **远期**：
   - 建立统一 DSL，涵盖功能、故障、测试描述，实现 GUI 与推理的语义统一。

### 5.4 Z3 支持要点
- **聚合化简**：对合并后的 SMT 片段调用 `simplify`, `propagate-ineqs`, `ctx-solver-simplify`，缓存结果以减少重复计算。
- **可检测性判定**：构造 `normal ∧ test_conditions ∧ fault_constraints`，若 `unsat` 说明测试可检测该故障；若 `sat`，记录满足解并提示调整测试阈值。
- **内部接口消元**：使用 `solve-eqs`、`elim-uncnstr` 消去内部变量，生成对外等效约束。
- **性能优化**：针对重复求解场景使用模型缓存，必要时引入增量求解或假设推理。

## 6. 数据库与存储设计
1. **新增/调整数据表**：
   - `container`：`id`, `name`, `level`, `parent_id`, `analysis_depth`, `schema_version`, `description`；
   - `container_relation`：`parent_id`, `child_id`, `order`, `inherit_flag`；
   - `container_port`：`id`, `container_id`, `name`, `type`, `quantity`, `direction`, `unit`, `bounds`, `symbol`, `source_container_id`；
   - `container_behavior`：`id`, `container_id`, `mode_type`, `mode_name`, `probability`, `expression`, `source_container_ids`, `last_simplified_at`；
   - `container_connection`：`id`, `parent_id`, `port_a`, `port_b`, `is_external`；
   - `function_spec`：`id`, `name`, `container_id`, `input_ports`, `expected_outputs`, `dependencies`, `fault_definition`；
   - `test_case`：`id`, `container_id`, `type`, `definition`, `complexity`, `cost`, `duration`, `equipment`, `source`；
   - `d_matrix`：`test_id`, `fault_id`, `detectability`, `isolatability`, `confidence`；
   - 预留 `metric_target`, `metric_actual` 用于指标分解。
2. **版本管理**：在工程文件记录 `schema_version`，配套迁移脚本与回滚策略。
3. **事务控制**：自动生成容器、批量创建测试、重算 D 矩阵时使用事务保证一致性；提供操作日志便于追溯。

## 7. 需要澄清的问题
1. **模式枚举策略**：默认仅保留 normal/fault，是否需要为特定容器提供更细粒度的故障枚举？触发条件如何判定？
2. **接口冲突处理**：多子容器聚合时接口同名不同量纲的解决策略是否有既定规则？
3. **概率数据来源**：故障模式概率是否由用户输入、历史数据估计或由系统提供默认模板？
4. **T 语言兼容**：后续是否计划完全迁移到 SMT/DSL，还是继续支持 T 语言输入？
5. **测试成本维度**：除了复杂度、费用、时间，还需要纳入资源占用、设备类型、人员等级等指标吗？
6. **性能目标**：在多大规模（容器数、故障模式数、测试数）下需要保证操作响应时间？

## 8. 参考实现建议
- 借鉴 TEAMS/eXpress 的层级建模界面，上下钻取显示聚合信息。
- D 矩阵采用稀疏存储，并结合向量化/并行计算提升性能。
- 决策树可采用 ID3/C4.5 的成本加权变种，结合测试费用与检测能力。
- 引入分步向导与提示面板，帮助用户完成功能定义、分层建模、测试生成。
- 设计脚本接口（Python 插件）支持批量测试导入或自动修复。

## 9. 里程碑规划
1. **M1：容器模型与数据库扩展（2 周）**
   - 完成容器数据结构、数据库表与基础 CRUD；实现容器树 UI 原型。
2. **M2：行为聚合与 Z3 化简（2-3 周）**
   - 完成接口整合、normal/fault 聚合、Z3 化简与日志输出。
3. **M3：功能定义与测试生成（3 周）**
   - 实现功能定义界面、依赖解析、信号/功能/故障测试生成与判定算法。
4. **M4：D 矩阵与测试管理（2 周）**
   - 构建 D 矩阵、实现测试管理界面、完成覆盖率统计 API。
5. **M5：指标分解与诊断树预研（2 周）**
   - 完成接口设计、数据结构预留与原型算法验证。

## 10. 风险与缓解
- **建模复杂度高**：通过可视化树、批量操作、模板化向导降低使用门槛。
- **SMT 规模膨胀**：默认仅保留 normal/fault，必要时限制枚举深度；引入缓存与增量求解。
- **性能瓶颈**：对树结构与矩阵操作采用懒加载、并行计算；必要时使用 C++ 扩展优化热点。
- **数据一致性**：通过数据库约束、事务与模型校验器确保一致性，提供错误日志与回滚。
- **用户学习成本**：提供示例工程、帮助文档、化简日志辅助理解。

## 11. 下一步行动
1. 与业务方确认第 7 节问题，形成最终需求基线。
2. 设计详细类图与数据字典，完善容器、接口、行为、测试等结构。
3. 制定旧工程转换计划，包含失败回滚策略与用户提示流程。
4. 在小型示例上验证聚合与测试生成算法，确保 Z3 化简效果符合预期。
5. 编写开发与测试计划，覆盖单元测试、集成测试与性能基准。

## 12. 关键实现条目（P0 必须完成）
1. **容器树模型与持久化**：实现 `ContainerModel`（`QAbstractItemModel`）、`ContainerRepository`（数据库访问），以及 `ContainerSyncService`（UI 与数据库同步）。
2. **接口聚合与行为整合引擎**：开发 `BehaviorAggregator`，负责接口整合、normal/fault 聚合、概率计算、冲突检测，并调用 `Z3Simplifier` 化简约束。
3. **功能定义与依赖解析**：扩展 `DialogFunctionManage`，实现输入/输出选择与依赖图展示；新增 `FunctionDependencyResolver` 计算实际输入集合。
4. **自动测试生成器**：实现 `TestGeneratorService`，覆盖信号、功能、故障三类测试，并与 `BehaviorAggregator` 协作计算检测/隔离能力。
5. **D 矩阵构建器**：开发 `DiagnosticMatrixBuilder`，负责稀疏矩阵构建、覆盖统计与 API 暴露。
6. **界面联动与日志**：实现层级建模界面、测试管理界面，集成化简日志、检测结果展示与一致性校验提示。

## 13. C++/Qt 任务分解清单
### 13.1 目录与模块规划（建议）
- `BO/Container/`
  - `containermodel.h/.cpp`：层级树模型。
  - `containerentity.h/.cpp`：容器、接口、行为数据结构。
  - `containerrepository.h/.cpp`：数据库访问封装。
- `BO/Behavior/`
  - `behavioraggregator.h/.cpp`：接口聚合、行为整合。
  - `z3simplifier.h/.cpp`：Z3 化简与求解接口（复用 `z3solverthread` 基础）。
- `BO/Function/`
  - `functionservice.h/.cpp`：功能 CRUD、依赖解析。
- `BO/Testability/`
  - `testgeneratorservice.h/.cpp`：自动测试生成。
  - `diagnosticmatrixbuilder.h/.cpp`：D 矩阵构建与统计。
- `services/`
  - `containersyncservice.h/.cpp`：UI ↔ 数据库同步。
  - `solverservice.h/.cpp`：封装 Z3 求解调用（可调用 `z3solverthread`）。
- `widget/`
  - `hierarchyeditorwidget.h/.cpp/.ui`：分层建模主界面。
  - `containerpropertypanel.h/.cpp/.ui`：容器属性与接口编辑。
  - `behaviorpreviewwidget.h/.cpp/.ui`：聚合行为与日志展示。
  - `testmanagementwidget.h/.cpp/.ui`：测试列表与 D 矩阵预览。

### 13.2 头文件接口草稿
```cpp
// containermodel.h
class ContainerModel : public QAbstractItemModel {
    Q_OBJECT
public:
    explicit ContainerModel(QObject *parent = nullptr);
    QModelIndex index(int row, int column, const QModelIndex &parent) const override;
    QModelIndex parent(const QModelIndex &child) const override;
    int rowCount(const QModelIndex &parent) const override;
    int columnCount(const QModelIndex &parent) const override;
    QVariant data(const QModelIndex &index, int role) const override;
    Qt::ItemFlags flags(const QModelIndex &index) const override;
    bool setData(const QModelIndex &index, const QVariant &value, int role) override;
    bool insertRows(int row, int count, const QModelIndex &parent) override;
    bool removeRows(int row, int count, const QModelIndex &parent) override;

    void loadFromDatabase();
    bool canReparent(const QModelIndex &source, const QModelIndex &target) const;
    bool reparent(const QModelIndex &source, const QModelIndex &target);
    ContainerNode *nodeFromIndex(const QModelIndex &index) const;

signals:
    void containerChanged(int containerId);
};

// behavioraggregator.h
struct AggregationResult {
    QVector<ContainerPort> ports;
    BehaviorSpec normalBehavior;
    BehaviorSpec faultBehavior;
    QVector<FaultContribution> faultContributions;
    QString simplificationLog;
};

class BehaviorAggregator {
public:
    AggregationResult aggregate(int containerId, const AggregationOptions &options);

private:
    AggregationResult inheritSingleChild(const ContainerNode &child);
    AggregationResult mergeChildren(const QVector<ContainerNode *> &children);
    QString simplifyWithZ3(const QString &smtScript, AggregationResult &result);
};

// testgeneratorservice.h
struct GeneratedTest {
    TestCase testCase;
    QVector<int> detectableFaultIds;
    QVector<int> isolatableFaultIds;
};

class TestGeneratorService {
public:
    explicit TestGeneratorService(BehaviorAggregator *aggregator);
    QVector<GeneratedTest> generateForContainer(int containerId, TestGenerationScope scope);

private:
    GeneratedTest buildSignalTest(const ContainerPort &port);
    GeneratedTest buildFunctionTest(const FunctionSpec &function);
    GeneratedTest buildFaultModeTest(const ContainerNode &componentNode);
    bool canDetectFault(const GeneratedTest &test, const FaultMode &fault) const;
};

// diagnosticmatrixbuilder.h
class DiagnosticMatrixBuilder {
public:
    DiagnosticMatrixBuilder();
    void rebuildForContainer(int containerId, int analysisDepth);
    CoverageStats getCoverageStats(int containerId) const;
};
```

### 13.3 集成注意事项
- `mainwindow`：新增菜单入口打开层级建模界面，加载工程时初始化容器树。
- `sqlitedatabase.*`：扩展以支持新表读写与事务控制。
- `z3solverthread.*`：提供批量化简与求解接口，供 `BehaviorAggregator` 与 `TestGeneratorService` 调用。
- `dialogfunctionmanage.*`、`dialogusertest.*`：复用现有对话框基础，增加新控件与数据绑定。
- `Model.db`：更新示例数据，包含分层容器、功能、测试样例，便于验证。

