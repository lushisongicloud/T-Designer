# 当前工作流程现状与缺口梳理

## 1. 元件建模（步骤 1）

- **已有能力**
  - `DialogUnitAttr` 负责库/工程器件的导入、编辑，保存至 `Equipment`、`Symbol`、`Symb2TermInfo` 等表（参见 `dialogUnitAttr.cpp:731`、`common.cpp:2340`）。
  - 功能子块 Tab 将 `Symb2TermInfo.ConnNum` 合并为 `|` 分隔的端号列表（`dialogUnitAttr.cpp:297-320`）。
  - CAD 导线通过 `ConnectLine` 表生成，`ProduceDBJXB()` 将其写入 `JXB`，完成端口到物理连线映射（`mainwindow.cpp:3662-3696`）。
- **缺口**
  - 缺少端号/端子与 T 模型变量的一致性校验 —— 已新建 `TModelValidator`，但尚未接入批量流程或导入流程。
  - Equipment 多实例仍共享同一 T 模型，需要后续支持实例级别参数化/继承策略。

## 2. 功能定义（步骤 2）

- **已有能力**
  - 功能管理对话框 `dialogfunctionmanage` 维护 `Function` 表，包括 `CmdValList`（输入约束）、`ExecsList`（执行器清单）等（`dialogfunctionmanage.cpp:47-107`）。
  - 功能依赖可在 UI 中录入，`SelectFunctionDialog` 提供依赖输入和链路定义（`widget/selectfunctiondialog.cpp:571-1312`）。
  - `FunctionInfo` 结构已封装关键字段；`FunctionDependencyResolver` 能够解析依赖闭包并求输入集合。
- **缺口**
  - 尚无全局功能拓扑图展示/校验；功能输入（`CmdValList`）仍为字符串，缺少结构化解析及与端口的映射。
  - 功能失效（故障）定义未与测试生成、D 矩阵联动。

## 3. 分层模型（步骤 3）

- **已有能力**
  - 容器树（`ContainerModel` + `ContainerTreeDialog`）支持系统→元件层级管理，`ContainerRepository` 存储层级结构与行为/接口 JSON。
  - 行为聚合器 `BehaviorAggregator` 已能根据子容器聚合接口/行为，供上层分析使用。
- **缺口**
  - 容器层级与功能映射尚未建模，`Container` 与 `Function` 的关联仅通过零散调用（目前通过 `TestGeneratorService.setContainerFunctions` 的临时映射完成）。
  - 缺少层级导航对接功能管理界面。

## 4. 自动测试生成（步骤 4）

- **已有能力**
  - `TestGeneratorService` 已能生成信号/功能/故障三类测试并写回 `Container.tests_json`。
  - `DiagnosticMatrixBuilder` 初步构建 D 矩阵并输出覆盖统计、候选测试、诊断树基础骨架。
  - 单元测试 `WorkflowCoreTest` 覆盖基础流程。
- **缺口**
  - 信号测试与端口类型（电气/液压/机械等）尚未接入，需要从 `Symb2TermInfo` 或元件元数据中补充类型枚举。
  - 功能测试依赖 `Function` 记录，需建立容器与功能的映射表/缓存，支持 UI 选择。
  - 故障测试仅生成普通故障模式和父级“正常判别”，尚未结合故障概率、依赖关系等高级逻辑。
  - 缺少 UI 列表展示与增删改查入口（仅容器树右键菜单触发生成）。

## 5. 测试性模型（步骤 5）

- **已有能力**
  - `DiagnosticMatrixBuilder` 产出 `MatrixEntry` 集合，可视为 D 矩阵的稀疏表示。
- **缺口**
  - 尚未持久化到数据库，也未提供 UI 展示矩阵、行列指标。
  - 缺少对不同层级（系统/子系统/元件）的矩阵聚合与过滤。

## 6. 指标分解（步骤 6）

- **现状**：无实现。尚需设计指标（检测率、隔离率）的层级分配算法，并将结果写回容器或测试记录。

## 7-9. 约束筛选、指标预估、诊断树生成

- **现状**：尚未实现。
  - 约束筛选：需引入测试属性（复杂度、费用、时间）及求解策略。
  - 指标预估：基于 D 矩阵统计与容器层级汇总，尚未开发。
  - 诊断树：目前 `DiagnosticMatrixBuilder::buildDecisionTree()` 仅提供占位的贪心版，需要接入成本、检测率等参数，并输出结构化结果。

## 7. 主要缺口与下一步建议

1. **数据结构统一**：建立容器、功能、端口、测试之间的关系表/缓存，确保生成与校验共享同一数据源。
2. **测试管理 UI**：新增测试管理面板（列表、详情、手动编辑），承接自动生成、增删改查。
3. **高级分析**：完善 D 矩阵持久化、指标分解、约束筛选、诊断树算法，并与 UI 交互。
4. **规范与工具**：在 `docs/tmodel_port_mapping_spec.md` 基础上，继续补充 T 语言、测试命名、端口类型等标准，并提供批量校验入口。

上述梳理完成后，可据此逐项落地剩余阶段实现。
