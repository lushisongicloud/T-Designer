# T-Designer 实现差距详细分析报告

**分析时间**: 2025-11-25  
**分析目标**: 评估 commit "D矩阵已初步可运行" (79b1ebd) 后的代码实现情况，对比开发目标，明确剩余工作

---

## 一、总体评估

### 1.1 已实现的核心功能

#### ✅ D矩阵功能（基本完成）
- **已实现**:
  - `DMatrixViewerDialog`: D矩阵查看对话框，基本移植自 T-Solver
  - `DMatrixModel`: D矩阵数据模型，支持行列显示与状态管理
  - `DMatrixSelectionDialog`: 故障/测试选择对话框
  - `DMatrixOptionsDialog`: D矩阵生成选项对话框
  - `DMatrixService`: D矩阵服务类，处理加载、保存、持久化
  - `DiagnosticMatrixBuilder`: D矩阵构建器，核心生成逻辑
  - `dmatrix_meta` 表: 数据库表结构已建立，支持元数据存储
  - 主界面"D矩阵"按钮 (`BtnDMatrix`) 及其 slot 处理函数
  - D矩阵自动保存/加载 JSON 文件的逻辑

- **待完善**:
  - D矩阵多维度信息扩充（测试复杂性、费用、时间、成功率、备注等）
  - 故障多维度信息扩充（概率、严重度、备注等）
  - 与现有测试优选、测试性指标预计、诊断决策树的深度集成

#### ✅ 功能管理（基本完成）
- **已实现**:
  - `FunctionManagerDialog`: 功能管理主对话框
  - `FunctionEditDialog`: 功能编辑对话框
  - `SelectFunctionDialog`: 功能选择对话框（从 T-Solver 移植）
  - `FunctionRepository`: 功能仓库，处理功能的 CRUD 操作
  - `FunctionDependencyResolver`: 依赖关系解析器
  - `SystemStructureService`: 系统结构服务，支持链路裁剪与边界识别
  - `function_definition`, `function_document` 等数据库表
  - 主界面"功能管理"按钮 (`BtnFunctionManage`) 及其 slot 处理函数
  - 自动查找依赖功能与边界条件的基础逻辑
  - 功能约束完整性检查（执行器取反验证）

- **待验证/完善**:
  - 链路信息从 CAD 连线自动构建功能的完整性
  - 边界条件自动识别在复杂系统中的准确性
  - 变量取值范围配置 (`VariableRangeConfig`) 的 UI 集成度

#### ✅ SMT 建模与验证（已实现）
- **已实现**:
  - `TModelParser`: T 语言模型解析器
  - `TModelValidator`: T 语言模型验证器
  - `SmtSyntaxChecker`: SMT 语法检查器
  - `TModelHelper`: T 语言模型辅助工具类
  - `TModelCheckService`: T 语言模型检查服务（UI 集成）
  - 元件属性界面 (`DialogUnitAttr`) 的"T语言模型"编辑器（QScintilla）
  - 本地物料库界面 (`DialogUnitManage`) 的"T语言模型"编辑器
  - "验证T语言模型"按钮及验证逻辑（语法、端口一致性）
  - "自动编译T语言模型"功能（解析并显示端口、参数、故障模式）
  - 占位符替换与参数绑定逻辑
  - 故障模式自动提取到维修信息表

- **待完善**:
  - 本地物料库与元件属性之间的验证逻辑复用（目前存在部分代码重复）
  - SMT 模型与端口配置的自动同步机制

#### ✅ 端口配置功能（已实现）
- **已实现**:
  - `PortConfigEditDialog`: 端口配置编辑对话框
  - `PortConfigPanel`: 端口配置面板（集成到元件属性/本地物料库）
  - `port_config` 表: 存储端口类型、方向、变量配置、连接宏等
  - `port_connect_macro_family` 表: 存储连接宏族定义
  - 内置三个宏族已初始化: `electric-connect`, `hydraulic-connect`, `mechanical-connect`
  - 端口类型选择（电气/液压/机械/其他）
  - 默认变量集显示与自定义
  - 连接宏族选择界面
  - 自定义宏族的添加/删除功能（UI 已实现）
  - 从库到项目的端口配置复制逻辑 (`copyPortConfig`)

- **待验证**:
  - 自定义宏族的完整工作流程（添加、编辑、删除、使用）
  - 宏族展开逻辑在系统连接生成中的应用

#### ✅ 元件与系统实体（已实现）
- **已实现**:
  - `ComponentEntity`: 元件实体类，封装元件的 SMT 描述、端口、参数、故障模式
  - `SystemEntity`: 系统实体类，处理系统级 SMT 求解、连接解析、观测变量管理
  - `component_smt` 表: 存储元件级 SMT 描述
  - `system_smt` 表: 存储系统级 SMT 描述（DEF 块、连接块、原始块）
  - Z3 求解器集成（增量求解会话、模型检查）
  - 连接解析逻辑（`connect2e`, `connect3e`, 多相数组端口等）

- **待完善**:
  - `component_smt` 和 `system_smt` 表的实际使用（目前表已建但代码中未见大量使用）
  - 系统 SMT 的自动生成与持久化流程需要完善

#### ✅ 容器模型（已实现）
- **已实现**:
  - `ContainerRepository`: 容器仓库，管理容器的 CRUD 操作
  - `ContainerEntity`: 容器实体类（定义在 `DO/containerentity.h`）
  - `container`, `container_hierarchy`, `container_component`, `container_interface` 等数据库表
  - 元件级容器的自动创建逻辑 (`ensureComponentContainer`)
  - 容器层级管理（系统、子系统、LRU、SRU、模块、子模块、元件）
  - 容器树视图对话框 (`ContainerTreeDialog`)

- **待完善**:
  - 元件级容器的接口与行为模型自动继承实体元件的逻辑
  - 元件级容器的 SMT 模型自动生成
  - 不同层级容器的完整管理界面与功能集成

---

## 二、详细功能对比与差距分析

### 2.1 功能 1-3：元件插入、CAD 绘图、连接建立 ✅ 基本实现

**现状**: 
- T-Designer 已支持从本地物料库插入元件到项目
- CAD 功能子块的绘制已实现（基于 MxDraw 控件）
- 端口间连接已实现（`ConnectLine` 表记录连接关系）

**差距**:
- ✅ 元件的 T 语言模型（SMT 描述）已在 `Equipment` 表的 `TModel` 字段存储
- ✅ 端口配置已有 `port_config` 表支持
- ⚠️  **需要验证**: CAD 连线到系统 SMT 连接约束的自动生成流程是否完整运行

**建议行动**:
1. 验证从 CAD 连线到 `textEditSystemDiscription` 的系统描述生成逻辑
2. 确认连接宏族的选择与展开逻辑在实际项目中能否正确工作
3. 测试多端口连接（3 端、4 端）的宏自动选择

---

### 2.2 功能 4：建立系统的所有功能 ⚠️ 部分实现

**现状**:
- `FunctionManagerDialog` 已实现，可手动创建/编辑功能
- 功能的链路 (`link`)、依赖关系 (`dependency`)、约束 (`constraint`) 已有 UI 支持
- "自动查找依赖功能"和"自动查找边界条件"功能已实现

**差距**:
- ❌ **链路信息从 CAD 连线自动构建**: 当前需要手动输入链路（如 `KM,FR,L8`），未见自动从连线表推导的完整逻辑
- ⚠️  依赖功能的自动查找逻辑需要在实际项目中测试准确性
- ⚠️  边界条件的推导算法需要验证对复杂系统的适用性

**建议行动**:
1. **高优先级**: 实现"链路自动构建"功能
   - 从 `ConnectLine` 表分析连通性
   - 根据用户选择的起点/终点设备，自动推导链路中的中间设备
   - 集成到 `FunctionEditDialog` 或 `FunctionManagerDialog` 中，添加"自动构建链路"按钮
2. 在 DemoSystem 或 DemoWorkflow 项目中测试边界识别算法
3. 补充文档说明链路与依赖的最佳实践

---

### 2.3 功能 5：查看/生成 D矩阵 ✅ 基本实现

**现状**:
- 主界面"D矩阵"按钮已添加（位于"测试性"栏，"故障诊断"按钮左侧）
- 点击按钮弹出 `DMatrixViewerDialog`
- 对话框上有"生成D矩阵"按钮 (`onBuildClicked`)
- D 矩阵生成逻辑已集成到 `DMatrixService::buildAndPersist`
- 自动保存/加载 JSON 文件（`<ProjectName>_dmatrix.json`）和元数据到 `dmatrix_meta` 表

**差距**:
- ⚠️  **多维度信息扩充**: 当前 D 矩阵只存储基本的故障-测试映射关系，缺少:
  - 测试的多维度信息: 复杂性、费用、时间、成功率、备注
  - 故障的多维度信息: 概率、严重度、备注
- ⚠️  **集成现有流程**: D 矩阵与"测试优选"、"测试性指标预计"、"诊断决策树"的集成需要进一步验证

**建议行动**:
1. **中优先级**: 扩充 `testability_types.h` 中的数据结构
   - 在 `TestabilityTest` 结构体中添加 `complexity`, `cost`, `time`, `successRate`, `remarks` 等字段
   - 在 `TestabilityFault` 结构体中添加 `probability`, `severity`, `remarks` 等字段
   - 更新 `DMatrixModel` 以显示这些信息（可选列）
2. **中优先级**: 在 `DMatrixOptionsDialog` 中添加是否包含扩展信息的选项
3. **低优先级**: 测试 D 矩阵数据如何与诊断决策树、测试优选算法协同工作

---

## 三、按 README 要求的详细检查

### 3.1 元件属性与本地物料库的 SMT 模型管理

**实现情况**: ✅ 已实现大部分功能
- 两个界面都有"T语言模型"编辑器（QScintilla，支持语法高亮）
- 都有"验证T语言模型"按钮
- 都有"自动编译T语言模型"功能
- 都有故障模式自动提取功能

**差距**:
- ⚠️  **代码复用**: 两处界面的验证逻辑有部分重复（`DialogUnitAttr::on_BtnValidateTModel_clicked` 和 `DialogUnitManage::performTModelValidation`），虽然核心逻辑在 `TModelValidator` 中已封装，但调用代码仍有冗余
- ✅ SMT 模型与端口配置一致性校验已在 `TModelCheckService` 中实现

**建议行动**:
1. **低优先级**: 进一步抽取验证调用代码到共享辅助函数，减少重复
2. 添加单元测试覆盖 SMT 验证的正反例

---

### 3.2 端口配置功能

**实现情况**: ✅ 已完全实现
- `PortConfigEditDialog` 完整实现，包括:
  - 端口类型选择（电气/液压/机械/其他）
  - 默认变量集显示与编辑
  - 连接宏族选择表格
  - 添加/删除自定义宏族按钮
- `port_config` 表与 `port_connect_macro_family` 表结构合理
- 内置三个宏族已初始化到 `templete/project.db`

**差距**:
- ⚠️  **实际使用验证**: 需要在实际项目中验证自定义宏族的完整生命周期（添加→使用→展开→求解）
- ⚠️  **文档缺失**: 端口配置与连接宏族的用户操作指南尚未编写

**建议行动**:
1. **中优先级**: 在 MyProjects 中的某个项目测试完整的端口配置→连接生成→求解流程
2. **中优先级**: 编写端口配置用户指南（markdown 文档）
3. 添加示例：如何为自定义元件（如三相电机）配置端口并创建自定义宏族

---

### 3.3 系统连接约束自动生成

**实现情况**: ⚠️ 部分实现
- `SystemEntity::prepareModel` 可解析系统描述中的连接语句（`connect2e`, `connect3e` 等）
- 连接宏的展开逻辑已在 `prepareModel` 中实现（基尔霍夫定律、等势约束）
- 从 CAD 连线到 `textEditSystemDiscription` 的生成逻辑存在（`LoadProjectSystemDescription`）

**差距**:
- ❌ **宏族自动选择**: 当前系统描述中直接写 `connect2e` 或 `connect3e`，未见根据连接点端口数量自动选择合适宏的逻辑
- ❌ **端口配置集成**: 生成连接约束时未见使用 `port_config` 表中的 `connect_macro` 字段
- ⚠️  **系统 SMT 持久化**: `system_smt` 表结构已建，但代码中未见完整的写入逻辑

**建议行动**:
1. **高优先级**: 实现连接约束自动生成的完整流程
   - 从 `ConnectLine` 表获取连接关系
   - 解析每个连接点涉及的端口（通过 `Symb2TermInfo` 或端口配置）
   - 查询每个端口的 `port_config`，获取 `connect_macro` 或默认宏族
   - 根据端口数量（arity）从宏族中选择合适的宏
   - 展开宏，生成 SMT 约束
   - 将生成的连接块写入 `system_smt` 表
2. **高优先级**: 在 `LoadProjectSystemDescription` 函数中添加宏族选择逻辑
3. 添加单元测试：2 端、3 端、4 端连接的宏自动选择

---

### 3.4 功能管理完整性

**实现情况**: ✅ 核心功能已实现，⚠️ 部分功能需要验证

**已完成**:
- 功能树结构的管理（添加、删除、编辑、保存）
- 功能的链路 (`link`)、依赖 (`dependency`)、约束 (`constraint`) 的定义
- "自动查找依赖功能"算法已实现
- "自动查找边界条件"算法已实现（基于 `SystemStructureService`）
- 执行器取反完整性检查已实现
- 变量取值范围配置 (`VariableRangeConfig`) 已实现

**差距**:
- ❌ **链路自动构建**: 未见从 CAD 连线自动推导链路的功能（当前需手动输入）
- ⚠️  **变量取值范围 UI**: `FunctionVariableValueDialog` 已实现，但在功能管理流程中的集成程度需要验证
- ⚠️  **离线求解结果**: 功能定义中包含 `offlineSolveResult`，但在 `FunctionManagerDialog` 中的显示与管理需要完善

**建议行动**:
1. **高优先级**: 实现"链路自动构建"功能（见 3.2.2）
2. **中优先级**: 在 `FunctionManagerDialog` 中添加"查看变量范围"按钮，集成 `FunctionVariableValueDialog`
3. **中优先级**: 完善离线求解结果的表格显示与管理（添加/删除/编辑）

---

### 3.5 D 矩阵生成与查看

**实现情况**: ✅ 基本实现，⚠️ 扩展功能待完善

**已完成**:
- D 矩阵生成服务 (`DMatrixService::buildAndPersist`)
- D 矩阵查看对话框 (`DMatrixViewerDialog`)
- 故障/测试选择对话框 (`DMatrixSelectionDialog`)
- D 矩阵选项对话框 (`DMatrixOptionsDialog`)
- JSON 文件自动保存/加载
- 元数据持久化到 `dmatrix_meta` 表

**差距**:
- ❌ **多维度信息**: 测试与故障的扩展属性（复杂性、费用、时间、概率、严重度等）未在数据结构与 UI 中体现
- ⚠️  **现有流程集成**: D 矩阵与"测试优选"、"测试性指标预计"、"诊断决策树"的集成需要验证

**建议行动**:
1. **中优先级**: 扩充数据结构（见 3.2.3）
2. **中优先级**: 在 `DMatrixViewerDialog` 中添加扩展信息的显示列（可选）
3. **低优先级**: 测试 D 矩阵数据如何被"测试优选"算法使用

---

### 3.6 元件级容器模型

**实现情况**: ✅ 基础实现，⚠️ 自动生成逻辑待完善

**已完成**:
- `ContainerRepository` 完整实现
- 元件级容器的自动创建 (`ensureComponentContainer`)
- 容器层级管理数据库表（`container`, `container_hierarchy`, `container_component`, `container_interface` 等）
- 容器树视图对话框 (`ContainerTreeDialog`)

**差距**:
- ❌ **接口与行为模型继承**: 元件级容器应自动继承实体元件的接口（端口）与行为（SMT 描述），当前逻辑不完善
- ❌ **容器 SMT 模型自动生成**: 未见从实体元件的 `TModel` 自动生成容器级 `component_smt` 的逻辑
- ⚠️  **不同层级容器管理**: 容器树视图已实现，但更高层级容器（子系统、LRU、SRU 等）的管理界面与功能集成需要完善

**建议行动**:
1. **中优先级**: 实现元件级容器的接口与行为模型自动同步
   - 当创建元件级容器时，从 `Equipment.TModel` 提取端口与变量
   - 生成容器的 `component_smt` 记录（复制或引用实体元件的 SMT）
   - 在 `container_interface` 表中记录容器的端口
2. **低优先级**: 完善不同层级容器的管理界面（添加、删除、移动、重命名）

---

### 3.7 数据库初始化与迁移

**实现情况**: ✅ 部分完成，⚠️ 需要更新

**已完成**:
- `templete/project.db` 已包含所有必要的表结构
- 内置连接宏族已初始化到 `port_connect_macro_family` 表
- `tools` 目录下有多个数据库迁移脚本（如 `db_migrate_project.py`, `update_template_db.py`）

**差距**:
- ⚠️  **旧项目迁移**: MyProjects 目录下的现有项目需要运行迁移脚本以更新数据库结构
- ⚠️  **Linux 路径适配**: `init_builtin_macro_families.py` 中硬编码了 Windows 路径（`d:\SynologyDrive\...`），需要改为相对路径

**建议行动**:
1. **高优先级**: 修改 `tools/init_builtin_macro_families.py` 为相对路径版本
   ```python
   import os
   import sys
   script_dir = os.path.dirname(os.path.abspath(__file__))
   db_path = os.path.join(script_dir, '..', 'templete', 'project.db')
   ```
2. **高优先级**: 编写统一的数据库迁移脚本 `tools/migrate_all_projects.py`
   - 遍历 `MyProjects` 目录下所有 `.db` 文件
   - 检查是否缺少新表或新字段
   - 执行增量迁移 SQL
   - 记录迁移日志
3. 在 README 中添加数据库迁移说明

---

### 3.8 文档与用户指南

**实现情况**: ❌ 基本缺失

**差距**:
- ❌ 功能管理的用户操作文档
- ❌ D 矩阵生成与查看的用户指南
- ❌ SMT 建模规范文档
- ❌ 端口配置与连接宏族的说明文档
- ⚠️  部分开发笔记存在（如 `docs/demo_workflow_function_usecase.md`），但不完整

**建议行动**:
1. **中优先级**: 编写用户操作手册
   - `docs/user_guide_function_management.md`: 功能管理操作指南
   - `docs/user_guide_dmatrix.md`: D 矩阵生成与查看指南
   - `docs/user_guide_smt_modeling.md`: SMT 建模规范与最佳实践
   - `docs/user_guide_port_config.md`: 端口配置与连接宏族使用指南
2. **低优先级**: 添加视频教程或截图演示

---

## 四、按优先级的修改建议

### 4.1 高优先级（必须完成）

1. **实现链路自动构建功能**
   - 分析 CAD 连线表 (`ConnectLine`)
   - 根据用户指定的起点/终点，自动推导链路
   - 集成到功能编辑对话框

2. **完善系统连接约束自动生成**
   - 根据端口数量自动选择连接宏
   - 从 `port_config` 表读取宏族配置
   - 展开宏并生成 SMT 约束
   - 持久化到 `system_smt` 表

3. **修改数据库初始化脚本为相对路径**
   - 更新 `tools/init_builtin_macro_families.py`
   - 确保在 Linux/macOS 环境下可运行

4. **编写统一的数据库迁移脚本**
   - `tools/migrate_all_projects.py`
   - 自动更新 MyProjects 下所有项目数据库

### 4.2 中优先级（重要但可延后）

1. **扩充 D 矩阵多维度信息**
   - 修改 `testability_types.h` 数据结构
   - 更新 `DMatrixModel` 显示逻辑
   - 在 `DMatrixOptionsDialog` 中添加选项

2. **实现元件级容器的接口与行为模型自动同步**
   - 从实体元件的 `TModel` 提取端口
   - 生成容器级 `component_smt`
   - 同步端口配置

3. **完善功能管理的变量取值范围 UI**
   - 在功能管理对话框中集成 `FunctionVariableValueDialog`
   - 添加"查看变量范围"按钮

4. **验证端口配置与连接宏族的完整工作流程**
   - 在实际项目中测试自定义宏族
   - 验证宏的展开与求解

5. **编写用户操作手册**
   - 功能管理、D 矩阵、SMT 建模、端口配置

### 4.3 低优先级（可选优化）

1. **完善不同层级容器的管理界面**
   - 子系统、LRU、SRU 等的添加/删除/移动

2. **测试 D 矩阵与现有流程的集成**
   - D 矩阵数据如何被测试优选算法使用
   - D 矩阵如何与诊断决策树协同

3. **进一步代码重构**
   - 减少元件属性与本地物料库之间的代码重复
   - 提取共享验证逻辑

4. **添加视频教程或截图演示**

---

## 五、具体实现路线图

### 阶段 1: 完善核心功能（1-2周）

**任务清单**:
- [ ] 修改 `tools/init_builtin_macro_families.py` 为相对路径
- [ ] 验证内置宏族在 `templete/project.db` 中已初始化
- [ ] 编写 `tools/migrate_all_projects.py` 迁移脚本
- [ ] 在一个示例项目中测试端口配置的完整流程
- [ ] 实现链路自动构建功能（添加"自动构建链路"按钮到功能编辑对话框）
- [ ] 完善系统连接约束自动生成（根据端口数量选择宏、展开、持久化）
- [ ] 验证 D 矩阵生成与查看的完整流程

### 阶段 2: 扩展与集成（2-3周）

**任务清单**:
- [ ] 扩充 D 矩阵多维度信息（数据结构 + UI）
- [ ] 实现元件级容器的接口与行为模型自动同步
- [ ] 完善功能管理的变量取值范围 UI
- [ ] 测试功能管理的边界识别算法在复杂系统中的准确性
- [ ] 验证 D 矩阵与测试优选、诊断决策树的集成

### 阶段 3: 文档与优化（1周）

**任务清单**:
- [ ] 编写功能管理用户操作手册
- [ ] 编写 D 矩阵用户指南
- [ ] 编写 SMT 建模规范文档
- [ ] 编写端口配置与连接宏族说明文档
- [ ] 代码审查与重构（减少重复代码）
- [ ] 添加单元测试覆盖关键功能

---

## 六、风险与注意事项

### 6.1 技术风险

1. **宏族展开逻辑的复杂性**
   - 不同类型端口（电气/液压/机械）的宏展开规则不同
   - 多相数组端口（如三相电）的处理需要特别注意
   - **缓解措施**: 先在简单案例中验证，逐步扩展到复杂场景

2. **链路自动构建的准确性**
   - CAD 连线可能非常复杂（多层、交叉、中间节点）
   - 自动推导的链路可能与用户预期不符
   - **缓解措施**: 提供手动编辑功能，自动构建仅作为辅助

3. **容器模型的复杂性**
   - 元件级容器的接口继承逻辑需要仔细设计
   - 不同层级容器的等效替代逻辑（本周期暂不实现）复杂度高
   - **缓解措施**: 本周期仅聚焦元件级容器，高层级容器暂不深入

### 6.2 数据一致性风险

1. **数据库迁移风险**
   - 旧项目数据库结构不一致可能导致迁移失败
   - **缓解措施**: 迁移脚本需要充分测试，提供回滚机制

2. **SMT 模型与端口配置的同步**
   - 用户修改 `TModel` 后，端口配置可能失效
   - **缓解措施**: 提供"重新同步端口"功能，或在保存时自动检查

### 6.3 用户体验风险

1. **学习曲线**
   - 功能管理、D 矩阵、SMT 建模的概念复杂
   - 用户可能不理解如何正确使用
   - **缓解措施**: 提供详细的用户手册、示例项目、视频教程

2. **性能风险**
   - 复杂系统的 D 矩阵生成可能耗时较长
   - **缓解措施**: 添加进度条、异步处理、缓存机制

---

## 七、总结

### 7.1 整体进度评估

**完成度**: 约 **70%**

- 核心框架与数据结构: ✅ 95%
- 功能完整性: ⚠️ 60%
- 用户体验与集成: ⚠️ 50%
- 文档与测试: ❌ 20%

### 7.2 关键成就

1. D 矩阵查看与生成的基础框架已完整移植
2. 功能管理的核心逻辑已实现
3. SMT 建模与验证功能已完整集成到 UI
4. 端口配置功能已完全实现
5. 数据库表结构设计合理，可扩展性好

### 7.3 核心挑战

1. 链路自动构建功能尚未实现
2. 系统连接约束自动生成需要完善宏族选择逻辑
3. D 矩阵多维度信息扩充需要修改数据结构与 UI
4. 元件级容器的自动同步逻辑需要进一步实现
5. 用户文档严重缺失

### 7.4 建议重点

**如果时间有限，优先完成以下 3 项**:
1. ✅ 链路自动构建功能（直接影响用户工作效率）
2. ✅ 系统连接约束自动生成（核心功能完整性）
3. ✅ 编写功能管理与 D 矩阵的用户操作手册（可用性）

---

**报告结束**

**下一步行动**: 根据本报告的优先级建议，制定详细的开发计划，逐项实现剩余功能。建议先在 DemoSystem 或 DemoWorkflow 项目中测试每个功能，确保稳定后再推广到其他项目。
