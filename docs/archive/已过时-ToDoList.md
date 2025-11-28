**【分类依据】本文件记录了具体的修复过程、调试分析或已过时的设计实现，作为问题解决的临时记录保留。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# T‑Designer × T‑Solver 深度集成 ToDo 列表（本周期）

目标：在 T‑Designer 中深度集成 T‑Solver 的系统建模、功能管理与 D 矩阵。以“容器层优先、最小侵入”为原则，完成从元件 SMT 建模、端口/变量一致性校验、连线 → 连接语法糖生成、功能管理重构，到 D 矩阵构建/查看的端到端整合，并保证与现有基于 D 矩阵的流程（测试优选、测试性指标预计、诊断决策树）兼容。

说明：
- 规范与原理参考 ref/T‑Solver/README.md、ref/T‑Solver/testability/*、ref/T‑Solver/widget/*。
- 数据仅落在项目数据库（项目同名 db）。模板更新遵循“项目验证 → templete/project.db 同步 → 提供 tools 迁移脚本”。
- 端口/变量命名遵循“电 i/u、液 p/q、机 F+v|n|x（其一）”与数组相位约定；支持用户自定义变量集与 connect 函数族。
- 本清单按“可独立提交的小步快跑”拆解，每一条任务可在一次交互中完成（含接口、边界与验证方式）。

---

## Phase 0 · 基线理解与对齐

- [x] 阅读与对齐 ref/T‑Solver/README.md 建模要点与接口边界（变量、端口、connect 语法糖、功能与链路、D 矩阵），记录差异点与兼容策略
- [x] 盘点 T‑Designer 现状：功能管理入口、容器层接口、现有 D 矩阵实现与 UI、T 语言校验逻辑
  - 产出：差异清单与决策笔记 docs/solver_integration_notes.md
  - 重点：液压用 p/q（代码中 connect2h 现用 p/f）；机械速度变量统一键为 v/n/x 之一（T‑Solver 现用 M）

---

## Phase 1 · 数据与持久化（项目 DB 专用）

- [x] 设计并评审项目 DB 表结构扩展（仅项目 DB；模板后置同步）
  - 新增/扩展建议：
    - component_instance_smt(id, container_id, comp_tag, smt_text, updated_at)
    - port_config(id, container_id, func_block, port_name, port_type, var_set, custom_vars_json)
    - system_smt(id, container_id, def_block, connect_block, raw_smt)
    - functions_xml(id, container_id, xml_text, updated_at)
    - dmatrix_meta(id, container_id, json_text, csv_path, updated_at)
  - 产出：SQL 草案与字段说明 docs/db_project_schema.md；验证脚本 tools/db_migrate_project.py（仅建表/幂等）

- [x] 在 MyProjects 示例库上验证新表创建、读写与回滚
  - 验证：sqlite3 与 tools/db_migrate_project.py 可正反操作

- [x] 评审通过后，同步 templete/project.db

---

## Phase 2 · 端口类型与变量集配置（双入口复用）

- [x] 新建复用控件 widget/PortConfigPanel（不侵入旧 UI，元件属性/本地物料库共用）
  - 能力：配置端口类型（电/液/机/其他）、默认变量集（i/u、p/q、F+v|n|x）、自定义变量集与自定义连接宏族（文本 → 展开式 SMT）
  - 接口：load(containerId)、save(containerId)、validate()

- [x] 将 PortConfigPanel 嵌入：
  - 元件属性 dialogUnitAttr.ui → "端口配置"页；
  - 本地物料库 dialogunitmanage.ui → "功能子块/端口配置"页。
  - 产出：装配代码与保存逻辑，统一走 port_config 表
  - **实现方案调整**：不使用独立的 PortConfigPanel tab页，而是与 tableTerm 深度集成
    - 在 tableTerm 增加"变量"列（第3列）显示端口配置的变量
    - 通过右键菜单打开 PortConfigEditDialog 编辑单个端口配置
    - 新建 widget/PortConfigEditDialog 对话框用于编辑单个端口
    - 实现 getPortVariables() 方法从 port_config 表读取变量并显示
    - 右键菜单提供"配置端口"和"删除配置"功能
    - tableTerm 列结构：0-子块代号, 1-端号, 2-描述, 3-变量, 4-测试代价, 5-已标注, 6-图片路径
  - **连接宏族支持**：
    - 数据库表：port_connect_macro_family（family_name, domain, description, is_builtin, macros_json）
    - 内置宏族：electric-connect（包含connect2e/3e/4e）、hydraulic-connect（包含connect2h/3h/4h）、mechanical-connect（包含connect2m/3m/4m）
    - 用户可添加自定义宏族，但内置宏族不可删除
    - 端口配置时选择宏族名称（如"electric-connect"），系统在生成连接时根据端口数自动选择对应宏（如3个端口相连时自动选择connect3e）
  - **已完成验证**：
    - ✅ port_config 表结构正确，包含所有必需字段
    - ✅ PortConfigEditDialog 的 SQL 操作正确（INSERT/UPDATE/DELETE）
    - ✅ m_componentContainerId 在两个对话框中正确设置和使用
    - ✅ getPortVariables() 正确从 port_config 读取并格式化变量
    - ✅ 右键菜单功能完整实现（showTableTermContextMenu, onConfigurePort, onRemovePortConfig）
    - ✅ 列号调整完成，所有涉及 tableTerm 的代码已更新为7列结构
    - ✅ 连接宏族管理功能实现（添加/删除宏族按钮，内置宏族保护）
    - ✅ 编译成功，无错误无警告
  - 详见：docs/phase2_implementation_summary.md 和 docs/port_config_fixes_summary.md

- [x] 变量集与连接宏族的规则落地文档 docs/port_variable_rules.md（含多相数组、层级端口）
  - 待补充：完整的宏族展开规则与多相数组处理细节

---

## Phase 3 · SMT 校验（语法 + 端口一致性）

- [x] 语法校验器：基于 Z3 解析（移植/复用 ref/T‑Solver/BO/systementity.cpp 中 parse_string/错误处理）

  - 新建 BO/function/SmtSyntaxChecker.{h,cpp}（输入 smt_text，输出错误行列与消息；离线可用）

- [x] 端口一致性校验器：扩展现有 BO/function/tmodelvalidator.* 支持多类型/多变量集
  - 支持：电(i/u)、液(p/q)、机(F+v|n|x 其一)、数组 select；占位符 %MARK%、多级端口名
  - 输出：缺失声明、未匹配变量、未使用端口、提示
- [x] 统一校验入口：
  - 元件属性 “T语言模型”页按钮 → 语法	+一致性合并反馈
  - 本地物料库 “T语言模型”页按钮 → 复用同一后端
  - 产出：widget/codecheckdialog 可重用弹窗/报告

- [ ] 离线批量脚本 tools/validate_smt_snippets.py（扫描工程/库并生成报表）

- [ ] 验证用例：tests/smt_validator_cases/…（正/反例各 5+，涵盖电/液/机、数组、占位符）

---

## Phase 4 · 连线 → 连接语法糖生成（Cad→SMT）

- [ ] 采集连线语义：复用现有连线表与功能子块端口映射（见 common.cpp:GetLinkRoadBySymbol, SystemStructure 等）

- [ ] 实现连接宏族管理：
  - 数据库表 port_connect_macro_family：family_name, domain, description, is_builtin, macros_json, created_at
  - 内置宏族初始化脚本：tools/init_builtin_macro_families.py
  - 三个内置宏族：electric-connect（包含connect2e/3e/4e）、hydraulic-connect（包含connect2h/3h/4h）、mechanical-connect（包含connect2m/3m/4m）
  - 宏族的macros_json格式：`[{arity:2, macro_name:"connect2e", expansion:"..."}, {arity:3, ...}, ...]`
  - UI支持：在PortConfigEditDialog中显示可用宏族、添加/删除自定义宏族（内置宏族不可删除）

- [ ] 生成连接语句：根据连接点端口数自动选择合适的连接宏
  - 新建 BO/behavior/ConnectSugarGenerator.{h,cpp}
  - 接口：generate(containerId, port_map, variable_sets) → QStringList connect_lines
  - 规则：
    - 电：i 守恒 + u 等势（从electric-connect宏族中根据端口数选择connect2e/3e/4e）
    - 液：q 守恒 + p 等势（从hydraulic-connect宏族中根据端口数选择connect2h/3h/4h）
    - 机：F 守恒 + 速度/转速/位移等势（按端口配置选择 v|n|x，从mechanical-connect宏族中选择connect2m/3m/4m）
    - 多相：select .i[0/1/2] 按相展开

- [ ] 系统模型拼接器：SystemModelAssembler.{h,cpp}
  - 输出 system_smt.def_block、connect_block、raw_smt；保存在 system_smt 表

- [ ] 单元测试：tests/connect_sugar/*.json → 断言展开后 SMT 片段包含预期约束

---

## Phase 5 · 功能管理（重构与贯通）

- [x] 引入/复用功能 XML 结构与计算逻辑（参考 ref/T‑Solver/widget/selectfunctiondialog.* 与 FunctionInfo 结构）
  - ✅ 新建 BO/function/FunctionRepository 读写 functions_xml（树结构、链路、依赖、约束、属性、离线结果、变量范围）

- [x] 链路裁剪与边界识别：复用 DO/model.{h,cpp} 中 SystemStructure；提供 crop + boundary API
  - ✅ 新增 BO/function/SystemStructureService 提供 `analyze/cropSystemDescription/boundaryComponents` 三项接口

- [x] 约束完整性检查：正向/反向执行器约束 + SAT 完整性评估，写回 constraintIntegrity
  - ✅ SelectFunctionDialog 通过 SystemStructureService 裁剪模型、正/反向 SAT 求解更新 constraintIntegrity，界面编辑即时回写并触发“未检查”状态管理

- [x] 变量范围配置与 SAT 样本：复用/移植 ref/T‑Solver/function_variable_config.* 与 variable_range_config.* 能力
  - ✅ FunctionEditDialog 挂载 FunctionVariableValueDialog，支持变量类型/范围/SAT 样本编辑并持久化 VariableConfigXml
  - UI：在 functioneditdialog.ui 增加“变量取值范围”入口（对齐 T‑Solver 交互）

- [x] UI 贯通：
  - 在项目导航“功能管理”入口调用新的 FunctionManagerDialog（可逐步替换现有 selectfunctiondialog 入口）
  - 支持：自动查找依赖功能、自动查找边界条件、执行器取反完整性检查、离线求解结果缓存

- [x] SAT 会话与增量求解：复用 ref/T‑Solver/BO/systementity::createIncrementalSolveSession 与 SmtFacade

- [x] 用例：在 DemoSystem/ 或新样例上录入 3+ 个功能，验证完整性与边界识别

---

## Phase AI · DeepSeek 自动建模

- [x] 批量自动编写：BtnBatchAutoGenerate 轮询最小类别（每轮每类最多 10 个）+ DeepSeek 长连 session 复用 + 日志断点续作（复用单器件自动编写逻辑）

---

## Phase 6 · D 矩阵（构建/查看/存储）

- [ ] 移植并适配 DMatrixBuilder（ref/T‑Solver/testability/d_matrix_builder.*）
  - 扩展：
    - 测试维度：复杂性、费用、时间、成功率、备注（元数据字段）
    - 故障维度：先验概率、影响严重度、备注
  - 结果入库：dmatrix_meta.json_text + csv_path（路径相对工程）

- [ ] 视图对齐：复用/移植 DMatrixViewerDialog（ref/T‑Solver/widget/dmatrixviewerdialog.*）作为“依赖矩阵”页的主视图
  - 增加“保存/另存为”同步启停状态到元数据 JSON

- [ ] 与现有流程对接：
  - TestManagementDialog 复用结果（或嵌入查看器）并保持按钮逻辑：测试优选、指标预计、诊断树
  - DiagnosticMatrixBuilder 与新 D 矩阵互通（如需，提供适配层）

- [ ] 用例：构建样例矩阵 → 导出 CSV/JSON → 重新载入并切换显示开关

---

## Phase 7 · 容器层集成（元件级优先）

- [ ] 元件级容器行为：新增 ContainerBehaviorAdapter.{h,cpp}
  - 从实体元件读取：功能子块（端口）、元件 SMT、端口配置
  - 输出：容器级接口（端口变量清单）、容器级 SMT 正常/故障模式（直接继承单元）

- [ ] 系统层/子系统层拼装：BehaviorAggregator 增强“平行组合 + 内部连线折叠”为容器等效描述（当前阶段保守：不自动等效化简，仅封装并汇聚）

- [ ] 与 Function/DMatrix 对接：以容器为最小分析单元，函数依赖与测试映射至容器上下文

- [ ] 用例：插入 2 个元件 → 自动生成 2 个元件容器 → 构建系统连接 → 功能与 D 矩阵可用

---

## Phase 8 · 工具与脚本

- [ ] tools/db_migrate_project.py：项目 DB 建表/升级；带 --dry-run、--apply
- [ ] tools/validate_smt_snippets.py：批量语法/一致性校验（输出 CSV 报告）
- [ ] tools/generate_demo_project.py：按演示案例创建 MyProjects/… 工程骨架、DB、示例 SMT/功能/连接

---

## Phase 9 · 测试与验证（WSL 可运行子集）

- [ ] tests/smt_validator_cases：基于文本与脚本验证语法/一致性（不依赖 GUI/axcontainer）
- [ ] tests/connect_sugar：输入端口映射与连线 → 断言 connect 语句展开
- [ ] tests/function_crop_boundary：功能链路裁剪与边界识别正确性
- [ ] tests/dmatrix_smoke：小模型构建 D 矩阵并导出 CSV/JSON（调用构建器，不启 UI）

---

## Phase 10 · 演示链路（端到端）

- [ ] 扩展 demo_projectbuilder（demo_projectbuilder.*）以新 DB 结构生成演示工程：
  - 元件：开关电源、断路器、指示灯、导线、保险丝（含 2–3 个故障模式）
  - 端口配置：电/液/机各 1 例；3 相示例 1 例
  - 自动：拼接 DEF/CONNECT/RAW、生成功能、构建 D 矩阵、导出 CSV/JSON

---

## Phase 11 · 文档与指南

- [ ] 使用指南：docs/integration_user_guide.md（端口配置、SMT 书写、功能与 D 矩阵流程）
- [ ] 开发指南：docs/integration_dev_guide.md（模块职责、关键接口、扩展点）
- [ ] 迁移说明：docs/migration_notes.md（旧 T 语言 → SMT、变量命名、脚本用法）

---

## Phase 12 · 兼容性与质量

- [ ] Z3 超时/unknown 处理与错误日志落地（复用 T‑Solver 的日志写入逻辑）
- [ ] 大模型性能保护：链路裁剪、变量范围约束、SAT 缓存（DMatrixBuilder 已内置）
- [ ] 错误提示与回滚：校验失败不得写库，提示未使用端口与修复建议

---

# 任务分解明细（可直接实施）

以下每一条为可在一次提交中完成的小任务，含输入/输出与主要改动点。

1) DB 建表脚本（项目库）
- [ ] 新增 tools/db_migrate_project.py：创建/升级 Phase 1 五类表，支持 --dry-run/--apply
- [ ] 文档 docs/db_project_schema.md 落库

2) 端口配置控件
- [ ] 新增 widget/portconfigpanel.h/.cpp/.ui，持久化至 port_config 表
- [ ] 在 dialogUnitAttr.ui:1272 与 dialogunitmanage.ui 嵌入并连通保存按钮

3) SMT 语法校验器
- [ ] 新增 BO/function/smtsyntaxchecker.h/.cpp；用 z3::context.parse_string() 校验 + 结构化错误
- [ ] 在 widget/codecheckdialog.cpp 接入，复用现有弹窗

4) 端口一致性校验（多类型）
- [ ] 扩展 BO/function/tmodelvalidator.*：支持 i/u、p/q、F+v|n|x、select(array …)
- [ ] 在 dialogUnitAttr.cpp:1345 处改为“语法+一致性”合并校验

5) 连接语法糖生成
- [ ] 新增 BO/behavior/connectsugargenerator.h/.cpp：电/液/机/多相展开
- [ ] 新增 BO/behavior/systemmodelassembler.h/.cpp：拼接 DEF/CONNECT/RAW，写入 system_smt

6) 功能仓库与 UI 贯通
- [x] 新增 BO/function/functionrepository.h/.cpp：functions_xml 读写
- [ ] 扩展 widget/functionmanagerdialog.* 集成功能编辑与“变量取值范围”入口

7) 变量范围与 SAT 样本
- [ ] 复用/移植 ref/T‑Solver/function_variable_config.* 与 variable_range_config.* 至 BO/function/
- [ ] 在 FunctionManagerDialog 中调用，写回 functions_xml

8) SmtFacade 与增量会话
- [ ] 复用/移植 ref/T‑Solver/testability/smt_facade.* 至 BO/behavior/
- [ ] 在构建/校验/功能完整性时统一走 facade + 增量会话

9) D 矩阵构建
- [ ] 复用/移植 ref/T‑Solver/testability/d_matrix_builder.* 至 BO/test/
- [ ] 将结果写入 dmatrix_meta，扩展维度字段（复杂性/费用/时间/成功率/备注、概率/严重度）

10) D 矩阵查看器
- [ ] 复用/移植 ref/T‑Solver/widget/dmatrixviewerdialog.* 至 widget/
- [ ] 在 TestManagementDialog 内提供“查看依赖矩阵（新）”按钮打开查看器

11) 测试样例与 CI（WSL 可跑）
- [ ] tests/smt_validator_cases/*、tests/connect_sugar/*、tests/function_crop_boundary/*、tests/dmatrix_smoke/*
- [ ] 轻量脚本驱动，不依赖 GUI 或 axcontainer

12) Demo 扩展
- [ ] 扩展 demo_projectbuilder.*：写入新表/示例功能/构建矩阵/导出

13) 模板同步
- [ ] 工程验证通过后，同步 templete/project.db；记录版本并更新 docs/migration_notes.md

---

## 已知差异与兼容策略（执行中核对）

- 液压变量名：README 约定 p/q，现 T‑Solver connect2h 使用 p/f → 统一迁移为 p/q（保留别名映射以兼容旧模型）。
- 机械速度键：README 约定 v|n|x（其一），现 T‑Solver 使用 M → 统一为 v（默认），端口配置可切换为 n/x；保留旧键别名。
- 多相数组：统一 select X.i 0/1/2；函数族 connect2e(3P,…)/connect3e(3P,…)/… 负责展开。

---

## 里程碑与验收口径

- M1（校验可用）：端口配置 + SMT 校验（语法/一致性）在两处界面可用；批量脚本可出报表。
- M2（建模贯通）：连线 → 连接语句自动生成；系统 SMT 拼接入库；功能管理可执行完整性检查并生成 SAT 样本。
- M3（分析闭环）：D 矩阵构建/查看/导出可用；与现有测试优选/预计/诊断树兼容。
- M4（容器整合）：元件级容器端到端贯通演示样例（2–3 组件），各层接口稳定。

---

备注：
- WSL 环境限制：不运行 axcontainer 相关；优先实现可在 WSL 下单测/静态校验的模块。
- 代码风格：Qt 5.12，4 空格缩进，UTF‑8，LF；遵循仓内现有模式，必要处最小侵入修改。
