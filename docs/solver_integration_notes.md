# Solver Integration Notes

## Reviewed Sources
- README.md（本周期总体目标与实现要点）
- ref/T-Solver/README.md（T-Solver 建模、功能、D 矩阵规范）
- 现有 T-Designer 实现：
  - BO/systementity.cpp（连接语句生成）
  - BO/function/tmodelvalidator.cpp、functionanalysisservice.cpp、functionrepository.cpp
  - widget/functioneditdialog.cpp、testmanagementdialog.cpp
  - BO/test/diagnosticmatrixbuilder.* 等

## 变量与端口命名
| 维度 | T-Solver 规范（README） | ref/T-Solver 现有代码 | T-Designer 当前实现 | 差异与影响 | 决策/兼容策略 |
| --- | --- | --- | --- | --- | --- |
| 电气端口 | `.i`（电流）、`.u`（电压） | 一致 | TModelValidator 仅识别 `.i`/`.u` | 无差异，但校验器仅覆盖电气 | 扩展校验器时保留现行规则 |
| 液压端口 | `.p`（压力）、`.q`（流量） | connect2h/connect3h 使用 `.p` / `.f` | 无液压特化逻辑；校验器不识别 | 代码使用 `.f` 表示流量，违背 README；T-Designer 尚未支持 | 统一标准为 `.p`/`.q`；在解析/生成时兼容旧 `.f`（读写时自动映射）；更新连接语句与校验器 |
| 机械端口 | `.F`（力）与 `.v`/`.n`/`.x` 三选一（速度/转速/位移） | connect2m/connect3m 使用 `.F` / `.M` | 仅存在 `.F`、`.M`；UI 无类型配置 | `.M` 与 README 不符；无办法区分速度/转速/位移 | 统一推荐键为 `.v`（默认），允许在端口配置中切换 `.n`/`.x`；解析旧 `.M` 时写入配置映射；生成时按配置输出 |
| 自定义变量 | README 允许用户自定义 | 代码未提供接口 | 缺省 | 未能覆盖扩展需求 | Phase 2 中通过 PortConfigPanel 支持自定义集合与别名 |

备注：迁移后需提供自动校正工具（如 scripts/port_alias_migrator）批量替换旧 `.f`、`.M`，并在模型加载时保留双向兼容（读取旧库 → 转为新命名；写回时使用新命名）。

## 连接语法糖（connect 系列）
- README 覆盖：connect2e/3e、connect2h/3h、connect2m/3m 与多相（1P/3P）数组展开。
- ref/T-Solver 实现：
  - 电气：实现完整（含 1P/3P）
  - 液压：使用 `.f`/`.p`，无 1P/3P 支持
  - 机械：使用 `.F`/`.M`，无 1P/3P；未处理可变速度键
- T-Designer 现状：
  - 仅实现 connect2e/3e、connecte（多端）、connect2m/3m；缺失 connect2h/3h 与 1P/3P 语法
  - 机械同样固定 `.F`/`.M`

差异与策略：
1. 新建 ConnectSugarGenerator 统一生成语法糖：
   - 电气：保持现有公式；保留 1P/3P 支持并在输出中使用 `(select X.i idx)`。
   - 液压：统一输出 `.q`/`.p`，为旧 `.f` 提供读取兼容；扩展 1P/3P 支持。
   - 机械：输出 `.F` 与配置选择的速度键（`.v` 默认）；若读取旧 `.M`，记录在端口配置别名中。
2. SystemModelAssembler 生成 DEF/CONNECT/RAW 时调用语法糖生成器，确保 CAD → SMT 转换遵循统一规则。
3. 校验器、可视化工具同时使用端口配置映射，避免硬编码。

## 功能定义与链路
- README/T-Solver：功能以 XML 存储，包含：
  - `link`（求解空间）、器件/功能依赖、边界条件
  - 变量约束及类型、典型值/区间、SAT 样本
  - 约束完整性状态、离线求解结果
- 当前 T-Solver 代码：SelectFunctionDialog/FunctionVariableConfig 支持自动查找依赖、链路裁剪、变量范围求解等。
- T-Designer 现状：
  - FunctionRepository 使用关系表（Function + function_bindings），字段仅涵盖执行器列表、链路字符串、依赖文本、先验概率等，不含变量配置、离线结果。
  - FunctionAnalysisService 仅基于 CAD 链路生成粗略链路/依赖；无 SAT 校验、反向执行器、变量范围等。
  - UI（FunctionEditDialog）仅允许手工录入变量目标值；无变量范围对话框、约束完整性检测。

差异与策略：
1. 引入 functions_xml 表保存完整 XML 结构，与 T-Solver 格式一致，便于复用现有解析/编辑逻辑。
2. 重构 FunctionManagerDialog：嵌入 T-Solver 的链路裁剪、依赖分析、变量范围配置与离线求解能力；现有关系表保留为兼容读写，可在迁移时一并导入 XML。
3. 更新 FunctionRepository：
   - 读取旧表 → 组装基础 XML（占位缺省值）。
   - 读写新表 → 完整同步 FunctionInfo、variableRangeConfig、offlineSolveResult。
4. SAT 会话统一走 SystemEntity::createIncrementalSolveSession/SmtFacade，确保功能编辑与 D 矩阵共用模型片段。

## D 矩阵生成与查看
- README/T-Solver：
  - DMatrixBuilder 根据功能/测试定义、SAT 判定结果生成 detectability，记录 normalSat/faultSat/guaranteed/metric 等细节。
  - DMatrixViewerDialog 提供测试/故障维度开关、启用状态保存（JSON 元数据）。
- T-Designer：
  - DiagnosticMatrixBuilder 基于 GeneratedTest.detectableFaults / isolatableFaults 简单推导覆盖率；无 SAT 校验。
  - TestManagementDialog 的“依赖矩阵”页仅显示静态表格；无 viewer、无启停状态保存、无扩展维度（费用、时间、备注等）。

差异与策略：
1. 复用 T-Solver DMatrixBuilder（含 SAT 缓存、自适应区间求解），扩展元数据存储字段以覆盖本周期新增维度（复杂性/费用/时间/成功率/备注、故障概率/严重度等）。
2. 将构建结果与元数据写入 dmatrix_meta 表（JSON + CSV 路径），保持与 viewer 的保存/另存为逻辑一致。
3. 引入 T-Solver 的 DMatrixViewerDialog 作为 TestManagementDialog 的查看组件，维持启用状态同步。
4. 为现有 DiagnosticMatrixBuilder 保留兼容层（过渡期可读取旧 GeneratedTest 列表，逐步切换至 SAT 判定结果）。

## 补充观察
- TModelValidator 目前只检查 `.i`/`.u` 的 declare/assert，引擎需扩展以覆盖 `.p`/`.q`、`.F` 与可配置速度键，并识别 `select`（数组）访问模式。
- 当前项目数据库缺少存放 SMT/功能 XML/D 矩阵结果的表，本周期需新增并通过迁移脚本维护。
- T-Solver 代码中存在日志（z3_error_*.txt）与错误处理逻辑，应在 T-Designer 中延续，方便排查模型问题。

## 下一步建议
1. 在 PortConfigPanel 设计阶段确定变量键别名映射策略，确保旧模型加载时自动转换。
2. 定义功能 XML 与关系表之间的迁移工具，支持双向同步（旧数据 → XML、XML → UI）。
3. 制定 D 矩阵元数据 JSON schema，明确新增维度字段名与类型，便于前后端共用。
4. 在测试目录新增针对语法/连接/功能/D 矩阵的基准用例，验证上述决策的正确性。

