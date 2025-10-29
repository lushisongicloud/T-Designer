# AGENTS 指南 — BO（业务对象层）

本文件适用于 `BO/` 目录及其子目录中的所有文件，指导在该层进行的开发与改动。请在修改或新增文件前先通读本指南，并遵循仓库根目录的 `AGENTS.md` 与 `T_DESIGNER.pro` 规范。

## 角色与边界
- 职责：封装业务规则与用例编排（Service/Repository/Worker 等），将 UI 与数据对象解耦。
- 依赖：
  - 可依赖 `DO/` 数据对象与公共工具（如 `common.*`）。
  - 如需数据库访问，请通过仓库/数据访问类实现（示例：`containerrepository.*`），可使用 `sqlitedatabase.*` 封装，不直接在 UI 层访问数据库。
  - 禁止依赖 Qt Widgets 与具体 UI 组件；优先使用 QtCore/QtSql。
- 输出：为 UI 层（`widget/` 与 `mainwindow.*`）提供清晰、稳定的接口（面向对象接口或信号/槽）。

## 设计准则
- 接口设计：
  - 面向用例与领域模型，提供明确的方法命名与职责划分。
  - 避免单例与全局可变状态；优先依赖注入（在构造函数或显式 setter 传入依赖）。
  - 长时操作使用异步（`QThread`/`QRunnable`/`QtConcurrent`），通过信号返回结果；不得阻塞 UI 线程。
- 数据与错误处理：
  - 入参与出参尽量使用 `const &` 或值语义（小对象），指针所有权清晰（`unique_ptr`/`shared_ptr`/裸指针仅作非拥有引用）。
  - 明确区分“无数据”和“失败”（例如返回 `std::optional<T>` 与错误码/错误对象）。
- 与模型规范对齐：
  - 新增实体/仓库前，先补充/确认 `DO/` 层的数据结构。
  - 迁移自 Livingstone 的求解逻辑时，参考 `MyProjects/DemoSystem/` 的流程与组织，将 T 语言描述改写为通用 SMT 表达，复用 `z3solverthread.*`。

## 本周期重点（T‑Solver 深度集成）
- SMT‑LIB 迁移与校验（BO/function）
  - 在 `tmodelvalidator.*` 基础上扩展：提供 1）SMT 语法校验，2）端口与变量一致性校验（与元件端口设置、功能子块端号对齐）。
  - 接口形态：`ValidationResult validateComponentSmt(const QString& smt, const PortSchema& schema)`；返回语法错误、未声明变量、缺失变量、端口/变量冲突清单。
  - 统一服务：供 “本地物料库/元件属性” 两处 UI 共用。
- 端口/变量体系与连接语法糖（BO/behavior + BO/function）
  - 端口类型电/液/机 → 变量集分别为 `i/u`、`p/q`、`F`+`v|n|x`（按元件选一）；允许自定义变量与 connect 函数族（注册表）。
  - 提供连接生成器：从 CAD 连线语义生成 `connect2e/3e`、`connect2h/3h`、`connect2m/3m` 约束（最终展开为 SMT 断言）。
  - 数组端口（1P/3P）按索引展开到 `(select X.i k)`。
- 容器优先实现（BO/container）
  - 元件级容器代理其包含的单一实体元件接口/行为；新增 SMT 建模/功能管理逻辑尽量落在容器与聚合器中（`behavioraggregator.*`）。
  - 从实体元件读取功能子块/端口设置，构造容器层的 SMT 变量命名空间（如 `K1.Coil.A1.i`）。
- 功能管理重构（BO/function）
  - 参考 `ref/T-Solver/README.md`：链路解析/裁剪、依赖功能展开、边界补全、离线解缓存（`offlineSolveResult`）。
  - 仓库接口：读/写功能定义（树结构、link、dependency、constraint、属性、样本与范围配置）。
  - 依赖三元组串行化存储与合并规则与 T‑Solver 保持一致。
- D 矩阵（BO/test）
  - 对齐 T‑Solver 的数据结构，扩展测试维度（复杂性/费用/时间/成功率/备注）与故障维度（概率/严重度/备注）。
  - 提供生成、合并、过滤、加权计算接口；与既有“测试优选/指标预计/诊断决策树”流程兼容。
- 数据持久化（BO/*Repository）
  - 仅使用项目 db 存储（项目同名 `.db`）；模板库字段更新需先在项目验证，再用 `tools/` 迁移脚本更新 `templete/project.db`。

## 目录指引
- `containerrepository.*`：容器/系统数据装载与持久化，屏蔽 DB 细节。
- `container/`：`behavioraggregator.*`、`containerdata.*` 聚合容器态业务；容器层 SMT/功能/测试性能力的主落点。
- `behavior/`：求解相关算法与工具（`z3simplifier.*` 等），线程安全，信号/槽返回结果。
- `function/`：`functionrepository.*`、`functionanalysisservice.*`、`tmodelvalidator.*`；新增链路/依赖/裁剪/校验与 SAT 调用准备逻辑。
- `test/`：`diagnosticmatrixbuilder.*`、`testgeneratorservice.*`；按新维度扩展，提供权重策略接口。
- `componententity.*`、`systementity.*`：系统/组件业务外观，负责把数据与求解准备整合给上层。

## 代码风格
- 遵循根目录 `AGENTS.md`：类 PascalCase，方法/变量 lowerCamelCase，4 空格缩进，UTF-8 with BOM，`clang-format`。
- 中文字符串：使用双引号或 `QString("中文")`，不要使用 `tr`/`QStringLiteral`。
- 头/源文件成对；公共接口在头文件，私有实现留在 cpp。

## 测试策略（Qt Test）
- 覆盖点：
  - SMT 语法与端口一致性校验（正/反例用例集）。
  - CAD→连接语法糖→SMT 展开正确性（电/液/机、2/3 端、1P/3P）。
  - 链路裁剪、依赖展开与边界补全；offline 结果序列化往返。
  - D 矩阵生成/合并/过滤与权重策略。
- 命名：`bo_<area>_test.cpp`；在 `T_DESIGNER.pro` 添加测试目标。

## 变更流程
- 新增/删除源文件：更新 `T_DESIGNER.pro`（`SOURCES`/`HEADERS`）。
- DB 结构调整：先在 `MyProjects/<Project>/<Project>.db` 验证；评审后用 `tools/` 脚本更新 `templete/project.db`。
- 对照 `ref/T-Solver/README.md` 与 `MyProjects/DemoSystem`，记录从 Livingstone→SMT 的差异与迁移要点。
- 禁止修改自动生成文件（如 `ui_*.h`）。

---
简述：BO 层专注业务编排与数据访问封装，本周期新增 SMT/功能管理/D 矩阵能力落在容器与服务上，向 UI 暴露稳定接口。
