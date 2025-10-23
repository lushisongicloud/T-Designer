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
  - 领域建模与层次关系请参考 `docs/hierarchical_modeling_requirements.md`，保持命名与关系图一致。
  - 在新增实体/仓库前，先补充/确认 `DO/` 层的数据结构。
  - 迁移自 Livingstone 的求解逻辑时，可参考 `MyProjects/DemoSystem/` 的业务流程与数据组织，将其状态机与 T 语言描述改写为通用 SMT 表达，并复用 `z3solverthread.*`。

## 代码风格
- 遵循根目录 `AGENTS.md` 约定：类 PascalCase，方法/变量 lowerCamelCase，4 空格缩进，UTF-8 with BOM，使用 `clang-format`（Qt/Google 风格均可，保持一致）。
- 在代码中需要使用中文的地方，请不要使用 `tr` 与 `QStringLiteral`，而是直接使用双引号字符串（如 `"中文"`）或 `QString("中文")`。
- 头/源文件成对命名；公共类型与接口放入头文件，私有实现细节留在 cpp。

## 典型目录内元素
- `containerrepository.*`：示例仓库类，负责容器/系统相关的数据装载/持久化，屏蔽底层存储细节。
- `container/`：包含 `behavioraggregator.*`、`containerdata.*` 等聚合/缓存辅助类，集中管理容器维度的业务状态。
- `behavior/`：封装求解器或复杂算法（如 `z3simplifier.*`）；保持线程安全，并通过信号返回结果。
- `function/`：包含 `functionrepository.*`、`functionanalysisservice.*`、`tmodelvalidator.*` 等函数定义/校验逻辑。
- `test/`：包含 `diagnosticmatrixbuilder.*`、`testgeneratorservice.*` 等测试流程生成器。
- `worker.*`：后台任务/计算单元，使用线程或任务并发执行，提供进度与结果信号。
- `componententity.*`、`systementity.*`：业务聚合根或领域对象的业务外观，协调 `DO/` 数据对象；其中 `systementity.cpp` 当前以 `ref/Model.db` 中的 SMT 数据为参考，用于验证系统/功能层建模。

## 测试策略（Qt Test）
- 为仓库与服务编写独立单元测试（不依赖 UI），覆盖：
  - 正常路径、边界条件与错误分支；
  - 并发/异步回调的时序与资源释放；
  - 与 `DO/` 的转换/映射一致性（例如从数据库行 -> DO 结构）。
- 测试文件放在 `tests/`，命名如 `bo_containerrepository_test.cpp`，在 `T_DESIGNER.pro` 中添加测试目标。

## 变更流程
- 新增/删除源文件后，务必更新 `T_DESIGNER.pro`（`SOURCES`/`HEADERS`）。
- 涉及数据库结构的改动，请在 `ref/` 目录下的示例数据库上读取或验证，并更新迁移/初始化逻辑；避免破坏共享示例数据。
- 调整求解器或业务流程时，请同步对照 `MyProjects/` 中的示例工程（尤其是 `DemoSystem/`），记录从 Livingstone 到 SMT/`z3` 的差异与迁移步骤。
- 禁止修改自动生成文件（如 `ui_*.h`）。

---
简述：BO 层专注业务编排与数据访问封装，不含 UI。面向 UI 暴露稳定接口，并与 `DO/`、数据库保持清晰边界。
