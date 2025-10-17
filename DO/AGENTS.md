# AGENTS 指南 — DO（数据对象层）

本文件适用于 `DO/` 目录及其子目录中的所有文件，指导数据对象（Domain/Data Objects）的设计与实现。

## 角色与边界
- 职责：承载领域数据与最小必要行为（如等值比较、拷贝/移动、序列化辅助）。
- 依赖：仅使用与平台无关的 QtCore/标准库类型（`QString/QVector/QMap/QUuid/std::*` 等）。
- 禁止：
  - 与 UI/Widgets、文件对话框等交互。
  - 直接数据库访问与 SQL 语句（数据库映射放在 BO 的 Repository 内）。
  - 复杂业务流程与线程操作。

## 设计准则
- 轻量与值语义优先：
  - 小对象可值传递；大对象使用 `const &` 传递。
  - 明确拷贝/移动语义与所有权；避免隐式共享踩坑（必要时显式实现 Rule of Five）。
- 数据完整性：
  - 提供基本不变量保障（构造即有效）；如需可空字段，使用 `std::optional<T>` 或约定的空值。
  - 提供 `operator==`/`qHash`（如需放入 `QSet/QHash`）。
- 序列化：
  - 如需 JSON/二进制持久化，提供 `toJson()`/`fromJson()` 或等价静态工厂；保持与 `BO` 的数据库映射一致。
- 命名与建模：
  - 与 `docs/hierarchical_modeling_requirements.md` 中的术语与层次一致（例如 Component/Container/System 等）。

## 代码风格
- 遵循根目录 `AGENTS.md`：类 PascalCase，字段/访问器 lowerCamelCase，4 空格缩进，UTF-8 with BOM，`clang-format`。
- 在代码中需要使用中文的地方，请不要使用 `tr` 与 `QStringLiteral`，而是直接使用双引号字符串（如 `"中文"`）或 `QString("中文")`。
- 头/源文件成对；头文件尽量最小化包含，使用前置声明降低编译耦合。

## 典型目录内元素
- `component.*`、`model.*`、`diagnosisgraph.*`、`parameter.*`：面向领域的数据结构与算法辅助类型；避免引入 UI/DB 依赖。
- `containerentity.h`：与 BO 层的聚合根命名保持一致，但在 DO 层仅表示纯数据形态（若存在同名，注意层内职责差异）。

## 测试策略（Qt Test）
- 覆盖：构造/不变量、等值与哈希、序列化往返（round-trip）、边界与异常输入。
- 测试文件位于 `tests/`，命名建议 `do_<type>_test.cpp`，在 `T_DESIGNER.pro` 添加测试目标。

## 变更流程
- 新增/删除数据结构时：
  - 同步更新与之交互的 `BO` 仓库/服务的数据映射与用例；
  - 如影响 UI 展示，通知 `widget/` 维护者更新视图/模型。
- 更新 `T_DESIGNER.pro` 中的 `SOURCES`/`HEADERS`。禁止修改自动生成文件（`ui_*.h`）。

---
简述：DO 层专注纯数据建模与最小行为，实现可测试、可复用、无 UI/DB 依赖的领域对象。

