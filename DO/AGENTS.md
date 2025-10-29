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
  - 明确拷贝/移动语义与所有权；必要时显式实现 Rule of Five。
- 数据完整性：
  - 不变量保障（构造即有效）；可空字段使用 `std::optional<T>` 或约定空值。
  - 提供 `operator==`/`qHash`（如需放入 `QSet/QHash`）。
- 序列化：
  - 如需 JSON/二进制持久化，提供 `toJson()`/`fromJson()` 或等价静态工厂；保持与 `BO` 的数据库映射一致。
- 命名与建模：
  - 与层次模型术语一致（System/Subsystem/LRU/SRU/模块/子模块/元件/容器）。
  - 参考 `ref/T-Solver/README.md` 与 `ref/Model.db` 的字段与语义，便于对接 `z3`。

## 本周期数据建模要点（SMT/功能/D 矩阵）
- 组件与端口
  - PortSchema：端口类型（电/液/机/其他）、端号集合、变量集合（默认 i/u、p/q、F+v|n|x；支持自定义）。
  - VariableDecl：SMT 变量声明与命名空间（如 `KM1.Coil.A1.i`）。
  - 支持用户自定义变量与 connect 函数族；以键控方式持久化（名称、参数个数、展开模板）。
- SMT 文本
  - ComponentSmt：`variable`（声明）、`description`（正常模式）、`failuremode`（XML-like），保留 `%<mark>%` 与参数占位符。
  - SystemSmt：`DEF` 定义块、连接（connect2e/h/m 等）与原生 SMT（`rawsmt`）。
- 功能定义
  - FunctionDefine：名称、link、dependency（器件/功能三元组串）、约束（变量/值/置信度/类型）、属性（Persistent|NotPersistent, 先验）、离线解（集合）。
  - VariableRangeConfig：全局变量类型范围；variableValueConfig：每功能的样本与可行区间。
- D 矩阵
  - DMatrix：测试×故障的依赖性与权重；扩展测试维度（复杂性/费用/时间/成功率/备注）、故障维度（概率/严重度/备注）。
- 容器
  - ComponentContainer：元件级容器数据快照（代理单一实体元件），其接口与行为模型直接继承包含的实体元件；在容器层保存 SMT/功能/测试性相关数据视图，减少对实体元件的侵入。

## 代码风格
- 遵循根目录 `AGENTS.md`：类 PascalCase，字段/访问器 lowerCamelCase，4 空格缩进，UTF-8 with BOM，`clang-format`。
- 中文字符串：使用双引号或 `QString("中文")`，不要使用 `tr`/`QStringLiteral`。
- 头/源文件成对；头文件最小包含，尽量前置声明。

## 典型目录内元素
- `component.*`、`model.*`、`diagnosisgraph.*`、`parameter.*`：领域数据结构；避免 UI/DB 依赖。
- `containerentity.h`：容器数据结构，与 BO 中聚合根呼应但职责纯数据化。

## 测试策略（Qt Test）
- 覆盖：构造/不变量、等值与哈希、序列化往返、边界与异常输入。
- 命名：`do_<type>_test.cpp`；在 `T_DESIGNER.pro` 添加测试目标。

## 变更流程
- 新增/删除数据结构：同步 `BO` 仓库/服务映射；如影响 UI，通知 `widget/` 更新模型。
- DB 表/字段变更：先用 `MyProjects/<Project>/<Project>.db` 验证；通过后用 `tools/` 脚本更新 `templete/project.db`；必要时更新示例。
- 更新 `T_DESIGNER.pro` 的 `SOURCES`/`HEADERS`；禁止修改 `ui_*.h`。

---
简述：DO 层聚焦数据与最小行为，补齐 SMT/功能/D 矩阵所需结构，为 BO 层提供稳定的数据载体。
