# AGENTS 指南 — ref（参考资料与离线样本）

本文件适用于 `ref/` 目录及其子树。该目录存放离线参考数据库、示例代码与 T‑Solver 仓库快照，用于对照、验证与迁移，不直接作为运行时数据源。

## 目录内容
- `LdMainData.db`：本地物料库离线镜像，仅供参考与比对；运行时实际加载 `C:/TBD/data/LdMainData.db`。
- `Model.db`：包含实体元件、系统的 SMT 描述与功能定义的离线样本；用于设计/验证字段结构与解析逻辑。
- `T-Solver/`：T‑Solver 的参考实现与说明文档，重点阅读 `ref/T-Solver/README.md` 了解：
  - 器件/系统的 SMT 建模约定与变量命名；
  - `DEF`/`connect2e|3e`/`rawsmt` 等语法，以及功能建模与依赖管理；
  - D 矩阵数据结构、UI 交互与扩展字段。
- `diagnosis_mainwindow.cpp`、`matrix_d_class.*`：历史实现与算法参考，仅作对照。

## 使用规则
- 不修改：`LdMainData.db` 与 `Model.db` 不直接改写；如需试验，请复制至 `MyProjects/<Project>` 后操作。
- 参考优先：实现新功能时以 README 与此处样本为蓝本，对齐命名与字段；具体代码请在项目内实现，不依赖拷贝的 ref 源码。
- 一致性：当项目侧实现与 T‑Solver 约定存在差异时，须在提交说明中记录理由与兼容策略。

## 与项目的边界
- 运行时数据仅来自项目同名数据库（位于 `MyProjects/<Project>/<Project>.db`）。
- 迁移与模板更新流程：先在项目 db 验证；通过评审后使用 `tools/` 脚本更新 `templete/project.db`。

---
简述：`ref/` 提供对齐 T‑Solver 的文档与样例，作为设计/验证的依据，不直接作为运行时依赖。

