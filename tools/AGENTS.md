# AGENTS 指南 — tools（脚本与工具）

本文件适用于 `tools/` 目录。此处存放工程数据库迁移/构建脚本与辅助工具。

## 原则
- 脚本语言：优先 Python；遵循可读、幂等、可回滚的原则。
- 变更说明：每个脚本必须在文件头部说明“用途/输入/输出/危险点/回滚策略”。
- 日志与备份：对数据库操作前先创建时间戳备份；输出关键步骤日志。

## 现有脚本
- `update_template_db.py`：将已在项目 db 验证通过的结构/字段更新到 `templete/project.db`；请完善：
  - 版本标记与变更记录（schema_version 表或等效机制）；
  - 幂等检查（重复执行不会破坏数据）；
  - 失败回滚与恢复指引。

## 本周期建议新增脚本
- `migrate_project_db.py`：对单个项目 db 应用 SMT/功能/D 矩阵所需的新表/字段；
- `validate_smt_snippets.py`：离线批量校验元件 SMT 片段（语法/变量一致性），生成报表供“本地物料库”使用；
- `export_dmatrix_csv.py`：导出/导入 D 矩阵到 CSV 以便审查与批量编辑。

## 使用注意
- 在 `MyProjects/<Project>` 中对项目 db 进行验证；不要直接操作 `templete/project.db` 与 `ref/Model.db`。
- 脚本运行路径、依赖与环境变量（如 `PATH` 中的 SQLite/Z3 工具）需在脚本内或 README 中注明。

---
简述：脚本服务于“先项目验证、后模板更新”的流程，保障数据库变更可控、可追溯、可回滚。

