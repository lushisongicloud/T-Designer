**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# Project DB Schema Extensions (Design Proposal)

## 1. Goals & Scope
- 支持本周期提出的 SMT 建模、功能管理、D 矩阵功能在**项目数据库**（MyProjects/工程同名 db）内持久化。
- 仅新增/扩展项目库结构；模板 `templete/project.db` 的更新作为后续动作，在样例验证无误后执行。
- 坚持最小侵入：保留现有表结构与业务，新增表或列以承载新能力；旧数据通过迁移脚本同步至新结构。
- 设计兼容 T‑Solver 现有模型（XML、SMT 片段、DMatrix JSON），并考虑未来工具链（端口变量集、connect 语法糖、自定义宏）。

## 2. 新增数据单元概览
| 模块 | 新增表 | 作用 | 关键关联 |
| --- | --- | --- | --- |
| 元件/容器 SMT | `component_smt` | 存放元件级容器/实体的 SMT 描述与校验信息 | `Equipment`, `container` |
| 端口配置 | `port_config`、`port_connect_macro` | 映射功能子块端口 → 变量集合、自定义连接宏 | `container` |
| 系统模型 | `system_smt` | 分离 DEF/CONNECT/RAW SMT 片段，支持多次生成 | `container` |
| 功能模型 | `function_document` | 保存完整功能 XML（与 T-Solver 兼容） | `container` |
| D 矩阵 | `dmatrix_meta` | 缓存 SAT 结果、测试/故障元数据、导出信息 | `container` |

> 说明：所有 JSON / XML 字段采用 `TEXT` 存储，约定 UTF-8 编码；时间字段使用 ISO8601 文本。

## 3. 表结构细则

### 3.1 `component_smt`
存储容器或实体元件的 SMT-LIB 描述与校验结果。

| 列名 | 类型 | 约束 | 说明 |
| --- | --- | --- | --- |
| `component_smt_id` | INTEGER | PK AUTOINCREMENT | 主键 |
| `equipment_id` | INTEGER | FK -> Equipment.Equipment_ID (可空) | 对应实体元件；容器聚合时可空 |
| `container_id` | INTEGER | FK -> container.container_id (可空) | 首选：指向元件级容器；至少有一方非空 |
| `model_scope` | TEXT | NOT NULL DEFAULT 'component' | 枚举：`component` / `container` / `aggregate` |
| `revision_tag` | TEXT | 可空 | 逻辑版本号（如生成批次） |
| `smt_text` | TEXT | NOT NULL | 完整 SMT 片段 |
| `port_signature` | TEXT | 可空 | 端口声明哈希或 JSON（便于一致性对比） |
| `syntax_status` | TEXT | NOT NULL DEFAULT 'unknown' | `unknown`/`valid`/`invalid` |
| `syntax_message` | TEXT | 可空 | 语法/一致性校验信息（JSON 或纯文本） |
| `metadata_json` | TEXT | 可空 | 附加属性（如生成源、Z3 版本） |
| `created_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 创建时间 |
| `updated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 更新时间 |

索引建议：
- `CREATE UNIQUE INDEX idx_component_smt_equipment ON component_smt(equipment_id) WHERE equipment_id IS NOT NULL;`
- `CREATE UNIQUE INDEX idx_component_smt_container_scope ON component_smt(container_id, model_scope) WHERE container_id IS NOT NULL;`
- `CHECK (equipment_id IS NOT NULL OR container_id IS NOT NULL)` 保证至少关联一端。

### 3.2 `port_config`
按容器+功能子块维度记录端口类型、变量集合与定制信息。

| 列名 | 类型 | 约束 | 说明 |
| --- | --- | --- | --- |
| `port_config_id` | INTEGER | PK AUTOINCREMENT | 主键 |
| `container_id` | INTEGER | FK -> container.container_id NOT NULL | 所属容器（通常为元件级容器） |
| `function_block` | TEXT | NOT NULL | 功能子块名称（如 `Coil`） |
| `port_name` | TEXT | NOT NULL | 端号（单个；若 UI 多端合并，用多行存储） |
| `port_type` | TEXT | NOT NULL | `electric` / `hydraulic` / `mechanical` / `other` |
| `direction` | TEXT | NOT NULL DEFAULT 'bidirectional' | `input`/`output`/`bidirectional`/`internal` |
| `variable_profile` | TEXT | NOT NULL DEFAULT 'default' | `default` / `custom` / `alias:<name>` |
| `variables_json` | TEXT | NOT NULL | JSON 列表，例如 `[{"name": "i", "kind": "flow", "required": true}]` |
| `connect_macro` | TEXT | 可空 | 关联的连接宏名（默认 `connect2e` 等） |
| `custom_metadata` | TEXT | 可空 | UI/算法附加信息（排序、备注） |
| `updated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 更新时间 |

索引：`CREATE UNIQUE INDEX idx_port_config_unique ON port_config(container_id, function_block, port_name);`

### 3.3 `port_connect_macro`
用户自定义 connect 语法糖或覆盖默认宏。

| 列名 | 类型 | 约束 | 说明 |
| --- | --- | --- | --- |
| `macro_id` | INTEGER | PK AUTOINCREMENT | 主键 |
| `container_id` | INTEGER | FK -> container.container_id NOT NULL | 生效范围（容器层级，可指向系统容器） |
| `macro_name` | TEXT | NOT NULL | 函数名（如 `connect4e`） |
| `domain` | TEXT | NOT NULL | `electric` / `hydraulic` / `mechanical` / `generic` |
| `arity` | INTEGER | NOT NULL | 参与端口数量（2/3/...） |
| `expansion_template` | TEXT | NOT NULL | SMT 展开模板，支持占位符 `%ARG1%` 等 |
| `description` | TEXT | 可空 | 说明 |
| `metadata_json` | TEXT | 可空 | 兼容扩展字段 |
| `updated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 更新时间 |

索引：`CREATE UNIQUE INDEX idx_connect_macro_unique ON port_connect_macro(container_id, macro_name);`

### 3.4 `system_smt`
系统级 SMT 由自动生成流程维护，分块存储以便调试、增量更新。

| 列名 | 类型 | 约束 | 说明 |
| --- | --- | --- | --- |
| `system_smt_id` | INTEGER | PK AUTOINCREMENT | 主键 |
| `container_id` | INTEGER | FK -> container.container_id NOT NULL UNIQUE | 对应系统/子系统容器 |
| `def_block` | TEXT | NOT NULL | DEF BEGIN…END 部分（实例化片段） |
| `connect_block` | TEXT | NOT NULL | CONNECT 语句（connect2*/link/raw） |
| `raw_block` | TEXT | 可空 | 用户自定义 SMT 片段 |
| `options_json` | TEXT | 可空 | 生成选项（网表来源、变量白名单等） |
| `checksum` | TEXT | 可空 | 校验值（hash） |
| `generated_by` | TEXT | 可空 | 生成模块标识 |
| `generated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 最近生成时间 |
| `updated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 更新时间（手工修改） |

索引：`UNIQUE(container_id)` 已覆盖；如需历史版本，可后续新增 history 表。

### 3.5 `function_document`
承载完整功能描述 XML，与 T-Solver `functiondefine` 结构一致。

| 列名 | 类型 | 约束 | 说明 |
| --- | --- | --- | --- |
| `function_document_id` | INTEGER | PK AUTOINCREMENT | 主键 |
| `container_id` | INTEGER | FK -> container.container_id NOT NULL | 通常指向系统容器；亦可支持组件级功能 |
| `xml_text` | TEXT | NOT NULL | 完整 XML 文档 |
| `format_version` | TEXT | NOT NULL DEFAULT '1.0' | 文档版本（与解析器兼容） |
| `checksum` | TEXT | 可空 | 校验值（便于变更检测） |
| `source_hint` | TEXT | 可空 | 生成来源（手动/导入/脚本） |
| `metadata_json` | TEXT | 可空 | 额外信息（功能统计、迁移记录） |
| `created_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 创建时间 |
| `updated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 更新时间 |

索引：
- `CREATE UNIQUE INDEX idx_function_document_container ON function_document(container_id);`
- 若需要历史版本，可去掉唯一约束并增加 `is_active` 字段。

### 3.6 `dmatrix_meta`
缓存 D 矩阵构建结果（含测试/故障详情与 UI 状态）。

| 列名 | 类型 | 约束 | 说明 |
| --- | --- | --- | --- |
| `dmatrix_meta_id` | INTEGER | PK AUTOINCREMENT | 主键 |
| `container_id` | INTEGER | FK -> container.container_id NOT NULL | 对应分析容器 |
| `result_json` | TEXT | NOT NULL | `DMatrixBuildResult` 序列化 JSON（含 tests、faults、cells） |
| `options_json` | TEXT | NOT NULL | 构建参数（DetectMode、超时、范围策略） |
| `state_json` | TEXT | 可空 | UI 状态（启用/禁用、过滤条件） |
| `csv_path` | TEXT | 可空 | 最近导出 CSV 相对路径 |
| `checksum` | TEXT | 可空 | 结果哈希，便于缓存命中 |
| `is_active` | INTEGER | NOT NULL DEFAULT 1 | 1=当前版本，0=历史 |
| `created_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 创建时间 |
| `updated_at` | TEXT | DEFAULT CURRENT_TIMESTAMP | 更新时间 |

索引：
- `CREATE INDEX idx_dmatrix_container ON dmatrix_meta(container_id, is_active);`
- 允许保留历史记录（多行），应用侧读取 `is_active=1` 最新版本。

## 4. 现有表扩展建议
| 表 | 新列 | 类型 / 默认值 | 用途 |
| --- | --- | --- | --- |
| `container` | `port_config_revision` | INTEGER DEFAULT 0 | 端口配置版本号（缓存失效） |
| `container` | `function_document_id` | INTEGER FK -> function_document (可空) | 快速关联主功能文档 |
| `Function` | `document_id` | INTEGER FK -> function_document (可空) | 迁移期双写/回读；后续可弃用旧字段 |

> 以上列可按需求阶段性添加；若保持查询通过联表完成，可延后实现。

## 5. 关系与数据流
```
Equipment ──┐
            ├─ component_smt ──┐
container ──┘                  │
                               ├─ system_smt (系统/子系统)
                               ├─ port_config + port_connect_macro
                               ├─ function_document
                               └─ dmatrix_meta
```
- 元件级容器（container.type = 'Component'）同时关联 Equipment 与 component_smt，用于 SMT 校验、行为聚合。
- 系统容器的系统级模型（system_smt）与功能文档、D 矩阵共享 `container_id`，支撑后续 SAT、D 矩阵构建。
- 端口配置与 connect 宏直接驱动 Cad→SMT 生成器；其版本号反馈至 `container.port_config_revision`，用于缓存控制。

## 6. 迁移与落库策略
1. **Schema 发布**：执行 `tools/db_migrate_project.py`（待开发）创建新表，确保多次执行幂等。
2. **初始填充**：
   - 元件级容器 → 从现有 `container.behavior_smt` / 本地元件 T 语言生成 `component_smt` 行，校验状态标记 `unknown`。
   - 端口配置 → 将 `container.interface_json` 解析后写入 `port_config`，保留旧字段以便回滚。
   - 功能文档 → 将 `Function` 表现有数据包裹为基础 XML（仅保留字段值），存入 `function_document`，`Function.document_id` 回写。
   - D 矩阵 → 暂留空表，待新构建流程写入。
3. **代码切换**：业务层改用新表读写；保留旧字段只读；待验证稳定后清理冗余列。
4. **模板同步**：确认 MyProjects 样例运行正常后，再更新 `templete/project.db` 并记录版本号。

## 7. 兼容性与注意事项
- 所有 FK 采用 `ON DELETE CASCADE` 处理，确保删除容器/元件时自动清理附属模型数据。
- JSON / XML 字段增大 DB 体积，需结合 `VACUUM` 保养；建议在工具脚本中提供压缩/导出选项。
- 校验列（如 `syntax_status`）供 UI 快速过滤；Z3 校验失败时将错误信息写入 `syntax_message`。
- 自定义 connect 宏需与端口类型一一对应；插入时应校验 `domain` 与 `port_type` 一致。
- 未来若需历史版本，可为各表新增 `version`/`is_active` 列或建立 history 表；当前设计保留扩展接口（metadata_json / revision_tag）。

## 8. 后续工作指引
- 开发 `tools/db_migrate_project.py`：负责建表、加列、migration checkpoint。
- 更新 `ContainerData`/`FunctionRepository`/`TestManagementDialog` 等业务层，改用新表。
- 在 `docs/integration_dev_guide.md` 中补充使用说明与数据模型示意。
- 在单元/集成测试中增加 schema 验证（例如 sqlite `PRAGMA table_info` 断言）。

