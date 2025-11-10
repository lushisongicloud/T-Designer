# AGENTS 指南 — widget（UI/控件层）

本文件适用于 `widget/` 目录及其子目录中的所有文件，指导 Qt Widgets/UI 层的开发与改动。

## 角色与边界
- 职责：
  - 提供界面交互、数据展示、输入校验与用户反馈。
  - 通过清晰接口调用 `BO/` 的服务/仓库，不直接操作数据库或业务细节。
- 禁止：
  - 将复杂业务逻辑放入 UI；
  - 进行长时阻塞操作；
  - 依赖自动生成文件（`ui_*.h`）。
- `MainWindow` 相关代码按功能拆分到仓库根目录的 `mainwindow_project.cpp`、`mainwindow_units.cpp`、`mainwindow_diagnosis.cpp` 中；新增入口或页签时，请跟随现有拆分结构。

## 本周期重点（T‑Solver 深度集成的 UI 落点）
- "本地物料库/元件属性"统一校验入口
  - 在两处的 "T语言模型/元件T语言" 文本编辑区提供统一的"校验"按钮；调用 `BO` 的 SMT 校验接口（语法 + 端口一致性）。
  - 校验结果以列表/定位的方式呈现；可一键跳转到变量声明/端口配置。
- 功能子块 → 端口配置功能（通过tableTerm右键菜单）
  - 在tableTerm表格中显示"变量"列（第3列），展示端口配置的变量集（如"i,u"）
  - 右键菜单提供"配置端口"和"删除配置"功能
  - "配置端口"打开PortConfigEditDialog对话框，支持：
    - 设置端口类型（电/液/机/其他）
    - 显示并编辑默认变量集（i/u、p/q、F+v|n|x）
    - 选择连接宏族（从可用宏族列表中选择，如electric-connect、hydraulic-connect等）
    - 管理连接宏族（添加自定义宏族、删除自定义宏族，内置宏族不可删除）
  - 宏族概念：
    - 宏族是一组支持不同端口数量的连接宏集合（如electric-connect包含connect2e/3e/4e）
    - 系统根据连接点的实际端口数量自动选择合适的宏（如3个端口相连时选择connect3e）
    - 内置宏族（is_builtin=1）包括：electric-connect、hydraulic-connect、mechanical-connect
    - 用户可创建自定义宏族支持特殊连接语义
  - 数据存储在port_config表（端口配置）和port_connect_macro_family表（宏族定义）
- 功能管理 UI 重构
  - 参考 `ref/T-Solver/README.md`：链路可从连线自动生成功能的"链路信息"，用户可修改与确认；
  - 依赖功能选择器：自动提示主链器件作为他功能的"执行器"的候选；
  - 边界条件查找与去重；求解前裁剪预览。
- 测试管理 → 依赖矩阵
  - 对齐 T‑Solver `dmatrixviewerdialog` 的布局、交互、配色与快捷操作；
  - 扩展列/行属性编辑（测试：复杂性/费用/时间/成功率/备注；故障：概率/严重度/备注）。

## UI 与模型
- 使用 Qt Designer 维护 `.ui` 文件；类名与 UI 文件名对应（如 `CodeCheckDialog` ↔ `codecheckdialog.ui`）。
- Model/View：
  - 复杂树/表数据使用 `QAbstractItemModel` 派生类（如 `containermodel.*`）。
  - 明确 `Role` 与 `data()` 契约；避免在 `data()` 中做重计算（交给 `BO` 预处理）。
- 信号/槽：
  - 用户操作转信号或调用 `BO`；
  - 通过信号接收异步结果并刷新 UI，避免跨线程直接访问控件。

## 性能与并发
- 耗时任务移交 `BO` 的 `Worker` 或后台任务；UI 线程仅做轻量操作。
- 批量更新模型时使用 `beginResetModel()/endResetModel()` 或细粒度 `beginInsertRows()` 等。

## 资源与文案
- 图标/图片统一通过 `image.qrc` 管理。
- 字符串默认使用 `tr()`，但依据根 `AGENTS.md`：代码中的中文常量可直接使用双引号或 `QString("中文")`。
- 示例项目用于 UI 验证时请拷贝副本；`DemoSystem/` 仍为 Livingstone 流程，用于理解概念并逐步迁移到 SMT/`z3`。
- 需要核对函数/系统描述时，参考 `ref/Model.db` 及 `selectfunctiondialog.cpp`、`systementity.cpp` 的读取方式，保持字段一致。

## 代码风格
- 遵循根目录 `AGENTS.md`：类 PascalCase，方法/变量 lowerCamelCase，4 空格缩进，UTF-8 with BOM，`clang-format`。
- 中文字符串：使用双引号或 `QString("中文")`，不要使用 `QStringLiteral`。
- 头/源文件成对；将业务交互点集中在少量方法中（如 `applyChanges()`/`loadFromBo()`）。

## 典型目录内元素
- `containermodel.*`：树形模型；确保持久索引正确、`parent()`/`index()` 成对一致。
- `containertreedialog.*`：容器树选择/浏览对话框；通过信号向外部报告选择结果。
- `codecheckdialog.*`、`selectfunctiondialog.*`：较大的对话框逻辑，复杂校验/计算下沉至 `BO`。

## 测试策略（Qt Test）
- 对模型类：验证行列数、角色数据、插入/删除与重置流程。
- 对对话框：将关键逻辑抽到可测试函数，编写用例。
- 测试位于 `tests/`，命名如 `widget_containermodel_test.cpp`；在 `T_DESIGNER.pro` 添加测试目标。

## 变更流程
- 修改/新增控件或模型：同步更新 `.ui` 与资源；如新增源文件，更新 `T_DESIGNER.pro`。
- 不修改自动生成文件 `ui_*.h`。

---
简述：widget 层专注表现与交互，本周期围绕 SMT 校验、功能管理与 D 矩阵重构对 UI 进行改造，核心逻辑由 `BO` 提供。
