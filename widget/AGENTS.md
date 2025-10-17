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

## UI 与模型
- 使用 Qt Designer 维护 `.ui` 文件；类名与 UI 文件名对应（例如 `CodeCheckDialog` ↔ `codecheckdialog.ui`）。
- Model/View：
  - 复杂树/表数据使用 `QAbstractItemModel` 派生类（例如 `containermodel.*`）。
  - 定义清晰的 `Role` 与 `data()` 约定，保证 `index`/`parent`/`flags`/`rowCount`/`columnCount` 的一致性与性能。
  - 不在 `data()` 中做重计算；缓存或让 `BO` 提供预处理结果。
- 信号/槽：
  - 将用户操作转为信号或调用 `BO` 接口；
  - 通过信号接收异步结果并刷新 UI，避免直接跨线程访问模型/控件。

## 性能与并发
- 耗时任务移交 `BO` 的 `Worker` 或后台任务；UI 线程仅做轻量操作。
- 批量更新模型时使用 `beginResetModel()/endResetModel()` 或细粒度 `beginInsertRows()` 等，保持视图一致性与最小重绘。

## 资源与国际化
- 图标/图片统一通过 `image.qrc` 管理，路径采用 `:/` 前缀。
- 字符串使用 `tr()` 以便后续国际化。

## 代码风格
- 遵循根目录 `AGENTS.md`：类 PascalCase，方法/变量 lowerCamelCase，4 空格缩进，UTF‑8，`clang-format`。
- 头/源文件成对；将业务交互点集中在少量方法中（如 `applyChanges()`/`loadFromBo()`）。

## 典型目录内元素
- `containermodel.*`：树形模型；请确保持久索引正确、`parent()`/`index()` 成对一致、避免循环引用。
- `containertreedialog.*`：容器树选择/浏览对话框；通过信号向外部报告选择结果。
- `codecheckdialog.*`、`selectfunctiondialog.*`：较大的对话框逻辑，务必将复杂校验/计算下沉至 `BO`。

## 测试策略（Qt Test）
- 对模型类进行单元测试：验证行列数、角色数据、插入/删除与重置流程；
- 对对话框的关键逻辑（不含交互）编写可调度的函数并测试；
- 测试文件位于 `tests/`，命名如 `widget_containermodel_test.cpp`，在 `T_DESIGNER.pro` 添加测试目标。

## 变更流程
- 修改/新增控件或模型：
  - 同步更新 `.ui` 文件与资源；
  - 如新增源文件，更新 `T_DESIGNER.pro`；
  - 不修改 `ui_*.h`（由 Qt 自动生成）。

---
简述：widget 层专注表现与交互，依赖 `BO` 获取/提交数据，避免业务下沉与阻塞 UI。

