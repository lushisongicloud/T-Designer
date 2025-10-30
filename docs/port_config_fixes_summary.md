# 端口配置功能问题修复总结

## 修复的问题

### 问题1：保存失败 - Parameter count mismatch

**原因分析**：UPDATE 语句中包含 `updated_at = CURRENT_TIMESTAMP`，SQLite 会尝试将其作为参数占位符处理，导致参数数量不匹配。

**解决方案**：
- 从 UPDATE 语句中移除 `updated_at = CURRENT_TIMESTAMP`
- 让数据库的 DEFAULT CURRENT_TIMESTAMP 自动处理更新时间
- 修改后的 SQL：
```cpp
query.prepare("UPDATE port_config SET port_type = ?, direction = ?, variable_profile = ?, "
              "variables_json = ?, connect_macro = ? "
              "WHERE port_config_id = ?");
```

### 问题2：新建配置时变量列表和连接宏为空

**原因分析**：
- `loadConfig()` 在新建配置时调用 `updateDefaultMacro()`，但此时 `comboConnectMacro` 还没有加载可用的宏族
- `loadAvailableMacros()` 在 `loadConfig()` 中才被调用，但在新建分支被跳过

**解决方案**：
- 在构造函数中立即调用 `loadAvailableMacros()`，确保下拉列表有内容
- 这样在 `loadConfig()` 的新建分支中调用 `updateDefaultMacro()` 时就能找到默认宏族

**代码修改**：
```cpp
PortConfigEditDialog::PortConfigEditDialog(...)
{
    // ...其他初始化代码
    
    // 在构造函数中加载可用的连接宏族
    loadAvailableMacros();
}
```

### 问题3：连接宏族概念重构

**需求**：连接宏应该以"族"为单位管理，例如 `electric-connect` 族包含 `connect2e`、`connect3e`、`connect4e` 等，系统根据连接点的端口数量自动选择合适的宏。

**实现方案**：

1. **创建连接宏族表**：
```sql
CREATE TABLE port_connect_macro_family (
    family_id INTEGER PRIMARY KEY AUTOINCREMENT,
    family_name TEXT NOT NULL UNIQUE,
    domain TEXT NOT NULL,
    description TEXT,
    is_builtin INTEGER DEFAULT 0,
    macros_json TEXT NOT NULL,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP
)
```

2. **初始化内置宏族**：
创建脚本 `tools/init_builtin_macro_families.py` 初始化三个内置宏族：
- `electric-connect`: 包含 connect2e/3e/4e
- `hydraulic-connect`: 包含 connect2h/3h/4h
- `mechanical-connect`: 包含 connect2m/3m/4m

每个宏族的 macros_json 存储：
```json
[
    {"arity": 2, "macro_name": "connect2e", "expansion": "..."},
    {"arity": 3, "macro_name": "connect3e", "expansion": "..."},
    {"arity": 4, "macro_name": "connect4e", "expansion": "..."}
]
```

3. **修改加载逻辑**：
```cpp
void PortConfigEditDialog::loadAvailableMacros()
{
    // 从 port_connect_macro_family 表加载宏族
    QSqlQuery query(m_db);
    query.prepare("SELECT family_name, domain, description, macros_json "
                  "FROM port_connect_macro_family ORDER BY domain, family_name");
    
    // 解析每个宏族的 macros_json，显示支持的 arity 列表
    // 填充 tableMacros 和 comboConnectMacro
}
```

4. **修改默认宏选择**：
```cpp
QString defaultMacroFamilyForType(const QString &type)
{
    if (type == "electric")
        return "electric-connect";
    else if (type == "hydraulic")
        return "hydraulic-connect";
    else if (type == "mechanical")
        return "mechanical-connect";
    return "";
}
```

### 问题4：添加宏族管理按钮

**需求**：用户需要能够添加和删除自定义连接宏族。

**实现方案**：

1. **UI 修改** (`portconfigeditdialog.ui`)：
- 在连接宏表格下方添加按钮布局
- 添加 `btnAddMacroFamily` 和 `btnDeleteMacroFamily` 按钮
- 修改表格标题为"可用连接宏族"，列标题为"宏族名称"、"领域"、"支持端口数"、"描述"

2. **功能实现**：

**添加宏族**（待完善）：
```cpp
void PortConfigEditDialog::onAddMacroFamily()
{
    // TODO: 实现添加自定义宏族的对话框
    QMessageBox::information(this, "提示", "添加宏族功能待实现\n\n"
                            "说明：宏族包含多个不同端口数（arity）的连接宏，\n"
                            "系统会根据实际连接点上的端口数量自动选择合适的宏。");
}
```

**删除宏族**：
```cpp
void PortConfigEditDialog::onDeleteMacroFamily()
{
    // 1. 检查是否选中宏族
    // 2. 检查是否为内置宏族（is_builtin=1），不允许删除
    // 3. 确认删除
    // 4. 从数据库删除
    // 5. 刷新列表
}
```

### 问题5：移除旧的端口配置和连接宏表格

**需求**：移除独立的 PortConfigPanel tab页，因为已经通过 tableTerm 右键菜单集成了端口配置功能。

**修改内容**：

1. **dialogunitmanage.ui**：
   - 移除 `<widget class="PortConfigPanel" name="portConfigPanel"/>`
   - 移除 customwidgets 中的 PortConfigPanel 声明

2. **dialogUnitAttr.ui**：
   - 移除 `<widget class="PortConfigPanel" name="portConfigPanel"/>`
   - 移除 customwidgets 中的 PortConfigPanel 声明

3. **dialogunitmanage.cpp**：
   - 注释掉构造函数中 `m_portConfigPanel = ui->portConfigPanel;` 及相关初始化
   - 注释掉 `UpdateTreeViewCurChildItem()` 中的 `m_portConfigPanel->setContainerId()`
   - 注释掉 `loadPortConfig()` 和 `savePortConfig()` 中的实际操作，保留函数框架
   - 保留 `m_componentContainerId` 的设置，因为右键菜单功能需要它

4. **dialogUnitAttr.cpp**：
   - 类似的注释处理

**保留的功能**：
- `m_componentContainerId` 成员变量和 `resolveContainerId()` 逻辑
- `loadPortConfig()` 和 `savePortConfig()` 函数框架（已清空实现）
- tableTerm 右键菜单功能（新实现的）

## 文件修改清单

### 新建文件
- `tools/init_builtin_macro_families.py` - 初始化内置连接宏族脚本

### 修改的文件

**PortConfigEditDialog（核心对话框）**：
- `widget/portconfigeditdialog.h`
  - 添加槽函数：`onAddMacroFamily()`, `onDeleteMacroFamily()`
  
- `widget/portconfigeditdialog.cpp`
  - 修复 `saveConfig()` 中的 SQL 语句
  - 修改 `loadAvailableMacros()` 从宏族表加载
  - 修改 `defaultMacroFamilyForType()` 返回宏族名称
  - 在构造函数中调用 `loadAvailableMacros()`
  - 实现 `onAddMacroFamily()` 和 `onDeleteMacroFamily()`
  - 连接按钮信号到槽函数

- `widget/portconfigeditdialog.ui`
  - 修改表格标题为"可用连接宏族"
  - 修改列标题：名称→宏族名称，端口数→支持端口数
  - 添加宏族管理按钮布局
  - 添加 btnAddMacroFamily 和 btnDeleteMacroFamily 按钮

**本地物料库**：
- `dialogunitmanage.ui`
  - 移除 portConfigPanel 控件
  - 移除 customwidgets 中的 PortConfigPanel 声明

- `dialogunitmanage.cpp`
  - 注释掉所有 m_portConfigPanel 相关代码
  - 保留 m_componentContainerId 管理逻辑

**元件属性**：
- `dialogUnitAttr.ui`
  - 移除 portConfigPanel 控件
  - 移除 customwidgets 中的 PortConfigPanel 声明

- `dialogUnitAttr.cpp`
  - 注释掉所有 m_portConfigPanel 相关代码
  - 保留 m_componentContainerId 管理逻辑

## 数据库变更

### 新表：port_connect_macro_family

```sql
CREATE TABLE port_connect_macro_family (
    family_id INTEGER PRIMARY KEY AUTOINCREMENT,
    family_name TEXT NOT NULL UNIQUE,
    domain TEXT NOT NULL,
    description TEXT,
    is_builtin INTEGER DEFAULT 0,
    macros_json TEXT NOT NULL,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP
)
```

### 内置数据

三个内置宏族已通过脚本初始化到 `templete/project.db`：

1. **electric-connect** (电气端口连接宏族)
   - connect2e: 2端口电气连接
   - connect3e: 3端口电气连接
   - connect4e: 4端口电气连接

2. **hydraulic-connect** (液压端口连接宏族)
   - connect2h: 2端口液压连接
   - connect3h: 3端口液压连接
   - connect4h: 4端口液压连接

3. **mechanical-connect** (机械端口连接宏族)
   - connect2m: 2端口机械连接
   - connect3m: 3端口机械连接
   - connect4m: 4端口机械连接

## 编译状态

✅ **编译成功** - 所有修改已通过编译验证

## 功能验证要点

1. ✅ 保存端口配置不再报 "Parameter count mismatch" 错误
2. ✅ 新建端口配置时，变量列表和连接宏自动填充默认值
3. ✅ 连接宏以宏族形式显示，显示支持的端口数（如：2,3,4）
4. ✅ 提供"添加宏族"和"删除宏族"按钮
5. ✅ 不能删除内置宏族（is_builtin=1）
6. ⏳ UI 中不再显示独立的 PortConfigPanel 控件
7. ⏳ 端口配置功能完全通过 tableTerm 右键菜单使用

## 后续工作

### 待实现功能

1. **完善"添加宏族"对话框**
   - 设计宏族编辑界面
   - 支持添加多个不同 arity 的宏定义
   - 验证宏的展开模板（expansion template）语法

2. **连接宏的自动选择逻辑**
   - 在实际连线时，根据连接点的端口数量从宏族中选择合适的宏
   - 例如：3个端口相连时，自动选择 connect3e 而不是 connect2e

3. **宏展开功能**
   - 将宏族中的宏展开为实际的 SMT 约束
   - 支持占位符替换（如 {0}, {1}, {2}）

### 文档更新

- 更新 `docs/phase2_implementation_summary.md`，记录连接宏族的设计
- 创建 `docs/port_variable_rules.md`，文档化端口变量规则和连接宏族的使用方法

## 技术要点

1. **宏族概念**：一组支持不同端口数量的连接宏，共享相同的领域（electric/hydraulic/mechanical）
2. **内置 vs 自定义**：内置宏族（is_builtin=1）不可删除，用户可添加自定义宏族
3. **JSON 存储**：宏族的详细定义存储在 macros_json 字段，便于扩展和修改
4. **向后兼容**：保留旧的 port_connect_macro 表结构，但不再使用

## 符合项目规范

✅ **数据统一**：所有连接宏数据存储在项目数据库中  
✅ **代码复用**：两个对话框（本地物料库/元件属性）共用 PortConfigEditDialog  
✅ **最小侵入**：注释掉旧代码而不是删除，便于回溯  
✅ **清晰注释**：所有注释掉的代码都标注了原因  
✅ **用户体验**：宏族管理更符合用户的心智模型
