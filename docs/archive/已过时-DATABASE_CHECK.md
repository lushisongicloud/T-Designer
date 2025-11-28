**【分类依据】本文件记录了具体的修复过程、调试分析或已过时的设计实现，作为问题解决的临时记录保留。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 测试管理对话框数据库使用检查

## 问题描述
TestManagementDialog 应该使用项目数据库（`./MyProjects/项目目录/项目名称.db`），而不是器件库（`./ref`目录）或模板库（`./templete`目录）。

## 数据库架构

### 项目数据库位置
- 路径：`./MyProjects/<项目目录>/<项目名称>.db`
- 全局变量：`T_ProjectDatabase`
- 初始化位置：`mainwindow_project.cpp` 第 3654-3662 行

```cpp
T_ProjectDatabase = QSqlDatabase::addDatabase("QSQLITE", CurProjectName);
T_ProjectDatabase.setDatabaseName(CurProjectPath + "/" + CurProjectName + ".db");
```

### 相关表结构
在项目数据库中，包含以下表：
1. `diagnosis_tree` - 存储决策树元数据
2. `diagnosis_tree_node` - 存储决策树节点
3. `container` - 容器信息
4. `test_definition` - 测试定义

## 当前实现

### TestManagementDialog 构造函数
```cpp
TestManagementDialog::TestManagementDialog(int containerId, const QSqlDatabase &db, QWidget *parent)
```

接收的参数：
- `containerId`: 容器ID
- `db`: QSqlDatabase 引用
- `parent`: 父窗口

### 数据库使用
- `m_db`: 存储传入的数据库引用
- `m_repo`: ContainerRepository，使用 `m_db`

## 检查点

### 1. 调用位置检查
**需要找到在哪里创建 TestManagementDialog 实例**

可能的调用位置：
- mainwindow_diagnosis.cpp
- mainwindow_units.cpp
- 其他 mainwindow_*.cpp 文件

### 2. 传入数据库检查
确保传入的数据库是 `T_ProjectDatabase`，而不是：
- `LdMainData.db` (器件库，位于 `C:/TBD/data/` 或 `./ref/`)
- `project.db` (模板库，位于 `./templete/`)

### 3. 调试信息
已添加以下调试输出：

**构造函数中：**
```cpp
qDebug() << "Container ID:" << m_containerId;
qDebug() << "数据库连接名:" << m_db.connectionName();
qDebug() << "数据库文件:" << m_db.databaseName();
qDebug() << "数据库是否打开:" << m_db.isOpen();
```

**加载决策树列表时：**
```cpp
qDebug() << "从数据库" << m_db.databaseName() << "加载了" << count << "个决策树";
```

## 预期行为

### 正确的数据库路径示例
```
D:/SynologyDrive/Project/T_DESIGNER/MyProjects/DemoSystem/DemoSystem.db
D:/SynologyDrive/Project/T_DESIGNER/MyProjects/双电机拖曳收放装置/双电机拖曳收放装置.db
```

### 错误的数据库路径
```
C:/TBD/data/LdMainData.db  （错误：器件库）
D:/SynologyDrive/Project/T_DESIGNER/ref/LdMainData.db  （错误：参考器件库）
D:/SynologyDrive/Project/T_DESIGNER/templete/project.db  （错误：模板库）
```

## 解决方案

### 方案 A：确保调用者传入正确的数据库
找到创建 TestManagementDialog 的代码，确保传入 `T_ProjectDatabase`：

```cpp
// 正确的调用方式
TestManagementDialog *dialog = new TestManagementDialog(containerId, T_ProjectDatabase, this);
dialog->exec();
```

### 方案 B：使用全局变量（不推荐）
如果找不到调用位置，可以在头文件中声明外部变量：

```cpp
// testmanagementdialog.cpp
extern QSqlDatabase T_ProjectDatabase;
extern QString CurProjectName;

// 然后在需要时直接使用
// 但这样会增加耦合性，不推荐
```

## 验证步骤

1. **编译并运行程序**
2. **打开一个项目**（如 DemoSystem）
3. **打开测试管理对话框**
4. **查看控制台输出**，检查：
   - 数据库连接名是否为项目名称
   - 数据库文件路径是否指向项目目录
   - 加载的决策树数量是否正确

5. **检查决策树内容**
   - 应该显示该项目特定的决策树
   - 不应该是模板或其他项目的决策树

## 测试数据

### DemoSystem 项目应包含的决策树
```sql
SELECT tree_id, name, description FROM diagnosis_tree WHERE container_id = 1;
-- 应该返回该项目中定义的决策树
```

可以使用以下命令检查：
```bash
sqlite3 "./MyProjects/DemoSystem/DemoSystem.db" "SELECT tree_id, container_id, name FROM diagnosis_tree;"
```
