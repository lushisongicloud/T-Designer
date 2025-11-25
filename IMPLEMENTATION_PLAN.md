# T-Designer 实施计划

**基于**: IMPLEMENTATION_GAP_ANALYSIS.md  
**目标**: 完成剩余 30% 的核心功能，使系统达到可用状态  
**预计工期**: 4-6 周

---

## 阶段 1: 数据库与基础设施修复（第 1 周）

### 任务 1.1: 修复数据库初始化脚本 ⭐⭐⭐

**目标**: 确保所有环境下可以正确初始化数据库

**文件涉及**:
- `tools/init_builtin_macro_families.py`
- `templete/project.db`

**具体步骤**:

1. **修改脚本使用相对路径**:
```python
# 修改前（硬编码 Windows 路径）
db_path = r'd:\SynologyDrive\Project\T_DESIGNER\templete\project.db'

# 修改后（相对路径）
import os
script_dir = os.path.dirname(os.path.abspath(__file__))
db_path = os.path.join(script_dir, '..', 'templete', 'project.db')
```

2. **验证内置宏族已初始化**:
```bash
cd /home/runner/work/T-Designer/T-Designer
sqlite3 templete/project.db "SELECT family_name, is_builtin FROM port_connect_macro_family;"
# 预期输出:
# electric-connect|1
# hydraulic-connect|1
# mechanical-connect|1
```

3. **测试脚本在 Linux/macOS/Windows 下的兼容性**

**验收标准**:
- ✅ 脚本可在任意平台运行
- ✅ 内置三个宏族正确初始化
- ✅ 脚本输出清晰的成功/失败信息

---

### 任务 1.2: 编写统一数据库迁移脚本 ⭐⭐⭐

**目标**: 自动更新 MyProjects 下所有项目的数据库结构

**文件涉及**:
- `tools/migrate_all_projects.py` （新建）

**具体步骤**:

1. **创建迁移脚本框架**:
```python
import os
import sqlite3
import sys
from pathlib import Path

def get_db_version(conn):
    """获取数据库版本号（从 schema_migrations 表）"""
    pass

def migrate_to_version(conn, target_version):
    """执行增量迁移到目标版本"""
    pass

def migrate_single_db(db_path):
    """迁移单个数据库文件"""
    print(f"正在迁移: {db_path}")
    conn = sqlite3.connect(db_path)
    # 检查版本
    # 执行迁移
    # 记录日志
    conn.close()

def main():
    """遍历 MyProjects 目录，迁移所有 .db 文件"""
    script_dir = Path(__file__).parent
    projects_dir = script_dir.parent / 'MyProjects'
    
    for db_file in projects_dir.rglob('*.db'):
        if db_file.name == 'LdMainData.db':
            continue  # 跳过元器件库
        migrate_single_db(db_file)

if __name__ == '__main__':
    main()
```

2. **定义迁移任务列表**:
```python
MIGRATIONS = [
    {
        'version': 1,
        'description': '添加 port_config 和 port_connect_macro_family 表',
        'sql': [
            'CREATE TABLE IF NOT EXISTS port_config (...)',
            'CREATE TABLE IF NOT EXISTS port_connect_macro_family (...)',
        ]
    },
    {
        'version': 2,
        'description': '初始化内置连接宏族',
        'sql': [
            "INSERT OR IGNORE INTO port_connect_macro_family ...",
        ]
    },
    # 更多迁移任务...
]
```

3. **添加备份与回滚机制**:
```python
import shutil
from datetime import datetime

def backup_db(db_path):
    """备份数据库"""
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    backup_path = f"{db_path}.backup_{timestamp}"
    shutil.copy2(db_path, backup_path)
    return backup_path
```

4. **测试迁移脚本**:
```bash
# 在测试项目上运行
python tools/migrate_all_projects.py --dry-run
# 实际执行
python tools/migrate_all_projects.py
```

**验收标准**:
- ✅ 脚本可遍历 MyProjects 下所有项目
- ✅ 自动检测数据库版本并执行增量迁移
- ✅ 迁移前自动备份数据库
- ✅ 迁移失败时提供回滚功能
- ✅ 输出详细的迁移日志

---

## 阶段 2: 链路自动构建功能（第 2 周）

### 任务 2.1: 分析 CAD 连线数据结构 ⭐⭐

**目标**: 理解 ConnectLine 表结构，掌握连线数据的存储方式

**文件涉及**:
- `templete/project.db` (ConnectLine 表)
- 可能涉及 `Symb2TermInfo`, `Symbol`, `Equipment` 表

**具体步骤**:

1. **查询 ConnectLine 表结构**:
```bash
sqlite3 MyProjects/DemoSystem/DemoSystem.db ".schema ConnectLine"
```

2. **分析示例数据**:
```sql
SELECT * FROM ConnectLine LIMIT 10;
-- 理解字段含义：
-- - 连线起点/终点的 Symbol_ID
-- - 连线起点/终点的端口信息（Terminal_ID?）
-- - 连线所属的页面 (Page_ID)
```

3. **绘制连通性图数据结构**:
```python
# 伪代码示例
class ConnectionGraph:
    def __init__(self, db_path):
        self.adjacency_list = {}  # {symbol_id: [connected_symbol_ids]}
        self.port_connections = {}  # {(symbol_id, port): [(other_symbol_id, other_port)]}
        
    def build_from_db(self):
        # 从 ConnectLine 表构建图
        pass
        
    def find_path(self, start_symbol, end_symbol):
        # BFS/DFS 查找路径
        pass
```

**验收标准**:
- ✅ 理解 ConnectLine 表的字段含义
- ✅ 可以从数据库提取连通性关系
- ✅ 实现简单的图数据结构与路径查找算法

---

### 任务 2.2: 实现链路自动构建算法 ⭐⭐⭐

**目标**: 根据用户选择的起点/终点设备，自动推导功能链路

**文件涉及**:
- `BO/function/linkbuilderservice.h/.cpp` （新建）
- `widget/functioneditdialog.cpp` （修改）

**具体步骤**:

1. **创建 LinkBuilderService 类**:
```cpp
// BO/function/linkbuilderservice.h
#ifndef LINKBUILDERSERVICE_H
#define LINKBUILDERSERVICE_H

#include <QString>
#include <QStringList>
#include <QSqlDatabase>

class LinkBuilderService
{
public:
    explicit LinkBuilderService(const QSqlDatabase &db);
    
    // 根据起点/终点设备，自动构建链路
    QStringList buildLink(const QStringList &startEquipments,
                          const QStringList &endEquipments,
                          QString *errorMessage = nullptr) const;
    
    // 根据单个设备，查找所有连接的设备
    QStringList findConnectedEquipments(const QString &equipmentName) const;
    
private:
    QSqlDatabase m_db;
    
    // 辅助函数：从 ConnectLine 表构建连通性图
    void buildConnectionGraph(QMap<QString, QSet<QString>> &graph) const;
    
    // 辅助函数：BFS 查找路径
    QStringList findPath(const QMap<QString, QSet<QString>> &graph,
                         const QString &start,
                         const QString &end) const;
};

#endif // LINKBUILDERSERVICE_H
```

2. **实现 buildLink 方法**:
```cpp
// BO/function/linkbuilderservice.cpp
QStringList LinkBuilderService::buildLink(const QStringList &startEquipments,
                                           const QStringList &endEquipments,
                                           QString *errorMessage) const
{
    // 1. 构建连通性图
    QMap<QString, QSet<QString>> graph;
    buildConnectionGraph(graph);
    
    // 2. 如果只有一个起点和一个终点，直接查找路径
    if (startEquipments.size() == 1 && endEquipments.size() == 1) {
        return findPath(graph, startEquipments.first(), endEquipments.first());
    }
    
    // 3. 多个起点/终点，查找最优路径（最短路径或覆盖所有点）
    // TODO: 实现更复杂的算法
    
    return QStringList();
}
```

3. **在 FunctionEditDialog 中添加"自动构建链路"按钮**:
```cpp
// widget/functioneditdialog.cpp
void FunctionEditDialog::on_btnAutoBuildLink_clicked()
{
    // 弹出对话框让用户选择起点/终点设备
    QStringList startEquipments = selectEquipmentsDialog("选择起点设备");
    QStringList endEquipments = selectEquipmentsDialog("选择终点设备");
    
    if (startEquipments.isEmpty() || endEquipments.isEmpty()) {
        return;
    }
    
    LinkBuilderService service(m_db);
    QString error;
    QStringList link = service.buildLink(startEquipments, endEquipments, &error);
    
    if (link.isEmpty()) {
        QMessageBox::warning(this, "构建失败", error);
        return;
    }
    
    // 将链路填入 textEditLink
    ui->textEditLink->setText(link.join(","));
}
```

4. **添加 UI 元素到 functioneditdialog.ui**:
```xml
<widget class="QPushButton" name="btnAutoBuildLink">
  <property name="text">
    <string>自动构建链路</string>
  </property>
</widget>
```

**验收标准**:
- ✅ 可以从 ConnectLine 表构建连通性图
- ✅ 给定起点/终点，能自动推导路径
- ✅ 在功能编辑对话框中显示"自动构建链路"按钮
- ✅ 用户点击按钮后，链路自动填入
- ✅ 在 DemoSystem 项目中测试成功

---

## 阶段 3: 系统连接约束自动生成（第 3 周）

### 任务 3.1: 实现宏族自动选择逻辑 ⭐⭐⭐

**目标**: 根据连接点的端口数量，自动从宏族中选择合适的宏

**文件涉及**:
- `BO/function/connectiongeneratorservice.h/.cpp` （新建）
- `BO/systementity.cpp` （修改）

**具体步骤**:

1. **创建 ConnectionGeneratorService 类**:
```cpp
// BO/function/connectiongeneratorservice.h
#ifndef CONNECTIONGENERATORSERVICE_H
#define CONNECTIONGENERATORSERVICE_H

#include <QString>
#include <QSqlDatabase>
#include <QMap>
#include <QList>

struct PortInfo {
    QString equipmentName;
    QString functionBlock;
    QString portName;
    QString portType;  // electric/hydraulic/mechanical
};

struct ConnectionPoint {
    QList<PortInfo> connectedPorts;
};

class ConnectionGeneratorService
{
public:
    explicit ConnectionGeneratorService(const QSqlDatabase &db);
    
    // 从 CAD 连线生成系统连接约束
    QString generateConnectionBlock(QString *errorMessage = nullptr) const;
    
private:
    QSqlDatabase m_db;
    
    // 辅助函数：提取连接点（多个端口连在一起）
    QList<ConnectionPoint> extractConnectionPoints() const;
    
    // 辅助函数：为连接点选择合适的宏
    QString selectMacroForConnection(const ConnectionPoint &point) const;
    
    // 辅助函数：从宏族中查找指定 arity 的宏
    QString findMacroByArity(const QString &macroFamilyName, int arity) const;
    
    // 辅助函数：展开宏，生成 SMT 约束
    QString expandMacro(const QString &macroName, 
                        const QString &expansion, 
                        const QStringList &portNames) const;
};

#endif // CONNECTIONGENERATORSERVICE_H
```

2. **实现 extractConnectionPoints 方法**:
```cpp
QList<ConnectionPoint> ConnectionGeneratorService::extractConnectionPoints() const
{
    QList<ConnectionPoint> points;
    
    // 从 ConnectLine 表查询所有连线
    QSqlQuery query(m_db);
    query.exec("SELECT Symbol_ID_Start, Terminal_Start, Symbol_ID_End, Terminal_End FROM ConnectLine");
    
    // 构建连接点：哪些端口连在一起
    // 使用并查集或图算法找出连通分量
    // 每个连通分量就是一个连接点
    
    // TODO: 实现具体逻辑
    
    return points;
}
```

3. **实现 selectMacroForConnection 方法**:
```cpp
QString ConnectionGeneratorService::selectMacroForConnection(const ConnectionPoint &point) const
{
    const int arity = point.connectedPorts.size();
    
    if (arity < 2) {
        return QString();  // 至少 2 个端口才能连接
    }
    
    // 假设所有端口类型相同（实际可能需要更复杂的逻辑）
    const QString portType = point.connectedPorts.first().portType;
    
    // 查询该端口类型的默认宏族
    QString macroFamilyName;
    if (portType == "electric") {
        macroFamilyName = "electric-connect";
    } else if (portType == "hydraulic") {
        macroFamilyName = "hydraulic-connect";
    } else if (portType == "mechanical") {
        macroFamilyName = "mechanical-connect";
    } else {
        return QString();  // 未知类型
    }
    
    // 从宏族中查找对应 arity 的宏
    QString macroExpansion = findMacroByArity(macroFamilyName, arity);
    
    if (macroExpansion.isEmpty()) {
        qWarning() << "未找到 arity =" << arity << "的连接宏，宏族 =" << macroFamilyName;
        return QString();
    }
    
    // 展开宏
    QStringList portNames;
    for (const auto &port : point.connectedPorts) {
        portNames.append(QString("%1.%2.%3").arg(port.equipmentName, port.functionBlock, port.portName));
    }
    
    return expandMacro(macroFamilyName, macroExpansion, portNames);
}
```

4. **实现 findMacroByArity 方法**:
```cpp
QString ConnectionGeneratorService::findMacroByArity(const QString &macroFamilyName, int arity) const
{
    QSqlQuery query(m_db);
    query.prepare("SELECT macros_json FROM port_connect_macro_family WHERE family_name = ?");
    query.addBindValue(macroFamilyName);
    
    if (!query.exec() || !query.next()) {
        return QString();
    }
    
    const QString macrosJson = query.value(0).toString();
    
    // 解析 JSON，查找对应 arity 的宏
    QJsonDocument doc = QJsonDocument::fromJson(macrosJson.toUtf8());
    QJsonArray macros = doc.array();
    
    for (const QJsonValue &value : macros) {
        QJsonObject macro = value.toObject();
        if (macro["arity"].toInt() == arity) {
            return macro["expansion"].toString();
        }
    }
    
    return QString();
}
```

5. **实现 expandMacro 方法**:
```cpp
QString ConnectionGeneratorService::expandMacro(const QString &macroName,
                                                 const QString &expansion,
                                                 const QStringList &portNames) const
{
    QString result = expansion;
    
    // 替换占位符 {0}, {1}, {2}, ...
    for (int i = 0; i < portNames.size(); ++i) {
        result.replace(QString("{%1}").arg(i), portNames[i]);
    }
    
    return result;
}
```

**验收标准**:
- ✅ 可以从 ConnectLine 表提取连接点
- ✅ 根据端口数量自动选择宏
- ✅ 宏正确展开为 SMT 约束
- ✅ 在测试项目中验证生成的连接约束

---

### 任务 3.2: 集成到系统描述生成流程 ⭐⭐⭐

**目标**: 将自动生成的连接约束集成到 `LoadProjectSystemDescription` 函数

**文件涉及**:
- `mainwindow_project.cpp` (LoadProjectSystemDescription)
- `BO/function/connectiongeneratorservice.cpp`

**具体步骤**:

1. **修改 LoadProjectSystemDescription 函数**:
```cpp
// mainwindow_project.cpp
void MainWindow::LoadProjectSystemDescription()
{
    // ... 现有代码：生成 DEF BEGIN ... DEF END 块 ...
    
    QString SystemDescription = "DEF BEGIN\n";
    for (QString EquipmentsInfo : ListEquipmentsInfo) 
        SystemDescription += EquipmentsInfo + "\n";
    SystemDescription += "DEF END\n\n";
    
    // ✨ 新增：使用 ConnectionGeneratorService 生成连接约束
    ConnectionGeneratorService connService(T_ProjectDatabase);
    QString connectionBlock = connService.generateConnectionBlock();
    
    if (!connectionBlock.isEmpty()) {
        SystemDescription += connectionBlock;
    } else {
        // 回退到旧方法（手动编写的连接）
        for (QString SystemConnections : ListSystemConnections) 
            SystemDescription += SystemConnections + "\n";
    }
    
    ui->textEditSystemDiscription->setText(SystemDescription);
}
```

2. **持久化到 system_smt 表**:
```cpp
void MainWindow::saveSystemSmtToDatabase(const QString &systemDescription)
{
    // 解析 systemDescription，分离 DEF 块和连接块
    QStringList parts = splitSystemDescription(systemDescription);
    QString defBlock = parts[0];
    QString connectBlock = parts[1];
    
    // 查询容器 ID
    ContainerRepository repo(T_ProjectDatabase);
    QList<ContainerEntity> roots = repo.fetchRoots();
    int containerId = roots.isEmpty() ? 0 : roots.first().id();
    
    if (containerId == 0) {
        qWarning() << "未找到系统容器，无法保存 system_smt";
        return;
    }
    
    // 插入或更新 system_smt 表
    QSqlQuery query(T_ProjectDatabase);
    query.prepare("INSERT OR REPLACE INTO system_smt "
                  "(container_id, def_block, connect_block, updated_at) "
                  "VALUES (?, ?, ?, CURRENT_TIMESTAMP)");
    query.addBindValue(containerId);
    query.addBindValue(defBlock);
    query.addBindValue(connectBlock);
    
    if (!query.exec()) {
        qWarning() << "保存 system_smt 失败:" << query.lastError();
    }
}
```

**验收标准**:
- ✅ LoadProjectSystemDescription 自动调用连接生成服务
- ✅ 生成的连接约束正确显示在 textEditSystemDiscription 中
- ✅ 系统 SMT 正确保存到 system_smt 表
- ✅ 在 DemoSystem 项目中测试完整流程

---

## 阶段 4: 元件级容器自动同步（第 4 周）

### 任务 4.1: 实现容器接口自动继承 ⭐⭐

**目标**: 当创建元件级容器时，自动从实体元件提取端口并同步

**文件涉及**:
- `BO/containerrepository.cpp` (ensureComponentContainer)
- `BO/container/containersyncservice.h/.cpp` （新建）

**具体步骤**:

1. **创建 ContainerSyncService 类**:
```cpp
// BO/container/containersyncservice.h
#ifndef CONTAINERSYNCSERVICE_H
#define CONTAINERSYNCSERVICE_H

#include <QSqlDatabase>
#include <QString>

class ContainerSyncService
{
public:
    explicit ContainerSyncService(const QSqlDatabase &db);
    
    // 从实体元件同步端口到容器
    bool syncPortsFromEquipment(int containerId, int equipmentId, QString *errorMessage = nullptr);
    
    // 从实体元件同步 SMT 模型到容器
    bool syncSmtFromEquipment(int containerId, int equipmentId, QString *errorMessage = nullptr);
    
private:
    QSqlDatabase m_db;
    
    // 辅助函数：提取元件的端口列表（从 TModel 或 port_config）
    QList<PortInfo> extractPortsFromEquipment(int equipmentId) const;
    
    // 辅助函数：将端口写入 container_interface 表
    bool writePortsToContainer(int containerId, const QList<PortInfo> &ports) const;
};

#endif // CONTAINERSYNCSERVICE_H
```

2. **实现 syncPortsFromEquipment 方法**:
```cpp
bool ContainerSyncService::syncPortsFromEquipment(int containerId, int equipmentId, QString *errorMessage)
{
    // 1. 提取元件的端口列表
    QList<PortInfo> ports = extractPortsFromEquipment(equipmentId);
    
    if (ports.isEmpty()) {
        if (errorMessage) {
            *errorMessage = "元件无端口配置";
        }
        return false;
    }
    
    // 2. 将端口写入 container_interface 表
    return writePortsToContainer(containerId, ports);
}
```

3. **实现 extractPortsFromEquipment 方法**:
```cpp
QList<PortInfo> ContainerSyncService::extractPortsFromEquipment(int equipmentId) const
{
    QList<PortInfo> ports;
    
    // 方法 1: 从 port_config 表读取（如果容器已有配置）
    // 首先查找该元件对应的容器 ID
    QSqlQuery queryContainer(m_db);
    queryContainer.prepare("SELECT container_id FROM container_component WHERE equipment_id = ?");
    queryContainer.addBindValue(equipmentId);
    
    if (queryContainer.exec() && queryContainer.next()) {
        int containerId = queryContainer.value(0).toInt();
        
        QSqlQuery queryPorts(m_db);
        queryPorts.prepare("SELECT function_block, port_name, port_type, variables_json "
                           "FROM port_config WHERE container_id = ?");
        queryPorts.addBindValue(containerId);
        
        if (queryPorts.exec()) {
            while (queryPorts.next()) {
                PortInfo port;
                port.functionBlock = queryPorts.value(0).toString();
                port.portName = queryPorts.value(1).toString();
                port.portType = queryPorts.value(2).toString();
                port.variablesJson = queryPorts.value(3).toString();
                ports.append(port);
            }
        }
    }
    
    // 方法 2: 从 TModel 解析端口（如果 port_config 为空）
    if (ports.isEmpty()) {
        QSqlQuery queryEquipment(m_db);
        queryEquipment.prepare("SELECT TModel FROM Equipment WHERE Equipment_ID = ?");
        queryEquipment.addBindValue(equipmentId);
        
        if (queryEquipment.exec() && queryEquipment.next()) {
            QString tmodel = queryEquipment.value(0).toString();
            // 使用 TModelParser 解析端口
            TModelParser parser;
            ports = parser.extractPorts(tmodel);
        }
    }
    
    return ports;
}
```

4. **修改 ensureComponentContainer 函数**:
```cpp
// BO/containerrepository.cpp
int ContainerRepository::ensureComponentContainer(int equipmentId)
{
    // ... 现有代码：检查是否已存在、创建容器 ...
    
    int containerId = createContainerForEquipment(equipmentId);
    
    if (containerId > 0) {
        // ✨ 新增：自动同步端口与 SMT 模型
        ContainerSyncService syncService(m_db);
        QString error;
        
        if (!syncService.syncPortsFromEquipment(containerId, equipmentId, &error)) {
            qWarning() << "同步端口失败:" << error;
        }
        
        if (!syncService.syncSmtFromEquipment(containerId, equipmentId, &error)) {
            qWarning() << "同步 SMT 模型失败:" << error;
        }
    }
    
    return containerId;
}
```

**验收标准**:
- ✅ 创建元件级容器时自动提取端口
- ✅ 端口正确写入 container_interface 表
- ✅ 容器的 SMT 模型正确写入 component_smt 表
- ✅ 在测试项目中验证同步逻辑

---

## 阶段 5: 文档与测试（第 5-6 周）

### 任务 5.1: 编写用户操作手册 ⭐⭐

**目标**: 提供清晰的用户文档，降低学习曲线

**文件涉及**:
- `docs/user_guide_function_management.md` （新建）
- `docs/user_guide_dmatrix.md` （新建）
- `docs/user_guide_smt_modeling.md` （新建）
- `docs/user_guide_port_config.md` （新建）

**具体步骤**:

1. **功能管理操作指南** (`docs/user_guide_function_management.md`):
   - 如何创建新功能
   - 如何使用"自动构建链路"
   - 如何查找依赖功能与边界条件
   - 如何执行完整性检查
   - 示例：为继电器电路建立功能

2. **D 矩阵生成与查看指南** (`docs/user_guide_dmatrix.md`):
   - 如何生成 D 矩阵
   - 如何查看与导出 D 矩阵
   - 如何选择故障/测试
   - D 矩阵与测试优选的关系

3. **SMT 建模规范** (`docs/user_guide_smt_modeling.md`):
   - T 语言模型语法规范
   - 端口命名约定
   - 参数与占位符使用
   - 故障模式定义
   - 示例：继电器、保险丝、电源的 SMT 模型

4. **端口配置与连接宏族使用指南** (`docs/user_guide_port_config.md`):
   - 如何配置端口类型
   - 如何选择连接宏族
   - 如何创建自定义宏族
   - 示例：三相电机的端口配置

**验收标准**:
- ✅ 每个文档包含清晰的步骤说明
- ✅ 每个文档包含至少一个完整示例
- ✅ 文档使用 markdown 格式，包含截图或图表
- ✅ 文档已审校，无明显错误

---

### 任务 5.2: 集成测试与验证 ⭐⭐⭐

**目标**: 在实际项目中验证所有功能的正确性

**测试项目**:
- `MyProjects/DemoSystem`
- `MyProjects/DemoWorkflow`
- `MyProjects/双电机拖曳收放装置`

**测试场景**:

1. **场景 1: 链路自动构建**
   - 在 DemoSystem 中打开功能管理
   - 创建新功能"电源回路"
   - 选择起点: T（输入电源）
   - 选择终点: FU（保险丝）
   - 点击"自动构建链路"
   - 预期：链路自动填入 `T,QS,FU`

2. **场景 2: 系统连接约束生成**
   - 在 DemoSystem 中打开项目
   - 点击"重新加载系统描述"
   - 预期：textEditSystemDiscription 中显示自动生成的连接约束
   - 验证：连接约束符合 SMT-LIB 语法

3. **场景 3: D 矩阵生成与查看**
   - 在 DemoSystem 中点击"D 矩阵"按钮
   - 点击"生成 D 矩阵"
   - 预期：D 矩阵正确显示故障-测试映射
   - 导出 CSV 文件，验证数据完整性

4. **场景 4: 元件级容器同步**
   - 在项目中插入新元件（如继电器 K2）
   - 为该元件配置端口
   - 预期：元件级容器自动创建，端口正确同步

**验收标准**:
- ✅ 所有测试场景通过
- ✅ 无严重 bug 或崩溃
- ✅ 性能可接受（复杂系统生成 D 矩阵 < 30 秒）
- ✅ 测试报告已编写，记录所有问题

---

## 总结

### 关键里程碑

| 周次 | 里程碑 | 完成标志 |
|------|--------|---------|
| Week 1 | 数据库迁移完成 | 所有项目数据库已更新到最新版本 |
| Week 2 | 链路自动构建可用 | 用户可在功能管理中自动构建链路 |
| Week 3 | 连接约束自动生成可用 | 系统描述自动包含正确的连接约束 |
| Week 4 | 元件级容器自动同步可用 | 插入元件时容器自动创建并同步 |
| Week 5-6 | 文档与测试完成 | 用户手册发布，所有测试场景通过 |

### 风险预案

**风险 1: 链路自动构建算法复杂度高**
- **预案**: 先实现简单场景（单起点、单终点），复杂场景手动补充

**风险 2: 连接约束生成性能问题**
- **预案**: 添加缓存机制，避免重复计算

**风险 3: 文档编写时间不足**
- **预案**: 优先完成核心功能文档，其他文档后续补充

---

**下一步行动**: 开始执行阶段 1 任务，修复数据库初始化脚本并编写迁移工具。
