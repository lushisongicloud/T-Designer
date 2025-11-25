# SMT集成使用指南

## 概述

本文档说明如何使用新实现的SMT仓库接口来访问器件描述、端口配置和连接宏族。

## 核心类概览

### 1. SmtRepository
管理组件和系统的SMT描述。

**主要功能：**
- 从ref/Model.db读取T-Solver风格的组件模板
- 从项目数据库读取/保存组件实例和系统SMT
- 自动替换模板占位符

### 2. SystemEntity（新增接口）
提供对系统组件列表和连接关系的访问。

**主要功能：**
- 获取组件实体列表
- 获取连接描述
- 从数据库构建系统描述

### 3. PortConfigRepository
管理端口配置（类型、变量、宏族关联）。

**主要功能：**
- 配置端口类型（electric/hydraulic/mechanical）
- 配置端口变量（默认或自定义）
- 关联连接宏族

### 4. MacroFamilyRepository
管理连接宏族，提供宏展开功能。

**主要功能：**
- 管理内置和自定义宏族
- 根据端口数量自动选择宏
- 展开宏为SMT约束

## 使用示例

### 示例1：获取组件SMT模板

```cpp
#include "BO/smtrepository.h"

// 创建SmtRepository实例
QSqlDatabase projectDb = QSqlDatabase::database();
SmtRepository smtRepo(projectDb, "ref/Model.db");

// 获取继电器KM的SMT模板
QString errorMsg;
QString kmTemplate = smtRepo.getComponentTemplate("KM", &errorMsg);
if (kmTemplate.isEmpty()) {
    qWarning() << "获取模板失败:" << errorMsg;
} else {
    qDebug() << "KM模板:" << kmTemplate;
}

// 获取组件的变量声明部分
QString kmVars = smtRepo.getComponentVariableDeclarations("KM", &errorMsg);

// 获取组件的约束描述部分
QString kmDesc = smtRepo.getComponentDescription("KM", &errorMsg);

// 获取组件的故障模式
QString kmFailure = smtRepo.getComponentFailureMode("KM", &errorMsg);
```

### 示例2：保存组件实例SMT

```cpp
#include "BO/smtrepository.h"

QSqlDatabase projectDb = QSqlDatabase::database();
SmtRepository smtRepo(projectDb);

// 为设备ID=123保存SMT描述
int equipmentId = 123;
QString smtText = 
    "(declare-fun KM1.A1_A2.i () Real)\n"
    "(declare-fun KM1.A1_A2.u () Real)\n"
    "(assert (= (* KM1.A1_A2.i R) (- KM1.A1_A2.u 220)))";
    
QString errorMsg;
bool success = smtRepo.saveComponentSmt(equipmentId, smtText, "", &errorMsg);
if (!success) {
    qWarning() << "保存SMT失败:" << errorMsg;
}

// 读取已保存的SMT
QString savedSmt = smtRepo.getComponentSmt(equipmentId, &errorMsg);
```

### 示例3：从SystemEntity获取组件和连接信息

```cpp
#include "BO/systementity.h"

SystemEntity *systemEntity = /* 获取SystemEntity实例 */;

// 准备模型（解析系统描述）
QString systemDescription = "DEF BEGIN\nKM KM1()\nL L1()\nDEF END\nconnect2e(KM1.1, L1.1)\n";
systemEntity->prepareModel(systemDescription);

// 获取组件列表
QList<ComponentEntity> components = systemEntity->getComponentEntityList();
for (const ComponentEntity &comp : components) {
    qDebug() << "组件:" << comp.getName();
}

// 获取组件名称列表
QStringList componentNames = systemEntity->getComponentNames();

// 获取指定组件
ComponentEntity km1 = systemEntity->getComponentByName("KM1");

// 获取连接描述
QStringList connections = systemEntity->getConnectionDescriptions();
for (const QString &conn : connections) {
    qDebug() << "连接:" << conn;
}

// 获取系统链路代码
QString systemLinkCode = systemEntity->getSystemLinkCode();
```

### 示例4：从数据库构建系统描述

```cpp
#include "BO/systementity.h"

SystemEntity *systemEntity = /* 获取SystemEntity实例 */;
QSqlDatabase projectDb = QSqlDatabase::database();

// 从项目数据库构建系统描述
QString errorMsg;
QString systemDesc = systemEntity->buildSystemDescriptionFromDatabase(projectDb, &errorMsg);
if (systemDesc.isEmpty()) {
    qWarning() << "构建系统描述失败:" << errorMsg;
} else {
    qDebug() << "系统描述:\n" << systemDesc;
    // 输出格式：
    // DEF BEGIN
    // KM KM1(Resistance=2200,ActCurrent=0.1)
    // L L1(Resistance=0.5)
    // DEF END
    // 
    // 导线 1
    // 导线 2
}

// 然后可以用生成的系统描述进行解析
systemEntity->prepareModel(systemDesc);
```

### 示例5：配置端口

```cpp
#include "BO/portconfigrepository.h"

QSqlDatabase projectDb = QSqlDatabase::database();
PortConfigRepository portRepo(projectDb);

// 创建端口配置
PortConfig config;
config.containerId = 1;
config.functionBlock = "Coil";
config.portName = "A1";
config.portType = "electric";
config.direction = "bidirectional";
config.variableProfile = "default";
config.variables = PortConfig::getDefaultVariables("electric"); // ["i", "u"]
config.connectMacroFamily = "electric-connect";

// 保存端口配置
QString errorMsg;
bool success = portRepo.savePortConfig(config, &errorMsg);

// 查询容器的所有端口配置
QList<PortConfig> configs = portRepo.getPortConfigsByContainer(1, &errorMsg);
for (const PortConfig &cfg : configs) {
    qDebug() << "端口:" << cfg.functionBlock << "." << cfg.portName 
             << "类型:" << cfg.portType 
             << "变量:" << cfg.variables.join(",");
}
```

### 示例6：使用连接宏族

```cpp
#include "BO/macrofamilyrepository.h"

QSqlDatabase projectDb = QSqlDatabase::database();
MacroFamilyRepository macroRepo(projectDb);

// 初始化内置宏族（只需要在项目加载时执行一次）
QString errorMsg;
if (!macroRepo.initializeBuiltinMacroFamilies(&errorMsg)) {
    qWarning() << "初始化内置宏族失败:" << errorMsg;
}

// 获取所有宏族
QList<MacroFamily> families = macroRepo.getAllMacroFamilies(&errorMsg);
for (const MacroFamily &family : families) {
    qDebug() << "宏族:" << family.familyName 
             << "领域:" << family.domain 
             << "内置:" << (family.isBuiltin ? "是" : "否");
}

// 展开3端口电气连接宏
QStringList ports = {"KM1.Coil.A1", "KM1.Coil.A2", "L1.1"};
QString expanded = macroRepo.expandMacro("electric-connect", 3, ports, &errorMsg);
qDebug() << "展开结果:\n" << expanded;
// 输出：
// (assert (= (+ KM1.Coil.A1.i KM1.Coil.A2.i L1.1.i) 0))
// (assert (= KM1.Coil.A1.u KM1.Coil.A2.u))
// (assert (= KM1.Coil.A2.u L1.1.u))

// 创建自定义宏族
MacroFamily customFamily;
customFamily.familyName = "my-custom-family";
customFamily.domain = "electric";
customFamily.description = "我的自定义连接宏族";
customFamily.isBuiltin = false;

// 添加2端口宏
ConnectionMacro macro2;
macro2.arity = 2;
macro2.macroName = "my2e";
macro2.expansionTemplate = "(assert (my-custom-constraint %1 %2))";
customFamily.macros.insert(2, macro2);

// 保存自定义宏族
macroRepo.saveMacroFamily(customFamily, &errorMsg);
```

## 集成到现有代码

### 在MainWindow中初始化

建议在MainWindow::LoadModel()中初始化内置宏族：

```cpp
void MainWindow::LoadModel()
{
    // ... 现有代码 ...
    
    systemEntity = new SystemEntity(database);
    
    // 初始化内置宏族
    QSqlDatabase projectDb = database->getDatabase();
    MacroFamilyRepository macroRepo(projectDb);
    QString errorMsg;
    if (!macroRepo.initializeBuiltinMacroFamilies(&errorMsg)) {
        qWarning() << "初始化内置宏族失败:" << errorMsg;
    }
    
    // ... 现有代码继续 ...
}
```

### 在SelectFunctionDialog中使用

```cpp
// 在构造函数或适当的地方
SmtRepository smtRepo(projectDb);
QString errorMsg;

// 获取系统描述
QString sysDesc = systemEntity->buildSystemDescriptionFromDatabase(projectDb, &errorMsg);
if (!sysDesc.isEmpty()) {
    systemEntity->prepareModel(sysDesc);
}

// 访问组件信息
QStringList componentNames = systemEntity->getComponentNames();
// ... 使用组件名称 ...
```

## 数据库表结构

### component_smt 表
存储组件实例和容器的SMT描述。

| 字段 | 类型 | 说明 |
|------|------|------|
| component_smt_id | INTEGER | 主键 |
| equipment_id | INTEGER | 设备ID（可空，与container_id互斥） |
| container_id | INTEGER | 容器ID（可空，与equipment_id互斥） |
| model_scope | TEXT | 模型范围（component/system） |
| smt_text | TEXT | SMT描述文本 |
| port_signature | TEXT | 端口签名 |
| syntax_status | TEXT | 语法状态（unknown/valid/invalid） |

### port_config 表
存储端口配置。

| 字段 | 类型 | 说明 |
|------|------|------|
| port_config_id | INTEGER | 主键 |
| container_id | INTEGER | 容器ID |
| function_block | TEXT | 功能子块名称 |
| port_name | TEXT | 端口名称 |
| port_type | TEXT | 端口类型（electric/hydraulic/mechanical/other） |
| direction | TEXT | 方向（input/output/bidirectional） |
| variable_profile | TEXT | 变量配置（default/custom） |
| variables_json | TEXT | 变量列表（JSON数组） |
| connect_macro | TEXT | 关联的宏族名称 |

### port_connect_macro_family 表
存储连接宏族定义。

| 字段 | 类型 | 说明 |
|------|------|------|
| family_id | INTEGER | 主键 |
| family_name | TEXT | 宏族名称（唯一） |
| domain | TEXT | 领域（electric/hydraulic/mechanical/other） |
| description | TEXT | 描述 |
| is_builtin | INTEGER | 是否内置（0/1） |
| macros_json | TEXT | 宏定义（JSON数组） |

macros_json格式示例：
```json
[
  {
    "arity": 2,
    "macro_name": "connect2e",
    "expansion": "(assert (= (+ %1.i %2.i) 0))\\n(assert (= %1.u %2.u))"
  },
  {
    "arity": 3,
    "macro_name": "connect3e",
    "expansion": "(assert (= (+ %1.i %2.i %3.i) 0))\\n(assert (= %1.u %2.u))\\n(assert (= %2.u %3.u))"
  }
]
```

## 后续工作

接下来需要实现的功能：

1. **连接自动生成**：从CAD连接自动生成SMT约束
   - 解析JXB表的连接关系
   - 识别连接点的端口及其类型
   - 根据端口数量自动选择合适的宏
   - 调用expandMacro()生成约束

2. **UI集成**：
   - 元件属性对话框中添加SMT编辑和验证
   - 端口配置界面
   - 宏族管理界面

3. **验证功能**：
   - 集成SmtSyntaxChecker进行语法检查
   - 验证端口与变量一致性

4. **功能管理数据库持久化**：
   - 使用function_definition表存储功能
   - XML与数据库双向同步

## 参考资料

- README.md - 项目总体目标和T-Solver模型说明
- BO/systementity.h - SystemEntity接口定义
- BO/smtrepository.h - SMT仓库接口
- BO/portconfigrepository.h - 端口配置接口
- BO/macrofamilyrepository.h - 宏族管理接口
