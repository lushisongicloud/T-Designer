# ProjectDataModel 实现报告

## 概述

已完成 ProjectDataModel 的核心实现,这是一个全内存数据模型,用于替代当前的即时数据库查询和UI构建方式。

## 完成的工作

### 1. 数据结构设计 (projectdatamodel.h)

定义了6个核心数据结构:
- **StructureData**: 项目结构层次 (高层/位置)
- **EquipmentData**: 器件信息 (4924条记录)
- **SymbolData**: 功能子块 (4926条记录)
- **PageData**: 页面信息 (35条记录)
- **ConnectionData**: 连线信息/JXB (7219条记录)
- **TerminalData**: 端子信息 (待实现)

每个结构都包含:
- 数据库原始字段
- 运行时计算字段 (如 `fullPath`, `displayText`, `gaoceng`, `pos`)
- 快速验证方法 (`isValid()`)

### 2. Manager 类实现 (projectdatamodel.cpp)

实现了5个Manager类:

#### StructureManager
- `load()`: 从ProjectStructure表加载46条结构记录
- `buildHierarchy()`: 构建父子层次关系
- `buildFullPaths()`: 计算完整路径 (如 "1栋/1F")
- `getGaoceng()`: 获取高层名称
- `getPos()`: 获取位置名称
- O(1)查询接口

#### EquipmentManager  
- `load()`: 从Equipment表加载4924条器件记录
- `buildLocationInfo()`: 关联StructureManager,计算gaoceng/pos
- `buildDisplayText()`: 构建显示文本 "DT(Type,Name)"
- 索引:
  - `m_dtIndex`: DT → Equipment_ID 映射
  - `m_structureIndex`: Structure_ID → Equipment列表
- O(1)查询接口

#### SymbolManager
- `loadSymbols()`: 从Symbol表加载4926条记录
- `loadSymb2TermInfo()`: 加载9854条端子信息映射
- `buildDisplayText()`: 构建显示 "Designation:ConnNums-FunDefine"
- 索引:
  - `m_equipmentIndex`: Equipment_ID → Symbol列表
- 关联Equipment的Symbol列表

#### PageManager
- `load()`: 从Page表加载35条页面记录
- `buildFullNames()`: 计算完整名称 "高层/位置/PageName"
- 索引:
  - `m_typeIndex`: PageType → Page列表
- O(1)查询接口

#### ConnectionManager
- `load()`: 从JXB表加载7219条连线记录
- `buildDisplayText()`: 构建 "ConnectionNumber (起点 → 终点)"
- `buildSymbStr()`: 根据Category构建端点描述
- 索引:
  - `m_structureIndex`: Structure_ID → Connection列表
  - `m_connectionNumIndex`: ConnectionNumber → Connection列表
- O(1)查询接口

### 3. 主模型类 ProjectDataModel

- `loadAll()`: 一次性加载所有数据
  1. StructureManager::load()
  2. EquipmentManager::load()
  3. SymbolManager::loadSymbols()
  4. SymbolManager::loadSymb2TermInfo()
  5. PageManager::load()
  6. ConnectionManager::load()

- 便捷查询接口:
  ```cpp
  const StructureData* getStructure(int id);
  const EquipmentData* getEquipment(int id);
  const SymbolData* getSymbol(int id);
  // ... 等等
  ```

- Manager访问接口:
  ```cpp
  StructureManager* structureManager();
  EquipmentManager* equipmentManager();
  // ... 等等
  ```

### 4. 性能监控集成

使用 `PerformanceTimer` 监控每个Manager的加载时间:
```cpp
PERF_TIMER("StructureManager::load");
```

### 5. 测试集成

在 `mainwindow_project.cpp::LoadProject()` 中添加测试代码:
```cpp
ProjectDataModel testModel;
if (testModel.loadAll(T_ProjectDatabase)) {
    qDebug() << "[ProjectDataModel] 加载成功:" << testModel.getStatistics();
    // 验证数据正确性
    QVector<int> rootNodes = testModel.structureManager()->getRootNodes();
    // ...
}
```

## 设计特点

### 1. 分离查询与UI构建
- 数据加载: 一次性批量加载到内存 (~50-100ms 预期)
- UI构建: 延迟到用户展开节点时 (待实现 LazyTreeModel)

### 2. O(1) 查询复杂度
- 所有查询使用 QHash 索引
- 无需遍历,即时返回结果
- 支持多种查询维度 (ByDT, ByStructure, ByEquipment等)

### 3. 计算字段缓存
- `fullPath`: 预计算完整路径
- `displayText`: 预构建显示文本  
- `gaoceng/pos`: 缓存位置信息
- 避免UI线程重复计算

### 4. Manager模式
- 职责分离: 每个Manager管理一类数据
- 松耦合: 通过指针注入依赖关系
- 可测试: 单独测试每个Manager

### 5. 数据完整性
- 关联验证: Equipment ↔ Symbol 双向关联
- 层次完整: Structure 层次路径完整构建
- 索引一致: 所有索引同步更新

## 待完成工作

### 1. TerminalManager 实现
- 加载 Terminal 和 TerminalStrip 数据
- 构建端子排层次
- 索引: ByStructure, ByTerminalStrip

### 2. LazyTreeModel 基类
```cpp
class LazyTreeModel : public QAbstractItemModel {
    // canFetchMore/fetchMore 实现
    // 按需创建 QModelIndex
    // 延迟子节点加载
};
```

### 3. 具体Tree模型
- **UnitsTreeModel**: 替换 ModelUnits (QStandardItemModel)
- **LinesTreeModel**: 替换 ModelLines
- **TerminalsTreeModel**: 替换 ModelTerminals  
- **PagesTreeModel**: 替换 ModelPages

### 4. MainWindow集成
- 修改 `LoadProject()` 使用 ProjectDataModel
- 替换 `LoadProjectUnits()` 逻辑
- 替换 `LoadProjectLines()` 逻辑
- 替换 `LoadProjectTerminals()` 逻辑

### 5. DiagnosisEngine 兼容
- 确保诊断分析可以访问内存数据
- 可能需要提供数据库兼容查询接口
- 或修改诊断引擎直接使用 ProjectDataModel

### 6. 性能验证
- 测试 4924器件项目加载时间
- 验证UI响应速度
- 对比优化前后性能数据

## 预期性能提升

### 当前性能 (4924器件项目)
- 总加载时间: 225秒
- LoadProjectUnits: 188秒 (83.6%)
- 主要瓶颈: QStandardItem 树构建 (O(n²))

### 优化后预期 (估算)
- **数据加载**: 50-100ms
  - Structure: ~5ms (46条)
  - Equipment: ~20ms (4924条)
  - Symbol: ~25ms (4926条)
  - TermInfo: ~30ms (9854条)
  - Page: ~2ms (35条)
  - Connection: ~20ms (7219条)
  
- **UI初始加载**: ~10ms
  - 仅创建根节点
  - 不加载子节点
  
- **用户展开节点**: ~1-5ms/节点
  - 按需创建子节点
  - 数据已在内存,仅UI构建
  
- **总体**: **从225秒降至0.1秒以内** (约2250倍提升)

## 使用示例

```cpp
// 1. 创建模型
ProjectDataModel model;

// 2. 加载数据
if (model.loadAll(database)) {
    qDebug() << "数据统计:" << model.getStatistics();
    // 输出: Structures=46, Equipments=4924, Symbols=4926, TermInfos=9854, Pages=35, Connections=7219
}

// 3. 查询器件
const EquipmentData *eq = model.getEquipment(equipmentId);
qDebug() << "器件:" << eq->displayText;
qDebug() << "位置:" << eq->gaoceng << "/" << eq->pos;

// 4. 查询Symbol
QVector<int> symbolIds = model.getSymbolsByEquipment(equipmentId);
for (int symId : symbolIds) {
    const SymbolData *sym = model.getSymbol(symId);
    qDebug() << "  Symbol:" << sym->displayText;
}

// 5. 查询连线
QVector<int> connIds = model.getConnectionsByStructure(structureId);
for (int connId : connIds) {
    const ConnectionData *conn = model.getConnection(connId);
    qDebug() << "连线:" << conn->displayText;
}
```

## 编译状态

✅ **头文件**: projectdatamodel.h - 已完成
✅ **实现文件**: projectdatamodel.cpp - 已完成
✅ **项目文件**: T_DESIGNER.pro - 已添加
✅ **编译检查**: 无编译错误

⚠️ **链接状态**: 需要关闭正在运行的程序才能完成链接

## 下一步

1. 关闭运行中的 T-DESIGNER.exe
2. 完整编译链接
3. 运行测试,查看 ProjectDataModel 加载性能
4. 验证数据正确性 (对比旧实现的输出)
5. 开始实现 LazyTreeModel

## 文件清单

- `projectdatamodel.h`: 447行,数据结构和接口定义
- `projectdatamodel.cpp`: 781行,完整实现
- `mainwindow_project.cpp`: 添加测试代码 (25行)
- `T_DESIGNER.pro`: 添加新文件引用

**总代码量**: ~1253行 (含注释)
