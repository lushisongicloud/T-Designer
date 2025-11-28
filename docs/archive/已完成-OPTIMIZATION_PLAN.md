**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 性能优化实施方案 - 基于实测数据

## 实测性能数据总结

```
总耗时: 3270ms
├─ LoadProjectLines: 1886ms (57.7%)
│  ├─ LoadModelLineByUnits: 1446ms (44.2%)
│  │  ├─ JXB处理: 1180ms (960次GetUnitTermimalGaocengAndPos调用)
│  │  └─ ComboBox填充: 265ms
│  └─ LoadModelLineDT: 438ms (13.4%)
│     └─ Structure查询: 960次
├─ LoadProjectUnits: 1194ms (36.5%)
│  ├─ Equipment处理: 223ms (439次Symbol查询)
│  ├─ LoadUnitTable: 59ms
│  └─ 隐藏开销: 912ms (GetUnitSpurStrBySymbol_ID中的Symb2TermInfo查询)
└─ LoadProjectPages: 10ms (0.3%)
```

## 🎯 优化目标

将加载时间从 **3270ms 降低到 500ms 以内** (提升 85%)

## 📋 实施计划

### 阶段1: 创建缓存系统 (预计节省 2200ms)

#### 1.1 创建 ProjectDataCache 类

**文件**: `projectdatacache.h` / `projectdatacache.cpp`

**核心功能**:
- 一次性加载所有常用查询数据
- 提供 O(1) 查找接口
- 线程安全（如需要）

**缓存内容**:
```cpp
class ProjectDataCache {
public:
    struct LocationInfo {
        QString gaoceng;
        QString pos;
        int projectStructureId;
    };
    
    struct SymbolTermInfo {
        int symbolId;
        int equipmentId;
        QString designation;
        QStringList connNums;  // 从Symb2TermInfo获取
    };

    // 核心查找接口
    LocationInfo getEquipmentLocation(int equipmentId);
    LocationInfo getTerminalLocation(int terminalId);
    LocationInfo getStructureLocation(int structureId);
    SymbolTermInfo getSymbolInfo(int symbolId);
    QVector<int> getSymbolIdsByEquipment(int equipmentId);

private:
    QHash<int, LocationInfo> m_equipmentLocations;
    QHash<int, LocationInfo> m_terminalLocations;
    QHash<int, LocationInfo> m_structures;
    QHash<int, SymbolTermInfo> m_symbols;
    QMultiHash<int, int> m_equipmentSymbols;
};
```

#### 1.2 批量加载数据

**加载流程**:
```cpp
void ProjectDataCache::loadAll(QSqlDatabase &db) {
    loadStructures(db);      // ~30条记录
    loadEquipments(db);      // ~439条记录
    loadSymbols(db);         // ~1500条记录
    loadSymb2TermInfo(db);   // ~1500条记录
    // 总计约4次查询，替代原来的5760+次查询
}
```

**SQL查询示例**:
```sql
-- 一次性获取所有Equipment的位置信息(JOIN方式)
SELECT 
    e.Equipment_ID,
    e.ProjectStructure_ID,
    p1.Structure_INT as Pos,
    p2.Structure_INT as Gaoceng
FROM Equipment e
LEFT JOIN ProjectStructure p1 ON e.ProjectStructure_ID = p1.ProjectStructure_ID
LEFT JOIN ProjectStructure p2 ON p1.Parent_ID = p2.ProjectStructure_ID;

-- 一次性获取所有Symbol和Symb2TermInfo
SELECT 
    s.Symbol_ID,
    s.Equipment_ID,
    s.Designation,
    GROUP_CONCAT(st.ConnNum, ' ￤ ') as ConnNums
FROM Symbol s
LEFT JOIN Symb2TermInfo st ON s.Symbol_ID = st.Symbol_ID
GROUP BY s.Symbol_ID;
```

### 阶段2: 重构 LoadModelLineByUnits (预计节省 1100ms)

**当前问题**:
- 960次 GetUnitTermimalGaocengAndPos() 调用
- 每次调用 6 次数据库查询
- 总计 5760 次查询！

**优化后**:
```cpp
void MainWindow::LoadModelLineByUnits() {
    PerformanceTimer timer("LoadModelLineByUnits");
    
    // 1. 创建并加载缓存
    ProjectDataCache cache;
    cache.loadAll(T_ProjectDatabase);
    timer.checkpoint("缓存加载完成");
    
    // 2. 使用QHash优化节点查找
    QHash<QString, QStandardItem*> gaocengNodes;
    QHash<QPair<QString,QString>, QStandardItem*> posNodes;
    
    ModelLineByUnits->clear();
    // ... 根节点创建 ...
    
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);
    QString temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    
    while(QueryJXB.next()) {
        for(int index=0; index<2; index++) {
            int symbId = (index==0) 
                ? QueryJXB.value("Symb1_ID").toInt()
                : QueryJXB.value("Symb2_ID").toInt();
            int category = (index==0)
                ? QueryJXB.value("Symb1_Category").toInt()
                : QueryJXB.value("Symb2_Category").toInt();
                
            if(symbId == 0) continue;
            
            // 从缓存获取位置信息 (O(1) 而不是 6次查询)
            auto location = (category == 0) 
                ? cache.getEquipmentLocationBySymbId(symbId)
                : cache.getTerminalLocation(symbId);
                
            QString gaoceng = location.gaoceng;
            QString pos = location.pos;
            
            // 使用Hash快速查找节点 (O(1) 而不是 O(n))
            QString gaocengKey = gaoceng;
            if(!gaocengNodes.contains(gaocengKey)) {
                auto *node = new QStandardItem(QIcon("..."), gaoceng);
                node->setData("高层", Qt::WhatsThisRole);
                fatherItem->appendRow(node);
                gaocengNodes[gaocengKey] = node;
            }
            
            QPair<QString,QString> posKey(gaoceng, pos);
            if(!posNodes.contains(posKey)) {
                auto *node = new QStandardItem(QIcon("..."), pos);
                node->setData("位置", Qt::WhatsThisRole);
                gaocengNodes[gaocengKey]->appendRow(node);
                posNodes[posKey] = node;
            }
            
            // 插入设备/端子节点
            InsertUnitTerminalToItem(posNodes[posKey], QueryJXB, index);
        }
    }
    
    timer.checkpoint("JXB处理完成");
    // ... 其余代码 ...
}
```

**优化效果**:
- 查询次数: 5760次 → 4次
- 节点查找: O(n) → O(1)
- 预计耗时: 1180ms → ~50ms
- **节省约 1100ms**

### 阶段3: 重构 LoadModelLineDT (预计节省 400ms)

**当前问题**:
- 960次 ProjectStructure 查询

**优化后**:
```cpp
void MainWindow::LoadModelLineDT() {
    PerformanceTimer timer("LoadModelLineDT");
    
    // 使用阶段1创建的缓存
    ProjectDataCache cache;
    cache.loadAll(T_ProjectDatabase);
    timer.checkpoint("缓存加载完成");
    
    // 使用Hash优化节点查找
    QHash<QString, QStandardItem*> gaocengNodes;
    QHash<QPair<QString,QString>, QStandardItem*> posNodes;
    
    ModelLineDT->clear();
    // ... 根节点创建 ...
    
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);
    QString temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    
    while(QueryJXB.next()) {
        int projectStructureId = QueryJXB.value("ProjectStructure_ID").toInt();
        
        // 从缓存获取位置信息 (替代2次查询)
        auto location = cache.getStructureLocation(projectStructureId);
        QString gaoceng = location.gaoceng;
        QString pos = location.pos;
        
        // 使用Hash快速查找节点
        // ... (同上) ...
        
        InsertLineToItem(posNodes[posKey], QueryJXB);
    }
    
    timer.checkpoint("JXB处理完成");
}
```

**优化效果**:
- 查询次数: 960次 → 复用缓存 (0次额外查询)
- 预计耗时: 437ms → ~30ms
- **节省约 400ms**

### 阶段4: 优化 LoadProjectUnits (预计节省 700ms)

**当前问题**:
- 439次 Symbol 查询
- 每个Symbol调用 GetUnitSpurStrBySymbol_ID() (查询Symb2TermInfo)
- 隐藏开销 912ms

**优化后**:
```cpp
void MainWindow::LoadProjectUnits() {
    PerformanceTimer timer("LoadProjectUnits");
    
    // 使用缓存
    ProjectDataCache cache;
    cache.loadAll(T_ProjectDatabase);
    timer.checkpoint("缓存加载完成");
    
    // ... 展开状态保存等 ...
    
    // 批量查询Equipment和Symbol (使用JOIN)
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);
    QString temp = "SELECT * FROM Equipment ORDER BY DT";
    QueryEquipment.exec(temp);
    
    while(QueryEquipment.next()) {
        int equipmentId = QueryEquipment.value("Equipment_ID").toInt();
        
        // 从缓存获取所有Symbol (替代单次查询)
        auto symbolIds = cache.getSymbolIdsByEquipment(equipmentId);
        
        // ... 创建设备节点 ...
        
        for(int symbolId : symbolIds) {
            // 从缓存获取Symbol信息 (包含Symb2TermInfo数据)
            auto symbolInfo = cache.getSymbolInfo(symbolId);
            
            // 构建显示字符串 (无需查询数据库)
            QString unitSpurStr = symbolInfo.designation.isEmpty() 
                ? symbolInfo.connNums.join(" ￤ ")
                : symbolInfo.designation + ":" + symbolInfo.connNums.join(" ￤ ");
            
            // 创建子块节点
            auto *item = new QStandardItem(icon, unitSpurStr);
            // ...
        }
    }
    
    timer.checkpoint("Equipment处理完成");
}
```

**优化效果**:
- Symbol查询: 439次 → 复用缓存
- Symb2TermInfo查询: ~1500次 → 复用缓存
- 预计耗时: 1194ms → ~400ms
- **节省约 700-800ms**

## 📊 预期优化效果

| 阶段 | 当前耗时 | 优化后 | 节省 | 累计节省 |
|-----|---------|--------|------|---------|
| 缓存初始化 | 0ms | 50ms | -50ms | -50ms |
| LoadModelLineByUnits | 1446ms | 100ms | 1346ms | 1296ms |
| LoadModelLineDT | 438ms | 50ms | 388ms | 1684ms |
| LoadProjectUnits | 1194ms | 400ms | 794ms | 2478ms |
| LoadProjectPages | 10ms | 10ms | 0ms | 2478ms |
| **总计** | **3270ms** | **~660ms** | **2610ms** | **80%⬆️** |

## 🔧 实施步骤

### 第1步: 创建缓存系统 (1-2小时)

1. 创建 `projectdatacache.h` 和 `projectdatacache.cpp`
2. 实现数据加载和查询接口
3. 单元测试验证缓存正确性

### 第2步: 逐个优化函数 (3-4小时)

1. 优化 LoadModelLineByUnits (最大收益)
2. 优化 LoadModelLineDT
3. 优化 LoadProjectUnits
4. 每次优化后测试验证

### 第3步: 性能测试和调优 (1小时)

1. 运行性能分析
2. 对比优化前后数据
3. 微调和完善

## 💡 注意事项

### 缓存一致性
- 缓存在LoadProject时创建，整个加载过程共享
- 如果需要支持热更新，需要实现缓存失效机制

### 内存消耗
- 预计缓存占用内存: ~2-5MB (对于439个设备的项目)
- 对于更大的项目，可以考虑使用LRU缓存

### 兼容性
- 保留原有函数接口，逐步替换调用点
- 可以添加开关控制是否使用缓存（用于回退）

## 🚀 下一步

需要我立即开始实现缓存系统吗？我可以：
1. 创建 `projectdatacache.h` 和 `.cpp` 文件
2. 实现核心的数据加载和查询接口
3. 修改 LoadModelLineByUnits 使用缓存
4. 提供详细的测试步骤

是否开始实施？
