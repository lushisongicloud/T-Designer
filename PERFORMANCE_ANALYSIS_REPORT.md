# 性能分析报告 - 集中油源动力系统项目

## 测试项目信息
- **项目名称**: 集中油源动力系统
- **器件数量**: 439
- **页面数量**: 30
- **JXB连线数**: 未统计(待下次运行确认)

## 总体性能数据

| 模块 | 耗时(ms) | 占比 | 状态 |
|-----|---------|------|------|
| LoadProjectPages | 8 | 0.3% | ✅ 正常 |
| LoadProjectUnits | 1181 | 40.1% | ⚠️ 需优化 |
| LoadProjectTerminals | 3 | 0.1% | ✅ 正常 |
| LoadProjectLines | 1701 | 57.8% | 🔴 严重瓶颈 |
| **总计** | **2945** | **100%** | |

## 详细分析

### 🔴 严重瓶颈1: LoadProjectLines (1701ms, 57.8%)

**子模块分解:**
- `LoadModelLineDT`: 418ms (24.6%)
- `LoadModelLineByUnits`: 1283ms (75.4%) ⚠️ **主要问题**

#### LoadModelLineDT 问题分析
```cpp
// 对每个 JXB 执行 2 次 ProjectStructure 查询
while(QueryJXB.next()) {  // 假设有 N 个 JXB
    // 查询 1: 获取位置
    SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = ?
    // 查询 2: 获取高层
    SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = ?
}
```
**问题**: N+1 查询模式
- 如果有 500 个 JXB，就会执行 1000 次 ProjectStructure 查询
- 每次查询约 0.8ms，累计耗时显著

#### LoadModelLineByUnits 问题分析
```cpp
while(QueryJXB.next()) {  // 对每个 JXB
    for(int index=0; index<2; index++) {  // 处理两端(Symb1和Symb2)
        GetUnitTermimalGaocengAndPos(...);  // 这个函数很可能有多次查询
        // 然后是嵌套循环查找树节点
        for(int i=0; i<fatherItem->rowCount(); i++) { ... }
    }
}
```

**预计问题**:
1. `GetUnitTermimalGaocengAndPos()` 对每个连线端点执行查询
2. 嵌套循环查找树节点 (O(n²) 复杂度)
3. 每个 JXB 处理 2 次（两个端点）

**预计查询数**:
- 如果有 1000 个 JXB，就会调用 2000 次 `GetUnitTermimalGaocengAndPos()`
- 每次调用可能执行 2-3 次数据库查询
- 总查询数: 4000-6000 次！

### ⚠️ 瓶颈2: LoadProjectUnits (1181ms, 40.1%)

**子模块分解:**
- Equipment表查询: 3ms
- Equipment表处理: 220ms (439个器件，439次Symbol查询)
- LoadUnitTable: 63ms
- **未明确跟踪的时间**: ~894ms (75.7%) ⚠️ **隐藏问题**

#### 问题分析

1. **Symbol 子查询 (220ms)**
```cpp
while(QueryEquipment.next()) {  // 439次
    SELECT * FROM Symbol WHERE Equipment_ID = ?  // 每次查询约0.5ms
}
```

2. **GetUnitSpurStrBySymbol_ID() 函数 (~894ms)**
```cpp
QString GetUnitSpurStrBySymbol_ID(QSqlQuery QuerySymbol) {
    // 对每个 Symbol 查询一次 Symb2TermInfo
    SELECT * FROM Symb2TermInfo WHERE Symbol_ID = ?
}
```

**预计问题**:
- 假设 439 个 Equipment 有 1500 个 Symbol
- 每个 Symbol 调用一次 `GetUnitSpurStrBySymbol_ID()`
- 每次调用执行 1 次 Symb2TermInfo 查询
- 如果每次查询 0.6ms，总耗时: 1500 × 0.6ms = 900ms ✅ **符合观察**

### ✅ 正常模块

- **LoadProjectPages** (8ms): 性能优秀
- **LoadProjectTerminals** (3ms): 性能优秀（本项目无端子排）

## 🎯 优化方案（按优先级）

### 优先级1: 优化 LoadModelLineByUnits (预计节省 800-1000ms)

**方案A: 批量查询 + 缓存**
```cpp
// 1. 一次性获取所有 ProjectStructure
QMap<int, StructureInfo> structureCache;
QSqlQuery query("SELECT ProjectStructure_ID, Structure_INT, Parent_ID, Structure_ID FROM ProjectStructure");
while(query.next()) {
    structureCache[query.value(0).toInt()] = {...};
}

// 2. 一次性获取所有 Equipment 的位置信息
QMap<int, QPair<QString,QString>> equipmentLocationCache;
QSqlQuery query("SELECT Equipment_ID, e.ProjectStructure_ID, p1.Structure_INT as Pos, p2.Structure_INT as Gaoceng "
                "FROM Equipment e "
                "LEFT JOIN ProjectStructure p1 ON e.ProjectStructure_ID = p1.ProjectStructure_ID "
                "LEFT JOIN ProjectStructure p2 ON p1.Parent_ID = p2.ProjectStructure_ID");

// 3. 使用缓存代替 GetUnitTermimalGaocengAndPos()
while(QueryJXB.next()) {
    // 从缓存中O(1)获取，而不是执行查询
    auto location = equipmentLocationCache.value(equipmentId);
}
```

**预期效果**: 
- 从 2000 次查询减少到 2 次查询
- 耗时从 1283ms 降低到 200-300ms
- **节省约 1000ms**

**方案B: 使用 QHash 优化树节点查找**
```cpp
// 当前: O(n) 线性搜索
for(int i=0; i<fatherItem->rowCount(); i++) {
    if(fatherItem->child(i,0)->data(...) == target) { ... }
}

// 优化: O(1) Hash 查找
QHash<QString, QStandardItem*> gaocengNodes;
QHash<QString, QStandardItem*> posNodes;
// 直接获取
QStandardItem* node = gaocengNodes.value(gaocengKey);
```

**预期效果**: 
- 减少 CPU 计算时间
- 节省约 100-200ms

### 优先级2: 优化 LoadModelLineDT (预计节省 200-300ms)

**方案: 批量查询 ProjectStructure**
```cpp
// 当前: 每个 JXB 查询 2 次
for each JXB:
    SELECT ... WHERE ProjectStructure_ID = ?  // 查询1
    SELECT ... WHERE ProjectStructure_ID = ?  // 查询2

// 优化: 使用上面建立的 structureCache
for each JXB:
    auto pos = structureCache.value(projectStructureId);
    auto gaoceng = structureCache.value(pos.parentId);
```

**预期效果**:
- 耗时从 418ms 降低到 100-150ms
- **节省约 300ms**

### 优先级3: 优化 LoadProjectUnits (预计节省 600-800ms)

**方案A: 批量查询 Symbol**
```cpp
// 当前: 439 次查询
for each Equipment:
    SELECT * FROM Symbol WHERE Equipment_ID = ?

// 优化: 1 次查询
SELECT * FROM Symbol WHERE Equipment_ID IN (1,2,3,...439)
// 然后在内存中按 Equipment_ID 分组
QMultiMap<int, SymbolInfo> symbolsByEquipment;
```

**预期效果**: 节省约 200ms

**方案B: 批量查询 Symb2TermInfo**
```cpp
// 当前: 每个 Symbol 查询 1 次 (约1500次)
for each Symbol:
    SELECT * FROM Symb2TermInfo WHERE Symbol_ID = ?

// 优化: 1 次查询所有
SELECT * FROM Symb2TermInfo WHERE Symbol_ID IN (1,2,3,...1500)
// 在内存中按 Symbol_ID 分组
QMultiMap<int, TermInfo> termsBySymbol;
```

**预期效果**: 节省约 600-800ms

## 🚀 实施计划

### 第一阶段: 快速见效（预计2-3小时）

1. **创建缓存辅助类** (30分钟)
```cpp
class ProjectDataCache {
public:
    void loadAll(QSqlDatabase &db);
    QPair<QString,QString> getEquipmentLocation(int equipmentId);
    StructureInfo getStructure(int structureId);
private:
    QHash<int, StructureInfo> structures;
    QHash<int, QPair<QString,QString>> equipmentLocations;
};
```

2. **优化 LoadModelLineByUnits** (1小时)
   - 使用缓存替代 GetUnitTermimalGaocengAndPos()
   - 使用 QHash 优化节点查找

3. **优化 LoadModelLineDT** (30分钟)
   - 使用缓存替代重复查询

4. **测试验证** (30-60分钟)

### 第二阶段: 彻底优化（预计2-3小时）

5. **优化 LoadProjectUnits**
   - 批量查询 Symbol
   - 批量查询 Symb2TermInfo
   - 修改 GetUnitSpurStrBySymbol_ID 支持缓存模式

6. **性能测试和调优**

## 📈 预期优化效果

| 阶段 | 当前耗时 | 优化后耗时 | 节省 | 提升 |
|-----|---------|-----------|------|------|
| 第一阶段 | 2945ms | ~1500ms | 1445ms | 49% ⬆️ |
| 第二阶段 | 1500ms | ~700ms | 800ms | 53% ⬆️ |
| **总计** | **2945ms** | **~700ms** | **2245ms** | **76% ⬆️** |

**最终目标**: 将 3 秒的加载时间降低到 0.7 秒以内！

## 🔍 需要进一步确认的信息

请运行更新后的代码，收集以下数据:

1. **LoadModelLineDT** 中的 JXB 数量和 Structure 查询次数
2. **LoadModelLineByUnits** 中的 JXB 数量和 `GetUnitTermimalGaocengAndPos` 调用次数
3. **Symbol** 的总数量
4. **Symb2TermInfo** 的总记录数

这些数据将帮助我们更精确地估算优化效果。

## 📝 下次运行时请注意

编译并运行更新后的代码，查看这些新的调试信息:
```
>>> [性能分析] LoadModelLineDT 开始
... [性能分析] LoadModelLineDT -> JXB处理完成: XXX毫秒 (JXB数: XXX, Structure查询次数: XXX)
<<< [性能分析] LoadModelLineDT 完成，总耗时: XXX毫秒

>>> [性能分析] LoadModelLineByUnits 开始
... [性能分析] LoadModelLineByUnits -> JXB处理完成: XXX毫秒 (JXB数: XXX, GetUnitTermimalGaocengAndPos调用: XXX次)
<<< [性能分析] LoadModelLineByUnits 完成，总耗时: XXX毫秒
```

有了这些数据，我们就能精确定位问题并实施优化！
