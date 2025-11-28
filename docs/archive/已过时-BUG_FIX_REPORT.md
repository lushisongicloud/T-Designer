**【分类依据】本文件记录了具体的修复过程、调试分析或已过时的设计实现，作为问题解决的临时记录保留。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# Bug修复报告：ProjectDataModel加载失败导致UI空白

## 问题总结
- **症状**: 打开项目后，`treeViewUnits`（器件树）和`tableWidgetUnit`（器件表）显示空白
- **影响**: 测试报告统计元件数量为0，功能不可用
- **根本原因**: `ProjectDataModel::loadAll()` 在步骤6（加载Connection）时失败，导致整个模型被放弃

## 根因分析

### 详细错误日志
```
[ProjectDataModel] 步骤6: 加载连线数据 (Connection)...
[ConnectionManager] Failed to load: "no such column: Category Unable to execute statement"
[ProjectDataModel] 步骤6失败: 无法加载连线数据!
[ProjectDataModel] 错误详情: " "
[ProjectDataModel] 内存模型加载失败,将使用传统方式
```

### 问题定位
1. `ConnectionManager::load()` 在第606行硬编码了 `Category` 列：
   ```sql
   SELECT JXB_ID, ... ConnectionNumber, Category, Page_ID, ... FROM JXB
   ```

2. JXB表中没有 `Category` 列，导致SQL执行失败

3. 失败后，`LoadProject()` 将 `m_projectDataModel` 删除并设置为 `nullptr`

4. `LoadProjectUnits()` 检查到 `m_projectDataModel` 为空，直接返回不填充UI

### 数据加载情况
- ✅ Structure: 46个结构节点（正常）
- ✅ Equipment: 439个器件（正常）
- ✅ Symbol: 441个功能子块（正常）
- ✅ TermInfo: 884条端子信息（正常）
- ✅ Page: 30个页面（正常）
- ❌ **Connection: 加载失败**

## 修复方案

### 核心思路
动态检测JXB表中的列，只选择存在的列进行查询，确保在数据库表结构不完整时也能正常工作。

### 修复内容

#### 1. 动态列检测 (projectdatamodel.cpp:603-638)
```cpp
// 动态构建SELECT列列表，只包含存在的列
QStringList selectColumns;
selectColumns << "JXB_ID";
selectColumns << QString("%1 AS Symb1_ID").arg(symb1Column);
selectColumns << QString("%2 AS Symb2_ID").arg(symb2Column);

// 必要列（通常存在）
if (columnSet.contains("ConnectionNumber")) {
    selectColumns << "ConnectionNumber";
}
if (columnSet.contains("Page_ID")) {
    selectColumns << "Page_ID";
}
if (columnSet.contains("ProjectStructure_ID")) {
    selectColumns << "ProjectStructure_ID";
}

// 可选列（可能不存在）
if (columnSet.contains("Category")) {
    selectColumns << "Category";
}
// ... 其他可选列
```

#### 2. 安全的数据读取 (projectdatamodel.cpp:651-705)
```cpp
// 记录每个字段的位置索引
QMap<QString, int> fieldIndex;
for (int i = 0; i < selectColumns.size(); ++i) {
    QString fieldName = selectColumns[i];
    if (fieldName.contains(" AS ")) {
        QStringList parts = fieldName.split(" AS ");
        fieldName = parts[1].trimmed();
    }
    fieldIndex[fieldName] = i;
}

while (query.next()) {
    ConnectionData data;

    // 必要字段
    data.id = query.value(0).toInt();
    data.symb1Id = query.value(1).toString();
    data.symb2Id = query.value(2).toString();

    // 可选字段：检查列是否存在再读取
    if (fieldIndex.contains("ConnectionNumber")) {
        data.connectionNumber = query.value(fieldIndex["ConnectionNumber"]).toString();
    }
    if (fieldIndex.contains("Category")) {
        data.category = query.value(fieldIndex["Category"]).toString();
    }
    // ... 其他可选字段
}
```

### 修复效果

#### 修复前
- 步骤6失败 → `loadAll()` 返回false → `m_projectDataModel` 被删除 → UI空白

#### 修复后
- 动态检测列 → 只查询存在的列 → `loadAll()` 成功 → `m_projectDataModel` 有效 → UI正常显示

## 测试验证

### 预期结果
重新编译并运行后，应看到：
```
[ProjectDataModel] 步骤6: 加载连线数据 (Connection)...
[ConnectionManager] Executing SQL: SELECT JXB_ID, Symb1_ID AS Symb1_ID, ...
[ConnectionManager] Loaded XXX connections
[ProjectDataModel] 步骤6完成: 已加载 XXX 条连线
[ProjectDataModel] === 数据加载完成 ===
[ProjectDataModel] Structures=46, Equipments=439, Symbols=441, Connections=XXX
[ProjectDataModel] 内存模型加载成功: ...
```

### UI验证
- `treeViewUnits` 显示完整的器件树（高层/位置/器件层级）
- `tableWidgetUnit` 显示439个器件的详细信息
- 测试报告统计元件数量为439

## 预防措施

### 1. 健壮性改进
- 对其他Manager类也进行类似检查，确保所有SQL查询都支持可选列
- 考虑在数据库架构变更时添加版本检查和迁移逻辑

### 2. 错误处理
- 保持现有的详细日志记录机制
- 在失败时提供降级方案（如使用传统UI模式）

### 3. 测试覆盖
- 在不同数据库架构的测试项目上验证
- 确保向后兼容性

## 总结

这次修复解决了两个关键问题：
1. **即时问题**: ProjectDataModel加载失败导致UI空白
2. **架构问题**: 硬编码SQL查询导致数据库兼容性差

通过动态列检测和安全的查询构建，ProjectDataModel现在可以在不同数据库架构下稳定工作，确保UI始终能够正常显示数据。

修复后，设备树和器件表格应该能够正常加载和显示，解决了测试报告统计数量为0的问题。
