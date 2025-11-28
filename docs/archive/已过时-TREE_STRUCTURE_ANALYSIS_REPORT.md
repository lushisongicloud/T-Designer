**【分类依据】本文件记录了具体的修复过程、调试分析或已过时的设计实现，作为问题解决的临时记录保留。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 项目导航器树形结构问题分析报告

## 问题概述

用户报告了项目导航器中树形结构存在的几个问题：

1. **"元件"tab页中有重复的"集中油源动力系统"节点**
2. **设备解析和目录结构正确性需要验证**
3. **同级同名节点需要合并**
4. **其他不合理或不正确的地方**

## 数据库分析结果

### 1. ProjectStructure表数据混乱

通过查询发现ProjectStructure表存在严重的数据冗余和结构混乱：

#### 重复的高层节点（Structure_ID=3）
```sql
ProjectStructure_ID | Structure_ID | Structure_INT    | Parent_ID
--------------------|--------------|------------------|------------
1002               | 3            | 油源动力系统     | 1
1003               | 3            | 油源动力系统     | 1001
1047               | 3            | 集中油源动力系统 | 1
```

**问题分析**：
- `Structure_ID=3`（"油源动力系统"）出现了**两次**：1002和1003
- `Structure_INT="集中油源动力系统"`出现了**两次**：1001和1047
- 这导致树形结构中出现两个同名的上层节点

#### 空白位置节点（Structure_ID=6）
```sql
ProjectStructure_ID | Structure_ID | Structure_INT | Parent_ID
--------------------|--------------|---------------|------------
1005-1030          | 6            | (空)          | 1004
1032-1035          | 6            | (空)          | 1031
```

**问题分析**：
- 26个空白节点（1005-1030）都属于控制柜（1004）
- 4个空白节点（1032-1035）都属于液压站（1031）
- 这些空白节点导致树形结构中出现大量无效层级

### 2. 设备分布验证

#### AM0001等设备（控制柜）
```sql
Equipment_ID | DT     | ProjectStructure_ID | 结构层级
-------------|--------|---------------------|----------
4555         | AM0001 | 1004                | 控制柜
4556         | AM0002 | 1004                | 控制柜
...         | ...    | ...                 | ...
```

**分析**：✅ AM0001等100个设备正确关联到控制柜（1004）

#### SA0101等设备（液压站）
```sql
Equipment_ID | DT     | ProjectStructure_ID | 结构层级
-------------|--------|---------------------|----------
3159         | SA0101 | 1032                | 空白节点
3160         | SA0102 | 1032                | 空白节点
```

**分析**：❌ SA0101等设备关联到空白节点（1032），而1032的父节点是1031（液压站）
- 设备应该直接关联到1031（液压站），而不是空白子节点1032

#### BT0101等设备（液压站）
```sql
Equipment_ID | DT     | ProjectStructure_ID | 结构层级
-------------|--------|---------------------|----------
3723         | BT0101 | 1031                | 液压站
3724         | BT0102 | 1031                | 液压站
```

**分析**：✅ BT0101等设备正确关联到液压站（1031）

### 3. 连线分布验证

#### CL-002816等连线
```sql
JXB_ID | ConnectionNumber | ProjectStructure_ID | 结构层级
-------|------------------|---------------------|----------
2816   | CL-002816        | 1032                | 空白节点
```

**分析**：❌ CL-002816等3000多条连线关联到空白节点（1032）

#### CL-005259等连线
```sql
JXB_ID | ConnectionNumber | ProjectStructure_ID | 结构层级
-------|------------------|---------------------|----------
5259   | CL-005259        | 1004                | 控制柜
5262   | CL-005262        | 1031                | 液压站
```

**分析**：✅ CL-005259在控制柜，CL-005262在液压站

## 树形结构问题详解

### 问题1：重复的"集中油源动力系统"节点

**原因**：数据库中存在两个不同的ProjectStructure记录：
- 1001: Structure_ID=1, "集中油源动力系统", Parent_ID=0（根）
- 1047: Structure_ID=3, "集中油源动力系统", Parent_ID=1

**结果**：在"元件"tab页中，由于EquipmentTreeModel根据structureId创建节点，如果两个节点的structureId不同，会创建两个独立节点。

### 问题2：空白位置节点

**原因**：ProjectStructure表中有大量Structure_ID=6且Structure_INT为空的记录

**结果**：
- 在"连线"tab页中，连线被分配到空白节点下
- 导致树形结构中出现大量无意义的层级

### 问题3：同级同名节点未合并

**当前行为**：EquipmentTreeModel按structureId创建节点，structureId不同则创建不同节点

**期望行为**：同级同名节点应该合并显示

## 解决方案

### 方案1：数据库清理（推荐）

#### 1.1 清理重复的高层节点
```sql
-- 删除重复的"油源动力系统"节点（保留1001下的，删除1002）
DELETE FROM ProjectStructure WHERE ProjectStructure_ID = 1002;

-- 删除重复的"集中油源动力系统"节点（保留1001，删除1047）
DELETE FROM ProjectStructure WHERE ProjectStructure_ID = 1047;
```

#### 1.2 合并空白位置节点
```sql
-- 删除空白的位置节点，将设备重新关联到父节点
UPDATE Equipment
SET ProjectStructure_ID = 1003
WHERE ProjectStructure_ID IN (1005, 1006, ..., 1030);

UPDATE Equipment
SET ProjectStructure_ID = 1031
WHERE ProjectStructure_ID IN (1032, 1033, 1034, 1035);

-- 删除空白节点
DELETE FROM ProjectStructure WHERE ProjectStructure_ID IN (1005-1035);
```

#### 1.3 清理连线关联
```sql
-- 类似处理JXB表中的连线关联
UPDATE JXB
SET ProjectStructure_ID = 1031
WHERE ProjectStructure_ID IN (1032-1035);

-- 删除空白节点
DELETE FROM ProjectStructure WHERE ProjectStructure_ID IN (1032-1035);
```

### 方案2：代码优化（同时实施）

#### 2.1 EquipmentTreeModel去重逻辑

修改`acquireGaocengNode`函数，按名称去重：

```cpp
auto acquireGaocengNode = [&](int structureId, const QString &name) -> Node* {
    // 首先按名称查找已存在的同名节点
    QString cleanName = name.trimmed();
    if (!cleanName.isEmpty()) {
        for (Node* existingNode : m_rootNodes->children) {
            if (existingNode->displayText == cleanName) {
                return existingNode;
            }
        }
    }
    // 如果没有找到同名节点，创建新节点
    // ...
};
```

#### 2.2 过滤空白节点

在buildTreeData中过滤空白节点：

```cpp
// 跳过Structure_INT为空的节点
if (posStructure && !posStructure->structureInt.isEmpty()) {
    // 创建位置节点
}
```

#### 2.3 合并同级同名节点

在sortChildren后添加合并逻辑：

```cpp
void mergeDuplicateNodes(Node* parent) {
    QHash<QString, Node*> nameToNode;
    QVector<Node*> mergedChildren;

    for (Node* child : parent->children) {
        QString name = child->displayText;
        if (nameToNode.contains(name)) {
            // 合并子节点
            Node* existing = nameToNode[name];
            existing->children.append(child->children);
        } else {
            nameToNode[name] = child;
            mergedChildren.append(child);
        }
    }

    parent->children = mergedChildren;

    for (Node* child : parent->children) {
        mergeDuplicateNodes(child);
    }
}
```

## 实施建议

### 阶段1：数据库备份与清理
1. 备份当前数据库
2. 执行数据清理脚本
3. 验证设备/连线的层级关系

### 阶段2：代码优化
1. 修改EquipmentTreeModel添加去重逻辑
2. 过滤空白节点
3. 合并同级同名节点

### 阶段3：验证与测试
1. 验证所有设备正确显示在预期位置
2. 验证连线树形结构正确
3. 确认无重复节点

## 验证方法

### SQL验证脚本
```sql
-- 1. 检查重复的高层名称
SELECT Structure_INT, COUNT(*) as count
FROM ProjectStructure
WHERE Parent_ID = 0 OR Parent_ID = 1
GROUP BY Structure_INT
HAVING COUNT(*) > 1;

-- 2. 检查空白节点数量
SELECT COUNT(*) as blank_count
FROM ProjectStructure
WHERE Structure_INT IS NULL OR Structure_INT = '';

-- 3. 检查设备分布
SELECT ps.Structure_INT, COUNT(e.Equipment_ID) as equipment_count
FROM ProjectStructure ps
LEFT JOIN Equipment e ON ps.ProjectStructure_ID = e.ProjectStructure_ID
GROUP BY ps.ProjectStructure_ID
ORDER BY equipment_count DESC;
```

## 预期结果

### 修复前
```
|-集中油源动力系统         (1001)
|-集中油源动力系统         (1047)  ❌重复
|-油源动力系统             (1002)  ❌重复
    |-液压站
        |-AM0001, SA0101, ...  ❌层级混乱
|-油源动力系统             (1003)
    |-控制柜
        |-BT0101, ...          ❌层级混乱
```

### 修复后
```
|-集中油源动力系统         (1001)
    |-油源动力系统           (1003)
        |-控制柜             (1004)
            |-AM0001, ...     ✅
            |-KM0001, ...     ✅
        |-液压站             (1031)
            |-BT0101, ...     ✅
            |-SA0101, ...     ✅
```

## 总结

通过数据库清理和代码优化，可以解决：
1. ✅ 消除重复的"集中油源动力系统"节点
2. ✅ 修正设备的层级结构
3. ✅ 合并同级同名节点
4. ✅ 过滤空白节点

建议优先实施数据库清理，然后实施代码优化以防止类似问题再次发生。
