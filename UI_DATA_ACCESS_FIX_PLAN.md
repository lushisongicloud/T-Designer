# ⚠️ UI数据访问问题修复计划 - 紧急

## 问题严重性: 🔴 HIGH

引入LazyTreeModel后,以下代码将**完全失效**,因为UI树不再包含所有节点!

## 发现的问题代码模式

### 1. 填充ComboBox - 遍历UI树获取高层/位置列表
**影响函数**: 
- `LoadProjectUnits()` - 行2084-2098
- `LoadProjectLines()` - 行1596-1610  
- `LoadProjectTerminals()` - 行1833-1847
- `LoadProjectPages()` - 行2602-2671

**问题代码示例**:
```cpp
// ❌ 错误: 假设ModelUnits包含所有节点
for(int i=0; i<ModelUnits->item(0,0)->rowCount(); i++) {
    ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
}
```

**LazyTreeModel下的问题**: 
- 树节点按需加载,未展开的节点不存在
- `rowCount()` 返回0 (如果节点未fetchMore)
- 遍历会遗漏大部分数据

### 2. 保存/恢复展开状态 - 遍历获取展开节点ID
**影响函数**:
- `LoadProjectUnits()` - 行1880-1888
- `LoadProjectTerminals()` - 行1665-1673
- `LoadProjectPages()` - 行2213-2228

**问题代码示例**:
```cpp
// ❌ 错误: 遍历树获取展开ID
for(int i=0; i<ModelUnits->item(0,0)->rowCount(); i++) {
    if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->index()))
        listGaocengExpendID.append(ModelUnits->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
}
```

**LazyTreeModel下的问题**:
- 只能获取已加载的节点
- 未展开过的节点状态丢失
- 需要从数据模型而非UI获取ID

### 3. 树视图过滤 - 遍历树隐藏/显示节点
**影响函数**:
- `FilterUnit()` - 行2993-3050
- `FilterLines()` - 行2833-2906
- `FilterTerminal()` - 行2714-2784
- `FilterPage()` - 行3110-3335

**问题代码示例**:
```cpp
// ❌ 错误: 遍历所有UI节点进行过滤
for(int i=0; i<ModelUnits->item(0,0)->rowCount(); i++) {
    if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString() != ui->CbUnitGaoceng->currentText()) {
        ui->treeViewUnits->setRowHidden(i, ModelUnits->item(0,0)->index(), true);
        continue;
    }
    // ...继续遍历子节点
}
```

**LazyTreeModel下的问题**:
- 只能过滤已加载的节点
- 用户展开节点时会看到未过滤的数据
- 过滤逻辑应该在Model层实现

### 4. 查找UI节点进行数据库查询 - 通过遍历获取ID
**影响函数**:
- `FilterTerminal()` - 行2756
- `FilterUnit()` - 行3035
- `AddDwgFileToIndex()` - 行2457-2520

**问题代码示例**:
```cpp
// ❌ 错误: 从UI节点获取ID查询数据库
QString SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = " + 
    ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString();
```

**LazyTreeModel下的问题**:
- 节点可能未加载,无法获取ID
- 应该直接从内存模型查询,不经过UI

### 5. 更新UI树节点 - 查找并修改节点
**影响函数**:
- `AddDwgFileToIndex()` - 行2280-2530
- 其他动态更新树的函数

**问题代码示例**:
```cpp
// ❌ 错误: 查找特定节点更新
for(int i=0; i<ModelPages->item(0,0)->rowCount(); i++) {
    if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString() == targetGaoceng) {
        // 找到了,添加子节点
        ModelPages->item(0,0)->child(i,0)->appendRow(newItem);
        break;
    }
}
```

**LazyTreeModel下的问题**:
- 查找的节点可能未加载
- 需要通知Model数据变化,由Model更新UI

## 修复优先级

### P0 - 立即修复 (阻断LazyTreeModel)
这些必须在引入LazyTreeModel之前修复,否则功能彻底失效:

#### 1.1 填充ComboBox
**文件**: mainwindow_project.cpp
**函数**: LoadProjectUnits, LoadProjectLines, LoadProjectTerminals, LoadProjectPages

**修复方案**:
```cpp
// ✅ 正确: 从ProjectDataModel获取
void MainWindow::LoadProjectUnits() {
    // ... 其他代码 ...
    
    // 旧代码 (删除):
    // for(int i=0; i<ModelUnits->item(0,0)->rowCount(); i++) {
    //     ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
    // }
    
    // 新代码:
    QStringList gaocengList = getUniqueGaocengList();
    for (const QString &gaoceng : gaocengList) {
        ui->CbUnitGaoceng->addItem(gaoceng);
    }
}
```

**影响行数**: ~120行代码需要修改

#### 1.2 展开状态持久化
**文件**: mainwindow_project.cpp
**函数**: LoadProjectUnits, LoadProjectTerminals, LoadProjectPages

**修复方案**:
```cpp
// ✅ 正确: 从设置文件读取/保存展开状态
// 不再遍历UI树,而是维护一个展开节点ID集合
QSettings settings("T-Designer", "ExpandedNodes");
QVariant expandedVar = settings.value("Units/ExpandedGaoceng");
QList<int> expandedIds = expandedVar.toList();

// 恢复展开状态
for (int id : expandedIds) {
    QModelIndex index = findIndexByStructureId(id);
    if (index.isValid()) {
        ui->treeViewUnits->expand(index);
    }
}
```

**影响行数**: ~80行代码需要修改

### P1 - 高优先级 (影响用户体验)

#### 2.1 树视图过滤
**文件**: mainwindow_project.cpp
**函数**: FilterUnit, FilterLines, FilterTerminal, FilterPage

**修复方案**:
过滤逻辑移到LazyTreeModel内部:
```cpp
// 在LazyTreeModel中实现
class UnitsTreeModel : public QAbstractItemModel {
    void setGaocengFilter(const QString &gaoceng);
    void setPosFilter(const QString &pos);
    void setTagFilter(const QString &tag);
    
protected:
    bool shouldShowItem(int structureId, int equipmentId) const;
};

// MainWindow中简化为:
void MainWindow::FilterUnit() {
    if (auto *model = qobject_cast<UnitsTreeModel*>(ui->treeViewUnits->model())) {
        model->setGaocengFilter(ui->CbUnitGaoceng->currentText());
        model->setPosFilter(ui->CbUnitPos->currentText());
        model->setTagFilter(ui->EdUnitTagSearch->text());
    }
}
```

**影响行数**: ~600行代码需要重构

### P2 - 中优先级 (功能完整性)

#### 3.1 动态更新树节点
**文件**: mainwindow_project.cpp
**函数**: AddDwgFileToIndex, 其他动态更新函数

**修复方案**:
```cpp
// 通知Model数据变化
void MainWindow::onNewPageAdded(int pageId) {
    // 先更新ProjectDataModel
    if (m_projectDataModel) {
        m_projectDataModel->pageManager()->refresh();
    }
    
    // 通知UI更新
    if (auto *model = qobject_cast<PagesTreeModel*>(ui->treeViewPages->model())) {
        model->notifyDataChanged();
    }
}
```

## 详细修复步骤

### 阶段1: ComboBox填充修复 (1-2天)

#### Step 1.1: 修改LoadProjectUnits
**位置**: mainwindow_project.cpp 行2084-2098

**当前代码**:
```cpp
for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
{
    ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
    for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)
    {
        bool CbPosExist=false;
        for(int k=0;k<ui->CbUnitPos->count();k++)
        {
            if(ui->CbUnitPos->itemText(k)==ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
            {
                CbPosExist=true;
                break;
            }
        }
        if(!CbPosExist)
            ui->CbUnitPos->addItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
    }
}
```

**新代码**:
```cpp
// 从内存模型获取唯一的高层列表
QStringList gaocengList = getUniqueGaocengList();
for (const QString &gaoceng : gaocengList) {
    ui->CbUnitGaoceng->addItem(gaoceng);
}

// 初始化时加载第一个高层的位置列表
if (!gaocengList.isEmpty()) {
    QStringList posList = getUniquePosListByGaoceng(gaocengList.first());
    for (const QString &pos : posList) {
        ui->CbUnitPos->addItem(pos);
    }
}
```

#### Step 1.2: 修改LoadProjectLines
**位置**: mainwindow_project.cpp 行1596-1610
类似修改,使用 `getUniqueGaocengList()` 和 `getUniquePosListByGaoceng()`

#### Step 1.3: 修改LoadProjectTerminals
**位置**: mainwindow_project.cpp 行1833-1847
类似修改

#### Step 1.4: 修改LoadProjectPages
**位置**: mainwindow_project.cpp 行2602-2671
需要额外实现 `getUniquePageTypeList()` 方法

### 阶段2: 展开状态持久化修复 (1天)

#### Step 2.1: 使用QSettings保存展开状态
不再遍历UI树,改为监听展开/折叠信号:

```cpp
// 在LoadProject中连接信号
connect(ui->treeViewUnits, &QTreeView::expanded, 
        this, &MainWindow::onUnitsNodeExpanded);
connect(ui->treeViewUnits, &QTreeView::collapsed,
        this, &MainWindow::onUnitsNodeCollapsed);

void MainWindow::onUnitsNodeExpanded(const QModelIndex &index) {
    int structureId = index.data(Qt::UserRole).toInt();
    QSettings settings("T-Designer", "ExpandedNodes");
    QList<QVariant> list = settings.value("Units/Expanded").toList();
    if (!list.contains(structureId)) {
        list.append(structureId);
        settings.setValue("Units/Expanded", list);
    }
}
```

### 阶段3: 过滤逻辑重构 (3-5天)

需要在LazyTreeModel中实现,详见后续LazyTreeModel设计文档。

## 测试计划

### 测试场景1: ComboBox功能
- [ ] 打开项目,检查高层下拉框是否完整
- [ ] 切换高层,检查位置下拉框是否正确更新
- [ ] 对比旧实现,确保列表内容一致

### 测试场景2: 展开状态
- [ ] 展开部分节点,关闭项目
- [ ] 重新打开项目,检查展开状态是否保持
- [ ] 大量节点场景测试 (4924器件)

### 测试场景3: 过滤功能
- [ ] 选择高层过滤,检查树是否正确过滤
- [ ] 输入标签过滤,检查是否匹配
- [ ] 组合过滤 (高层+位置+标签)

## 风险评估

### 风险1: 修改量大,回归风险高
**缓解措施**:
- 小步快跑,每次修改一个函数
- 每次修改后立即测试
- 保留旧代码作为注释,方便回滚

### 风险2: 用户依赖特定行为
**缓解措施**:
- 确保新实现行为与旧实现完全一致
- 添加详细日志,便于调试
- Beta测试阶段收集反馈

### 风险3: 性能回退
**缓解措施**:
- 内存模型查询已优化为O(1)
- 避免重复计算,使用缓存
- 性能测试对比

## 工作量估算

| 任务 | 估算时间 | 优先级 |
|------|---------|--------|
| ComboBox填充修复 | 1-2天 | P0 |
| 展开状态修复 | 1天 | P0 |
| 过滤逻辑重构 | 3-5天 | P1 |
| 动态更新修复 | 2-3天 | P2 |
| 测试验证 | 2-3天 | P0 |
| **总计** | **9-16天** | - |

## 下一步行动

### 立即执行 (今天)
1. ✅ 创建本修复计划文档
2. [ ] 修复 LoadProjectUnits 中的ComboBox填充
3. [ ] 修复 LoadProjectLines 中的ComboBox填充
4. [ ] 编译测试

### 短期目标 (本周)
1. [ ] 完成所有ComboBox填充修复
2. [ ] 实现展开状态持久化新方案
3. [ ] 验证基础功能正常

### 中期目标 (下周)
1. [ ] 设计LazyTreeModel接口
2. [ ] 实现过滤逻辑
3. [ ] 集成测试

## 附录: 受影响函数完整列表

### mainwindow_project.cpp
```
LoadProjectUnits()        - 行1860-2100  [ComboBox填充, 展开状态]
LoadProjectLines()        - 行1330-1640  [ComboBox填充]
LoadProjectTerminals()    - 行1650-1860  [ComboBox填充, 展开状态]
LoadProjectPages()        - 行2170-2680  [ComboBox填充, 展开状态]
FilterUnit()              - 行2990-3100  [树过滤]
FilterLines()             - 行2830-2920  [树过滤]
FilterTerminal()          - 行2710-2800  [树过滤]
FilterPage()              - 行3110-3400  [树过滤]
AddDwgFileToIndex()       - 行2280-2530  [动态更新树]
InsertLineToItem()        - 行1330-1395  [动态更新树]
```

### mainwindow.cpp
```
getUniqueGaocengList()    - 新增便捷方法 [从内存模型获取]
getUniquePosListByGaoceng() - 新增便捷方法
```

---

**文档状态**: 🔴 紧急 - 需要立即处理
**创建时间**: 2025-11-10
**负责人**: 待分配
**审核人**: 待审核
