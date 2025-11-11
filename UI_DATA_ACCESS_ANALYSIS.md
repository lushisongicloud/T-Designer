# UI数据访问模式分析

## 从UI控件获取数据的代码模式

### 1. 从QTableWidget获取数据

#### mainwindow_diagnosis.cpp::buildTestReportMetrics()
```cpp
// 从 ui->tableWidgetUnit 获取Equipment_ID
for (int row = 0; row < rowCount; ++row) {
    int equipmentId = 0;
    if (auto *item = ui->tableWidgetUnit->item(row, 0)) {
        equipmentId = item->data(Qt::UserRole).toInt();
    }
}
```
**状态**: ✅ 同时使用数据库查询,UI仅用于获取Equipment列表
**影响**: 低 - buildTestReportMetrics主要从数据库查询,UI只提供Equipment_ID列表

#### mainwindow_diagnosis.cpp (其他地方)
```cpp
// 从 ui->tableWidgetExecConn 获取Symbol_ID
ListSymbolID.append(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toInt());
```
**状态**: ⚠️ 需要检查这些table是如何填充的

### 2. 从QStandardItemModel Tree获取数据

#### mainwindow_project.cpp 中大量使用:

##### 从 ModelUnits 获取数据
```cpp
// 遍历Units树获取展开状态
listGaocengExpendID.append(ModelUnits->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
listPosExpendID.append(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
listEquipmentExpendID.append(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());

// 填充ComboBox
ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
ui->CbUnitPos->addItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());

// 过滤显示
if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbUnitGaoceng->currentText())
    continue;
```

##### 从 ModelLineByUnits 获取数据
```cpp
// 类似的模式用于连线树
ui->CbLineGaoceng->addItem(ModelLineByUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
ui->CbLinePos->addItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());

// 过滤
if(ModelLineByUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbLineGaoceng->currentText())
    continue;
```

##### 从 ModelTerminals 获取数据
```cpp
// 端子树类似模式
ui->CbTermGaoceng->addItem(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
ui->CbTermPos->addItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
```

##### 从 ModelPages 获取数据
```cpp
// 页面树
listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
ui->CbPageGaocengFilter->addItem(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
```

**状态**: ⚠️ **高影响** - 这些是主要的数据访问模式

### 3. 数据访问用途分类

#### A. UI状态管理
```cpp
// 保存/恢复展开状态
listGaocengExpendID.append(ModelUnits->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
```
**影响**: 中 - 需要确保新模型支持展开状态查询

#### B. 填充过滤器ComboBox
```cpp
// 填充高层/位置下拉框
ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
```
**影响**: 高 - 需要从内存模型直接获取唯一的高层/位置列表

#### C. 树视图过滤
```cpp
// 根据选择的高层/位置过滤显示
if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbUnitGaoceng->currentText())
    continue;
```
**影响**: 高 - 需要在新的LazyTreeModel中实现过滤逻辑

#### D. 获取数据库ID进行查询
```cpp
// 获取Terminal_ID进行数据库查询
QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+
    ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString();
```
**影响**: 高 - 应该直接从内存模型查询,不应通过UI间接获取

## 重构策略

### 阶段1: 保持兼容 (当前实现)
- ProjectDataModel 加载所有数据到内存
- 现有UI代码保持不变
- 两套系统并行运行
- **测试**: 对比数据一致性

### 阶段2: 添加数据访问接口
在MainWindow添加便捷方法:
```cpp
// 替代从ModelUnits获取数据
QStringList MainWindow::getGaocengList() const {
    if (m_projectDataModel) {
        return m_projectDataModel->structureManager()->getUniqueGaocengList();
    }
    // fallback: 从ModelUnits获取
    // ...
}

QVector<int> MainWindow::getEquipmentIdsByStructure(int structureId) const {
    if (m_projectDataModel) {
        return m_projectDataModel->getEquipmentsByStructure(structureId);
    }
    // fallback
    // ...
}
```

### 阶段3: 实现LazyTreeModel
```cpp
class UnitsTreeModel : public QAbstractItemModel {
    ProjectDataModel *m_dataModel;
    
    // 按需创建QModelIndex
    // 延迟加载子节点
    // 支持过滤 (高层/位置/标签)
};
```

### 阶段4: 逐步替换UI数据访问
优先顺序:
1. **ComboBox填充** - 直接从ProjectDataModel获取唯一值列表
2. **数据库ID获取** - 不应通过UI获取,直接从内存模型查询
3. **树视图过滤** - 移到LazyTreeModel内部实现
4. **展开状态** - 使用QModelIndex持久化,而非ID列表

### 阶段5: 移除旧的QStandardItemModel
- 删除 LoadProjectUnits/Lines/Terminals/Pages 中的UI构建代码
- ModelUnits/ModelLineByUnits/ModelTerminals/ModelPages 替换为LazyTreeModel

## 需要特别注意的函数

### mainwindow_project.cpp
- `LoadProjectUnits()` - 构建Units树,大量UI操作
- `LoadProjectLines()` - 构建Lines树
- `LoadProjectTerminals()` - 构建Terminals树
- `LoadProjectPages()` - 构建Pages树
- `on_CbUnitGaoceng_currentTextChanged()` - 过滤Units树
- `on_CbLineGaoceng_currentTextChanged()` - 过滤Lines树
- `on_CbTermGaoceng_currentTextChanged()` - 过滤Terminals树
- `on_CbPageGaocengFilter_currentIndexChanged()` - 过滤Pages树
- `ShowTableWidgetUnit()` - 填充table,可能需要从内存模型获取数据

### mainwindow_diagnosis.cpp
- `buildTestReportMetrics()` - ✅ 主要从数据库查询,影响小
- 其他使用 `ui->tableWidgetExecConn` 的函数 - 需要检查数据来源

## 立即可做的优化

### 1. 添加ProjectDataModel成员
```cpp
// mainwindow.h
private:
    ProjectDataModel *m_projectDataModel;  // 新的内存模型
    ProjectDataCache *m_projectCache;      // 旧的缓存 (保留兼容)
```

### 2. 在LoadProject中加载
```cpp
void MainWindow::LoadProject() {
    // 清理旧模型
    if (m_projectDataModel) {
        delete m_projectDataModel;
        m_projectDataModel = nullptr;
    }
    
    // 加载新模型
    m_projectDataModel = new ProjectDataModel();
    if (m_projectDataModel->loadAll(T_ProjectDatabase)) {
        qDebug() << "[ProjectDataModel] 加载成功:" << m_projectDataModel->getStatistics();
    }
    
    // 保留旧的UI构建逻辑 (暂时)
    LoadProjectUnits();
    LoadProjectLines();
    // ...
}
```

### 3. 提供数据访问助手方法
```cpp
// mainwindow.h
public:
    const StructureData* getStructure(int id) const;
    const EquipmentData* getEquipment(int id) const;
    QVector<int> getEquipmentsByStructure(int structureId) const;
    QStringList getUniqueGaocengList() const;
    QStringList getUniquePosListByGaoceng(const QString &gaoceng) const;
```

### 4. 逐步替换UI数据访问
从简单的开始:
```cpp
// 旧代码
ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());

// 新代码
for (const QString &gaoceng : getUniqueGaocengList()) {
    ui->CbUnitGaoceng->addItem(gaoceng);
}
```

## 关键原则

1. **数据访问应该是单向的**: 数据库 → 内存模型 → UI,不应该反向
2. **UI是数据的视图,不是数据源**: 不应该从UI获取业务数据
3. **保持向后兼容**: 在完全替换之前,两套系统并行运行
4. **渐进式重构**: 小步快跑,每次修改可独立测试
5. **优先处理高频访问**: ComboBox填充、过滤等高频操作优先优化

## 测试策略

1. **数据一致性测试**: 对比ProjectDataModel和数据库查询结果
2. **性能测试**: 记录加载时间,确保显著提升
3. **功能回归测试**: 确保UI行为不变
4. **边界测试**: 空项目、大型项目、异常数据
