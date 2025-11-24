# T-Designer 功能实现位置分析

## 问题概述
本文档分析 "DiagnoseUI" 分支中以下四个功能的实现位置：
1. 项目导航器中的连线（按连接代号）显示
2. 项目导航器中的连线（按元件）显示
3. 项目导航器中的连线（按连接代号&按元件）在具体连线上的右键菜单中"转到目标"、"转到源"功能
4. 项目导航器中元件页面，具体器件的功能子块的绘制状态显示与自动更新

## 详细分析

### 1. 项目导航器中的连线（按连接代号）显示

**主要实现文件：`mainwindow_project.cpp`**

**核心函数：**

#### `void MainWindow::LoadModelLineDT()` (第1397-1468行)
这是"按连接代号"显示连线的主要函数。

**功能说明：**
- 从 `JXB` 表中查询所有连接，按 `ConnectionNumber` 排序
- 构建项目树形结构：项目 → 高层 → 位置 → 线号 → 具体连线
- 每条连线的显示格式为：源端 `<->` 目标端

**关键代码片段：**
```cpp
void MainWindow::LoadModelLineDT()
{
    //根据线号================
    ModelLineDT->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelLineDT->appendRow(fatherItem);

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);
    temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    while(QueryJXB.next())
    {
        // ... 构建高层、位置节点 ...
        //在PosNodeItem下插入连线
        InsertLineToItem(PosNodeItem,QueryJXB);
    }
    if(ModelLineDT->rowCount()>0) ui->treeViewLineDT->expand(fatherItem->index());
}
```

#### `void MainWindow::InsertLineToItem(QStandardItem *Item, QSqlQuery QueryJXBLine)` (第1329-1395行)
这是将连线插入到树节点的辅助函数。

**功能说明：**
- 根据 `ConnectionNumber` 创建或查找线号节点
- 创建连线项，格式为 "源端<->目标端"
- 将连线的详细信息（JXB_ID, Symb1_ID, Symb1_Category, Symb2_ID, Symb2_Category）保存在 UserRole 中供后续使用

**关键代码片段：**
```cpp
void MainWindow::InsertLineToItem(QStandardItem *Item,QSqlQuery QueryJXBLine)
{
    QString ConnectionNumber=QueryJXBLine.value("ConnectionNumber").toString();
    QStandardItem *ConnectionNumberNodeItem;
    // ... 创建或查找线号节点 ...
    
    //在列表中添加导线
    QString Symb1Str,Symb2Str;
    if(Symb1_Category=="0")//元件
        Symb1Str=GetUnitTermStrByTermID(Symb1_ID);
    else if(Symb1_Category=="1")//端子排
        Symb1Str=GetTerminalTermStrByTermID(Symb1_ID);
    // ... 处理Symb2 ...
    
    QString LineStr=Symb1Str+"<->"+Symb2Str;
    QStandardItem *LineItem=new QStandardItem(QIcon("C:/TBD/data/连线图标.png"),LineStr);
    LineItem->setData(QVariant("连线"),Qt::WhatsThisRole);
    QStringList ListLineItemData;
    ListLineItemData.append(QueryJXBLine.value("JXB_ID").toString());
    ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
    ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
    ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
    ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
    LineItem->setData(QVariant(ListLineItemData),Qt::UserRole);
    ConnectionNumberNodeItem->appendRow(LineItem);
}
```

#### `void MainWindow::LoadProjectLines()` (第1595-1599行)
这是顶层调用函数，同时加载两种连线显示方式。

```cpp
void MainWindow::LoadProjectLines()
{
    LoadModelLineDT();
    LoadModelLineByUnits();
}
```

**总结：**
- 主要实现在 `mainwindow_project.cpp` 的 `LoadModelLineDT()` 和 `InsertLineToItem()` 函数
- 使用 `ui->treeViewLineDT` 控件显示
- 数据结构：项目 → 高层 → 位置 → 线号(ConnectionNumber) → 连线

---

### 2. 项目导航器中的连线（按元件）显示

**主要实现文件：`mainwindow_project.cpp`**

**核心函数：**

#### `void MainWindow::LoadModelLineByUnits()` (第1470-1593行)
这是"按元件"显示连线的主要函数。

**功能说明：**
- 从 `JXB` 表中查询所有连接，按 `ConnectionNumber` 排序
- 构建项目树形结构：项目 → 高层 → 位置 → 元件/端子排 → 功能子块 → 连线
- 对每条连线的两端（Symb1和Symb2）分别处理，插入到各自所属的元件或端子排节点下

**关键代码片段：**
```cpp
void MainWindow::LoadModelLineByUnits()
{
    //根据元件=================
    ModelLineByUnits->clear();
    // ... 创建项目根节点 ...
    
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);
    temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    while(QueryJXB.next())
    {
        QString StrGaoceng,StrPos;
        for(int index=0;index<2;index++)  // 处理连线的两端
        {
            if(index==0)
            {
                if(QueryJXB.value("Symb1_ID").toString()!="")
                {
                    GetUnitTermimalGaocengAndPos(QueryJXB.value("Symb1_Category").toInt(),
                                                 QueryJXB.value("Symb1_ID").toInt(),
                                                 StrGaoceng,StrPos);
                }
                else continue;
            }
            else if(index==1)
            {
                if(QueryJXB.value("Symb2_ID").toString()!="")
                {
                    GetUnitTermimalGaocengAndPos(QueryJXB.value("Symb2_Category").toInt(),
                                                 QueryJXB.value("Symb2_ID").toInt(),
                                                 StrGaoceng,StrPos);
                }
                else continue;
            }
            // ... 构建高层、位置节点 ...
            //在PosNodeItem下插入器件
            InsertUnitTerminalToItem(PosNodeItem,QueryJXB,index);
        }
    }
    if(ModelLineByUnits->rowCount()>0) ui->treeViewLineByUnit->expand(fatherItem->index());
}
```

#### `void MainWindow::InsertUnitTerminalToItem(QStandardItem *Item, QSqlQuery QueryJXBLine, int index)` (第1275-1327行)
这是将元件/端子及其连线插入到树节点的辅助函数。

**功能说明：**
- 根据 `index` 参数确定是处理连线的源端(0)还是目标端(1)
- 查找或创建元件/端子排节点
- 调用 `InsertTermToUnitStrip()` 将具体的端子及连线信息插入到元件/端子排下

**关键代码片段：**
```cpp
void MainWindow::InsertUnitTerminalToItem(QStandardItem *Item,QSqlQuery QueryJXBLine,int index)
{
    QString Symb_ID;
    if(index==0) Symb_ID=QueryJXBLine.value("Symb1_ID").toString();
    else if(index==1) Symb_ID=QueryJXBLine.value("Symb2_ID").toString();
    
    QString Symb_Category;
    if(index==0) Symb_Category=QueryJXBLine.value("Symb1_Category").toString();
    else if(index==1) Symb_Category=QueryJXBLine.value("Symb2_Category").toString();
    
    //找到Symb_ID对应的器件
    QString DT;
    int UnitStripID=GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
    
    //查看当前的器件是否在列表中已经存在
    bool UnitStripExisted=false;
    for(int i=0;i<Item->rowCount();i++)
    {
        if((Item->child(i,0)->data(Qt::UserRole).toInt()==UnitStripID)&&
           (Item->child(i,0)->data(Qt::WhatsThisRole).toString()==Symb_Category))
        {
            UnitStripExisted=true;
            InsertTermToUnitStrip(Item->child(i,0),QueryJXBLine,Symb_ID,Symb_Category,index);
            break;
        }
    }
    if(!UnitStripExisted)//元件不存在，添加元件和端口
    {
        QStandardItem *UnitStripItem=new QStandardItem(QIcon("C:/TBD/data/端子排图标.png"),DT);
        UnitStripItem->setData(QVariant(Symb_Category),Qt::WhatsThisRole);
        UnitStripItem->setData(QVariant(UnitStripID),Qt::UserRole);
        Item->appendRow(UnitStripItem);
        InsertTermToUnitStrip(UnitStripItem,QueryJXBLine,Symb_ID,Symb_Category,index);
    }
}
```

**总结：**
- 主要实现在 `mainwindow_project.cpp` 的 `LoadModelLineByUnits()` 和 `InsertUnitTerminalToItem()` 函数
- 使用 `ui->treeViewLineByUnit` 控件显示
- 数据结构：项目 → 高层 → 位置 → 元件/端子排 → 功能子块 → 连线
- 特点：每条连线的两端分别插入到各自所属的元件/端子排节点下

---

### 3. 右键菜单中"转到目标"、"转到源"功能

**主要实现文件：`mainwindow_units.cpp`**

这个功能在两个树视图中都有实现：
- `treeViewLineDT`（按连接代号显示）
- `treeViewLineByUnit`（按元件显示）

#### 3.1 按连接代号显示的右键菜单

##### `void MainWindow::ShowtreeViewLineDTPopMenu(const QPoint &pos)` (第1803-1818行)
创建右键菜单并绑定槽函数。

**关键代码片段：**
```cpp
void MainWindow::ShowtreeViewLineDTPopMenu(const QPoint &pos)
{
    if(!ui->treeViewLineDT->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewLineDT->indexAt(pos).data(Qt::WhatsThisRole).toString()!="连线") return;

    QAction actShowLineTarget("转到目标", this);
    tree_menu.addAction(&actShowLineTarget);
    connect(&actShowLineTarget,SIGNAL(triggered()),this,SLOT(ShowLineTargetInDwg()));
    
    QAction actShowLineSource("转到源", this);
    tree_menu.addAction(&actShowLineSource);
    connect(&actShowLineSource,SIGNAL(triggered()),this,SLOT(ShowLineSourceInDwg()));
    
    tree_menu.exec(QCursor::pos());
}
```

##### `void MainWindow::ShowLineTargetInDwg()` (第1704-1730行)
"转到目标"的实现函数。

**功能说明：**
- 从当前选中的连线项获取 UserRole 数据（包含 JXB_ID, Symb1_ID, Symb1_Category, Symb2_ID, Symb2_Category）
- 根据 Symb2_Category 判断目标是元件(0)还是端子排(1)
- 调用对应的显示函数在CAD图中高亮显示目标元件/端子

**关键代码片段：**
```cpp
void MainWindow::ShowLineTargetInDwg()//转到目标
{
    QStringList ListLineItemData=ui->treeViewLineDT->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;

    if(ListLineItemData.at(4)=="0")  // 目标是元件
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(3);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(4)=="1")  // 目标是端子排
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(3);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}
```

##### `void MainWindow::ShowLineSourceInDwg()` (第1759-1784行)
"转到源"的实现函数。

**功能说明：**
- 逻辑与 `ShowLineTargetInDwg()` 类似
- 区别是处理源端（Symb1）而不是目标端（Symb2）
- ListLineItemData.at(1) 是 Symb1_ID，ListLineItemData.at(2) 是 Symb1_Category

**关键代码片段：**
```cpp
void MainWindow::ShowLineSourceInDwg()//转到源
{
    QStringList ListLineItemData=ui->treeViewLineDT->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;
    
    if(ListLineItemData.at(2)=="0")  // 源是元件
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(1);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(2)=="1")  // 源是端子排
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(1);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}
```

#### 3.2 按元件显示的右键菜单

##### `void MainWindow::ShowtreeViewLineByUnitPopMenu(const QPoint &pos)` (第1786-1801行)
为"按元件"视图创建右键菜单。

**关键代码片段：**
```cpp
void MainWindow::ShowtreeViewLineByUnitPopMenu(const QPoint &pos)
{
    if(!ui->treeViewLineByUnit->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewLineByUnit->indexAt(pos).data(Qt::WhatsThisRole).toString()!="功能子块") return;

    QAction actShowLineTarget("转到目标", this);
    tree_menu.addAction(&actShowLineTarget);
    connect(&actShowLineTarget,SIGNAL(triggered()),this,SLOT(ShowLineByUnitTargetInDwg()));
    
    QAction actShowLineSource("转到源", this);
    tree_menu.addAction(&actShowLineSource);
    connect(&actShowLineSource,SIGNAL(triggered()),this,SLOT(ShowLineByUnitSourceInDwg()));
    
    tree_menu.exec(QCursor::pos());
}
```

##### `void MainWindow::ShowLineByUnitTargetInDwg()` (第1676-1702行)
按元件视图中"转到目标"的实现。

**关键代码片段：**
```cpp
void MainWindow::ShowLineByUnitTargetInDwg()
{
    QStringList ListLineItemData=ui->treeViewLineByUnit->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;

    if(ListLineItemData.at(4)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(3);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(4)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(3);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}
```

##### `void MainWindow::ShowLineByUnitSourceInDwg()` (第1732-1757行)
按元件视图中"转到源"的实现。

**关键代码片段：**
```cpp
void MainWindow::ShowLineByUnitSourceInDwg()
{
    QStringList ListLineItemData=ui->treeViewLineByUnit->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;
    
    if(ListLineItemData.at(2)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(1);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(2)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(1);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}
```

#### 辅助函数

##### `void MainWindow::ShowSpurInDwgBySymbolID(QString SymbolID)` (第1622-1668行)
在CAD图中显示并定位到指定的功能子块。

##### `void MainWindow::ShowTerminalInDwgByTerminalID(QString TerminalID)` (第1566-1615行)
在CAD图中显示并定位到指定的端子。

**总结：**
- 主要实现在 `mainwindow_units.cpp` 中
- 涉及的函数：
  - 按连接代号显示：
    - `ShowtreeViewLineDTPopMenu()` - 创建右键菜单
    - `ShowLineTargetInDwg()` - 转到目标
    - `ShowLineSourceInDwg()` - 转到源
  - 按元件显示：
    - `ShowtreeViewLineByUnitPopMenu()` - 创建右键菜单
    - `ShowLineByUnitTargetInDwg()` - 转到目标
    - `ShowLineByUnitSourceInDwg()` - 转到源
- 核心逻辑：从树节点的 UserRole 中获取连线两端的详细信息，然后调用相应的CAD显示函数

---

### 4. 功能子块的绘制状态显示与自动更新

这个功能涉及两个主要部分：
1. 显示功能子块的绘制状态（通过图标区分）
2. 自动更新图标状态（当在CAD中绘制、删除或剪切功能子块时）

#### 4.1 功能子块状态显示

**主要实现文件：`mainwindow_project.cpp`**

##### `void MainWindow::LoadProjectUnits()` (第1804-2021行)
这是加载项目元件树的主函数，其中包含了功能子块状态的显示逻辑。

**功能说明：**
- 从数据库中查询所有元件及其功能子块
- 根据 `Symbol_Handle` 字段判断功能子块是否已被绘制到CAD图上
- 根据不同状态显示不同的图标：
  - `Symbol_Handle != ""` → 已插入 → "逻辑支路图标_已插入.png"
  - `Symbol_Handle == ""` 且 `Symbol != ""` → 未插入 → "逻辑支路图标_未插入.png"
  - `Symbol == ""` 且 FunDefine 不是"黑盒"或"PLC盒子" → 不可插入 → "逻辑支路图标_不可插入.png"

**关键代码片段（第1919-1961行）：**
```cpp
//在元件节点下插入所有的功能子块,在Symbol表中检索与元件关联的所有子块
QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);
temp = QString("SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"'");
QuerySymbol.exec(temp);
while(QuerySymbol.next())
{
    QStandardItem *UnitSpurItem;
    QString UnitSpurStr;
    UnitSpurStr=GetUnitSpurStrBySymbol_ID(QuerySymbol);
    
    //根据Symbol_Handle是否存在确定功能子块图标和文字
    if(QuerySymbol.value("Symbol").toString()==""&&
       (QuerySymbol.value("FunDefine").toString()!="黑盒")&&
       (QuerySymbol.value("FunDefine").toString()!="PLC 盒子"))
    {
        // 情况1：不可插入（Symbol为空，且不是黑盒或PLC盒子）
        UnitSpurStr+="-"+QuerySymbol.value("FunDefine").toString();
        UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_不可插入.png"),UnitSpurStr);
    }
    else
    {
        if(QuerySymbol.value("Symbol_Handle").toString()!="")
        {
            // 情况2：已插入（Symbol_Handle不为空）
            //根据实际子块插入的位置，得到子块实际放置的图纸位置名称
            UnitSpurStr+="("+GetPageNameByPageID(QuerySymbol.value("Page_ID").toString().toInt())+")";
            UnitSpurStr+=QuerySymbol.value("FunDefine").toString();
            UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_已插入.png"),UnitSpurStr);
        }
        else
        {
            // 情况3：未插入（Symbol_Handle为空）
            UnitSpurStr+="-"+QuerySymbol.value("FunDefine").toString();
            UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_未插入.png"),UnitSpurStr);
        }
    }
    
    UnitSpurItem->setData(QVariant("功能子块"),Qt::WhatsThisRole);
    UnitSpurItem->setData(QVariant(QuerySymbol.value("Symbol_ID").toInt()),Qt::UserRole);
    UnitSpurItem->setFlags(UnitSpurItem->flags()|Qt::ItemIsDragEnabled);
    UnitItem->appendRow(UnitSpurItem);
    
    if(SelectSymbol_ID==QuerySymbol.value("Symbol_ID").toInt())
    {
        ui->treeViewUnits->expand(UnitItem->index());
        ui->treeViewUnits->setCurrentIndex(UnitSpurItem->index());
    }
}
```

**判断逻辑总结：**
1. **不可插入状态**（显示"逻辑支路图标_不可插入.png"）：
   - 条件：`Symbol == ""` 且 `FunDefine != "黑盒"` 且 `FunDefine != "PLC 盒子"`
   - 含义：没有定义符号库，无法插入到CAD图中

2. **已插入状态**（显示"逻辑支路图标_已插入.png"）：
   - 条件：`Symbol_Handle != ""`
   - 含义：已经在CAD图中绘制，有对应的图形句柄
   - 显示格式：`(页面名称)功能定义`

3. **未插入状态**（显示"逻辑支路图标_未插入.png"）：
   - 条件：`Symbol_Handle == ""` 且 `Symbol != ""`（或是黑盒/PLC盒子）
   - 含义：有符号库定义但尚未插入到CAD图中
   - 显示格式：`-功能定义`

#### 4.2 功能子块状态自动更新机制

**主要实现文件：`formaxwidget.cpp` 和 `mainwindow_project.cpp`**

状态更新的触发机制基于信号-槽机制：

##### 信号定义：`formaxwidget.h`（第197行）
```cpp
signals:
    void UpdateProjectUnits();
```

##### 信号发射位置：`formaxwidget.cpp`

在以下操作后会发射 `UpdateProjectUnits()` 信号（导致 `LoadProjectUnits()` 重新加载并更新图标）：

1. **插入功能子块后**（第500行）：
```cpp
emit(UpdateProjectUnits());
```

2. **插入功能子块后**（第699行）：
```cpp
emit(UpdateProjectUnits());
```

3. **更新符号块后**（第3704行）：
```cpp
emit(UpdateProjectUnits());
```

4. **拖拽插入功能子块后**（第4759, 4866, 4898行）：
```cpp
emit(UpdateProjectUnits());
```

5. **等距绘制功能子块后**（第5081行）：
```cpp
if(CurEqualDrawMode==0) emit(UpdateProjectUnits());
```

6. **删除CAD实体后**（第6086, 6148, 6191行）：
当删除的实体是功能子块时：
```cpp
emit(UpdateProjectUnits());
```

7. **剪切CAD实体后**（第6264行）：
当剪切的实体是功能子块时：
```cpp
emit(UpdateProjectUnits());
```

##### 信号连接：`mainwindow_project.cpp`

在创建或打开CAD图纸窗口时，连接信号与槽（多处）：

**第537行：**
```cpp
connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
```

**第828, 835, 3836行：**
```cpp
connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
```

##### Symbol_Handle 字段的更新

**插入功能子块时设置 Symbol_Handle：**

在 `formaxwidget.cpp` 中，当成功插入功能子块到CAD图后，会更新数据库中的 `Symbol_Handle` 字段：

```cpp
// 示例：第4824行
QString StrSql="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle WHERE Symbol_ID = "+CurSymbol_ID;
QSqlQuery queryUpdate(T_ProjectDatabase);
queryUpdate.prepare(StrSql);
queryUpdate.bindValue(":Page_ID",Page_IDInDB);
queryUpdate.bindValue(":Symbol_Handle",blk_ent->dynamicCall("handle()").toString());
queryUpdate.exec();
```

**删除或剪切功能子块时清空 Symbol_Handle：**

在 `formaxwidget.cpp` 中，当删除或剪切CAD图中的功能子块时，会清空数据库中的 `Symbol_Handle` 字段：

```cpp
// 示例：第5428行
QString SqlStr="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID = "+QString::number(Symbol_ID);
QSqlQuery queryUpdate(T_ProjectDatabase);
queryUpdate.prepare(SqlStr);
queryUpdate.bindValue(":Page_ID","");
queryUpdate.bindValue(":Symbol_Handle","");
queryUpdate.bindValue(":InsertionPoint","");
queryUpdate.exec();
```

同时，在 `mainwindow_project.cpp` 的页面删除、拷贝功能中也会清空 Symbol_Handle（第291-294行）：

```cpp
temp="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID = "+query.value("Symbol_ID").toString();
QSqlQuery queryUpdate(T_ProjectDatabase);
queryUpdate.prepare(temp);
queryUpdate.bindValue(":Page_ID","");
queryUpdate.bindValue(":Symbol_Handle","");
queryUpdate.bindValue(":InsertionPoint","");
queryUpdate.exec();
```

#### 自动更新流程图

```
CAD操作（插入/删除/剪切功能子块）
    ↓
更新数据库 Symbol_Handle 字段
    ↓
发射 UpdateProjectUnits() 信号
    ↓
触发 LoadProjectUnits() 槽函数
    ↓
重新从数据库查询所有元件和功能子块
    ↓
根据 Symbol_Handle 是否为空判断状态
    ↓
更新树视图中的图标和文本
    ↓
界面自动刷新，显示最新状态
```

**总结：**
- **显示逻辑**：在 `mainwindow_project.cpp` 的 `LoadProjectUnits()` 函数（第1919-1961行）
- **更新机制**：
  1. CAD操作（`formaxwidget.cpp`）修改数据库中的 `Symbol_Handle` 字段
  2. 发射 `UpdateProjectUnits()` 信号
  3. 信号连接到 `MainWindow::LoadProjectUnits()` 槽函数
  4. 槽函数重新加载整个元件树，根据最新的 `Symbol_Handle` 值显示对应图标
- **关键判断字段**：`Symbol_Handle`
  - 非空 → 已插入
  - 空 → 未插入或不可插入
- **涉及的图标**：
  - `C:/TBD/data/逻辑支路图标_已插入.png`
  - `C:/TBD/data/逻辑支路图标_未插入.png`
  - `C:/TBD/data/逻辑支路图标_不可插入.png`

---

## 总结表格

| 功能 | 主要实现文件 | 核心函数 | UI控件 |
|------|-------------|---------|--------|
| 连线（按连接代号）显示 | `mainwindow_project.cpp` | `LoadModelLineDT()`<br>`InsertLineToItem()` | `ui->treeViewLineDT` |
| 连线（按元件）显示 | `mainwindow_project.cpp` | `LoadModelLineByUnits()`<br>`InsertUnitTerminalToItem()` | `ui->treeViewLineByUnit` |
| 右键菜单"转到目标/源"（按连接代号） | `mainwindow_units.cpp` | `ShowtreeViewLineDTPopMenu()`<br>`ShowLineTargetInDwg()`<br>`ShowLineSourceInDwg()` | `ui->treeViewLineDT` |
| 右键菜单"转到目标/源"（按元件） | `mainwindow_units.cpp` | `ShowtreeViewLineByUnitPopMenu()`<br>`ShowLineByUnitTargetInDwg()`<br>`ShowLineByUnitSourceInDwg()` | `ui->treeViewLineByUnit` |
| 功能子块状态显示 | `mainwindow_project.cpp` | `LoadProjectUnits()`<br>（第1919-1961行） | `ui->treeViewUnits` |
| 功能子块状态自动更新 | `formaxwidget.cpp`<br>`mainwindow_project.cpp` | 信号：`UpdateProjectUnits()`<br>槽：`LoadProjectUnits()` | 信号-槽机制 |

## 关键数据结构

### 连线数据（UserRole 中保存的 QStringList）
索引 | 内容 | 说明
-----|------|-----
0 | JXB_ID | 连接表主键
1 | Symb1_ID | 源端ID（Symb2TermInfo_ID 或 TerminalTerm_ID）
2 | Symb1_Category | 源端类型（0=元件，1=端子排）
3 | Symb2_ID | 目标端ID（Symb2TermInfo_ID 或 TerminalTerm_ID）
4 | Symb2_Category | 目标端类型（0=元件，1=端子排）

### 功能子块状态判断依据
- **Symbol** 字段：符号库名称，为空表示无符号定义
- **Symbol_Handle** 字段：CAD图形句柄，为空表示未绘制到图上
- **FunDefine** 字段：功能定义名称

---

*本文档基于代码审查和分析编写，详细记录了 T-Designer 项目中连线显示和功能子块状态管理的实现细节。*
