# T-Designer Feature Implementation Analysis Summary

## Overview
This document provides a summary of the implementation locations for four key features in the T-Designer project, specifically in the "DiagnoseUI" branch context.

## Question
Where are the following features mainly implemented in the source code?
1. Connection display by code number in project navigator
2. Connection display by component in project navigator
3. Right-click menu "Go to Target" and "Go to Source" functions for connections
4. Functional block drawing status display and auto-update in component view

## Answers

### 1. Connection Display by Code Number (按连接代号显示)

**Primary Implementation:** `mainwindow_project.cpp`

**Key Functions:**
- `LoadModelLineDT()` (lines 1397-1468)
  - Queries all connections from JXB table ordered by ConnectionNumber
  - Builds tree structure: Project → Layer → Location → Connection Number → Connection Lines
  - Uses `ui->treeViewLineDT` widget for display

- `InsertLineToItem()` (lines 1329-1395)
  - Creates or finds connection number nodes
  - Formats connection as "Source <-> Target"
  - Stores connection details in Qt::UserRole for later use

- `LoadProjectLines()` (lines 1595-1599)
  - Top-level function that loads both connection views

**UI Widget:** `ui->treeViewLineDT`

**Data Structure:** Project → Layer → Location → Connection Number → Connection Lines

### 2. Connection Display by Component (按元件显示)

**Primary Implementation:** `mainwindow_project.cpp`

**Key Functions:**
- `LoadModelLineByUnits()` (lines 1470-1593)
  - Queries all connections from JXB table ordered by ConnectionNumber
  - Processes both ends (Symb1 and Symb2) of each connection separately
  - Builds tree structure: Project → Layer → Location → Component/Terminal → Functional Block → Connections
  - Uses `ui->treeViewLineByUnit` widget for display

- `InsertUnitTerminalToItem()` (lines 1275-1327)
  - Determines if processing source (index=0) or target (index=1) end
  - Creates or finds component/terminal strip nodes
  - Calls `InsertTermToUnitStrip()` to insert terminal and connection details

**UI Widget:** `ui->treeViewLineByUnit`

**Data Structure:** Project → Layer → Location → Component/Terminal Strip → Functional Block → Connections

**Key Feature:** Each connection's two ends are inserted separately under their respective component/terminal nodes

### 3. Right-Click Menu "Go to Target/Source" Functions

**Primary Implementation:** `mainwindow_units.cpp`

This functionality is implemented for both tree views:

#### 3.1 For Connection Code View (treeViewLineDT)

**Functions:**
- `ShowtreeViewLineDTPopMenu()` (lines 1803-1818)
  - Creates context menu for connection items
  - Adds "Go to Target" (转到目标) and "Go to Source" (转到源) actions
  
- `ShowLineTargetInDwg()` (lines 1704-1730)
  - Retrieves connection data from Qt::UserRole
  - Checks target type (Symb2_Category): 0=component, 1=terminal
  - Calls appropriate function to highlight target in CAD drawing

- `ShowLineSourceInDwg()` (lines 1759-1784)
  - Similar to ShowLineTargetInDwg but processes source end (Symb1)

#### 3.2 For Component View (treeViewLineByUnit)

**Functions:**
- `ShowtreeViewLineByUnitPopMenu()` (lines 1786-1801)
  - Creates context menu for functional block items
  - Adds "Go to Target" and "Go to Source" actions

- `ShowLineByUnitTargetInDwg()` (lines 1676-1702)
  - Implementation for "Go to Target" in component view

- `ShowLineByUnitSourceInDwg()` (lines 1732-1757)
  - Implementation for "Go to Source" in component view

**Connection Data Structure (stored in Qt::UserRole as QStringList):**
- Index 0: JXB_ID (connection table primary key)
- Index 1: Symb1_ID (source ID)
- Index 2: Symb1_Category (source type: 0=component, 1=terminal)
- Index 3: Symb2_ID (target ID)
- Index 4: Symb2_Category (target type: 0=component, 1=terminal)

**Helper Functions:**
- `ShowSpurInDwgBySymbolID()` (lines 1622-1668) - Shows component in CAD
- `ShowTerminalInDwgByTerminalID()` (lines 1566-1615) - Shows terminal in CAD

### 4. Functional Block Drawing Status Display and Auto-Update

This feature involves two main aspects:
1. **Display Logic:** Showing correct icon based on drawing status
2. **Auto-Update Mechanism:** Updating icon when blocks are drawn/deleted/cut

#### 4.1 Display Logic

**Primary Implementation:** `mainwindow_project.cpp`

**Key Function:** `LoadProjectUnits()` (lines 1804-2021)
- Queries all components and their functional blocks from database
- Determines icon based on `Symbol_Handle` field (lines 1919-1961)

**Icon Selection Logic:**
1. **Cannot Insert** (`逻辑支路图标_不可插入.png`):
   - Condition: `Symbol == ""` AND `FunDefine != "黑盒"` AND `FunDefine != "PLC 盒子"`
   - Meaning: No symbol defined, cannot be inserted into CAD

2. **Inserted** (`逻辑支路图标_已插入.png`):
   - Condition: `Symbol_Handle != ""`
   - Meaning: Already drawn in CAD, has graphic handle
   - Display format: `(PageName)FunctionName`

3. **Not Inserted** (`逻辑支路图标_未插入.png`):
   - Condition: `Symbol_Handle == ""` AND (`Symbol != ""` OR is black box/PLC box)
   - Meaning: Symbol defined but not yet inserted into CAD
   - Display format: `-FunctionName`

**Key Code Section (lines 1919-1961):**
```cpp
//根据Symbol_Handle是否存在确定功能子块图标和文字
if(QuerySymbol.value("Symbol").toString()==""&&
   (QuerySymbol.value("FunDefine").toString()!="黑盒")&&
   (QuerySymbol.value("FunDefine").toString()!="PLC 盒子"))
{
    // Cannot insert
    UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_不可插入.png"),UnitSpurStr);
}
else
{
    if(QuerySymbol.value("Symbol_Handle").toString()!="")
    {
        // Inserted
        UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_已插入.png"),UnitSpurStr);
    }
    else
    {
        // Not inserted
        UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_未插入.png"),UnitSpurStr);
    }
}
```

#### 4.2 Auto-Update Mechanism

**Implementation:** Signal-slot pattern across `formaxwidget.cpp` and `mainwindow_project.cpp`

**Signal Definition:** `formaxwidget.h` (line 197)
```cpp
signals:
    void UpdateProjectUnits();
```

**Signal Emission Locations in formaxwidget.cpp:**
The `UpdateProjectUnits()` signal is emitted after:
1. Inserting functional blocks (lines 500, 699, 3704)
2. Drag-and-drop inserting blocks (lines 4759, 4866, 4898)
3. Equal-distance drawing blocks (line 5081)
4. Deleting CAD entities that are functional blocks (lines 6086, 6148, 6191)
5. Cutting CAD entities that are functional blocks (line 6264)

**Signal Connection in mainwindow_project.cpp:**
When CAD drawing windows are created or opened (lines 537, 828, 835, 3836):
```cpp
connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
```

**Symbol_Handle Field Updates:**
- **When inserting:** Set to the CAD graphic handle
  ```cpp
  queryUpdate.bindValue(":Symbol_Handle",blk_ent->dynamicCall("handle()").toString());
  ```
- **When deleting/cutting:** Set to empty string
  ```cpp
  queryUpdate.bindValue(":Symbol_Handle","");
  ```

**Auto-Update Flow:**
```
CAD Operation (Insert/Delete/Cut functional block)
    ↓
Update Symbol_Handle field in database
    ↓
Emit UpdateProjectUnits() signal
    ↓
Trigger LoadProjectUnits() slot function
    ↓
Re-query all components and functional blocks from database
    ↓
Check Symbol_Handle field to determine status
    ↓
Update tree view with appropriate icon and text
    ↓
UI automatically refreshes with latest status
```

## Summary Table

| Feature | Main File(s) | Core Functions | UI Widget |
|---------|-------------|----------------|-----------|
| Connection by Code | `mainwindow_project.cpp` | `LoadModelLineDT()`<br>`InsertLineToItem()` | `ui->treeViewLineDT` |
| Connection by Component | `mainwindow_project.cpp` | `LoadModelLineByUnits()`<br>`InsertUnitTerminalToItem()` | `ui->treeViewLineByUnit` |
| Context Menu (Code View) | `mainwindow_units.cpp` | `ShowtreeViewLineDTPopMenu()`<br>`ShowLineTargetInDwg()`<br>`ShowLineSourceInDwg()` | `ui->treeViewLineDT` |
| Context Menu (Component View) | `mainwindow_units.cpp` | `ShowtreeViewLineByUnitPopMenu()`<br>`ShowLineByUnitTargetInDwg()`<br>`ShowLineByUnitSourceInDwg()` | `ui->treeViewLineByUnit` |
| Block Status Display | `mainwindow_project.cpp` | `LoadProjectUnits()` (lines 1919-1961) | `ui->treeViewUnits` |
| Block Status Auto-Update | `formaxwidget.cpp`<br>`mainwindow_project.cpp` | Signal: `UpdateProjectUnits()`<br>Slot: `LoadProjectUnits()` | Signal-slot mechanism |

## Key Database Fields

### Symbol Table Fields
- **Symbol**: Symbol library name (empty = no symbol defined)
- **Symbol_Handle**: CAD graphic handle (empty = not drawn on diagram)
- **FunDefine**: Function definition name
- **Page_ID**: Page where the block is drawn

### JXB Table Fields (Connection Table)
- **JXB_ID**: Connection table primary key
- **ConnectionNumber**: Connection code/number
- **Symb1_ID**: Source terminal ID
- **Symb1_Category**: Source type (0=component, 1=terminal strip)
- **Symb2_ID**: Target terminal ID
- **Symb2_Category**: Target type (0=component, 1=terminal strip)

---

*This analysis is based on detailed code review of the T-Designer project, documenting the implementation details of connection display and functional block status management features.*
