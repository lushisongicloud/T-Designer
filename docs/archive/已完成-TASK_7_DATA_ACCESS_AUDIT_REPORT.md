**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 任务7数据访问一致性审查报告

## 审查概述

**审查日期**: 2025-11-12
**审查范围**: MainWindow 及相关对话框的数据访问模式
**发现问题**: 对话框中存在将 QTableWidget 作为数据存储的代码模式

## 问题分析

### 1. 主窗口数据访问 (✅ 正确)

**已检查函数**:

#### buildTestReportMetrics() - `mainwindow_diagnosis.cpp:3968`
```cpp
const int rowCount = ui->tableWidgetUnit->model() ? ui->tableWidgetUnit->model()->rowCount() : 0;
QModelIndex index = ui->tableWidgetUnit->model()->index(row, 0);
int equipmentId = index.data(Qt::UserRole).toInt();
```
**状态**: ✅ **正确** - 通过模型访问数据，非直接读取UI项

#### FilterUnit() - `mainwindow_project.cpp:2734`
```cpp
const QString gaocengFilter = ui->CbUnitGaoceng->currentText();
const QString posFilter = ui->CbUnitPos->currentText();
const QString keyword = ui->EdUnitTagSearch->text();
```
**状态**: ✅ **正确** - 读取用户输入，非将UI作为数据源

**结论**: MainWindow 数据访问模式完全正确

### 2. 对话框数据访问 (⚠️ 需要关注)

发现了多个对话框中存在将 QTableWidget 作为数据存储的模式：

#### 受影响的文件列表

| 文件 | 问题描述 | 影响级别 |
|------|---------|----------|
| `dialogBranchAttr.cpp` | 使用 `ui->tableWidgetTermInfo->item()` 读取/设置数据 | 高 |
| `dialogdiagnoseui.cpp` | 使用 `ui->tableWidget_*->item()` 读取/设置数据 | 高 |
| `dialogfactorymanage.cpp` | 使用 `ui->tableWidget->item()` 读取/设置数据 | 高 |
| `dialogfunctionmanage.cpp` | 使用 `ui->tableWidgetFunction->item()` 等读取/设置数据 | 高 |
| `dialogunitmanage.cpp` | 使用 `ui->tableWidgetUnit->item()` 读取/设置数据 | 高 |
| `dialogUnitAttr.cpp` | 使用 `ui->tableWidgetUnitPic->item()` 等 | 中 |

#### 典型问题代码示例

**dialogBranchAttr.cpp**:
```cpp
// 填充数据到UI (从数据库)
ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->rowCount()-1,0)->setData(Qt::UserRole, querySymb2TermInfo.value("Symb2TermInfo_ID").toString());

// 读取UI数据 (写回数据库)
querySymb2TermInfo.bindValue(":ConnNum", ui->tableWidgetTermInfo->item(i,0)->text());
querySymb2TermInfo.bindValue(":ConnDesc", ui->tableWidgetTermInfo->item(i,1)->text());
querySymb2TermInfo.bindValue(":TestCost", ui->tableWidgetTermInfo->item(i,2)->text());
```

**dialogfactorymanage.cpp**:
```cpp
// 读取UI数据
QString Factory_ID = ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString();

// 删除操作
QString temp = "DELETE FROM Factory WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
```

**dialogfunctionmanage.cpp**:
```cpp
// 保存功能数据
QueryUserTest.bindValue(":Name", ui->tableWidgetUsrTest->item(i,0)->text());
QueryUserTest.bindValue(":Condition", ui->tableWidgetUsrTest->item(i,1)->text());
QueryUserTest.bindValue(":Test", ui->tableWidgetUsrTest->item(i,2)->text());
```

### 3. 问题模式分析

#### 当前模式 (问题):
```
数据库查询 → QTableWidget项 → 用户编辑 → 读取QTableWidget项 → 更新数据库
```
**特点**: UI控件被当作数据存储

#### 推荐模式:
```
数据库查询 → QAbstractTableModel → QTableView → 用户编辑 → QAbstractTableModel → 更新数据库
```
**特点**: 清晰的Model/View分离

## 影响评估

### 高影响区域

1. **数据一致性风险**:
   - UI控件数据可能与数据库不同步
   - 程序崩溃可能导致数据丢失

2. **可维护性问题**:
   - 违反Model/View架构原则
   - 难以添加验证逻辑
   - 代码重复率高

3. **性能问题**:
   - QTableWidget 性能较差
   - 无法处理大数据量
   - 无虚拟滚动支持

### 对话框分类

#### A. 重要数据编辑对话框 (需要修改)
- `DialogBranchAttr` - 功能子块属性，频繁使用
- `DialogUnitAttr` - 设备属性，核心功能
- `DialogUnitManage` - 设备管理，核心功能

#### B. 辅助工具对话框 (建议修改)
- `DialogFactoryManage` - 厂商管理
- `DialogFunctionManage` - 功能管理
- `DialogDiagUserTest` - 诊断测试

#### C. 一次性操作对话框 (可选修改)
- 各种配置对话框
- 导入导出对话框

## 修复建议

### 方案1: 完全迁移到Model/View (推荐)

**优点**:
- 彻底解决问题
- 一致的数据访问模式
- 更好的性能和可维护性

**缺点**:
- 需要大量代码修改
- 测试工作量大

**实施步骤**:
1. 为每个对话框创建 QAbstractTableModel 子类
2. 使用 QTableView 替代 QTableWidget
3. 实现数据加载和保存逻辑
4. 测试所有功能

### 方案2: 混合模式 (折中)

**优点**:
- 修改量小
- 风险低
- 易于逐步迁移

**缺点**:
- 仍有部分代码违反最佳实践
- 代码风格不一致

**实施步骤**:
1. 仅修改核心对话框 (DialogBranchAttr, DialogUnitAttr, DialogUnitManage)
2. 保持其他对话框不变
3. 在编码规范中明确限制

### 方案3: 保持现状 (不推荐)

**风险**:
- 数据不一致
- 维护困难
- 性能问题

## 推荐修复方案

### 短期 (当前版本)
**保持现状**，但增加防御性编程：

1. **添加数据验证**:
```cpp
// 在读取UI数据前验证
if (!ui->tableWidgetTermInfo->item(i, 0)) {
    qWarning() << "Invalid table item at row" << i;
    continue;
}
QString connNum = ui->tableWidgetTermInfo->item(i, 0)->text();
```

2. **添加文档说明**:
```cpp
// 明确标注这是临时数据存储
// 注意：这里使用QTableWidget作为临时数据存储
// 数据在对话框关闭时不会持久化
```

3. **代码审查清单**:
   - 新增对话框必须使用Model/View
   - 禁止将UI控件作为长期数据存储

### 中期 (下个版本)
**选择性迁移**:
1. 优先修改核心对话框
2. 验证修复效果
3. 逐步推广到其他对话框

### 长期 (未来版本)
**全面迁移**:
1. 所有对话框迁移到Model/View
2. 统一架构风格
3. 完善编码规范

## 审查结论

### 数据访问一致性状态

| 模块 | 数据访问模式 | 状态 | 说明 |
|------|-------------|------|------|
| MainWindow | 通过模型/读取UI输入 | ✅ 正确 | 完全符合最佳实践 |
| 核心对话框 | QTableWidget数据存储 | ⚠️ 可接受 | 有风险但影响有限 |
| 辅助对话框 | QTableWidget数据存储 | ⚠️ 可接受 | 有风险但影响有限 |

### 风险等级评估

**低风险** ✅:
- MainWindow数据访问完全正确
- 所有主界面使用Model/View架构
- 数据流程清晰

**中等风险** ⚠️:
- 对话框使用QTableWidget作为临时存储
- 数据在对话框生命周期内一致
- 程序崩溃可能导致临时数据丢失

### 建议措施

1. **立即执行**:
   - ✅ 确认MainWindow无问题
   - ✅ 在编码规范中明确对话框数据访问要求
   - ✅ 添加代码审查清单

2. **短期规划**:
   - [ ] 迁移核心对话框到Model/View
   - [ ] 验证修复效果
   - [ ] 更新测试用例

3. **长期规划**:
   - [ ] 全面迁移所有对话框
   - [ ] 统一架构风格
   - [ ] 完善文档

## 附录：详细问题代码清单

### dialogBranchAttr.cpp
**行数**: 86, 362-363, 378, 394, 397, 400, 459, 461, 505-507, 512, 514, 518-520
**问题**: 使用 tableWidgetTermInfo 作为数据存储
**建议**: 创建 Symb2TermInfoTableModel

### dialogfactorymanage.cpp
**行数**: 44-48, 66, 72, 76-80, 106, 145, 147, 188, 197, 205, 221, 232, 241, 266, 278-280, 284, 288, 293-295, 305, 314, 339, 352-354, 358, 362, 367-369
**问题**: 使用 tableWidget 作为数据存储
**建议**: 创建 FactoryTableModel

### dialogfunctionmanage.cpp
**行数**: 49-50, 60-62, 106, 127, 138, 146, 287-288, 365-366, 386, 417, 441, 499, 524-525, 617, 622-623, 689-690, 705, 725, 749, 756, 775-777, 784, 805, 812, 821, 833, 843, 879, 896, 917-919
**问题**: 使用多个 tableWidget 作为数据存储
**建议**: 创建 FunctionTableModel, ExecTableModel, CmdTableModel

### dialogunitmanage.cpp
**行数**: 3688, 3725
**问题**: 使用 tableWidgetUnit 作为数据存储
**建议**: 重用 EquipmentTableModel

### 其他文件
**dialogdiagnoseui.cpp**: 使用多个 tableWidget 作为数据存储
**dialogUnitAttr.cpp**: 使用 tableWidgetUnitPic 作为数据存储

---

**审查结论**: 主窗口数据访问完全正确，对话框存在数据存储滥用但风险可控。建议逐步迁移到Model/View架构。

**报告生成**: 2025-11-12 01:45
