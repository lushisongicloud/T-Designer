**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 故障诊断系统 - 新架构文档

## 概述

T-Designer的故障诊断模块已从外部依赖（L2test.exe）迁移到自包含的决策树引擎。新系统基于`diagnosis_tree`和`diagnosis_tree_node`两张数据库表，实现了自动化的测试推荐和故障隔离。

## 文档导航

### 🚀 快速入门
- **[QUICK_START.md](QUICK_START.md)** - 5分钟快速启动指南，包含UI临时测试方案

### 📋 详细文档
- **[COMPLETION_REPORT.md](COMPLETION_REPORT.md)** - 完整工作报告，包含时间线、决策记录、问题清单
- **[DIAGNOSIS_INTEGRATION_SUMMARY.md](DIAGNOSIS_INTEGRATION_SUMMARY.md)** - 技术实现总结，代码统计，API说明
- **[DIAGNOSIS_REDESIGN.md](DIAGNOSIS_REDESIGN.md)** - 原始设计文档，需求分析，数据模型

### 🛠️ 工具脚本
- **[tools/migrate_diagnosis_data.py](tools/migrate_diagnosis_data.py)** - 数据迁移脚本（Function → diagnosis_tree）
- **[tools/extend_diagnosis_tables.sql](tools/extend_diagnosis_tables.sql)** - 数据库schema扩展脚本
- **[tools/test_function_data.sql](tools/test_function_data.sql)** - 测试数据生成脚本

## 系统架构

```
┌─────────────────────────────────────────┐
│          UI Layer (MainWindow)          │
│  - LoadAllFunction()                    │
│  - on_toolButton_start_diagnosis_*()    │
│  - displayCurrentTest()                 │
│  - recordCurrentTestResult()            │
└────────────────┬────────────────────────┘
                 │
                 ↓
┌─────────────────────────────────────────┐
│     BO Layer (DiagnosisEngine)          │
│  - startDiagnosisSession()              │
│  - getCurrentRecommendedTest()          │
│  - recordTestResult()                   │
│  - isFaultIsolated()                    │
└────────────────┬────────────────────────┘
                 │
                 ↓
┌─────────────────────────────────────────┐
│  DO Layer (DiagnosisTree/TreeNode)      │
│  - loadFullTree()                       │
│  - findChildByOutcome()                 │
│  - loadFromDatabase()                   │
│  - saveToDatabase()                     │
└────────────────┬────────────────────────┘
                 │
                 ↓
┌─────────────────────────────────────────┐
│      Database (project.db)              │
│  - diagnosis_tree                       │
│  - diagnosis_tree_node                  │
└─────────────────────────────────────────┘
```

## 核心类说明

### 1. DiagnosisTreeNode (DO层)
**文件：** `DO/diagnosistreenode.h/.cpp`

**职责：** 诊断树节点的数据对象，对应数据库表`diagnosis_tree_node`

**关键方法：**
```cpp
// 树形结构
DiagnosisTreeNode* parent() const;
QList<DiagnosisTreeNode*> children() const;
DiagnosisTreeNode* findChildByOutcome(TestOutcome outcome);

// 数据库操作
bool loadFromDatabase(QSqlDatabase& db, int nodeId);
bool saveToDatabase(QSqlDatabase& db);
bool updateToDatabase(QSqlDatabase& db);

// 属性访问
int nodeId() const;
DiagnosisNodeType nodeType() const;
QString testDescription() const;
QString faultHypothesis() const;
```

**枚举类型：**
```cpp
enum class DiagnosisNodeType { Test, Fault, Branch };
enum class TestOutcome { Unknown, Pass, Fail, Skip };
```

### 2. DiagnosisTree (DO层)
**文件：** `DO/diagnosistree.h/.cpp`

**职责：** 管理完整的诊断树结构

**关键方法：**
```cpp
// 树加载
bool loadByFunctionId(QSqlDatabase& db, int functionId);
bool loadFullTree(QSqlDatabase& db, int treeId);

// 树查询
DiagnosisTreeNode* findNodeById(int nodeId);
QList<DiagnosisTreeNode*> getAllLeafNodes();
QList<DiagnosisTreeNode*> getAllTestNodes();

// 树验证
bool validateTree(QString& errorMsg);
```

### 3. DiagnosisEngine (BO层)
**文件：** `BO/diagnosisengine.h/.cpp`

**职责：** 诊断推理引擎，实现会话管理和故障隔离

**关键方法：**
```cpp
// 会话管理
bool startDiagnosisSession(int treeId);
void resetSession();
void cancelSession();

// 测试推荐
DiagnosisTreeNode* getCurrentRecommendedTest();
bool recordTestResult(TestOutcome outcome);

// 故障隔离
bool isFaultIsolated() const;
DiagnosisTreeNode* getFaultConclusion();
int getIsolationLevel() const;

// 路径跟踪
QList<DiagnosisStep> getDiagnosisPath() const;
QString getPathSummary() const;
```

**信号：**
```cpp
signals:
    void testRecommended(DiagnosisTreeNode* testNode);
    void faultIsolated(DiagnosisTreeNode* faultNode);
    void sessionStateChanged(DiagnosisSessionState newState);
```

## 数据库Schema

### diagnosis_tree 表
| 字段 | 类型 | 说明 |
|------|------|------|
| tree_id | INTEGER PK | 树ID |
| function_id | INTEGER | 关联功能ID |
| root_node_id | INTEGER FK | 根节点ID |
| name | TEXT | 树名称 |
| description | TEXT | 描述 |
| created_time | TEXT | 创建时间 |
| auto_generated | INTEGER | 是否自动生成 |

### diagnosis_tree_node 表
| 字段 | 类型 | 说明 |
|------|------|------|
| node_id | INTEGER PK | 节点ID |
| tree_id | INTEGER FK | 所属树ID |
| parent_node_id | INTEGER FK | 父节点ID |
| test_id | INTEGER | 关联测试ID |
| state_id | INTEGER | 关联状态ID |
| node_type | TEXT | 节点类型（Test/Fault/Branch） |
| outcome | TEXT | 测试结果（Pass/Fail/Skip） |
| test_description | TEXT | 测试描述 |
| expected_result | TEXT | 预期结果 |
| fault_hypothesis | TEXT | 故障假设 |
| isolation_level | INTEGER | 隔离度 |
| test_priority | INTEGER | 测试优先级 |
| comment | TEXT | 备注 |

## 工作流程

### 标准诊断流程
```
1. 用户选择功能
   ↓
2. MainWindow::on_toolButton_start_diagnosis_clicked()
   ↓
3. diagnosisEngine->startDiagnosisSession(tree_id)
   ├─ DiagnosisTree::loadByFunctionId()
   ├─ 验证树结构
   └─ 初始化currentNode为根节点
   ↓
4. displayCurrentTest()
   ├─ getCurrentRecommendedTest() → 返回Test类型节点
   ├─ 显示testDescription和expectedResult
   └─ 等待用户输入
   ↓
5. 用户点击"测试通过/失败/跳过"
   ↓
6. recordCurrentTestResult(outcome)
   ├─ diagnosisEngine->recordTestResult(outcome)
   ├─ 查找对应outcome的子节点
   ├─ 更新currentNode
   └─ 记录到diagnosisPath
   ↓
7. 递归回到步骤4，直到：
   - currentNode->nodeType() == Fault → 诊断完成
   - 无有效子节点 → 诊断失败
   ↓
8. 显示诊断结果
   ├─ 故障假设
   ├─ 隔离度
   └─ 完整诊断路径
```

### 决策树导航逻辑
```cpp
// 示例：线性决策树
root (Branch)
├─ test1 (Test)
│  ├─ [outcome=Fail] → fault1 (Fault: "test1故障")
│  └─ [outcome=Pass] → branch1 (Branch)
│     └─ test2 (Test)
│        ├─ [outcome=Fail] → fault2 (Fault: "test2故障")
│        └─ [outcome=Pass] → branch2 (Branch)
│           └─ test3 (Test)
│              ├─ [outcome=Fail] → fault3 (Fault: "test3故障")
│              └─ [outcome=Pass] → fault_other (Fault: "其他故障")

// 导航：
// currentNode = root
// recordTestResult(Pass) → currentNode = test1
// recordTestResult(Pass) → currentNode = test2
// recordTestResult(Fail) → currentNode = fault2 (诊断完成)
```

## 迁移指南

### 从旧系统迁移
```powershell
# 1. 备份现有数据库
copy MyProjects\YourProject\project.db MyProjects\YourProject\project.db.backup

# 2. 执行schema扩展
sqlite3 MyProjects\YourProject\project.db < tools\extend_diagnosis_tables.sql

# 3. 运行数据迁移脚本
python tools\migrate_diagnosis_data.py MyProjects\YourProject\project.db

# 4. 验证迁移结果
sqlite3 MyProjects\YourProject\project.db "SELECT COUNT(*) FROM diagnosis_tree;"
sqlite3 MyProjects\YourProject\project.db "SELECT COUNT(*) FROM diagnosis_tree_node;"
```

### 数据验证
```sql
-- 检查树完整性
SELECT dt.tree_id, dt.name, COUNT(dtn.node_id) AS node_count
FROM diagnosis_tree dt
LEFT JOIN diagnosis_tree_node dtn ON dt.tree_id = dtn.tree_id
GROUP BY dt.tree_id;

-- 检查节点类型分布
SELECT tree_id, node_type, COUNT(*) AS count
FROM diagnosis_tree_node
GROUP BY tree_id, node_type;

-- 检查孤儿节点
SELECT node_id, tree_id, parent_node_id
FROM diagnosis_tree_node
WHERE parent_node_id NOT IN (SELECT node_id FROM diagnosis_tree_node)
  AND parent_node_id IS NOT NULL;
```

## API使用示例

### 示例1：启动诊断会话
```cpp
// 1. 获取tree_id（从UI选择）
int treeId = ui->tableWidget_function_select->item(row, 0)->data(Qt::UserRole).toInt();

// 2. 启动会话
if (!diagnosisEngine->startDiagnosisSession(treeId)) {
    QMessageBox::warning(this, "错误", "启动诊断会话失败！");
    return;
}

// 3. 获取第一个测试
DiagnosisTreeNode* firstTest = diagnosisEngine->getCurrentRecommendedTest();
if (firstTest) {
    displayTest(firstTest);
}
```

### 示例2：记录测试结果
```cpp
void MainWindow::on_btnTestPass_clicked() {
    // 1. 记录结果
    if (!diagnosisEngine->recordTestResult(TestOutcome::Pass)) {
        QMessageBox::warning(this, "错误", "记录测试结果失败！");
        return;
    }
    
    // 2. 检查是否完成
    if (diagnosisEngine->isFaultIsolated()) {
        showDiagnosisResult();
    } else {
        // 3. 显示下一个测试
        DiagnosisTreeNode* nextTest = diagnosisEngine->getCurrentRecommendedTest();
        if (nextTest) {
            displayTest(nextTest);
        }
    }
}
```

### 示例3：显示诊断结果
```cpp
void MainWindow::showDiagnosisResult() {
    DiagnosisTreeNode* faultNode = diagnosisEngine->getFaultConclusion();
    if (!faultNode) {
        QMessageBox::warning(this, "错误", "未找到故障结论！");
        return;
    }
    
    QString result = QString("故障: %1\n隔离度: %2\n")
        .arg(faultNode->faultHypothesis())
        .arg(faultNode->isolationLevel());
    
    // 添加诊断路径
    QList<DiagnosisStep> path = diagnosisEngine->getDiagnosisPath();
    result += "\n诊断路径:\n";
    for (int i = 0; i < path.size(); ++i) {
        QString outcome = (path[i].outcome == TestOutcome::Pass) ? "通过" : "失败";
        result += QString("%1. %2 -> %3\n")
            .arg(i + 1)
            .arg(path[i].testNode->testDescription())
            .arg(outcome);
    }
    
    QMessageBox::information(this, "诊断完成", result);
}
```

## 性能优化

### 数据库索引
```sql
CREATE INDEX idx_diagnosis_tree_function ON diagnosis_tree(function_id);
CREATE INDEX idx_diagnosis_tree_node_tree ON diagnosis_tree_node(tree_id);
CREATE INDEX idx_diagnosis_tree_node_parent ON diagnosis_tree_node(parent_node_id);
CREATE INDEX idx_diagnosis_tree_node_type ON diagnosis_tree_node(node_type);
CREATE INDEX idx_diagnosis_tree_node_outcome ON diagnosis_tree_node(outcome);
```

### 缓存策略
- DiagnosisEngine在会话期间缓存整棵树，避免重复查询
- 使用QHash<int, DiagnosisTreeNode*>加速节点查找
- 预加载所有子节点，避免递归数据库查询

### 内存管理
- DiagnosisTree拥有所有节点的所有权
- 析构时自动释放所有节点内存
- 避免跨会话共享节点指针

## 故障排查

### 常见问题
1. **编译错误："TestOutcome未定义"**
   - 确保包含`#include "BO/diagnosisengine.h"`
   - TestOutcome是全局enum class，不需要类限定符

2. **运行时错误："getCurrentRecommendedTest返回nullptr"**
   - 检查树是否正确加载：`diagnosisEngine->getTree()`
   - 验证根节点类型：应为Branch，第一个子节点应为Test
   - 检查outcome是否正确设置

3. **数据库错误："no such table: diagnosis_tree"**
   - 执行`tools/extend_diagnosis_tables.sql`
   - 或使用迁移后的数据库

4. **诊断无法完成："未找到故障结论"**
   - 检查决策树是否有Fault类型的叶子节点
   - 验证树结构：`validateTree(errorMsg)`
   - 查看诊断路径：`getDiagnosisPath()`

### 调试日志
启用详细日志输出：
```cpp
qSetMessagePattern("[%{time hh:mm:ss.zzz}] %{type}: %{message}");
QLoggingCategory::setFilterRules("qt.diagnosis.*=true");
```

## 下一步开发

### 优先级1：UI完善
- [ ] 添加测试结果按钮（btnTestPass/Fail/Skip）
- [ ] 调整测试描述布局
- [ ] 添加诊断进度条

### 优先级2：功能增强
- [ ] 测试优先级排序算法
- [ ] 支持测试跳过条件
- [ ] 诊断历史记录
- [ ] 导出诊断报告

### 优先级3：工具完善
- [ ] 决策树可视化编辑器
- [ ] 树结构验证工具
- [ ] 性能分析工具
- [ ] 单元测试套件

## 联系与贡献
遇到问题或有改进建议，请：
1. 查阅相关文档（见"文档导航"）
2. 检查代码注释（类和方法都有详细说明）
3. 运行工具脚本验证数据完整性
4. 提交Issue描述问题和复现步骤

---

**最后更新：** 2025-11-10 08:00  
**版本：** 2.0（新诊断系统）  
**状态：** ✅ 核心功能完成，待UI完善和功能测试
