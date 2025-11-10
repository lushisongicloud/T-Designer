# 故障诊断系统完整设计方案

## 1. 需求分析

### 1.1 核心需求
1. **多功能诊断决策树管理**：每个待诊断功能有独立的诊断决策树（约十几个节点）
2. **交互式诊断流程**：用户选择功能→系统推荐测试→用户反馈结果→最终故障隔离
3. **五个关键按钮功能**：
   - `btn_TestPass`: 测试通过
   - `btn_TestFail`: 测试失败
   - `BtnLastStep`: 回退到上一步
   - `toolButton_skip_this_test`: 跳过当前测试（自动推荐下一个）
   - `toolButton_slelct_other_test`: 手动选择其他测试
4. **决策树可视化管理**：在testmanagementdialog的tabDecision中展示、编辑决策树
5. **功能管理**：新建/编辑系统功能和对应的诊断决策树

### 1.2 技术约束
- Qt 5.12.9 + SQLite数据库
- 现有架构：DO(数据对象层) / BO(业务对象层) / UI(界面层)
- 已有组件：DiagnosisEngine, DiagnosisTree, DiagnosisTreeNode
- 界面文件：dialogdiagnoseui.ui 和 testmanagementdialog.ui

## 2. 总体架构设计

### 2.1 三层架构图
```
┌─────────────────────────────────────────────────────────┐
│                    UI Layer                             │
├────────────────────────┬────────────────────────────────┤
│ dialogDiagnoseUI       │ TestManagementDialog          │
│ - 诊断执行界面         │ - 决策树管理界面              │
│ - 5个按钮操作          │ - 树结构可视化                │
│ - 动态按钮文本         │ - 节点编辑                    │
└────────────────────────┴────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────────┐
│                 Business Object Layer                   │
├──────────────────────┬──────────────────────────────────┤
│ DiagnosisEngine      │ DecisionTreeManager              │
│ - 会话管理           │ - 树结构CRUD                     │
│ - 测试推荐算法       │ - 节点验证                       │
│ - 路径记录与回退     │ - 数据导入导出                   │
│ - 状态机管理         │                                  │
└──────────────────────┴──────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────────┐
│                  Data Object Layer                      │
├──────────────────────┬──────────────────────────────────┤
│ DiagnosisTree        │ DiagnosisTreeNode                │
│ DiagnosisSession     │ TestRecommendation               │
└──────────────────────┴──────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────────┐
│                    Database Schema                      │
├──────────────────────────────────────────────────────────┤
│ diagnosis_tree, diagnosis_tree_node                     │
│ diagnosis_session, diagnosis_step_history               │
│ function_definition, test_recommendation_pool           │
└─────────────────────────────────────────────────────────┘
```

### 2.2 核心数据流
```
用户选择功能 → 加载决策树 → 推荐首个测试
     ↓
用户点击按钮 → 记录测试结果 → 更新当前节点
     ↓
判断节点类型：
   - 测试节点 → 推荐新测试 (循环)
   - 故障节点 → 显示故障结论 (结束)
   - 无子节点 → 诊断失败 (结束)
```

## 3. 数据库设计

### 3.1 现有表扩展

#### diagnosis_tree_node 表 (扩展字段)
```sql
ALTER TABLE diagnosis_tree_node ADD COLUMN skip_count INTEGER DEFAULT 0;
ALTER TABLE diagnosis_tree_node ADD COLUMN skip_reason TEXT;
ALTER TABLE diagnosis_tree_node ADD COLUMN alternative_tests TEXT; -- JSON数组
ALTER TABLE diagnosis_tree_node ADD COLUMN cost_estimate REAL DEFAULT 0.0;
ALTER TABLE diagnosis_tree_node ADD COLUMN duration_estimate REAL DEFAULT 0.0;
```

### 3.2 新增表设计

#### diagnosis_session 表 (诊断会话记录)
```sql
CREATE TABLE IF NOT EXISTS diagnosis_session (
    session_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    function_id INTEGER,
    start_time TEXT NOT NULL,
    end_time TEXT,
    session_state TEXT NOT NULL, -- NotStarted, InProgress, Completed, Failed, Cancelled
    fault_node_id INTEGER,
    total_steps INTEGER DEFAULT 0,
    total_duration REAL DEFAULT 0.0,
    user_id TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id),
    FOREIGN KEY (fault_node_id) REFERENCES diagnosis_tree_node(node_id)
);
```

#### diagnosis_step_history 表 (诊断步骤历史)
```sql
CREATE TABLE IF NOT EXISTS diagnosis_step_history (
    step_id INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id INTEGER NOT NULL,
    step_number INTEGER NOT NULL,
    node_id INTEGER NOT NULL,
    test_outcome TEXT NOT NULL, -- Pass, Fail, Skip
    timestamp TEXT NOT NULL,
    user_comment TEXT,
    duration REAL DEFAULT 0.0,
    can_rollback INTEGER DEFAULT 1,
    FOREIGN KEY (session_id) REFERENCES diagnosis_session(session_id),
    FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id)
);
```

#### test_recommendation_pool 表 (测试推荐池)
```sql
CREATE TABLE IF NOT EXISTS test_recommendation_pool (
    recommendation_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    node_id INTEGER NOT NULL,
    alternative_node_ids TEXT, -- JSON数组：可替代的测试节点
    recommendation_score REAL DEFAULT 0.0,
    recommendation_reason TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id),
    FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id)
);
```

## 4. DiagnosisEngine 功能扩展

### 4.1 新增方法设计

```cpp
class DiagnosisEngine : public QObject {
    Q_OBJECT

public:
    // ===== 高级导航功能 =====
    
    /**
     * @brief 回退到上一步
     * @return 成功返回true，无法回退返回false
     */
    bool stepBack();
    
    /**
     * @brief 跳过当前测试并自动推荐下一个
     * @return 成功返回true
     */
    bool skipTestAndRecommendNext();
    
    /**
     * @brief 获取可选的替代测试列表
     * @return 替代测试节点列表
     */
    QList<DiagnosisTreeNode*> getAlternativeTests();
    
    /**
     * @brief 手动选择特定测试
     * @param nodeId 目标测试节点ID
     * @return 成功返回true
     */
    bool selectManualTest(int nodeId);
    
    /**
     * @brief 获取历史步骤（用于显示诊断路径）
     * @return 步骤列表
     */
    QList<DiagnosisStep> getStepHistory() const { return m_diagnosisPath; }
    
    /**
     * @brief 检查是否可以回退
     */
    bool canStepBack() const { return m_diagnosisPath.size() > 0; }
    
    // ===== 智能推荐算法 =====
    
    /**
     * @brief 基于历史和上下文推荐测试
     * @param considerCost 是否考虑成本
     * @param considerDuration 是否考虑时间
     * @return 推荐的测试节点
     */
    DiagnosisTreeNode* recommendNextTest(bool considerCost = true, 
                                         bool considerDuration = true);
    
    /**
     * @brief 计算测试推荐分数
     * @param node 候选测试节点
     * @return 推荐分数 (0-100)
     */
    double calculateRecommendationScore(DiagnosisTreeNode* node);
    
    // ===== 会话持久化 =====
    
    /**
     * @brief 保存当前会话到数据库
     * @return 会话ID
     */
    int saveSession();
    
    /**
     * @brief 加载历史会话
     * @param sessionId 会话ID
     * @return 成功返回true
     */
    bool loadSession(int sessionId);

private:
    // ===== 内部状态 =====
    QStack<DiagnosisStep> m_stepStack;  // 用于回退的步骤栈
    int m_currentSessionId;
    QMap<int, double> m_nodeScoreCache; // 节点分数缓存
    
    // ===== 内部算法 =====
    QList<DiagnosisTreeNode*> findAlternativeTestsInternal();
    bool validateStepTransition(DiagnosisTreeNode* from, DiagnosisTreeNode* to);
    void updateRecommendationCache();
};
```

### 4.2 测试推荐算法设计

**推荐分数计算公式：**
```
Score = W1×故障检测能力 + W2×故障隔离能力 + W3×(1-成本归一化) + W4×(1-时间归一化) + W5×历史成功率
```

权重配置：
- W1 = 0.35 (故障检测能力最重要)
- W2 = 0.30 (故障隔离能力次之)
- W3 = 0.15 (成本因素)
- W4 = 0.10 (时间因素)
- W5 = 0.10 (历史成功率)

## 5. UI实现设计

### 5.1 dialogDiagnoseUI 按钮功能实现

#### 5.1.1 btn_TestPass (测试通过)
```cpp
void dialogDiagnoseUI::on_btn_TestPass_clicked() {
    if (!diagnosisEngine || !diagnosisEngine->hasActiveSession()) {
        QMessageBox::warning(this, "错误", "没有活动的诊断会话");
        return;
    }
    
    recordTestResult(TestOutcome::Pass);
}
```

#### 5.1.2 btn_TestFail (测试失败)
```cpp
void dialogDiagnoseUI::on_btn_TestFail_clicked() {
    if (!diagnosisEngine || !diagnosisEngine->hasActiveSession()) {
        QMessageBox::warning(this, "错误", "没有活动的诊断会话");
        return;
    }
    
    recordTestResult(TestOutcome::Fail);
}
```

#### 5.1.3 BtnLastStep (上一步)
```cpp
void dialogDiagnoseUI::on_BtnLastStep_clicked() {
    if (!diagnosisEngine || !diagnosisEngine->canStepBack()) {
        QMessageBox::information(this, "提示", "无法回退");
        return;
    }
    
    if (diagnosisEngine->stepBack()) {
        displayCurrentTest();
        QMessageBox::information(this, "成功", "已回退到上一步");
    } else {
        QMessageBox::warning(this, "错误", "回退失败");
    }
}
```

#### 5.1.4 toolButton_skip_this_test (跳过当前测试)
```cpp
void dialogDiagnoseUI::on_toolButton_skip_this_test_clicked() {
    if (!diagnosisEngine || !diagnosisEngine->hasActiveSession()) {
        QMessageBox::warning(this, "错误", "没有活动的诊断会话");
        return;
    }
    
    if (diagnosisEngine->skipTestAndRecommendNext()) {
        displayCurrentTest();
    } else {
        QMessageBox::warning(this, "错误", "无法跳过测试或找不到替代测试");
    }
}
```

#### 5.1.5 toolButton_slelct_other_test (选择其他测试)
```cpp
void dialogDiagnoseUI::on_toolButton_slelct_other_test_clicked() {
    if (!diagnosisEngine || !diagnosisEngine->hasActiveSession()) {
        QMessageBox::warning(this, "错误", "没有活动的诊断会话");
        return;
    }
    
    QList<DiagnosisTreeNode*> alternatives = diagnosisEngine->getAlternativeTests();
    if (alternatives.isEmpty()) {
        QMessageBox::information(this, "提示", "没有可选的替代测试");
        return;
    }
    
    // 创建选择对话框
    DialogSelectAnotherTest* dialog = new DialogSelectAnotherTest(alternatives, this);
    if (dialog->exec() == QDialog::Accepted) {
        int selectedNodeId = dialog->getSelectedNodeId();
        if (diagnosisEngine->selectManualTest(selectedNodeId)) {
            displayCurrentTest();
        }
    }
    delete dialog;
}
```

### 5.2 dialogdiagnoseui.ui 控件布局

需要在界面中添加以下控件：
```xml
<widget class="QTextEdit" name="textEdit_TestDesc">
  <property name="readOnly"><bool>true</bool></property>
</widget>

<widget class="QPushButton" name="btn_TestPass">
  <property name="text"><string>测试通过</string></property>
</widget>

<widget class="QPushButton" name="btn_TestFail">
  <property name="text"><string>测试失败</string></property>
</widget>

<widget class="QPushButton" name="BtnLastStep">
  <property name="text"><string>上一步</string></property>
</widget>

<widget class="QToolButton" name="toolButton_skip_this_test">
  <property name="text"><string>跳过当前测试</string></property>
</widget>

<widget class="QToolButton" name="toolButton_slelct_other_test">
  <property name="text"><string>选择其他测试</string></property>
</widget>
```

## 6. TestManagementDialog 决策树可视化

### 6.1 功能需求
1. 显示功能列表（关联的诊断树）
2. 树形展示决策树结构
3. 节点详细信息查看/编辑
4. 新建/编辑/删除节点
5. 树结构验证

### 6.2 界面设计
```
tabDecision布局：
┌──────────────────────────────────────────────────┐
│ 功能选择：[ComboBox: 选择功能]  [刷新按钮]      │
├──────────────────────────────────────────────────┤
│ QSplitter (水平分割)                             │
│ ┌─────────────────┬──────────────────────────┐  │
│ │ QTreeWidget     │ 节点详情面板             │  │
│ │ - 树形展示      │ - 节点ID                 │  │
│ │ - 节点类型图标  │ - 节点类型               │  │
│ │ - 拖拽排序      │ - 测试描述               │  │
│ │                 │ - 期望结果               │  │
│ │                 │ - 故障假设               │  │
│ │                 │ - 按钮文本               │  │
│ │                 │ - 成本/时间              │  │
│ │                 │ [保存] [取消]            │  │
│ └─────────────────┴──────────────────────────┘  │
├──────────────────────────────────────────────────┤
│ [新建节点] [删除节点] [验证树结构] [导出]       │
└──────────────────────────────────────────────────┘
```

### 6.3 实现方法
```cpp
void TestManagementDialog::loadDecisionTreeForFunction(int functionId) {
    // 加载诊断树
    DiagnosisTree* tree = loadTreeFromDatabase(functionId);
    if (!tree) return;
    
    // 清空树控件
    ui->treeDecision->clear();
    
    // 递归构建UI树
    buildTreeWidgetRecursive(tree->rootNode(), nullptr);
}

void TestManagementDialog::buildTreeWidgetRecursive(
    DiagnosisTreeNode* node, QTreeWidgetItem* parentItem) {
    
    QTreeWidgetItem* item = new QTreeWidgetItem();
    
    // 设置节点图标和文本
    QIcon icon = getIconForNodeType(node->nodeType());
    item->setIcon(0, icon);
    item->setText(0, node->testDescription().left(50));
    item->setData(0, Qt::UserRole, node->nodeId());
    
    if (parentItem) {
        parentItem->addChild(item);
    } else {
        ui->treeDecision->addTopLevelItem(item);
    }
    
    // 递归添加子节点
    for (DiagnosisTreeNode* child : node->children()) {
        buildTreeWidgetRecursive(child, item);
    }
}
```

## 7. 实施计划

### 7.1 任务分解
1. **阶段1：数据库扩展** (2小时)
   - 创建新表
   - 扩展现有表字段
   - 测试数据迁移脚本

2. **阶段2：DiagnosisEngine扩展** (3小时)
   - 实现回退功能
   - 实现跳过测试
   - 实现替代测试推荐
   - 测试推荐算法
   - 会话持久化

3. **阶段3：UI控件创建** (1小时)
   - 在dialogdiagnoseui.ui中添加控件
   - 调整布局

4. **阶段4：dialogDiagnoseUI功能实现** (2小时)
   - 实现5个按钮的槽函数
   - 创建DialogSelectAnotherTest对话框
   - 更新displayCurrentTest方法

5. **阶段5：TestManagementDialog决策树可视化** (3小时)
   - 实现树形展示
   - 实现节点编辑面板
   - 实现新建/删除功能
   - 树结构验证

6. **阶段6：集成测试** (1小时)
   - 编译测试
   - 功能测试
   - Bug修复

### 7.2 时间估算
总计约12小时（符合8小时睡眠期间的工作量，考虑到深入分析和测试）

## 8. 测试计划

### 8.1 单元测试
- DiagnosisEngine::stepBack() 测试
- DiagnosisEngine::skipTestAndRecommendNext() 测试
- DiagnosisEngine::getAlternativeTests() 测试
- 推荐算法分数计算测试

### 8.2 集成测试场景
1. **完整诊断流程测试**
   - 选择功能 → 执行测试 → 点击通过/失败 → 到达故障结论

2. **回退功能测试**
   - 执行3个测试 → 回退2次 → 验证状态正确

3. **跳过测试测试**
   - 跳过当前测试 → 验证推荐了替代测试

4. **手动选择测试测试**
   - 打开选择对话框 → 选择特定测试 → 验证跳转正确

5. **决策树编辑测试**
   - 加载树 → 修改节点 → 保存 → 验证数据库

### 8.3 边界条件测试
- 空树处理
- 单节点树
- 深层嵌套树
- 循环引用检测
- 无替代测试时的处理

## 9. 风险评估

### 9.1 技术风险
| 风险 | 影响 | 概率 | 缓解措施 |
|------|------|------|----------|
| UI控件命名冲突 | 中 | 低 | 检查现有ui文件，使用唯一命名 |
| 回退算法复杂度 | 高 | 中 | 使用栈结构简化实现 |
| 数据库迁移失败 | 高 | 低 | 备份数据库，提供回滚脚本 |
| 树结构循环引用 | 高 | 低 | 实现循环检测算法 |

### 9.2 质量保证
- 代码审查检查点
- 单元测试覆盖率目标：80%
- 集成测试场景覆盖率：100%

## 10. 后续优化方向
1. 基于机器学习的测试推荐
2. 诊断历史统计分析
3. 多用户协作诊断
4. 诊断报告生成与导出
5. 移动端诊断界面
