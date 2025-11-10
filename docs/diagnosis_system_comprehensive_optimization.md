# 诊断系统全面优化方案

## 问题汇总

### 1. 数据库问题 ✅ 已修复
- **root_node_id错误**: 树2和树3的root_node_id都写成了1，导致加载错误节点
  - 修复：树2 root_node_id = 20, 树3 root_node_id = 33
- **缺失字段**: diagnosis_tree_node表缺少skip_count等扩展字段
  - 修复：添加skip_count, skip_reason, cost_estimate, duration_estimate字段

### 2. Branch节点处理逻辑 ✅ 已修复
- **问题**: recordTestResult找到Branch节点后直接失败
- **修复**: 自动查找Branch节点下的第一个Test子节点

### 3. 故障隔离后的会话状态 ⚠️ 需改进
- **问题**: 故障隔离后会话状态变为Completed，无法回退
- **建议**: 
  - 保持会话InProgress直到用户主动关闭
  - 或允许从Completed状态回退并恢复InProgress

### 4. 用户体验优化建议

#### 4.1 按钮行为优化
**当前行为**:
- Pass/Fail按钮：记录结果 → 自动跳转下一个测试
- 上一步按钮：回退到前一个测试
- 跳过按钮：跳过当前测试 → 自动推荐替代测试
- 选择其他测试：手动选择测试节点

**建议优化**:
1. **故障隔离后的行为**
   - 隐藏Pass/Fail按钮
   - 显示"重新诊断"按钮和"返回"按钮
   - 上一步按钮应该可用（允许回退重新诊断）

2. **诊断路径显示**
   - 当前仅显示✓/✗符号，建议添加测试名称
   - 格式：`测试1(✓) → 测试2(✓) → 测试3(✗) → 故障X`

3. **测试描述增强**
   - 当前仅显示test_description
   - 建议添加expected_result的显示
   - 格式：
     ```
     【测试步骤】
     测试AC220V供电是否正常
     
     【预期结果】
     万用表显示电压220V±10%
     
     【操作提示】
     1. 使用万用表测试AC220V输入端
     2. 记录电压值
     ```

#### 4.2 错误提示优化
**当前提示**: "无法记录测试结果"
**建议改进**:
- "无法继续诊断：未找到匹配的下一步"
- "无法继续诊断：Branch节点下没有可用的测试节点"
- "诊断会话已结束，请重新开始诊断"

#### 4.3 跳过测试功能增强
**当前问题**: "Failed to update skip_count: Parameter count mismatch"
**修复**: 已添加缺失的数据库字段

**建议增强**:
- 跳过时记录跳过原因（可选输入框）
- 显示跳过次数："此测试已被跳过 N 次"
- 跳过次数过多时警告："此测试被频繁跳过，可能影响诊断准确性"

## 代码优化建议

### 1. recordTestResult方法重构

```cpp
bool DiagnosisEngine::recordTestResult(TestOutcome outcome, const QString &userComment)
{
    if (!hasActiveSession()) {
        qDebug() << "No active diagnosis session";
        return false;
    }

    if (!m_currentNode || !m_currentNode->isTestNode()) {
        qDebug() << "Current node is not a valid test node";
        return false;
    }

    // 记录诊断步骤
    DiagnosisStep step;
    step.stepNumber = m_diagnosisPath.size() + 1;
    step.testNode = m_currentNode;
    step.outcome = outcome;
    step.timestamp = QDateTime::currentDateTime();
    step.userComment = userComment;
    m_diagnosisPath.append(step);

    emit testResultRecorded(step);

    qDebug() << "Test result recorded - Step" << step.stepNumber
             << "Node:" << m_currentNode->nodeId()
             << "Outcome:" << (outcome == TestOutcome::Pass ? "Pass" : 
                              outcome == TestOutcome::Fail ? "Fail" : "Skip");

    // 查找下一个节点
    DiagnosisTreeNode* nextNode = findNextNode(m_currentNode, outcome);
    
    if (!nextNode) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("无法继续诊断，没有匹配的下一步");
        return false;
    }

    // 递归处理Branch节点，直到找到Test或Fault节点
    nextNode = resolveToExecutableNode(nextNode);
    
    if (!nextNode) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("无法找到可执行的测试或故障节点");
        return false;
    }

    m_currentNode = nextNode;

    // 检查是否到达故障节点
    if (m_currentNode->isFaultNode()) {
        // 保持InProgress状态以支持回退
        // updateSessionState(DiagnosisSessionState::Completed);
        m_sessionEndTime = QDateTime::currentDateTime();
        emit faultIsolated(m_currentNode);
        qDebug() << "Fault isolated:" << m_currentNode->faultHypothesis();
        return true;
    }

    // 推荐新测试
    emit testRecommended(m_currentNode);
    return true;
}

// 新增辅助方法：递归解析Branch节点
DiagnosisTreeNode* DiagnosisEngine::resolveToExecutableNode(DiagnosisTreeNode* node)
{
    if (!node) return nullptr;
    
    // 如果是Test或Fault节点，直接返回
    if (node->isTestNode() || node->isFaultNode()) {
        return node;
    }
    
    // 如果是Branch节点，查找第一个Test子节点
    if (node->isBranchNode() && node->hasChildren()) {
        for (DiagnosisTreeNode* child : node->children()) {
            // 递归处理（支持多层Branch嵌套）
            DiagnosisTreeNode* resolved = resolveToExecutableNode(child);
            if (resolved && (resolved->isTestNode() || resolved->isFaultNode())) {
                return resolved;
            }
        }
    }
    
    return nullptr;
}
```

### 2. stepBack方法增强

```cpp
bool DiagnosisEngine::stepBack()
{
    if (!canStepBack()) {
        qDebug() << "Cannot step back: no history";
        return false;
    }

    // 允许从Completed状态回退
    if (m_sessionState != DiagnosisSessionState::InProgress && 
        m_sessionState != DiagnosisSessionState::Completed) {
        qDebug() << "Cannot step back: invalid session state";
        return false;
    }

    // 获取并移除最后一步
    DiagnosisStep lastStep = m_diagnosisPath.takeLast();
    
    qDebug() << "Stepping back from step" << lastStep.stepNumber 
             << ", node" << lastStep.testNode->nodeId();
    
    // 如果还有步骤，恢复到前一个节点
    if (!m_diagnosisPath.isEmpty()) {
        DiagnosisStep previousStep = m_diagnosisPath.last();
        m_currentNode = previousStep.testNode;
    } else {
        // 回到第一个测试节点
        m_currentNode = findFirstTestNode();
        if (!m_currentNode) {
            qDebug() << "Cannot find first test node";
            return false;
        }
    }
    
    // 恢复会话状态为InProgress
    if (m_sessionState == DiagnosisSessionState::Completed) {
        updateSessionState(DiagnosisSessionState::InProgress);
        qDebug() << "Session state restored to InProgress";
    }
    
    // 触发测试推荐信号
    if (m_currentNode && m_currentNode->isTestNode()) {
        emit testRecommended(m_currentNode);
    }
    
    return true;
}

// 辅助方法：查找第一个测试节点
DiagnosisTreeNode* DiagnosisEngine::findFirstTestNode()
{
    if (!m_currentTree || !m_currentTree->rootNode()) {
        return nullptr;
    }
    
    DiagnosisTreeNode* root = m_currentTree->rootNode();
    
    // 如果根节点就是测试节点，直接返回
    if (root->isTestNode()) {
        return root;
    }
    
    // 递归查找第一个测试节点
    return findFirstTestNodeRecursive(root);
}

DiagnosisTreeNode* DiagnosisEngine::findFirstTestNodeRecursive(DiagnosisTreeNode* node)
{
    if (!node) return nullptr;
    
    if (node->isTestNode()) {
        return node;
    }
    
    if (node->hasChildren()) {
        for (DiagnosisTreeNode* child : node->children()) {
            DiagnosisTreeNode* testNode = findFirstTestNodeRecursive(child);
            if (testNode) {
                return testNode;
            }
        }
    }
    
    return nullptr;
}
```

### 3. UI显示优化

```cpp
void dialogDiagnoseUI::displayCurrentTest()
{
    if (!diagnosisEngine) {
        qWarning() << "DiagnosisEngine is null";
        return;
    }
    
    DiagnosisTreeNode* currentTest = diagnosisEngine->getCurrentRecommendedTest();
    
    if (!currentTest) {
        // 检查是否已完成诊断
        if (diagnosisEngine->isFaultIsolated()) {
            showDiagnosisResult();
        } else {
            QMessageBox::warning(this, "错误", "诊断流程异常：无推荐测试且未完成故障定位");
            SetStackIndex(0);
        }
        return;
    }
    
    // 获取测试信息
    QString testDesc = currentTest->testDescription();
    QString expectedResult = currentTest->expectedResult();
    QString passButtonText = currentTest->passButtonText();
    QString failButtonText = currentTest->failButtonText();
    
    // 默认值
    if (passButtonText.isEmpty()) passButtonText = "是";
    if (failButtonText.isEmpty()) failButtonText = "否";
    
    // 更新标题
    if (ui->label_test_procedure) {
        QString title = QString("步骤 %1: %2")
            .arg(diagnosisEngine->getDiagnosisPath().size() + 1)
            .arg(testDesc.isEmpty() ? "执行测试" : testDesc);
        ui->label_test_procedure->setText(title);
    }
    
    // 更新详细描述
    if (ui->textEdit_TestDesc) {
        QString detailedInfo;
        detailedInfo += "【测试步骤】\n";
        detailedInfo += testDesc.isEmpty() ? "无描述" : testDesc;
        detailedInfo += "\n\n【预期结果】\n";
        detailedInfo += expectedResult.isEmpty() ? "无预期结果" : expectedResult;
        
        // 添加提示信息
        if (currentTest->skipCount() > 0) {
            detailedInfo += QString("\n\n【提示】此测试已被跳过 %1 次")
                .arg(currentTest->skipCount());
        }
        
        ui->textEdit_TestDesc->setPlainText(detailedInfo);
    }
    
    // 更新诊断路径（带详细信息）
    if (ui->label_test_road) {
        QList<DiagnosisStep> path = diagnosisEngine->getDiagnosisPath();
        QString pathText = "诊断路径:\n";
        
        for (int i = 0; i < path.size(); ++i) {
            QString outcomeStr = (path[i].outcome == TestOutcome::Pass) ? "✓通过" : 
                                (path[i].outcome == TestOutcome::Fail) ? "✗失败" : "跳过";
            QString testName = path[i].testNode->testDescription();
            if (testName.length() > 15) {
                testName = testName.left(12) + "...";
            }
            pathText += QString("%1. %2 [%3]\n")
                .arg(i + 1)
                .arg(testName)
                .arg(outcomeStr);
        }
        
        if (path.isEmpty()) {
            pathText += "  (起始状态)";
        }
        
        ui->label_test_road->setText(pathText);
    }
    
    // 动态更新按钮
    if (ui->btn_TestPass) {
        ui->btn_TestPass->setText(passButtonText);
        ui->btn_TestPass->setVisible(true);
        ui->btn_TestPass->setEnabled(true);
    }
    
    if (ui->btn_TestFail) {
        ui->btn_TestFail->setText(failButtonText);
        ui->btn_TestFail->setVisible(true);
        ui->btn_TestFail->setEnabled(true);
    }
    
    // 上一步按钮状态
    if (ui->BtnLastStep) {
        ui->BtnLastStep->setEnabled(diagnosisEngine->canStepBack());
    }
    
    qDebug() << "显示测试: node_id=" << currentTest->nodeId() 
             << ", 按钮=[" << passButtonText << "/" << failButtonText << "]";
}
```

## 实施步骤

### 立即执行（已完成）
1. ✅ 修复数据库root_node_id
2. ✅ 添加缺失的数据库字段
3. ✅ 修复Branch节点处理逻辑

### 短期优化（建议实施）
1. 实现resolveToExecutableNode递归方法
2. 增强stepBack支持从Completed状态恢复
3. 优化UI显示（路径、步骤编号、跳过提示）
4. 改进错误消息文案

### 中期优化
1. 添加跳过原因输入
2. 实现会话持久化（保存/恢复诊断历史）
3. 添加诊断报告生成功能
4. 实现决策树可视化编辑器

## 测试验证清单

- [ ] 树1（液压泵站启动）完整诊断流程
- [ ] 树2（压力控制）完整诊断流程  
- [ ] 树3（液压油质量监测）完整诊断流程
- [ ] 上一步功能（各种场景）
- [ ] 跳过测试功能
- [ ] 手动选择测试功能
- [ ] 故障隔离后回退功能
- [ ] 多分支节点嵌套场景
- [ ] 错误处理和边界情况
