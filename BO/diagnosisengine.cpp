#include "diagnosisengine.h"

DiagnosisEngine::DiagnosisEngine(QSqlDatabase &db, QObject *parent)
    : QObject(parent)
    , m_database(db)
    , m_currentTree(nullptr)
    , m_currentNode(nullptr)
    , m_sessionState(DiagnosisSessionState::NotStarted)
    , m_functionId(0)
{
}

DiagnosisEngine::~DiagnosisEngine()
{
    cleanupSession();
}

bool DiagnosisEngine::startDiagnosisSession(int treeId)
{
    // 重置旧会话
    if (hasActiveSession()) {
        resetSession();
    }

    m_sessionStartTime = QDateTime::currentDateTime();

    // 加载诊断树（使用 tree_id 而不是 function_id）
    if (!loadDiagnosisTreeById(treeId)) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("无法加载诊断树");
        return false;
    }
    
    // 从树中获取 function_id
    m_functionId = m_currentTree->functionId();

    // 验证树结构
    if (!m_currentTree->validateTree()) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("诊断树结构无效");
        return false;
    }

    // 定位到根节点
    m_currentNode = m_currentTree->rootNode();
    if (!m_currentNode) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("找不到根节点");
        return false;
    }

    // 如果根节点就是测试节点，直接推荐
    // 否则需要找到第一个测试节点
    if (!m_currentNode->isTestNode() && m_currentNode->hasChildren()) {
        // 尝试找到第一个测试节点
        bool foundTest = false;
        for (DiagnosisTreeNode* child : m_currentNode->children()) {
            if (child->isTestNode()) {
                m_currentNode = child;
                foundTest = true;
                break;
            }
        }
        
        if (!foundTest) {
            updateSessionState(DiagnosisSessionState::Failed);
            emit diagnosisFailed("找不到可用的测试节点");
            return false;
        }
    }

    updateSessionState(DiagnosisSessionState::InProgress);
    
    qDebug() << "Diagnosis session started. Tree ID:" << treeId << ", Function ID:" << m_functionId;
    qDebug() << "Initial test node:" << m_currentNode->testDescription();
    
    return true;
}

void DiagnosisEngine::resetSession()
{
    cleanupSession();
    updateSessionState(DiagnosisSessionState::NotStarted);
}

void DiagnosisEngine::cancelSession()
{
    cleanupSession();
    updateSessionState(DiagnosisSessionState::Cancelled);
}

void DiagnosisEngine::cleanupSession()
{
    if (m_currentTree) {
        delete m_currentTree;
        m_currentTree = nullptr;
    }
    m_currentNode = nullptr;
    m_diagnosisPath.clear();
    m_functionId = 0;
}

DiagnosisTreeNode* DiagnosisEngine::getCurrentRecommendedTest()
{
    if (!hasActiveSession()) {
        return nullptr;
    }

    if (m_currentNode && m_currentNode->isTestNode()) {
        return m_currentNode;
    }

    return nullptr;
}

QString DiagnosisEngine::getCurrentTestDescription() const
{
    if (m_currentNode && m_currentNode->isTestNode()) {
        return m_currentNode->testDescription();
    }
    return QString();
}

QString DiagnosisEngine::getCurrentExpectedResult() const
{
    if (m_currentNode && m_currentNode->isTestNode()) {
        return m_currentNode->expectedResult();
    }
    return QString();
}

bool DiagnosisEngine::recordTestResult(TestOutcome outcome, const QString &userComment)
{
    if (!hasActiveSession()) {
        qDebug() << "No active diagnosis session";
        return false;
    }

    if (!m_currentNode) {
        qDebug() << "No current node";
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
             << "Outcome:" << m_currentNode->outcomeString();

    // 查找下一个节点
    DiagnosisTreeNode* nextNode = findNextNode(m_currentNode, outcome);
    
    if (!nextNode) {
        // 没有下一个节点，诊断失败
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("无法继续诊断，没有匹配的下一步");
        return false;
    }

    m_currentNode = nextNode;

    // 检查是否到达故障节点
    if (m_currentNode->isFaultNode()) {
        updateSessionState(DiagnosisSessionState::Completed);
        m_sessionEndTime = QDateTime::currentDateTime();
        emit faultIsolated(m_currentNode);
        qDebug() << "Fault isolated:" << m_currentNode->faultHypothesis();
        return true;
    }

    // 如果到达Branch节点，需要继续查找下一个Test节点
    // 可能需要递归穿过多层Branch节点
    int branchDepth = 0;
    const int maxBranchDepth = 10; // 防止无限循环
    
    while (m_currentNode->isBranchNode() && branchDepth < maxBranchDepth) {
        qDebug() << "Reached branch node" << m_currentNode->nodeId() << ", looking for next test (depth:" << branchDepth << ")";
        
        bool foundNext = false;
        
        // 查找子节点中的Test或Branch节点
        if (m_currentNode->hasChildren()) {
            // 优先查找Test节点
            for (DiagnosisTreeNode* child : m_currentNode->children()) {
                if (child->isTestNode()) {
                    m_currentNode = child;
                    qDebug() << "Found test node in branch:" << m_currentNode->nodeId();
                    foundNext = true;
                    break;
                }
            }
            
            // 如果没有Test节点，继续进入下一个Branch节点
            if (!foundNext) {
                for (DiagnosisTreeNode* child : m_currentNode->children()) {
                    if (child->isBranchNode()) {
                        m_currentNode = child;
                        qDebug() << "Entering nested branch node:" << m_currentNode->nodeId();
                        foundNext = true;
                        branchDepth++;
                        break;
                    }
                }
            }
        }
        
        // 如果既没有Test也没有Branch，检查是否有Fault节点
        if (!foundNext && m_currentNode->hasChildren()) {
            for (DiagnosisTreeNode* child : m_currentNode->children()) {
                if (child->isFaultNode()) {
                    m_currentNode = child;
                    qDebug() << "Branch leads directly to fault node:" << m_currentNode->nodeId();
                    foundNext = true;
                    break;
                }
            }
        }
        
        if (!foundNext) {
            updateSessionState(DiagnosisSessionState::Failed);
            emit diagnosisFailed("Branch节点下没有可用的测试节点、分支节点或故障节点");
            return false;
        }
        
        // 如果找到了非Branch节点，退出循环
        if (!m_currentNode->isBranchNode()) {
            break;
        }
    }
    
    if (branchDepth >= maxBranchDepth) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("Branch节点嵌套层数过深，可能存在循环");
        return false;
    }

    // 最终检查：必须是测试节点
    if (!m_currentNode->isTestNode()) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("到达非测试节点且非故障节点");
        return false;
    }

    // 推荐新测试
    emit testRecommended(m_currentNode);
    return true;
}

bool DiagnosisEngine::skipCurrentTest()
{
    return recordTestResult(TestOutcome::Skip);
}

bool DiagnosisEngine::isFaultIsolated() const
{
    return m_sessionState == DiagnosisSessionState::Completed &&
           m_currentNode &&
           m_currentNode->isFaultNode();
}

DiagnosisTreeNode* DiagnosisEngine::getFaultConclusion() const
{
    if (isFaultIsolated()) {
        return m_currentNode;
    }
    return nullptr;
}

QString DiagnosisEngine::getFaultDescription() const
{
    DiagnosisTreeNode* faultNode = getFaultConclusion();
    if (faultNode) {
        return faultNode->faultHypothesis();
    }
    return QString();
}

int DiagnosisEngine::getIsolationLevel() const
{
    DiagnosisTreeNode* faultNode = getFaultConclusion();
    if (faultNode) {
        return faultNode->isolationLevel();
    }
    return 0;
}

QStringList DiagnosisEngine::getCandidateFaults() const
{
    QStringList candidates;
    
    if (!m_currentTree || !m_currentNode) {
        return candidates;
    }
    
    // 如果当前节点是测试节点，获取其可隔离故障列表
    if (m_currentNode->isTestNode()) {
        QString isolatable = m_currentNode->isolatableFaults();
        if (!isolatable.isEmpty()) {
            // 假设故障用逗号或分号分隔
            QStringList faults = isolatable.split(QRegExp("[,;]"), QString::SkipEmptyParts);
            for (QString &fault : faults) {
                fault = fault.trimmed();
                if (!fault.isEmpty() && !candidates.contains(fault)) {
                    candidates.append(fault);
                }
            }
        }
        
        // 如果 isolatableFaults 为空，尝试从子节点收集故障假设
        if (candidates.isEmpty() && m_currentNode->hasChildren()) {
            collectFaultsFromSubtree(m_currentNode, candidates);
        }
    } else if (m_currentNode->isFaultNode()) {
        // 如果当前节点已经是故障节点，只返回这一个故障
        QString fault = m_currentNode->faultHypothesis();
        if (!fault.isEmpty()) {
            candidates.append(fault);
        }
    } else {
        // 从当前节点的子树中收集所有可能的故障
        collectFaultsFromSubtree(m_currentNode, candidates);
    }
    
    return candidates;
}

void DiagnosisEngine::collectFaultsFromSubtree(DiagnosisTreeNode* node, QStringList &faults) const
{
    if (!node) return;
    
    // 如果是故障节点，添加故障假设
    if (node->isFaultNode()) {
        QString fault = node->faultHypothesis();
        if (!fault.isEmpty() && !faults.contains(fault)) {
            faults.append(fault);
        }
    }
    
    // 递归处理子节点
    if (node->hasChildren()) {
        for (DiagnosisTreeNode* child : node->children()) {
            collectFaultsFromSubtree(child, faults);
        }
    }
}

QString DiagnosisEngine::getPathSummary() const
{
    QString summary;
    for (int i = 0; i < m_diagnosisPath.size(); ++i) {
        const DiagnosisStep &step = m_diagnosisPath[i];
        summary += QString("步骤%1: %2 - 结果: %3\n")
                   .arg(step.stepNumber)
                   .arg(step.testNode->testDescription())
                   .arg(step.testNode->outcomeString());
    }
    return summary;
}

int DiagnosisEngine::getExecutedTestCount() const
{
    int count = 0;
    for (const DiagnosisStep &step : m_diagnosisPath) {
        if (step.outcome == TestOutcome::Pass || step.outcome == TestOutcome::Fail) {
            count++;
        }
    }
    return count;
}

int DiagnosisEngine::getSkippedTestCount() const
{
    int count = 0;
    for (const DiagnosisStep &step : m_diagnosisPath) {
        if (step.outcome == TestOutcome::Skip) {
            count++;
        }
    }
    return count;
}

int DiagnosisEngine::getSessionDuration() const
{
    if (m_sessionState == DiagnosisSessionState::NotStarted) {
        return 0;
    }

    QDateTime endTime = m_sessionState == DiagnosisSessionState::Completed
                       ? m_sessionEndTime
                       : QDateTime::currentDateTime();

    return m_sessionStartTime.secsTo(endTime);
}

void DiagnosisEngine::debugPrintSession() const
{
    qDebug() << "=== Diagnosis Session ===";
    qDebug() << "Function ID:" << m_functionId;
    qDebug() << "State:" << static_cast<int>(m_sessionState);
    qDebug() << "Steps executed:" << m_diagnosisPath.size();
    qDebug() << "Current node:" << (m_currentNode ? m_currentNode->nodeId() : 0);
    
    if (isFaultIsolated()) {
        qDebug() << "Fault isolated:" << getFaultDescription();
    }
    
    qDebug() << "\nDiagnosis path:";
    qDebug().noquote() << getPathSummary();
}

bool DiagnosisEngine::loadDiagnosisTreeById(int treeId)
{
    m_currentTree = new DiagnosisTree();
    
    // 根据树ID加载诊断树
    if (!m_currentTree->loadFromDatabase(m_database, treeId)) {
        qDebug() << "Failed to load diagnosis tree with tree_id" << treeId;
        delete m_currentTree;
        m_currentTree = nullptr;
        return false;
    }

    // 加载完整树结构
    if (!m_currentTree->loadFullTree(m_database)) {
        qDebug() << "Failed to load full tree structure";
        delete m_currentTree;
        m_currentTree = nullptr;
        return false;
    }

    qDebug() << "Diagnosis tree loaded successfully";
    qDebug() << "Tree ID:" << m_currentTree->treeId();
    qDebug() << "Function ID:" << m_currentTree->functionId();
    qDebug() << "Total nodes:" << m_currentTree->countNodes();
    
    return true;
}

bool DiagnosisEngine::loadDiagnosisTree(int functionId)
{
    m_currentTree = new DiagnosisTree();
    
    // 根据功能ID加载诊断树
    if (!m_currentTree->loadByFunctionId(m_database, functionId)) {
        qDebug() << "Failed to load diagnosis tree for function" << functionId;
        delete m_currentTree;
        m_currentTree = nullptr;
        return false;
    }

    // 加载完整树结构
    if (!m_currentTree->loadFullTree(m_database)) {
        qDebug() << "Failed to load full tree structure";
        delete m_currentTree;
        m_currentTree = nullptr;
        return false;
    }

    qDebug() << "Diagnosis tree loaded successfully";
    qDebug() << "Tree ID:" << m_currentTree->treeId();
    qDebug() << "Total nodes:" << m_currentTree->countNodes();
    
    return true;
}

DiagnosisTreeNode* DiagnosisEngine::findNextNode(DiagnosisTreeNode* currentNode, TestOutcome outcome)
{
    if (!currentNode) {
        qDebug() << "findNextNode: currentNode is null";
        return nullptr;
    }

    QString outcomeStr = (outcome == TestOutcome::Pass) ? "Pass" : 
                         (outcome == TestOutcome::Fail) ? "Fail" : "Skip";
    
    qDebug() << "findNextNode: Current node" << currentNode->nodeId() 
             << ", looking for outcome:" << outcomeStr
             << ", has" << currentNode->children().size() << "children";

    // 首先尝试根据outcome精确匹配子节点
    DiagnosisTreeNode* nextNode = currentNode->findChildByOutcome(outcome);
    if (nextNode) {
        qDebug() << "Found exact match: node" << nextNode->nodeId() 
                 << "type:" << (nextNode->isTestNode() ? "Test" : 
                               nextNode->isFaultNode() ? "Fault" : "Branch");
        return nextNode;
    }

    qDebug() << "No exact outcome match found";

    // 如果没有精确匹配，尝试查找任意子节点
    // 这适用于分支节点或者outcome不匹配的情况
    if (currentNode->hasChildren()) {
        QList<DiagnosisTreeNode*> children = currentNode->children();
        
        // 输出所有子节点信息
        for (int i = 0; i < children.size(); ++i) {
            DiagnosisTreeNode* child = children[i];
            QString childOutcome = (child->outcome() == TestOutcome::Pass) ? "Pass" : 
                                   (child->outcome() == TestOutcome::Fail) ? "Fail" : 
                                   (child->outcome() == TestOutcome::Skip) ? "Skip" : "Unknown";
            qDebug() << "  Child" << i << ": node_id=" << child->nodeId() 
                     << ", outcome=" << childOutcome 
                     << ", type=" << (child->isTestNode() ? "Test" : 
                                     child->isFaultNode() ? "Fault" : "Branch");
        }
        
        // 优先选择测试节点
        for (DiagnosisTreeNode* child : children) {
            if (child->isTestNode()) {
                qDebug() << "No exact outcome match, using first test child:" << child->nodeId();
                return child;
            }
        }
        
        // 其次选择故障节点
        for (DiagnosisTreeNode* child : children) {
            if (child->isFaultNode()) {
                qDebug() << "No test child, using first fault child";
                return child;
            }
        }
        
        // 最后返回第一个子节点
        qDebug() << "Using first child node";
        return children.first();
    }

    qDebug() << "No next node found";
    return nullptr;
}

void DiagnosisEngine::updateSessionState(DiagnosisSessionState newState)
{
    if (m_sessionState != newState) {
        m_sessionState = newState;
        emit sessionStateChanged(newState);
    }
}

// ===== 新增功能实现 =====

bool DiagnosisEngine::stepBack()
{
    if (!canStepBack()) {
        qDebug() << "Cannot step back: no history";
        return false;
    }

    // 允许从Completed状态回退
    if (m_sessionState != DiagnosisSessionState::InProgress && 
        m_sessionState != DiagnosisSessionState::Completed) {
        qDebug() << "Cannot step back: invalid session state" << static_cast<int>(m_sessionState);
        return false;
    }

    // 获取并移除最后一步
    DiagnosisStep lastStep = m_diagnosisPath.takeLast();
    
    // 如果还有步骤，恢复到前一个节点
    if (!m_diagnosisPath.isEmpty()) {
        DiagnosisStep previousStep = m_diagnosisPath.last();
        m_currentNode = previousStep.testNode;
    } else {
        // 回到根节点
        m_currentNode = m_currentTree->rootNode();
        
        // 如果根节点不是测试节点，找第一个测试节点
        if (!m_currentNode->isTestNode() && m_currentNode->hasChildren()) {
            for (DiagnosisTreeNode* child : m_currentNode->children()) {
                if (child->isTestNode()) {
                    m_currentNode = child;
                    break;
                }
            }
        }
    }
    
    // 确保会话状态正确
    if (m_sessionState == DiagnosisSessionState::Completed) {
        updateSessionState(DiagnosisSessionState::InProgress);
    }
    
    qDebug() << "Stepped back to node:" << (m_currentNode ? m_currentNode->nodeId() : 0);
    
    // 触发测试推荐信号
    if (m_currentNode && m_currentNode->isTestNode()) {
        emit testRecommended(m_currentNode);
    }
    
    return true;
}

bool DiagnosisEngine::skipTestAndRecommendNext()
{
    if (!hasActiveSession()) {
        qDebug() << "Cannot skip test: no active session";
        return false;
    }

    if (!m_currentNode || !m_currentNode->isTestNode()) {
        qDebug() << "Cannot skip: current node is not a test";
        return false;
    }

    // 查找替代测试
    QList<DiagnosisTreeNode*> alternatives = getAlternativeTests();
    
    if (alternatives.isEmpty()) {
        qDebug() << "No alternative tests available, recording as Skip";
        // 没有替代测试，记录为Skip并继续原流程
        return recordTestResult(TestOutcome::Skip);
    }

    // 选择第一个替代测试（可以根据推荐分数排序）
    DiagnosisTreeNode* nextTest = alternatives.first();
    
    // 记录跳过
    DiagnosisStep skipStep;
    skipStep.stepNumber = m_diagnosisPath.size() + 1;
    skipStep.testNode = m_currentNode;
    skipStep.outcome = TestOutcome::Skip;
    skipStep.timestamp = QDateTime::currentDateTime();
    skipStep.userComment = QString("跳过，推荐替代测试：%1").arg(nextTest->testDescription());
    m_diagnosisPath.append(skipStep);
    
    // 更新跳过计数（需要在数据库中更新）
    updateSkipCount(m_currentNode->nodeId());
    
    // 切换到新测试
    m_currentNode = nextTest;
    
    emit testRecommended(m_currentNode);
    
    qDebug() << "Skipped test, recommended alternative:" << nextTest->testDescription();
    
    return true;
}

QList<DiagnosisTreeNode*> DiagnosisEngine::getAlternativeTests()
{
    QList<DiagnosisTreeNode*> alternatives;
    
    if (!hasActiveSession() || !m_currentTree) {
        return alternatives;
    }

    // 查找所有测试节点
    alternatives = findAlternativeTestsInternal();
    
    // 根据推荐分数排序
    std::sort(alternatives.begin(), alternatives.end(), 
        [this](DiagnosisTreeNode* a, DiagnosisTreeNode* b) {
            return calculateRecommendationScore(a) > calculateRecommendationScore(b);
        });
    
    return alternatives;
}

bool DiagnosisEngine::selectManualTest(int nodeId)
{
    if (!hasActiveSession()) {
        qDebug() << "Cannot select manual test: no active session";
        return false;
    }

    if (!m_currentTree) {
        qDebug() << "Cannot select manual test: no tree loaded";
        return false;
    }

    // 查找指定节点
    DiagnosisTreeNode* targetNode = m_currentTree->findNodeById(nodeId);
    
    if (!targetNode) {
        qDebug() << "Cannot find node with ID:" << nodeId;
        return false;
    }

    if (!targetNode->isTestNode()) {
        qDebug() << "Selected node is not a test node";
        return false;
    }

    // 验证转换是否有效
    if (!validateStepTransition(m_currentNode, targetNode)) {
        qDebug() << "Invalid step transition";
        return false;
    }

    // 记录当前测试为跳过
    if (m_currentNode && m_currentNode->isTestNode()) {
        DiagnosisStep skipStep;
        skipStep.stepNumber = m_diagnosisPath.size() + 1;
        skipStep.testNode = m_currentNode;
        skipStep.outcome = TestOutcome::Skip;
        skipStep.timestamp = QDateTime::currentDateTime();
        skipStep.userComment = QString("手动选择测试：%1").arg(targetNode->testDescription());
        m_diagnosisPath.append(skipStep);
        
        updateSkipCount(m_currentNode->nodeId());
    }

    // 切换到新测试
    m_currentNode = targetNode;
    
    emit testRecommended(m_currentNode);
    
    qDebug() << "Manually selected test:" << targetNode->testDescription();
    
    return true;
}

QList<DiagnosisTreeNode*> DiagnosisEngine::findAlternativeTestsInternal()
{
    QList<DiagnosisTreeNode*> alternatives;
    
    if (!m_currentTree) {
        return alternatives;
    }

    // 获取所有测试节点
    QList<DiagnosisTreeNode*> allNodes = m_currentTree->getAllNodes();
    
    for (DiagnosisTreeNode* node : allNodes) {
        if (!node->isTestNode()) {
            continue;
        }
        
        // 排除当前节点
        if (node == m_currentNode) {
            continue;
        }
        
        // 排除已执行的测试
        bool alreadyExecuted = false;
        for (const DiagnosisStep& step : m_diagnosisPath) {
            if (step.testNode == node && step.outcome != TestOutcome::Skip) {
                alreadyExecuted = true;
                break;
            }
        }
        
        if (!alreadyExecuted) {
            alternatives.append(node);
        }
    }
    
    return alternatives;
}

bool DiagnosisEngine::validateStepTransition(DiagnosisTreeNode* from, DiagnosisTreeNode* to)
{
    // 基本验证
    if (!from || !to) {
        return false;
    }

    // 同一棵树
    if (from->treeId() != to->treeId()) {
        return false;
    }

    // 目标必须是测试节点
    if (!to->isTestNode()) {
        return false;
    }

    // 不能跳转到已经执行过的测试
    for (const DiagnosisStep& step : m_diagnosisPath) {
        if (step.testNode == to && step.outcome != TestOutcome::Skip) {
            return false;
        }
    }

    return true;
}

double DiagnosisEngine::calculateRecommendationScore(DiagnosisTreeNode* node)
{
    if (!node || !node->isTestNode()) {
        return 0.0;
    }

    double score = 0.0;
    
    // 基础分数：测试优先级 (0-100)
    score += node->testPriority() * 100.0;
    
    // 成本因素：成本越低分数越高 (0-20)
    double costFactor = 20.0;
    if (node->costEstimate() > 0.0) {
        costFactor = 20.0 / (1.0 + node->costEstimate() / 10.0);
    }
    score += costFactor;
    
    // 时间因素：时间越短分数越高 (0-20)
    double timeFactor = 20.0;
    if (node->durationEstimate() > 0.0) {
        timeFactor = 20.0 / (1.0 + node->durationEstimate() / 5.0);
    }
    score += timeFactor;
    
    // 历史成功率（从数据库查询，暂时使用默认值）(0-10)
    score += 5.0;
    
    // 跳过惩罚：跳过次数越多分数越低
    score -= node->skipCount() * 2.0;
    
    // 确保分数在合理范围内
    if (score < 0.0) score = 0.0;
    if (score > 100.0) score = 100.0;
    
    return score;
}

void DiagnosisEngine::updateSkipCount(int nodeId)
{
    if (!m_database.isOpen()) {
        return;
    }

    QSqlQuery query(m_database);
    query.prepare("UPDATE diagnosis_tree_node SET skip_count = skip_count + 1 WHERE node_id = ?");
    query.addBindValue(nodeId);
    
    if (!query.exec()) {
        qDebug() << "Failed to update skip count:" << query.lastError().text();
    }
}
