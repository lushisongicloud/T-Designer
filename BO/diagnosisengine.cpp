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

bool DiagnosisEngine::startDiagnosisSession(int functionId)
{
    // 重置旧会话
    if (hasActiveSession()) {
        resetSession();
    }

    m_functionId = functionId;
    m_sessionStartTime = QDateTime::currentDateTime();

    // 加载诊断树
    if (!loadDiagnosisTree(functionId)) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("无法加载诊断树");
        return false;
    }

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
    
    qDebug() << "Diagnosis session started for function" << functionId;
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

    // 检查是否还有测试
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
    if (!currentNode) return nullptr;

    // 首先尝试根据outcome精确匹配子节点
    DiagnosisTreeNode* nextNode = currentNode->findChildByOutcome(outcome);
    if (nextNode) {
        return nextNode;
    }

    // 如果没有精确匹配，尝试查找任意子节点
    // 这适用于分支节点或者outcome不匹配的情况
    if (currentNode->hasChildren()) {
        QList<DiagnosisTreeNode*> children = currentNode->children();
        
        // 优先选择测试节点
        for (DiagnosisTreeNode* child : children) {
            if (child->isTestNode()) {
                qDebug() << "No exact outcome match, using first test child";
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
