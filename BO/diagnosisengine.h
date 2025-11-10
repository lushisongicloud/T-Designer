#ifndef DIAGNOSISENGINE_H
#define DIAGNOSISENGINE_H

#include <QObject>
#include <QString>
#include <QList>
#include <QStack>
#include <QSqlDatabase>
#include <QDateTime>
#include "../DO/diagnosistree.h"
#include "../DO/diagnosistreenode.h"

/**
 * @brief 诊断会话状态枚举
 */
enum class DiagnosisSessionState {
    NotStarted,     // 未开始
    InProgress,     // 进行中
    Completed,      // 已完成（找到故障）
    Failed,         // 失败（无法继续）
    Cancelled       // 已取消
};

/**
 * @brief 诊断步骤记录
 */
struct DiagnosisStep {
    int stepNumber;                // 步骤编号
    DiagnosisTreeNode* testNode;   // 测试节点
    TestOutcome outcome;            // 测试结果
    QDateTime timestamp;            // 时间戳
    QString userComment;            // 用户备注
};

/**
 * @brief 诊断引擎类
 * 
 * 负责管理诊断会话，推荐测试，记录诊断路径，定位故障
 */
class DiagnosisEngine : public QObject
{
    Q_OBJECT

public:
    explicit DiagnosisEngine(QSqlDatabase &db, QObject *parent = nullptr);
    ~DiagnosisEngine();

    // ===== 会话管理 =====
    /**
     * @brief 开始新的诊断会话
     * @param treeId 要使用的诊断树ID
     * @return 成功返回true
     */
    bool startDiagnosisSession(int treeId);

    /**
     * @brief 重置诊断会话
     */
    void resetSession();

    /**
     * @brief 取消当前诊断会话
     */
    void cancelSession();

    /**
     * @brief 获取当前会话状态
     */
    DiagnosisSessionState sessionState() const { return m_sessionState; }

    /**
     * @brief 检查是否有活动会话
     */
    bool hasActiveSession() const {
        return m_sessionState == DiagnosisSessionState::InProgress;
    }

    // ===== 测试推荐 =====
    /**
     * @brief 获取当前推荐的测试
     * @return 推荐的测试节点，如果没有返回nullptr
     */
    DiagnosisTreeNode* getCurrentRecommendedTest();

    /**
     * @brief 获取当前测试的描述信息
     */
    QString getCurrentTestDescription() const;

    /**
     * @brief 获取当前测试的期望结果
     */
    QString getCurrentExpectedResult() const;

    /**
     * @brief 记录测试结果并移动到下一个节点
     * @param outcome 测试结果
     * @param userComment 用户备注（可选）
     * @return 成功返回true
     */
    bool recordTestResult(TestOutcome outcome, const QString &userComment = QString());

    /**
     * @brief 跳过当前测试
     * @return 成功返回true
     */
    bool skipCurrentTest();

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
     * @brief 检查是否可以回退
     */
    bool canStepBack() const { return m_diagnosisPath.size() > 0; }

    // ===== 诊断结果 =====
    /**
     * @brief 检查是否已隔离故障
     */
    bool isFaultIsolated() const;

    /**
     * @brief 获取故障结论
     * @return 如果已隔离故障，返回故障节点，否则返回nullptr
     */
    DiagnosisTreeNode* getFaultConclusion() const;

    /**
     * @brief 获取故障描述
     */
    QString getFaultDescription() const;

    /**
     * @brief 获取隔离级别
     */
    int getIsolationLevel() const;

    // ===== 诊断路径 =====
    /**
     * @brief 获取完整诊断路径
     */
    QList<DiagnosisStep> getDiagnosisPath() const { return m_diagnosisPath; }

    /**
     * @brief 获取当前步骤编号
     */
    int getCurrentStepNumber() const { return m_diagnosisPath.size(); }

    /**
     * @brief 获取诊断路径摘要
     * @return 格式化的路径字符串
     */
    QString getPathSummary() const;

    // ===== 统计信息 =====
    /**
     * @brief 获取已执行的测试数量
     */
    int getExecutedTestCount() const;

    /**
     * @brief 获取跳过的测试数量
     */
    int getSkippedTestCount() const;

    /**
     * @brief 获取会话开始时间
     */
    QDateTime getSessionStartTime() const { return m_sessionStartTime; }

    /**
     * @brief 获取会话持续时间（秒）
     */
    int getSessionDuration() const;

    // ===== 辅助方法 =====
    /**
     * @brief 获取当前加载的诊断树
     */
    DiagnosisTree* currentTree() const { return m_currentTree; }

    /**
     * @brief 获取当前节点
     */
    DiagnosisTreeNode* currentNode() const { return m_currentNode; }

    /**
     * @brief 获取功能ID
     */
    int functionId() const { return m_functionId; }

    /**
     * @brief 打印诊断会话信息（用于调试）
     */
    void debugPrintSession() const;

signals:
    /**
     * @brief 会话状态改变信号
     */
    void sessionStateChanged(DiagnosisSessionState newState);

    /**
     * @brief 推荐新测试信号
     */
    void testRecommended(DiagnosisTreeNode* testNode);

    /**
     * @brief 测试结果已记录信号
     */
    void testResultRecorded(const DiagnosisStep &step);

    /**
     * @brief 故障已隔离信号
     */
    void faultIsolated(DiagnosisTreeNode* faultNode);

    /**
     * @brief 诊断失败信号
     */
    void diagnosisFailed(const QString &reason);

private:
    /**
     * @brief 根据树ID加载诊断树
     */
    bool loadDiagnosisTreeById(int treeId);
    
    /**
     * @brief 根据功能ID加载诊断树
     */
    bool loadDiagnosisTree(int functionId);

    /**
     * @brief 查找下一个推荐的测试节点
     * @param currentNode 当前节点
     * @param outcome 测试结果
     * @return 下一个节点，如果没有返回nullptr
     */
    DiagnosisTreeNode* findNextNode(DiagnosisTreeNode* currentNode, TestOutcome outcome);

    /**
     * @brief 更新会话状态
     */
    void updateSessionState(DiagnosisSessionState newState);

    /**
     * @brief 清理会话数据
     */
    void cleanupSession();

    /**
     * @brief 查找替代测试节点（内部方法）
     */
    QList<DiagnosisTreeNode*> findAlternativeTestsInternal();
    
    /**
     * @brief 验证步骤转换是否有效
     */
    bool validateStepTransition(DiagnosisTreeNode* from, DiagnosisTreeNode* to);
    
    /**
     * @brief 计算推荐分数（用于测试推荐）
     */
    double calculateRecommendationScore(DiagnosisTreeNode* node);
    
    /**
     * @brief 更新节点跳过计数
     */
    void updateSkipCount(int nodeId);

    // 数据成员
    QSqlDatabase &m_database;
    DiagnosisTree* m_currentTree;
    DiagnosisTreeNode* m_currentNode;
    DiagnosisSessionState m_sessionState;
    int m_functionId;
    QList<DiagnosisStep> m_diagnosisPath;
    QDateTime m_sessionStartTime;
    QDateTime m_sessionEndTime;
    QStack<DiagnosisStep> m_stepStack;  // 用于回退的步骤栈
    int m_currentSessionId;  // 当前会话ID（用于持久化）
};

#endif // DIAGNOSISENGINE_H
