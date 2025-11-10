#ifndef DIAGNOSISTREENODE_H
#define DIAGNOSISTREENODE_H

#include <QString>
#include <QList>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QDebug>

/**
 * @brief 诊断树节点类型枚举
 */
enum class DiagnosisNodeType {
    Test,      // 测试节点：推荐执行的测试
    Fault,     // 故障节点：叶子节点，表示故障结论
    Branch     // 分支节点：用于组织树结构
};

/**
 * @brief 测试结果枚举
 */
enum class TestOutcome {
    Unknown,   // 未知/未测试
    Pass,      // 测试通过
    Fail,      // 测试失败
    Skip       // 跳过测试
};

/**
 * @brief 诊断树节点数据对象类
 * 
 * 对应数据库表 diagnosis_tree_node
 */
class DiagnosisTreeNode
{
public:
    DiagnosisTreeNode();
    ~DiagnosisTreeNode();

    // ===== 基本属性访问 =====
    int nodeId() const { return m_nodeId; }
    void setNodeId(int id) { m_nodeId = id; }

    int treeId() const { return m_treeId; }
    void setTreeId(int id) { m_treeId = id; }

    int parentNodeId() const { return m_parentNodeId; }
    void setParentNodeId(int id) { m_parentNodeId = id; }

    int testId() const { return m_testId; }
    void setTestId(int id) { m_testId = id; }

    int stateId() const { return m_stateId; }
    void setStateId(int id) { m_stateId = id; }

    DiagnosisNodeType nodeType() const { return m_nodeType; }
    void setNodeType(DiagnosisNodeType type) { m_nodeType = type; }

    TestOutcome outcome() const { return m_outcome; }
    void setOutcome(TestOutcome outcome) { m_outcome = outcome; }

    QString comment() const { return m_comment; }
    void setComment(const QString &comment) { m_comment = comment; }

    QString testDescription() const { return m_testDescription; }
    void setTestDescription(const QString &desc) { m_testDescription = desc; }

    QString expectedResult() const { return m_expectedResult; }
    void setExpectedResult(const QString &result) { m_expectedResult = result; }

    QString faultHypothesis() const { return m_faultHypothesis; }
    void setFaultHypothesis(const QString &hypothesis) { m_faultHypothesis = hypothesis; }

    int isolationLevel() const { return m_isolationLevel; }
    void setIsolationLevel(int level) { m_isolationLevel = level; }

    double testPriority() const { return m_testPriority; }
    void setTestPriority(double priority) { m_testPriority = priority; }

    QString passButtonText() const { return m_passButtonText; }
    void setPassButtonText(const QString &text) { m_passButtonText = text; }

    QString failButtonText() const { return m_failButtonText; }
    void setFailButtonText(const QString &text) { m_failButtonText = text; }

    int skipCount() const { return m_skipCount; }
    void setSkipCount(int count) { m_skipCount = count; }

    QString skipReason() const { return m_skipReason; }
    void setSkipReason(const QString &reason) { m_skipReason = reason; }

    QString alternativeTests() const { return m_alternativeTests; }
    void setAlternativeTests(const QString &tests) { m_alternativeTests = tests; }

    double costEstimate() const { return m_costEstimate; }
    void setCostEstimate(double cost) { m_costEstimate = cost; }

    double durationEstimate() const { return m_durationEstimate; }
    void setDurationEstimate(double duration) { m_durationEstimate = duration; }

    QString detectableFaults() const { return m_detectableFaults; }
    void setDetectableFaults(const QString &faults) { m_detectableFaults = faults; }

    QString isolatableFaults() const { return m_isolatableFaults; }
    void setIsolatableFaults(const QString &faults) { m_isolatableFaults = faults; }

    // ===== 树形结构管理 =====
    DiagnosisTreeNode* parent() const { return m_parent; }
    void setParent(DiagnosisTreeNode* parent) { m_parent = parent; }

    QList<DiagnosisTreeNode*> children() const { return m_children; }
    void addChild(DiagnosisTreeNode* child);
    void removeChild(DiagnosisTreeNode* child);
    void clearChildren();

    DiagnosisTreeNode* findChildByOutcome(TestOutcome outcome) const;
    bool hasChildren() const { return !m_children.isEmpty(); }
    bool isLeaf() const { return m_children.isEmpty(); }
    bool isRoot() const { return m_parentNodeId == 0; }

    // ===== 数据库操作 =====
    /**
     * @brief 从数据库加载节点数据
     * @param db 数据库连接
     * @param nodeId 节点ID
     * @return 成功返回true
     */
    bool loadFromDatabase(QSqlDatabase &db, int nodeId);

    /**
     * @brief 保存节点数据到数据库
     * @param db 数据库连接
     * @return 成功返回true，失败返回false
     */
    bool saveToDatabase(QSqlDatabase &db);

    /**
     * @brief 更新节点数据到数据库
     * @param db 数据库连接
     * @return 成功返回true
     */
    bool updateToDatabase(QSqlDatabase &db);

    /**
     * @brief 从数据库删除节点
     * @param db 数据库连接
     * @return 成功返回true
     */
    bool deleteFromDatabase(QSqlDatabase &db);

    // ===== 辅助方法 =====
    /**
     * @brief 获取节点类型的字符串表示
     */
    QString nodeTypeString() const;

    /**
     * @brief 获取测试结果的字符串表示
     */
    QString outcomeString() const;

    /**
     * @brief 从字符串解析节点类型
     */
    static DiagnosisNodeType parseNodeType(const QString &str);

    /**
     * @brief 从字符串解析测试结果
     */
    static TestOutcome parseOutcome(const QString &str);

    /**
     * @brief 判断是否为测试节点
     */
    bool isTestNode() const { return m_nodeType == DiagnosisNodeType::Test; }

    /**
     * @brief 判断是否为故障节点
     */
    bool isFaultNode() const { return m_nodeType == DiagnosisNodeType::Fault; }

    /**
     * @brief 判断是否为分支节点
     */
    bool isBranchNode() const { return m_nodeType == DiagnosisNodeType::Branch; }

    /**
     * @brief 获取节点深度（从根节点开始）
     */
    int depth() const;

    /**
     * @brief 打印节点信息（用于调试）
     */
    void debugPrint(int indent = 0) const;

private:
    // 数据库字段
    int m_nodeId;
    int m_treeId;
    int m_parentNodeId;
    int m_testId;
    int m_stateId;
    DiagnosisNodeType m_nodeType;
    TestOutcome m_outcome;
    QString m_comment;
    QString m_testDescription;
    QString m_expectedResult;
    QString m_faultHypothesis;
    int m_isolationLevel;
    double m_testPriority;
    QString m_passButtonText;
    QString m_failButtonText;
    int m_skipCount;
    QString m_skipReason;
    QString m_alternativeTests;
    double m_costEstimate;
    double m_durationEstimate;
    QString m_detectableFaults;
    QString m_isolatableFaults;

    // 树形结构
    DiagnosisTreeNode* m_parent;
    QList<DiagnosisTreeNode*> m_children;
};

#endif // DIAGNOSISTREENODE_H
