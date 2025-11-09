#include "diagnosistreenode.h"

DiagnosisTreeNode::DiagnosisTreeNode()
    : m_nodeId(0)
    , m_treeId(0)
    , m_parentNodeId(0)
    , m_testId(0)
    , m_stateId(0)
    , m_nodeType(DiagnosisNodeType::Test)
    , m_outcome(TestOutcome::Unknown)
    , m_isolationLevel(0)
    , m_testPriority(0.5)
    , m_parent(nullptr)
{
}

DiagnosisTreeNode::~DiagnosisTreeNode()
{
    clearChildren();
}

void DiagnosisTreeNode::addChild(DiagnosisTreeNode* child)
{
    if (child && !m_children.contains(child)) {
        m_children.append(child);
        child->setParent(this);
    }
}

void DiagnosisTreeNode::removeChild(DiagnosisTreeNode* child)
{
    if (child) {
        m_children.removeOne(child);
        child->setParent(nullptr);
    }
}

void DiagnosisTreeNode::clearChildren()
{
    for (DiagnosisTreeNode* child : m_children) {
        delete child;
    }
    m_children.clear();
}

DiagnosisTreeNode* DiagnosisTreeNode::findChildByOutcome(TestOutcome outcome) const
{
    for (DiagnosisTreeNode* child : m_children) {
        if (child->outcome() == outcome) {
            return child;
        }
    }
    return nullptr;
}

bool DiagnosisTreeNode::loadFromDatabase(QSqlDatabase &db, int nodeId)
{
    QSqlQuery query(db);
    query.prepare("SELECT * FROM diagnosis_tree_node WHERE node_id = ?");
    query.addBindValue(nodeId);

    if (!query.exec()) {
        qDebug() << "Failed to load diagnosis tree node:" << query.lastError().text();
        return false;
    }

    if (!query.next()) {
        qDebug() << "Diagnosis tree node not found:" << nodeId;
        return false;
    }

    // 加载基本字段
    m_nodeId = query.value("node_id").toInt();
    m_treeId = query.value("tree_id").toInt();
    m_parentNodeId = query.value("parent_node_id").toInt();
    m_testId = query.value("test_id").toInt();
    m_stateId = query.value("state_id").toInt();
    m_comment = query.value("comment").toString();

    // 加载扩展字段
    QString nodeTypeStr = query.value("node_type").toString();
    m_nodeType = parseNodeType(nodeTypeStr);

    QString outcomeStr = query.value("outcome").toString();
    m_outcome = parseOutcome(outcomeStr);

    m_testDescription = query.value("test_description").toString();
    m_expectedResult = query.value("expected_result").toString();
    m_faultHypothesis = query.value("fault_hypothesis").toString();
    m_isolationLevel = query.value("isolation_level").toInt();
    m_testPriority = query.value("test_priority").toDouble();

    return true;
}

bool DiagnosisTreeNode::saveToDatabase(QSqlDatabase &db)
{
    QSqlQuery query(db);
    query.prepare(
        "INSERT INTO diagnosis_tree_node "
        "(tree_id, parent_node_id, test_id, state_id, node_type, outcome, comment, "
        " test_description, expected_result, fault_hypothesis, isolation_level, test_priority) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    );

    query.addBindValue(m_treeId);
    query.addBindValue(m_parentNodeId > 0 ? m_parentNodeId : QVariant());
    query.addBindValue(m_testId > 0 ? m_testId : QVariant());
    query.addBindValue(m_stateId > 0 ? m_stateId : QVariant());
    query.addBindValue(nodeTypeString());
    query.addBindValue(outcomeString());
    query.addBindValue(m_comment);
    query.addBindValue(m_testDescription);
    query.addBindValue(m_expectedResult);
    query.addBindValue(m_faultHypothesis);
    query.addBindValue(m_isolationLevel);
    query.addBindValue(m_testPriority);

    if (!query.exec()) {
        qDebug() << "Failed to save diagnosis tree node:" << query.lastError().text();
        return false;
    }

    m_nodeId = query.lastInsertId().toInt();
    return true;
}

bool DiagnosisTreeNode::updateToDatabase(QSqlDatabase &db)
{
    if (m_nodeId == 0) {
        qDebug() << "Cannot update node without valid ID";
        return false;
    }

    QSqlQuery query(db);
    query.prepare(
        "UPDATE diagnosis_tree_node SET "
        "tree_id = ?, parent_node_id = ?, test_id = ?, state_id = ?, "
        "node_type = ?, outcome = ?, comment = ?, "
        "test_description = ?, expected_result = ?, fault_hypothesis = ?, "
        "isolation_level = ?, test_priority = ? "
        "WHERE node_id = ?"
    );

    query.addBindValue(m_treeId);
    query.addBindValue(m_parentNodeId > 0 ? m_parentNodeId : QVariant());
    query.addBindValue(m_testId > 0 ? m_testId : QVariant());
    query.addBindValue(m_stateId > 0 ? m_stateId : QVariant());
    query.addBindValue(nodeTypeString());
    query.addBindValue(outcomeString());
    query.addBindValue(m_comment);
    query.addBindValue(m_testDescription);
    query.addBindValue(m_expectedResult);
    query.addBindValue(m_faultHypothesis);
    query.addBindValue(m_isolationLevel);
    query.addBindValue(m_testPriority);
    query.addBindValue(m_nodeId);

    if (!query.exec()) {
        qDebug() << "Failed to update diagnosis tree node:" << query.lastError().text();
        return false;
    }

    return true;
}

bool DiagnosisTreeNode::deleteFromDatabase(QSqlDatabase &db)
{
    if (m_nodeId == 0) {
        qDebug() << "Cannot delete node without valid ID";
        return false;
    }

    QSqlQuery query(db);
    query.prepare("DELETE FROM diagnosis_tree_node WHERE node_id = ?");
    query.addBindValue(m_nodeId);

    if (!query.exec()) {
        qDebug() << "Failed to delete diagnosis tree node:" << query.lastError().text();
        return false;
    }

    return true;
}

QString DiagnosisTreeNode::nodeTypeString() const
{
    switch (m_nodeType) {
        case DiagnosisNodeType::Test:   return "test";
        case DiagnosisNodeType::Fault:  return "fault";
        case DiagnosisNodeType::Branch: return "branch";
        default: return "test";
    }
}

QString DiagnosisTreeNode::outcomeString() const
{
    switch (m_outcome) {
        case TestOutcome::Pass:    return "pass";
        case TestOutcome::Fail:    return "fail";
        case TestOutcome::Skip:    return "skip";
        case TestOutcome::Unknown: return "";
        default: return "";
    }
}

DiagnosisNodeType DiagnosisTreeNode::parseNodeType(const QString &str)
{
    QString lower = str.toLower();
    if (lower == "test") return DiagnosisNodeType::Test;
    if (lower == "fault") return DiagnosisNodeType::Fault;
    if (lower == "branch") return DiagnosisNodeType::Branch;
    return DiagnosisNodeType::Test; // 默认
}

TestOutcome DiagnosisTreeNode::parseOutcome(const QString &str)
{
    QString lower = str.toLower();
    if (lower == "pass") return TestOutcome::Pass;
    if (lower == "fail") return TestOutcome::Fail;
    if (lower == "skip") return TestOutcome::Skip;
    return TestOutcome::Unknown;
}

int DiagnosisTreeNode::depth() const
{
    int d = 0;
    const DiagnosisTreeNode* node = this;
    while (node->parent() != nullptr) {
        d++;
        node = node->parent();
    }
    return d;
}

void DiagnosisTreeNode::debugPrint(int indent) const
{
    QString indentStr(indent * 2, ' ');
    qDebug().noquote() << indentStr << "Node" << m_nodeId << ":"
                       << nodeTypeString()
                       << (m_testDescription.isEmpty() ? m_faultHypothesis : m_testDescription)
                       << "(outcome:" << outcomeString() << ")";
    
    for (DiagnosisTreeNode* child : m_children) {
        child->debugPrint(indent + 1);
    }
}
