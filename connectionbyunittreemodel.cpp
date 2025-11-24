#include "connectionbyunittreemodel.h"
#include <QIcon>
#include <QSqlQuery>
#include <QSqlError>
#include "performancetimer.h"
#include "common.h"
#include "projectdatacache.h"

extern QSqlDatabase T_ProjectDatabase;

namespace {

bool shouldSkipSymbId(const QString &symbId)
{
    return symbId.contains(":C") || symbId.contains(":G") || symbId.contains(":1") ||
           symbId.contains(":2") || symbId.contains(":3");
}

QString buildUnitTermStr(const QString &termId)
{
    bool ok = false;
    const int termInfoId = termId.toInt(&ok);
    if (!ok || !T_ProjectDatabase.isOpen()) {
        return QString();
    }

    QSqlQuery querySymb(T_ProjectDatabase);
    querySymb.prepare("SELECT Symbol_ID, ConnNum FROM Symb2TermInfo WHERE Symb2TermInfo_ID = :id");
    querySymb.bindValue(":id", termInfoId);
    if (!querySymb.exec() || !querySymb.next()) {
        return QString();
    }
    const int symbolId = querySymb.value("Symbol_ID").toInt();
    const QString connNum = querySymb.value("ConnNum").toString();

    QSqlQuery querySymbol(T_ProjectDatabase);
    querySymbol.prepare("SELECT Equipment_ID FROM Symbol WHERE Symbol_ID = :sid");
    querySymbol.bindValue(":sid", symbolId);
    if (!querySymbol.exec() || !querySymbol.next()) {
        return QString();
    }
    const int equipmentId = querySymbol.value("Equipment_ID").toInt();

    QSqlQuery queryEquipment(T_ProjectDatabase);
    queryEquipment.prepare("SELECT ProjectStructure_ID, DT FROM Equipment WHERE Equipment_ID = :eid");
    queryEquipment.bindValue(":eid", equipmentId);
    if (!queryEquipment.exec() || !queryEquipment.next()) {
        return QString();
    }
    const int structureId = queryEquipment.value("ProjectStructure_ID").toInt();
    const QString dt = queryEquipment.value("DT").toString();
    const QString structureTag = GetProjectStructureStrByProjectStructureID(structureId);

    if (structureTag.isEmpty()) {
        return dt + ":" + connNum;
    }
    return structureTag + "-" + dt + ":" + connNum;
}

QString buildTerminalTermStr(const QString &termId)
{
    if (!T_ProjectDatabase.isOpen()) {
        return QString();
    }

    const int dotPos = termId.indexOf(".");
    const QString instanceIdStr = dotPos > 0 ? termId.left(dotPos) : termId;
    bool ok = false;
    const int instanceId = instanceIdStr.toInt(&ok);
    if (!ok) {
        return QString();
    }

    QSqlQuery queryInstance(T_ProjectDatabase);
    queryInstance.prepare("SELECT Terminal_ID FROM TerminalInstance WHERE TerminalInstanceID = :id");
    queryInstance.bindValue(":id", instanceId);
    if (!queryInstance.exec() || !queryInstance.next()) {
        return QString();
    }
    const int terminalId = queryInstance.value("Terminal_ID").toInt();

    QSqlQuery queryTerminal(T_ProjectDatabase);
    queryTerminal.prepare("SELECT TerminalStrip_ID, Designation FROM Terminal WHERE Terminal_ID = :tid");
    queryTerminal.bindValue(":tid", terminalId);
    if (!queryTerminal.exec() || !queryTerminal.next()) {
        return QString();
    }
    const int stripId = queryTerminal.value("TerminalStrip_ID").toInt();
    const QString designation = queryTerminal.value("Designation").toString();

    QSqlQuery queryStrip(T_ProjectDatabase);
    queryStrip.prepare("SELECT ProjectStructure_ID, DT FROM TerminalStrip WHERE TerminalStrip_ID = :sid");
    queryStrip.bindValue(":sid", stripId);
    if (!queryStrip.exec() || !queryStrip.next()) {
        return QString();
    }
    const int structureId = queryStrip.value("ProjectStructure_ID").toInt();
    const QString dt = queryStrip.value("DT").toString();
    const QString structureTag = GetProjectStructureStrByProjectStructureID(structureId);
    const QString suffix = dotPos > 0 ? termId.mid(dotPos) : QString();

    QString prefix = dt;
    if (!structureTag.isEmpty()) {
        prefix = structureTag + "-" + dt;
    }
    return prefix + ":" + designation + suffix;
}

QString getTerminalDesignation(const QString &termId)
{
    bool ok = false;
    const int terminalTermId = termId.toInt(&ok);
    if (!ok || !T_ProjectDatabase.isOpen()) {
        return QString();
    }

    QSqlQuery queryTerm(T_ProjectDatabase);
    queryTerm.prepare("SELECT Terminal_ID FROM TerminalTerm WHERE TerminalTerm_ID = :id");
    queryTerm.bindValue(":id", terminalTermId);
    if (!queryTerm.exec() || !queryTerm.next()) {
        return QString();
    }

    QSqlQuery queryTerminal(T_ProjectDatabase);
    queryTerminal.prepare("SELECT Designation FROM Terminal WHERE Terminal_ID = :tid");
    queryTerminal.bindValue(":tid", queryTerm.value("Terminal_ID").toInt());
    if (!queryTerminal.exec() || !queryTerminal.next()) {
        return QString();
    }

    return queryTerminal.value("Designation").toString();
}

QString buildEndpointDisplay(const QString &symbId, const QString &category)
{
    if (category == QStringLiteral("0")) {
        return buildUnitTermStr(symbId);
    }
    if (category == QStringLiteral("1")) {
        return buildTerminalTermStr(symbId);
    }
    return QString();
}

} // namespace

ConnectionByUnitTreeModel::ConnectionByUnitTreeModel(QObject *parent)
    : QAbstractItemModel(parent)
{
    m_rootNode = new TreeNode(Type_Root);
    m_rootNode->displayText = "项目";
}

int ConnectionByUnitTreeModel::rowCount(const QModelIndex &parent) const
{
    if (!parent.isValid()) {
        return m_rootNode->children.size();
    }

    TreeNode *parentNode = static_cast<TreeNode*>(parent.internalPointer());
    if (!parentNode) {
        return 0;
    }

    return parentNode->children.size();
}

int ConnectionByUnitTreeModel::columnCount(const QModelIndex &parent) const
{
    Q_UNUSED(parent);
    return 1;  // 单列显示
}

QModelIndex ConnectionByUnitTreeModel::index(int row, int column, const QModelIndex &parent) const
{
    if (column != 0) {
        return QModelIndex();
    }

    TreeNode *parentNode = nullptr;
    if (!parent.isValid()) {
        parentNode = m_rootNode;
    } else {
        parentNode = static_cast<TreeNode*>(parent.internalPointer());
    }

    if (!parentNode || row < 0 || row >= parentNode->children.size()) {
        return QModelIndex();
    }

    TreeNode *childNode = parentNode->children[row];
    return createIndex(row, column, childNode);
}

QModelIndex ConnectionByUnitTreeModel::parent(const QModelIndex &child) const
{
    if (!child.isValid()) {
        return QModelIndex();
    }

    TreeNode *childNode = static_cast<TreeNode*>(child.internalPointer());
    if (!childNode || childNode == m_rootNode) {
        return QModelIndex();
    }

    TreeNode *parentNode = childNode->parent;
    if (!parentNode) {
        return QModelIndex();
    }

    // 找到在父节点中的行号
    int row = 0;
    if (parentNode->parent) {
        row = parentNode->parent->children.indexOf(parentNode);
    }

    return createIndex(row, 0, parentNode);
}

QVariant ConnectionByUnitTreeModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid()) {
        return QVariant();
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    if (!node) {
        return QVariant();
    }

    if (role == Qt::DisplayRole) {
        return node->displayText;
    } else if (role == Qt::WhatsThisRole) {
        switch (node->type) {
        case Type_Root:
            return "项目";
        case Type_Gaoceng:
            return "高层";
        case Type_Position:
            return "位置";
        case Type_UnitStrip:
            return node->category == "1" ? "端子排" : "元件";
        case Type_ConnectionEnd:
            return "功能子块";
        default:
            return "未知";
        }
    } else if (role == Qt::UserRole) {
        if (node->type == Type_ConnectionEnd) {
            QStringList list;
            list << QString::number(node->connectionId)
                 << node->symbId << node->category
                 << node->otherSymbId << node->otherCategory;
            return list;
        } else if (node->type == Type_UnitStrip) {
            return node->unitStripId;
        }
    }

    return QVariant();
}

QVariant ConnectionByUnitTreeModel::headerData(int section, Qt::Orientation orientation, int role) const
{
    if (orientation == Qt::Horizontal && role == Qt::DisplayRole) {
        if (section == 0) {
            return "按单元分组连线";
        }
    }
    return QAbstractItemModel::headerData(section, orientation, role);
}

void ConnectionByUnitTreeModel::setProjectDataModel(ProjectDataModel *model)
{
    m_projectDataModel = model;
}

void ConnectionByUnitTreeModel::setProjectDataCache(ProjectDataCache *cache)
{
    m_projectCache = cache;
}

void ConnectionByUnitTreeModel::rebuild()
{
    beginResetModel();
    clear();
    if (m_projectDataModel && m_projectDataModel->isLoaded()) {
        buildTreeData();
    }
    endResetModel();
}

void ConnectionByUnitTreeModel::clear()
{
    qDeleteAll(m_rootNode->children);
    m_rootNode->children.clear();
    m_gaocengKeyToNode.clear();
    m_posKeyToNode.clear();
    m_unitKeyToNode.clear();
}

void ConnectionByUnitTreeModel::buildTreeData()
{
    if (!m_projectDataModel) {
        return;
    }

    const auto *connectionMgr = m_projectDataModel->connectionManager();
    const auto *structureMgr = m_projectDataModel->structureManager();

    if (!connectionMgr || !structureMgr) {
        return;
    }

    const auto addEndpoint = [&](const ConnectionData *connection, int endpointIndex) {
        if (!connection) return;

        const QString endpointSymbId = (endpointIndex == 0) ? connection->symb1Id : connection->symb2Id;
        const QString endpointCategory = (endpointIndex == 0) ? connection->symb1Category : connection->symb2Category;
        const QString otherSymbId = (endpointIndex == 0) ? connection->symb2Id : connection->symb1Id;
        const QString otherCategory = (endpointIndex == 0) ? connection->symb2Category : connection->symb1Category;

        if (endpointSymbId.isEmpty() || shouldSkipSymbId(endpointSymbId)) return;

        bool ok = false;
        const int endpointId = endpointSymbId.toInt(&ok);
        if (!ok) return;

        // 获取端点所属的高层/位置
        QString gaoceng = structureMgr->getGaoceng(connection->structureId);
        QString pos = structureMgr->getPos(connection->structureId);
        GetUnitTermimalGaocengAndPos_Cached(m_projectCache, endpointCategory.toInt(), endpointId, gaoceng, pos);
        if (gaoceng.isEmpty()) gaoceng = QString("未分配高层");
        if (pos.isEmpty()) pos = QString("未分配位置");

        // 获取元件/端子排ID与显示名称
        QString unitDt;
        int unitStripId = GetUnitStripIDByTermID(endpointCategory.toInt(), endpointId, unitDt);
        if (unitStripId <= 0) return;

        int structureId = connection->structureId;
        QSqlQuery query(T_ProjectDatabase);
        if (endpointCategory == "0") {
            query.prepare("SELECT ProjectStructure_ID FROM Equipment WHERE Equipment_ID = :id");
        } else {
            query.prepare("SELECT ProjectStructure_ID FROM TerminalStrip WHERE TerminalStrip_ID = :id");
        }
        query.bindValue(":id", unitStripId);
        if (query.exec() && query.next()) {
            structureId = query.value(0).toInt();
        }

        // 创建或获取高层节点
        TreeNode *gaocengNode = nullptr;
        const QString gaocengKey = QString::number(structureId) + "|" + gaoceng;
        if (m_gaocengKeyToNode.contains(gaocengKey)) {
            gaocengNode = m_gaocengKeyToNode.value(gaocengKey);
        } else {
            for (TreeNode *existingNode : m_rootNode->children) {
                if (existingNode->type == Type_Gaoceng && existingNode->displayText == gaoceng) {
                    gaocengNode = existingNode;
                    break;
                }
            }
            if (!gaocengNode) {
                gaocengNode = new TreeNode(Type_Gaoceng);
                gaocengNode->displayText = gaoceng;
                gaocengNode->structureId = structureId;
                gaocengNode->gaoceng = gaoceng;
                gaocengNode->parent = m_rootNode;
                m_rootNode->children.append(gaocengNode);
            }
            m_gaocengKeyToNode.insert(gaocengKey, gaocengNode);
        }

        // 创建或获取位置节点
        TreeNode *positionNode = nullptr;
        const QString positionDisplay = pos.isEmpty() ? QString("未分配位置") : pos;
        const QString posKey = gaoceng + "|" + positionDisplay;
        if (m_posKeyToNode.contains(posKey)) {
            positionNode = m_posKeyToNode.value(posKey);
        } else {
            positionNode = new TreeNode(Type_Position);
            positionNode->displayText = positionDisplay;
            positionNode->structureId = structureId;
            positionNode->gaoceng = gaoceng;
            positionNode->position = pos;
            positionNode->parent = gaocengNode;
            gaocengNode->children.append(positionNode);
            m_posKeyToNode.insert(posKey, positionNode);
        }

        // 创建或获取元件/端子排节点
        TreeNode *unitNode = nullptr;
        const QString unitNodeKey = posKey + "|" + QString::number(unitStripId) + "|" + endpointCategory;
        if (m_unitKeyToNode.contains(unitNodeKey)) {
            unitNode = m_unitKeyToNode.value(unitNodeKey);
        } else {
            unitNode = new TreeNode(Type_UnitStrip);
            unitNode->displayText = unitDt;
            unitNode->unitStripId = unitStripId;
            unitNode->category = endpointCategory;
            unitNode->structureId = structureId;
            unitNode->gaoceng = gaoceng;
            unitNode->position = pos;
            unitNode->parent = positionNode;
            positionNode->children.append(unitNode);
            m_unitKeyToNode.insert(unitNodeKey, unitNode);
        }

        // 防止重复插入
        for (TreeNode *child : unitNode->children) {
            if (child->connectionId == connection->id &&
                child->symbId == endpointSymbId &&
                child->otherSymbId == otherSymbId) {
                return;
            }
        }

        // 添加连线端点节点
        TreeNode *connectionEndNode = new TreeNode(Type_ConnectionEnd);
        connectionEndNode->displayText = buildConnectionEndText(connection, endpointIndex);
        connectionEndNode->connectionId = connection->id;
        connectionEndNode->endpointIndex = endpointIndex;
        connectionEndNode->structureId = structureId;
        connectionEndNode->gaoceng = gaoceng;
        connectionEndNode->position = pos;
        connectionEndNode->symbId = endpointSymbId;
        connectionEndNode->category = endpointCategory;
        connectionEndNode->otherSymbId = otherSymbId;
        connectionEndNode->otherCategory = otherCategory;
        connectionEndNode->parent = unitNode;
        unitNode->children.append(connectionEndNode);
    };

    QVector<int> connectionIds = connectionMgr->getAllConnectionIds();
    for (int connId : connectionIds) {
        const ConnectionData *connection = connectionMgr->getConnection(connId);
        if (!connection) continue;
        if (shouldSkipSymbId(connection->symb1Id) || shouldSkipSymbId(connection->symb2Id)) {
            continue;
        }
        addEndpoint(connection, 0);
        addEndpoint(connection, 1);
    }
}

QString ConnectionByUnitTreeModel::buildUnitStripDisplayText(int unitStripId, const QString &category, const QString &dt) const
{
    Q_UNUSED(unitStripId);
    Q_UNUSED(category);
    Q_UNUSED(dt);
    return QString();
}

QString ConnectionByUnitTreeModel::buildConnectionEndText(const ConnectionData *connection, int endpointIndex) const
{
    if (!connection) {
        return QString();
    }

    const QString endpointSymbId = (endpointIndex == 0) ? connection->symb1Id : connection->symb2Id;
    const QString endpointCategory = (endpointIndex == 0) ? connection->symb1Category : connection->symb2Category;
    const QString otherSymbId = (endpointIndex == 0) ? connection->symb2Id : connection->symb1Id;
    const QString otherCategory = (endpointIndex == 0) ? connection->symb2Category : connection->symb1Category;

    QString termLabel;
    if (endpointCategory == "0") {
        bool ok = false;
        const int termId = endpointSymbId.toInt(&ok);
        if (ok) {
            QSqlQuery query(T_ProjectDatabase);
            query.prepare("SELECT ConnNum FROM Symb2TermInfo WHERE Symb2TermInfo_ID = :id");
            query.bindValue(":id", termId);
            if (query.exec() && query.next()) {
                termLabel = query.value(0).toString();
            }
        }
    } else if (endpointCategory == "1") {
        termLabel = getTerminalDesignation(endpointSymbId);
    }

    QString text = termLabel;
    if (!connection->connectionNumber.isEmpty()) {
        text += "(" + connection->connectionNumber + ")";
    }

    const QString otherSide = buildEndpointDisplay(otherSymbId, otherCategory);
    if (!otherSide.isEmpty()) {
        if (!text.isEmpty()) {
            text += "<->" + otherSide;
        } else {
            text = otherSide;
        }
    }

    if (text.isEmpty()) {
        return connection->connectionNumber;
    }
    return text;
}

QString ConnectionByUnitTreeModel::getSymbolDisplayText(int symbolId) const
{
    if (!m_projectDataModel) {
        return QString();
    }

    const auto *symbolMgr = m_projectDataModel->symbolManager();
    if (!symbolMgr) {
        return QString();
    }

    const SymbolData *symbol = symbolMgr->getSymbol(symbolId);
    if (!symbol) {
        return QString();
    }

    // 格式：Designation:ConnNums-FunDefine
    QString text = symbol->designation;
    if (!symbol->connNums.isEmpty()) {
        text += ":" + symbol->connNums.join(",");
    }
    if (!symbol->funDefine.isEmpty()) {
        text += "-" + symbol->funDefine;
    }

    return text;
}

QString ConnectionByUnitTreeModel::getTerminalDisplayText(int terminalInstanceId) const
{
    Q_UNUSED(terminalInstanceId);
    return QString("端子排端子");
}

QString ConnectionByUnitTreeModel::getEquipmentDisplayText(int equipmentId) const
{
    Q_UNUSED(equipmentId);
    return QString();
}

QString ConnectionByUnitTreeModel::getTerminalStripDisplayText(int terminalStripId) const
{
    Q_UNUSED(terminalStripId);
    return QString();
}

ConnectionByUnitTreeModel::NodeType ConnectionByUnitTreeModel::getNodeType(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return Type_Root;
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->type : Type_Root;
}

int ConnectionByUnitTreeModel::getConnectionId(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return 0;
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->connectionId : 0;
}

int ConnectionByUnitTreeModel::getUnitStripId(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return 0;
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->unitStripId : 0;
}

QString ConnectionByUnitTreeModel::getGaoceng(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return QString();
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->gaoceng : QString();
}

QString ConnectionByUnitTreeModel::getPosition(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return QString();
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->position : QString();
}
