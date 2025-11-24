#include "connectiontreemodel.h"
#include <QIcon>
#include <QSqlQuery>
#include <QSqlError>
#include "performancetimer.h"
#include "common.h"

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

ConnectionTreeModel::ConnectionTreeModel(QObject *parent)
    : QAbstractItemModel(parent)
{
    m_rootNode = new TreeNode(Type_Root);
    m_rootNode->displayText = "项目";
}

int ConnectionTreeModel::rowCount(const QModelIndex &parent) const
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

int ConnectionTreeModel::columnCount(const QModelIndex &parent) const
{
    Q_UNUSED(parent);
    return 1;  // 单列显示
}

QModelIndex ConnectionTreeModel::index(int row, int column, const QModelIndex &parent) const
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

QModelIndex ConnectionTreeModel::parent(const QModelIndex &child) const
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

QVariant ConnectionTreeModel::data(const QModelIndex &index, int role) const
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
        case Type_ConnectionNum:
            return "线号";
        case Type_Connection:
            return "连线";
        default:
            return "未知";
        }
    } else if (role == Qt::UserRole) {
        if (node->type == Type_Connection) {
            QStringList list;
            list << QString::number(node->connectionId)
                 << node->symb1Id << node->symb1Category
                 << node->symb2Id << node->symb2Category;
            return list;
        }
        return node->connectionId;
    }

    return QVariant();
}

QVariant ConnectionTreeModel::headerData(int section, Qt::Orientation orientation, int role) const
{
    if (orientation == Qt::Horizontal && role == Qt::DisplayRole) {
        if (section == 0) {
            return "连线";
        }
    }
    return QAbstractItemModel::headerData(section, orientation, role);
}

void ConnectionTreeModel::setProjectDataModel(ProjectDataModel *model)
{
    m_projectDataModel = model;
}

void ConnectionTreeModel::rebuild()
{
    beginResetModel();
    clear();
    if (m_projectDataModel && m_projectDataModel->isLoaded()) {
        buildTreeData();
    }
    endResetModel();
}

void ConnectionTreeModel::clear()
{
    qDeleteAll(m_rootNode->children);
    m_rootNode->children.clear();
    m_structureToGaocengNode.clear();
    m_posKeyToNode.clear();
    m_connNumKeyToNode.clear();
}

void ConnectionTreeModel::buildTreeData()
{
    if (!m_projectDataModel) {
        return;
    }

    const auto *connectionMgr = m_projectDataModel->connectionManager();
    const auto *structureMgr = m_projectDataModel->structureManager();

    if (!connectionMgr || !structureMgr) {
        return;
    }

    QVector<int> connectionIds = connectionMgr->getAllConnectionIds();

    // 构建树结构
    for (int connId : connectionIds) {
        const ConnectionData *connection = connectionMgr->getConnection(connId);
        if (!connection) continue;

        // 过滤特殊节点（CO、G等）
        if (shouldSkipSymbId(connection->symb1Id) || shouldSkipSymbId(connection->symb2Id)) {
            continue;
        }

        // 获取高层和位置信息
        QString gaoceng = structureMgr->getGaoceng(connection->structureId);
        QString position = structureMgr->getPos(connection->structureId);

        // 创建或获取高层节点（按名称去重）
        TreeNode *gaocengNode = nullptr;
        QString gaocengKey = QString::number(connection->structureId);

        // 首先尝试按structureId查找
        if (m_structureToGaocengNode.contains(connection->structureId)) {
            gaocengNode = m_structureToGaocengNode[connection->structureId];
        } else {
            // 按名称查找已存在的同名节点，避免重复创建
            for (TreeNode *existingNode : m_rootNode->children) {
                if (existingNode->type == Type_Gaoceng && existingNode->displayText == gaoceng) {
                    gaocengNode = existingNode;
                    break;
                }
            }

            // 如果没有找到同名节点，创建新节点
            if (!gaocengNode) {
                gaocengNode = new TreeNode(Type_Gaoceng);
                gaocengNode->displayText = gaoceng;
                gaocengNode->structureId = connection->structureId;
                gaocengNode->gaoceng = gaoceng;
                gaocengNode->parent = m_rootNode;
                m_rootNode->children.append(gaocengNode);
            }

            // 缓存节点
            m_structureToGaocengNode[connection->structureId] = gaocengNode;
        }

        // 创建或获取位置节点（按名称去重，空名称显示为"未分配位置"）
        TreeNode *positionNode = nullptr;
        QString positionDisplay = position.isEmpty() ? QString("未分配位置") : position;
        QString posKey = gaoceng + "|" + positionDisplay;
        if (m_posKeyToNode.contains(posKey)) {
            positionNode = m_posKeyToNode[posKey];
        } else {
            positionNode = new TreeNode(Type_Position);
            positionNode->displayText = positionDisplay;
            positionNode->structureId = connection->structureId;
            positionNode->gaoceng = gaoceng;
            positionNode->position = position;
            positionNode->parent = gaocengNode;
            gaocengNode->children.append(positionNode);
            m_posKeyToNode[posKey] = positionNode;
        }

        // 创建或获取线号节点
        TreeNode *connNumNode = nullptr;
        QString connNumKey = posKey + "|" + connection->connectionNumber;
        if (m_connNumKeyToNode.contains(connNumKey)) {
            connNumNode = m_connNumKeyToNode[connNumKey];
        } else {
            connNumNode = new TreeNode(Type_ConnectionNum);
            connNumNode->displayText = connection->connectionNumber;
            connNumNode->connectionId = connId;
            connNumNode->structureId = connection->structureId;
            connNumNode->gaoceng = gaoceng;
            connNumNode->position = position;
            connNumNode->parent = positionNode;
            positionNode->children.append(connNumNode);
            m_connNumKeyToNode[connNumKey] = connNumNode;
        }

        // 创建导线节点
        TreeNode *connectionNode = new TreeNode(Type_Connection);
        connectionNode->displayText = buildConnectionText(connection);
        connectionNode->connectionId = connId;
        connectionNode->structureId = connection->structureId;
        connectionNode->gaoceng = gaoceng;
        connectionNode->position = position;
        connectionNode->symb1Id = connection->symb1Id;
        connectionNode->symb2Id = connection->symb2Id;
        connectionNode->symb1Category = connection->symb1Category;
        connectionNode->symb2Category = connection->symb2Category;
        connectionNode->parent = connNumNode;
        connNumNode->children.append(connectionNode);
    }
}

QString ConnectionTreeModel::buildConnectionText(const ConnectionData *connection) const
{
    if (!connection) {
        return QString();
    }

    const QString startStr = buildTerminalStr(connection->symb1Id, connection->symb1Category);
    const QString endStr = buildTerminalStr(connection->symb2Id, connection->symb2Category);

    if (!startStr.isEmpty() || !endStr.isEmpty()) {
        return startStr + "<->" + endStr;
    }

    return connection->connectionNumber;
}

QString ConnectionTreeModel::buildTerminalStr(const QString &symbId, const QString &category) const
{
    return buildEndpointDisplay(symbId, category);
}

QString ConnectionTreeModel::getSymbolDisplayText(int symbolId) const
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

QString ConnectionTreeModel::getTerminalDisplayText(int terminalInstanceId) const
{
    // TODO: 实现端子显示文本
    Q_UNUSED(terminalInstanceId);
    return QString("端子");
}

ConnectionTreeModel::NodeType ConnectionTreeModel::getNodeType(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return Type_Root;
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->type : Type_Root;
}

int ConnectionTreeModel::getConnectionId(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return 0;
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->connectionId : 0;
}

QString ConnectionTreeModel::getGaoceng(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return QString();
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->gaoceng : QString();
}

QString ConnectionTreeModel::getPosition(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return QString();
    }

    TreeNode *node = static_cast<TreeNode*>(index.internalPointer());
    return node ? node->position : QString();
}
