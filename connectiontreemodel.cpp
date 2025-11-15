#include "connectiontreemodel.h"
#include <QIcon>
#include "performancetimer.h"

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
            return "导线";
        default:
            return "未知";
        }
    } else if (role == Qt::UserRole) {
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
    const auto *symbolMgr = m_projectDataModel->symbolManager();

    if (!connectionMgr || !structureMgr || !symbolMgr) {
        return;
    }

    QVector<int> connectionIds = connectionMgr->getAllConnectionIds();

    // 构建树结构
    for (int connId : connectionIds) {
        const ConnectionData *connection = connectionMgr->getConnection(connId);
        if (!connection) continue;

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
        connectionNode->parent = connNumNode;
        connNumNode->children.append(connectionNode);
    }
}

QString ConnectionTreeModel::buildConnectionText(const ConnectionData *connection) const
{
    if (!connection) {
        return QString();
    }

    QString startStr = buildTerminalStr(connection->symb1Id, connection->symb1Category);
    QString endStr = buildTerminalStr(connection->symb2Id, connection->symb2Category);

    // 格式：ConnectionNumber (起点 → 终点)
    QString text = connection->connectionNumber;
    if (!startStr.isEmpty() && !endStr.isEmpty()) {
        text += QString(" (%1 → %2)").arg(startStr).arg(endStr);
    }

    return text;
}

QString ConnectionTreeModel::buildTerminalStr(const QString &symbId, const QString &category) const
{
    if (symbId.isEmpty()) {
        return QString();
    }

    // 判断是端子排还是元件
    if (category == "1") {
        // 端子排：格式为 TerminalInstanceID.Format
        int dotPos = symbId.indexOf(".");
        if (dotPos > 0) {
            QString termInstanceId = symbId.left(dotPos);
            QString format = symbId.mid(dotPos);
            // 这里需要查询端子排信息
            // 简化处理，返回原始ID
            return QString("端子排%1%2").arg(termInstanceId).arg(format);
        }
    } else if (category == "0") {
        // 元件：从Symb2TermInfo获取Symbol和Terminal信息
        bool ok = false;
        int termId = symbId.toInt(&ok);
        if (ok) {
            // 这里需要查询Symb2TermInfo表
            // 简化处理，返回termId
            return QString("T%1").arg(termId);
        }
    }

    return symbId;
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
