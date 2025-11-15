#include "connectionbyunittreemodel.h"
#include <QIcon>
#include "performancetimer.h"

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
            return "连线端点";
        default:
            return "未知";
        }
    } else if (role == Qt::UserRole) {
        if (node->type == Type_ConnectionEnd) {
            return node->connectionId;
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
    const auto *symbolMgr = m_projectDataModel->symbolManager();
    const auto *equipmentMgr = m_projectDataModel->equipmentManager();

    if (!connectionMgr || !structureMgr || !symbolMgr || !equipmentMgr) {
        return;
    }

    QVector<int> connectionIds = connectionMgr->getAllConnectionIds();

    // 收集所有端点信息
    struct EndpointInfo {
        int connectionId;
        int symbolId;
        QString symbId;         // Symb1_ID or Symb2_ID
        QString category;       // Symb1_Category or Symb2_Category
        QString gaoceng;
        QString position;
        int structureId;
    };

    QVector<EndpointInfo> allEndpoints;
    allEndpoints.reserve(connectionIds.size() * 2);

    for (int connId : connectionIds) {
        const ConnectionData *connection = connectionMgr->getConnection(connId);
        if (!connection) continue;

        // 获取端点1
        bool ok = false;
        int symb1Id = connection->symb1Id.toInt(&ok);
        if (ok) {
            EndpointInfo endpoint1;
            endpoint1.connectionId = connId;
            endpoint1.symbolId = symb1Id;
            endpoint1.symbId = connection->symb1Id;
            endpoint1.category = connection->symb1Category;
            endpoint1.gaoceng = structureMgr->getGaoceng(connection->structureId);
            endpoint1.position = structureMgr->getPos(connection->structureId);
            endpoint1.structureId = connection->structureId;
            allEndpoints.append(endpoint1);
        }

        // 获取端点2
        int symb2Id = connection->symb2Id.toInt(&ok);
        if (ok) {
            EndpointInfo endpoint2;
            endpoint2.connectionId = connId;
            endpoint2.symbolId = symb2Id;
            endpoint2.symbId = connection->symb2Id;
            endpoint2.category = connection->symb2Category;
            endpoint2.gaoceng = structureMgr->getGaoceng(connection->structureId);
            endpoint2.position = structureMgr->getPos(connection->structureId);
            endpoint2.structureId = connection->structureId;
            allEndpoints.append(endpoint2);
        }
    }

    // 按元件/端子排分组
    QMap<QString, QVector<EndpointInfo>> unitEndpointsMap;

    for (const EndpointInfo &endpoint : allEndpoints) {
        QString unitKey;
        if (endpoint.category == "0") {
            // 元件：从Symbol获取Equipment
            const SymbolData *symbol = symbolMgr->getSymbol(endpoint.symbolId);
            if (symbol && symbol->equipmentId > 0) {
                unitKey = QString("EQ_%1").arg(symbol->equipmentId);
            }
        } else if (endpoint.category == "1") {
            // 端子排：直接使用terminalStripId (简化处理，这里使用symbolId作为标识)
            unitKey = QString("TS_%1").arg(endpoint.symbolId);
        }

        if (!unitKey.isEmpty()) {
            unitEndpointsMap[unitKey].append(endpoint);
        }
    }

    // 构建树结构
    for (auto it = unitEndpointsMap.begin(); it != unitEndpointsMap.end(); ++it) {
        const QString &unitKey = it.key();
        const QVector<EndpointInfo> &endpoints = it.value();

        if (endpoints.isEmpty()) continue;

        const EndpointInfo &firstEndpoint = endpoints.first();

        // 获取显示名称
        QString displayText;
        QString category = firstEndpoint.category;
        if (category == "0") {
            // 元件
            const SymbolData *symbol = symbolMgr->getSymbol(firstEndpoint.symbolId);
            if (symbol) {
                const EquipmentData *equipment = equipmentMgr->getEquipment(symbol->equipmentId);
                displayText = equipment ? equipment->dt : QString("元件_%1").arg(symbol->equipmentId);
            }
        } else if (category == "1") {
            // 端子排 (简化显示)
            displayText = QString("端子排_%1").arg(firstEndpoint.symbolId);
        }

        // 创建或获取高层节点（按名称去重）
        TreeNode *gaocengNode = nullptr;
        QString gaocengKey = QString::number(firstEndpoint.structureId);

        // 首先尝试按structureId查找
        if (m_gaocengKeyToNode.contains(gaocengKey)) {
            gaocengNode = m_gaocengKeyToNode[gaocengKey];
        } else {
            // 按名称查找已存在的同名节点，避免重复创建
            QString gaocengName = firstEndpoint.gaoceng;
            for (TreeNode *existingNode : m_rootNode->children) {
                if (existingNode->type == Type_Gaoceng && existingNode->displayText == gaocengName) {
                    gaocengNode = existingNode;
                    break;
                }
            }

            // 如果没有找到同名节点，创建新节点
            if (!gaocengNode) {
                gaocengNode = new TreeNode(Type_Gaoceng);
                gaocengNode->displayText = gaocengName;
                gaocengNode->structureId = firstEndpoint.structureId;
                gaocengNode->gaoceng = gaocengName;
                gaocengNode->parent = m_rootNode;
                m_rootNode->children.append(gaocengNode);
            }

            // 缓存节点
            m_gaocengKeyToNode[gaocengKey] = gaocengNode;
        }

        // 创建或获取位置节点（按名称去重，空名称显示为"未分配位置"）
        TreeNode *positionNode = nullptr;
        QString positionDisplay = firstEndpoint.position.isEmpty() ? QString("未分配位置") : firstEndpoint.position;
        QString posKey = firstEndpoint.gaoceng + "|" + positionDisplay;
        if (m_posKeyToNode.contains(posKey)) {
            positionNode = m_posKeyToNode[posKey];
        } else {
            positionNode = new TreeNode(Type_Position);
            positionNode->displayText = positionDisplay;
            positionNode->structureId = firstEndpoint.structureId;
            positionNode->gaoceng = firstEndpoint.gaoceng;
            positionNode->position = firstEndpoint.position;
            positionNode->parent = gaocengNode;
            gaocengNode->children.append(positionNode);
            m_posKeyToNode[posKey] = positionNode;
        }

        // 创建或获取元件/端子排节点
        TreeNode *unitNode = nullptr;
        QString unitNodeKey = posKey + "|" + unitKey;
        if (m_unitKeyToNode.contains(unitNodeKey)) {
            unitNode = m_unitKeyToNode[unitNodeKey];
        } else {
            unitNode = new TreeNode(Type_UnitStrip);
            unitNode->displayText = displayText;
            unitNode->unitStripId = firstEndpoint.symbolId;
            unitNode->category = category;
            unitNode->structureId = firstEndpoint.structureId;
            unitNode->gaoceng = firstEndpoint.gaoceng;
            unitNode->position = firstEndpoint.position;
            unitNode->parent = positionNode;
            positionNode->children.append(unitNode);
            m_unitKeyToNode[unitNodeKey] = unitNode;
        }

        // 添加连线端点
        for (const EndpointInfo &endpoint : endpoints) {
            const ConnectionData *connection = connectionMgr->getConnection(endpoint.connectionId);
            if (!connection) continue;

            TreeNode *connectionEndNode = new TreeNode(Type_ConnectionEnd);
            connectionEndNode->displayText = buildConnectionEndText(connection,
                endpoint.symbId == connection->symb1Id ? 0 : 1);
            connectionEndNode->connectionId = endpoint.connectionId;
            connectionEndNode->endpointIndex = (endpoint.symbId == connection->symb1Id) ? 0 : 1;
            connectionEndNode->structureId = endpoint.structureId;
            connectionEndNode->gaoceng = endpoint.gaoceng;
            connectionEndNode->position = endpoint.position;
            connectionEndNode->parent = unitNode;
            unitNode->children.append(connectionEndNode);
        }
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

    QString endpointSymbId = (endpointIndex == 0) ? connection->symb1Id : connection->symb2Id;
    QString endpointCategory = (endpointIndex == 0) ? connection->symb1Category : connection->symb2Category;

    QString endpointText;
    if (endpointCategory == "0") {
        // 元件端点
        bool ok = false;
        int symbId = endpointSymbId.toInt(&ok);
        if (ok) {
            endpointText = getSymbolDisplayText(symbId);
        }
    } else if (endpointCategory == "1") {
        // 端子排端点
        endpointText = getTerminalDisplayText(endpointSymbId.toInt());
    }

    // 格式：ConnectionNumber -> 端点描述
    QString text = connection->connectionNumber;
    if (!endpointText.isEmpty()) {
        text += " → " + endpointText;
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
