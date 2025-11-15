#include "equipmenttreemodel.h"
#include "projectdatamodel.h"

#include <algorithm>

EquipmentTreeModel::EquipmentTreeModel(QObject *parent)
    : QAbstractItemModel(parent)
{
}

EquipmentTreeModel::~EquipmentTreeModel()
{
    clear();
}

void EquipmentTreeModel::setProjectDataModel(ProjectDataModel *model)
{
    m_projectDataModel = model;
}

void EquipmentTreeModel::clear()
{
    beginResetModel();
    m_rootNodes.clear();
    m_nodeStorage.clear();
    m_gaocengIndex.clear();
    m_posIndex.clear();
    m_equipmentIndex.clear();
    m_symbolIndex.clear();
    m_defaultRoot = nullptr;
    endResetModel();
}

void EquipmentTreeModel::rebuild()
{
    beginResetModel();
    m_rootNodes.clear();
    m_nodeStorage.clear();
    m_gaocengIndex.clear();
    m_posIndex.clear();
    m_equipmentIndex.clear();
    m_symbolIndex.clear();
    m_defaultRoot = nullptr;

    if (!m_projectDataModel || !m_projectDataModel->isLoaded()) {
        endResetModel();
        return;
    }

    const StructureManager *structureMgr = m_projectDataModel->structureManager();
    const EquipmentManager *equipmentMgr = m_projectDataModel->equipmentManager();
    const SymbolManager *symbolMgr = m_projectDataModel->symbolManager();

    Node *projectNode = createNode(NodeType::Project, 0, nullptr);
    projectNode->displayText = QString("项目");
    if (structureMgr) {
        QVector<int> rootStructures = structureMgr->getRootNodes();
        for (int rootId : rootStructures) {
            const StructureData *rootData = structureMgr->getStructure(rootId);
            if (!rootData) continue;
            if (rootData->structureName == QString("项目名称")) {
                projectNode->id = rootData->id;
                if (!rootData->structureInt.isEmpty()) {
                    projectNode->displayText = rootData->structureInt;
                }
                break;
            }
        }
    }
    m_defaultRoot = projectNode;

    QHash<int, Node*> gaocengNodes;
    QHash<int, Node*> posNodes;
    QHash<QString, int> syntheticGaocengIds;
    QHash<QString, int> syntheticPosIds;
    int nextGaocengSyntheticId = -1;
    int nextPosSyntheticId = -10001;

    auto acquireGaocengNode = [&](int structureId, const QString &name) -> Node* {
        int nodeId = structureId;
        QString display = name.trimmed();
        if (nodeId <= 0) {
            QString key = display.isEmpty() ? QString("__UNASSIGNED_GAOCENG__") : display;
            nodeId = syntheticGaocengIds.value(key, 0);
            if (nodeId == 0) {
                nodeId = nextGaocengSyntheticId--;
                syntheticGaocengIds.insert(key, nodeId);
            }
        }

        Node *node = gaocengNodes.value(nodeId);
        if (!node) {
            // 首先按名称查找已存在的同名节点，避免重复创建
            if (!display.isEmpty()) {
                for (Node *existingNode : projectNode->children) {
                    if (existingNode->type == NodeType::Gaoceng && existingNode->displayText == display) {
                        // 复用已存在的同名节点
                        gaocengNodes.insert(nodeId, existingNode);
                        m_gaocengIndex.insert(nodeId, existingNode);
                        return existingNode;
                    }
                }
            }

            // 如果没有找到同名节点，创建新节点
            node = createNode(NodeType::Gaoceng, nodeId, projectNode);
            node->displayText = display.isEmpty() ? QString("未分配高层") : display;
            gaocengNodes.insert(nodeId, node);
            m_gaocengIndex.insert(nodeId, node);
        }
        return node;
    };

    auto acquirePosNode = [&](Node *gaocengNode, int structureId, const QString &name) -> Node* {
        if (!gaocengNode) gaocengNode = projectNode;
        int parentId = gaocengNode->id;
        int nodeId = structureId;
        QString display = name.trimmed();
        if (nodeId <= 0) {
            QString key = QString::number(parentId) + "|" + (display.isEmpty() ? QString("__UNASSIGNED_POS__") : display);
            nodeId = syntheticPosIds.value(key, 0);
            if (nodeId == 0) {
                nodeId = nextPosSyntheticId--;
                syntheticPosIds.insert(key, nodeId);
            }
        }
        Node *node = posNodes.value(nodeId);
        if (!node) {
            // 在当前高层节点下按名称查找同名位置节点，避免重复创建
            if (!display.isEmpty()) {
                for (Node *existingNode : gaocengNode->children) {
                    if (existingNode->type == NodeType::Pos && existingNode->displayText == display) {
                        // 复用已存在的同名节点
                        posNodes.insert(nodeId, existingNode);
                        m_posIndex.insert(nodeId, existingNode);
                        return existingNode;
                    }
                }
            }

            // 如果没有找到同名节点，创建新节点
            node = createNode(NodeType::Pos, nodeId, gaocengNode);
            node->displayText = display.isEmpty() ? QString("未分配位置") : display;
            posNodes.insert(nodeId, node);
            m_posIndex.insert(nodeId, node);
        }
        return node;
    };

    // 一次性获取所有数据，避免嵌套循环
    if (equipmentMgr && symbolMgr) {
        // 预加载所有Symbol数据，按Equipment分组
        QHash<int, QVector<int>> equipmentToSymbols;
        QHash<int, const SymbolData*> symbolMap;
        QVector<int> allSymbolIds = symbolMgr->getAllSymbolIds();
        for (int symbolId : allSymbolIds) {
            const SymbolData *symbol = symbolMgr->getSymbol(symbolId);
            if (!symbol) continue;
            symbolMap.insert(symbolId, symbol);
            if (symbol->equipmentId > 0) {
                equipmentToSymbols[symbol->equipmentId].append(symbolId);
            }
        }

        // 获取所有Equipment数据
        QVector<int> equipmentIds = equipmentMgr->getAllEquipmentIds();
        std::sort(equipmentIds.begin(), equipmentIds.end(), [equipmentMgr](int lhs, int rhs) {
            const EquipmentData *l = equipmentMgr->getEquipment(lhs);
            const EquipmentData *r = equipmentMgr->getEquipment(rhs);
            QString lKey = l ? l->dt : QString();
            QString rKey = r ? r->dt : QString();
            return lKey.localeAwareCompare(rKey) < 0;
        });

        // 用缓存避免重复查询Structure
        QHash<int, const StructureData*> structureCache;

        for (int equipmentId : equipmentIds) {
            const EquipmentData *equipment = equipmentMgr->getEquipment(equipmentId);
            if (!equipment) continue;

            // 从缓存获取Structure，避免重复查询
            const StructureData *posStructure = structureCache.contains(equipment->structureId)
                ? structureCache.value(equipment->structureId)
                : structureMgr ? structureMgr->getStructure(equipment->structureId) : nullptr;
            if (posStructure && !structureCache.contains(equipment->structureId)) {
                structureCache.insert(equipment->structureId, posStructure);
            }
            int posStructureId = posStructure ? posStructure->id : equipment->structureId;
            QString posName = posStructure ? posStructure->structureInt : equipment->pos;

            int gaocengStructureId = posStructure ? posStructure->parentId : 0;
            const StructureData *gaocengStructure = structureCache.contains(gaocengStructureId)
                ? structureCache.value(gaocengStructureId)
                : structureMgr ? structureMgr->getStructure(gaocengStructureId) : nullptr;
            if (gaocengStructure && !structureCache.contains(gaocengStructureId)) {
                structureCache.insert(gaocengStructureId, gaocengStructure);
            }
            QString gaocengName = gaocengStructure ? gaocengStructure->structureInt : equipment->gaoceng;

            Node *gaocengNode = acquireGaocengNode(gaocengStructureId, gaocengName);
            Node *posNode = nullptr;
            if (posStructureId > 0 || !posName.isEmpty()) {
                posNode = acquirePosNode(gaocengNode, posStructureId, posName);
            } else {
                // 即使位置为空，也创建"未分配位置"节点，保持层级一致性
                posNode = acquirePosNode(gaocengNode, 0, QString("未分配位置"));
            }

            Node *equipmentParent = posNode ? posNode : gaocengNode;
            if (!equipmentParent) equipmentParent = projectNode;

            Node *equipmentNode = createNode(NodeType::Equipment, equipmentId, equipmentParent);
            equipmentNode->displayText = equipment->displayText;
            m_equipmentIndex.insert(equipmentId, equipmentNode);

            // 直接从预加载的数据获取Symbol
            QVector<int> symbolIds = equipmentToSymbols.value(equipmentId);
            for (int symbolId : symbolIds) {
                const SymbolData *symbol = symbolMap.value(symbolId);
                if (!symbol) continue;
                Node *symbolNode = createNode(NodeType::Symbol, symbolId, equipmentNode);
                symbolNode->displayText = buildSymbolDisplayText(*symbol);
                if (symbol->symbol.isEmpty() && symbol->funDefine != QString("黑盒") && symbol->funDefine != QString("PLC 盒子")) {
                    symbolNode->symbolVisualState = 2;
                } else if (symbol->isInserted()) {
                    symbolNode->symbolVisualState = 0;
                } else {
                    symbolNode->symbolVisualState = 1;
                }
                m_symbolIndex.insert(symbolId, symbolNode);
            }
        }
    }

    sortChildren(projectNode);

    endResetModel();
}

QModelIndex EquipmentTreeModel::indexForEquipment(int equipmentId) const
{
    return indexFromNode(m_equipmentIndex.value(equipmentId));
}

QModelIndex EquipmentTreeModel::indexForSymbol(int symbolId) const
{
    return indexFromNode(m_symbolIndex.value(symbolId));
}

QModelIndex EquipmentTreeModel::indexForStructure(NodeType type, int structureId) const
{
    if (type == NodeType::Gaoceng) {
        return indexFromNode(m_gaocengIndex.value(structureId));
    }
    if (type == NodeType::Pos) {
        return indexFromNode(m_posIndex.value(structureId));
    }
    return QModelIndex();
}

QModelIndex EquipmentTreeModel::index(int row, int column, const QModelIndex &parent) const
{
    if (!hasIndex(row, column, parent)) return QModelIndex();
    Node *parentNode = parent.isValid() ? static_cast<Node*>(parent.internalPointer()) : nullptr;
    Node *childNode = parentNode ? parentNode->children.value(row, nullptr) : m_rootNodes.value(row, nullptr);
    if (!childNode) return QModelIndex();
    return createIndex(row, column, childNode);
}

QModelIndex EquipmentTreeModel::parent(const QModelIndex &child) const
{
    if (!child.isValid()) return QModelIndex();
    Node *childNode = static_cast<Node*>(child.internalPointer());
    Node *parentNode = childNode ? childNode->parent : nullptr;
    if (!parentNode) return QModelIndex();
    int row = parentNode->parent ? parentNode->parent->children.indexOf(parentNode)
                                 : m_rootNodes.indexOf(parentNode);
    if (row < 0) return QModelIndex();
    return createIndex(row, 0, parentNode);
}

int EquipmentTreeModel::rowCount(const QModelIndex &parent) const
{
    if (parent.column() > 0) return 0;
    if (!parent.isValid()) {
        return m_rootNodes.size();
    }
    Node *parentNode = static_cast<Node*>(parent.internalPointer());
    return parentNode ? parentNode->children.size() : 0;
}

int EquipmentTreeModel::columnCount(const QModelIndex &) const
{
    return 1;
}

QVariant EquipmentTreeModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid()) return QVariant();
    Node *node = static_cast<Node*>(index.internalPointer());
    switch (role) {
    case Qt::DisplayRole:
        return node->displayText;
    case Qt::DecorationRole:
        return iconForNode(node);
    case Qt::WhatsThisRole:
        return whatsThisForNode(node);
    case Qt::UserRole:
        return node->id;
    default:
        return QVariant();
    }
}

Qt::ItemFlags EquipmentTreeModel::flags(const QModelIndex &index) const
{
    if (!index.isValid()) return Qt::NoItemFlags;
    Node *node = static_cast<Node*>(index.internalPointer());
    Qt::ItemFlags base = Qt::ItemIsEnabled | Qt::ItemIsSelectable;
    if (node->type == NodeType::Symbol) {
        base |= Qt::ItemIsDragEnabled;
    }
    return base;
}

EquipmentTreeModel::Node* EquipmentTreeModel::createNode(NodeType type, int id, Node *parent)
{
    auto node = std::make_unique<Node>();
    node->type = type;
    node->id = id;
    node->parent = parent;
    Node *raw = node.get();
    if (parent) {
        parent->children.append(raw);
    } else {
        m_rootNodes.append(raw);
    }
    m_nodeStorage.push_back(std::move(node));
    return raw;
}

QString EquipmentTreeModel::whatsThisForNode(const Node *node) const
{
    switch (node->type) {
    case NodeType::Project: return QString("项目");
    case NodeType::Gaoceng: return QString("高层");
    case NodeType::Pos: return QString("位置");
    case NodeType::Equipment: return QString("元件");
    case NodeType::Symbol: return QString("功能子块");
    }
    return QString();
}

QIcon EquipmentTreeModel::iconForNode(const Node *node) const
{
    static QIcon projectIcon(QString("C:/TBD/data/项目图标.png"));
    static QIcon gaocengIcon(QString("C:/TBD/data/高层图标.png"));
    static QIcon posIcon(QString("C:/TBD/data/位置图标.png"));
    static QIcon equipmentIcon(QString("C:/TBD/data/元件图标.png"));
    static QIcon symbolInsertedIcon(QString("C:/TBD/data/逻辑支路图标_已插入.png"));
    static QIcon symbolPendingIcon(QString("C:/TBD/data/逻辑支路图标_未插入.png"));
    static QIcon symbolDisabledIcon(QString("C:/TBD/data/逻辑支路图标_不可插入.png"));

    switch (node->type) {
    case NodeType::Project: return projectIcon;
    case NodeType::Gaoceng: return gaocengIcon;
    case NodeType::Pos: return posIcon;
    case NodeType::Equipment: return equipmentIcon;
    case NodeType::Symbol:
        if (node->symbolVisualState == 2) return symbolDisabledIcon;
        if (node->symbolVisualState == 1) return symbolPendingIcon;
        return symbolInsertedIcon;
    }
    return QIcon();
}

QString EquipmentTreeModel::buildSymbolDisplayText(const SymbolData &symbol) const
{
    QString text;
    if (!symbol.designation.isEmpty()) {
        text += symbol.designation + ":";
    }
    for (int i = 0; i < symbol.connNums.size(); ++i) {
        if (i > 0) text += QString(" ￤ ");
        text += symbol.connNums.at(i);
    }

    auto appendFunDefine = [&](const QString &prefix) {
        if (!symbol.funDefine.isEmpty()) {
            text += prefix + symbol.funDefine;
        }
    };

    if (symbol.symbol.isEmpty() && symbol.funDefine != QString("黑盒") && symbol.funDefine != QString("PLC 盒子")) {
        appendFunDefine(QString("-"));
    } else if (symbol.isInserted()) {
        QString pageName;
        if (m_projectDataModel && m_projectDataModel->pageManager()) {
            const PageData *page = m_projectDataModel->pageManager()->getPage(symbol.pageId);
            if (page) pageName = page->pageName;
        }
        if (!pageName.isEmpty()) {
            text += "(" + pageName + ")";
        }
        appendFunDefine(QString());
    } else {
        appendFunDefine(QString("-"));
    }

    return text;
}

QModelIndex EquipmentTreeModel::indexFromNode(Node *node) const
{
    if (!node) return QModelIndex();
    Node *parentNode = node->parent;
    int row = -1;
    if (parentNode) {
        row = parentNode->children.indexOf(node);
    } else {
        row = m_rootNodes.indexOf(node);
    }
    if (row < 0) return QModelIndex();
    return createIndex(row, 0, node);
}

void EquipmentTreeModel::sortChildren(Node *node)
{
    if (!node) return;
    std::sort(node->children.begin(), node->children.end(), [](Node *a, Node *b) {
        return a->displayText.localeAwareCompare(b->displayText) < 0;
    });
    for (Node *child : node->children) {
        sortChildren(child);
    }
}
