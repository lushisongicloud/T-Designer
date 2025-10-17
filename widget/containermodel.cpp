#include "widget/containermodel.h"
#include <QBrush>
#include <algorithm>
#include <functional>

namespace {

QString typeToText(ContainerType type)
{
    switch (type) {
    case ContainerType::System: return QString("System");
    case ContainerType::Subsystem: return QString("Subsystem");
    case ContainerType::LRU: return QString("LRU");
    case ContainerType::SRU: return QString("SRU");
    case ContainerType::Module: return QString("Module");
    case ContainerType::Submodule: return QString("Submodule");
    case ContainerType::Component: return QString("Component");
    }
    return {};
}

}

ContainerModel::ContainerModel(QObject *parent)
    : QAbstractItemModel(parent)
    , m_repo(QSqlDatabase::database())
    , m_root(new ContainerNode{})
    , m_sortColumn(1)
    , m_sortOrder(Qt::AscendingOrder)
{
    m_repo.ensureTables();
    buildTree();
}

ContainerModel::~ContainerModel()
{
    delete m_root;
}

void ContainerModel::setDatabase(const QSqlDatabase &db)
{
    m_repo = ContainerRepository(db);
    m_repo.ensureTables();
    buildTree();
}

void ContainerModel::buildTree()
{
    beginResetModel();
    qDeleteAll(m_root->children);
    m_root->children.clear();

    const auto roots = m_repo.fetchRoots();
    std::function<void(ContainerNode*)> populate = [&](ContainerNode *node) {
        const auto children = m_repo.fetchChildren(node->entity.id());
        for (const auto &child : children) {
            auto *childNode = new ContainerNode{child, node};
            node->children.append(childNode);
            populate(childNode);
        }
    };

    for (const auto &rootEntity : roots) {
        auto *rootNode = new ContainerNode{rootEntity, m_root};
        populate(rootNode);
        m_root->children.append(rootNode);
    }

    std::function<void(ContainerNode*)> sortNode = [&](ContainerNode *node) {
        if (node->children.isEmpty()) return;
        auto comparator = [&](ContainerNode *a, ContainerNode *b) {
            if (m_sortColumn == 1) {
                int lhs = static_cast<int>(a->entity.type());
                int rhs = static_cast<int>(b->entity.type());
                if (lhs == rhs) {
                    int cmp = QString::localeAwareCompare(a->entity.name(), b->entity.name());
                    return m_sortOrder == Qt::AscendingOrder ? cmp < 0 : cmp > 0;
                }
                return m_sortOrder == Qt::AscendingOrder ? lhs < rhs : lhs > rhs;
            }
            int cmp = QString::localeAwareCompare(a->entity.name(), b->entity.name());
            return m_sortOrder == Qt::AscendingOrder ? cmp < 0 : cmp > 0;
        };
        std::sort(node->children.begin(), node->children.end(), comparator);
        for (ContainerNode *child : node->children) sortNode(child);
    };
    sortNode(m_root);
    endResetModel();
}

QModelIndex ContainerModel::index(int row, int column, const QModelIndex &parent) const
{
    if (row < 0 || column < 0 || column >= 2) return {};
    ContainerNode *parentNode = nodeFromIndex(parent);
    if (!parentNode) parentNode = m_root;
    if (row >= parentNode->children.size()) return {};
    return createIndex(row, column, parentNode->children.at(row));
}

QModelIndex ContainerModel::parent(const QModelIndex &child) const
{
    if (!child.isValid()) return {};
    auto *node = static_cast<ContainerNode*>(child.internalPointer());
    if (!node || !node->parent || node->parent == m_root) return {};
    ContainerNode *parentNode = node->parent;
    ContainerNode *grandParent = parentNode->parent;
    int row = 0;
    if (grandParent)
        row = grandParent->children.indexOf(parentNode);
    else
        row = m_root->children.indexOf(parentNode);
    if (row < 0) row = 0;
    return createIndex(row, 0, parentNode);
}

int ContainerModel::rowCount(const QModelIndex &parent) const
{
    ContainerNode *parentNode = nodeFromIndex(parent);
    if (!parentNode) parentNode = m_root;
    return parentNode->children.size();
}

QVariant ContainerModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid()) return {};
    auto *node = static_cast<ContainerNode*>(index.internalPointer());
    if (!node) return {};

    if (role == Qt::DisplayRole || role == Qt::EditRole) {
        if (index.column() == 0) return node->entity.name();
        if (index.column() == 1) return typeToText(node->entity.type());
    }
    return {};
}

QVariant ContainerModel::headerData(int section, Qt::Orientation orientation, int role) const
{
    if (orientation == Qt::Horizontal && role == Qt::DisplayRole) {
        if (section == 0) return tr("Name");
        if (section == 1) return tr("Type");
    }
    return {};
}

Qt::ItemFlags ContainerModel::flags(const QModelIndex &index) const
{
    if (!index.isValid()) return Qt::NoItemFlags;
    Qt::ItemFlags f = Qt::ItemIsEnabled | Qt::ItemIsSelectable;
    if (index.column() == 0) f |= Qt::ItemIsEditable;
    return f;
}

bool ContainerModel::setData(const QModelIndex &index, const QVariant &value, int role)
{
    if (role != Qt::EditRole || !index.isValid() || index.column() != 0) return false;
    auto *node = static_cast<ContainerNode*>(index.internalPointer());
    if (!node) return false;
    node->entity.setName(value.toString().trimmed());
    if (!m_repo.update(node->entity)) return false;
    emit dataChanged(index, index, {Qt::DisplayRole, Qt::EditRole});
    return true;
}

void ContainerModel::reload()
{
    buildTree();
}

void ContainerModel::sort(int column, Qt::SortOrder order)
{
    if (m_sortColumn == column && m_sortOrder == order) return;
    m_sortColumn = column;
    m_sortOrder = order;
    buildTree();
}

bool ContainerModel::addChild(const QModelIndex &parent, const QString &name, ContainerType type)
{
    ContainerNode *parentNode = nodeFromIndex(parent);
    int parentId = 0;
    if (!parentNode)
        parentNode = m_root;
    else
        parentId = parentNode->entity.id();

    if (parentNode != m_root) {
        if (!ContainerRepository::canContain(parentNode->entity.type(), type)) return false;
    } else {
        if (type != ContainerType::System) return false;
    }

    ContainerEntity entity;
    entity.setName(name);
    entity.setType(type);
    entity.setParentId(parentId);
    entity.setOrderIndex(parentNode->children.size());
    if (!m_repo.insert(entity)) return false;

    int row = parentNode->children.size();
    beginInsertRows(parent, row, row);
    auto *node = new ContainerNode{entity, parentNode};
    parentNode->children.append(node);
    endInsertRows();
    return true;
}

bool ContainerModel::removeAt(const QModelIndex &index)
{
    if (!index.isValid()) return false;
    auto *node = static_cast<ContainerNode*>(index.internalPointer());
    if (!node) return false;
    ContainerNode *parentNode = node->parent ? node->parent : m_root;
    int row = index.row();
    if (!m_repo.remove(node->entity.id())) return false;
    beginRemoveRows(parent(index), row, row);
    parentNode->children.remove(row);
    delete node;
    endRemoveRows();
    return true;
}

ContainerEntity ContainerModel::entityForIndex(const QModelIndex &index) const
{
    auto *node = nodeFromIndex(index);
    if (!node) return {};
    return node->entity;
}

ContainerNode *ContainerModel::nodeFromIndex(const QModelIndex &index) const
{
    if (!index.isValid()) return nullptr;
    return static_cast<ContainerNode*>(index.internalPointer());
}
