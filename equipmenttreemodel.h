#ifndef EQUIPMENTTREEMODEL_H
#define EQUIPMENTTREEMODEL_H

#include <QAbstractItemModel>
#include <QHash>
#include <QIcon>
#include <QVector>
#include <memory>
#include <vector>

class ProjectDataModel;
struct SymbolData;

class EquipmentTreeModel : public QAbstractItemModel
{
    Q_OBJECT

public:
    enum class NodeType {
        Project,
        Gaoceng,
        Pos,
        Equipment,
        Symbol
    };

    explicit EquipmentTreeModel(QObject *parent = nullptr);
    ~EquipmentTreeModel() override;

    void setProjectDataModel(ProjectDataModel *model);
    ProjectDataModel *projectDataModel() const { return m_projectDataModel; }

    void rebuild();

    QModelIndex indexForEquipment(int equipmentId) const;
    QModelIndex indexForSymbol(int symbolId) const;
    QModelIndex indexForStructure(NodeType type, int structureId) const;

    QModelIndex index(int row, int column, const QModelIndex &parent = QModelIndex()) const override;
    QModelIndex parent(const QModelIndex &child) const override;
    int rowCount(const QModelIndex &parent = QModelIndex()) const override;
    int columnCount(const QModelIndex &parent = QModelIndex()) const override;
    QVariant data(const QModelIndex &index, int role = Qt::DisplayRole) const override;
    Qt::ItemFlags flags(const QModelIndex &index) const override;

private:
    struct Node {
        NodeType type = NodeType::Project;
        int id = 0;
        Node *parent = nullptr;
        QVector<Node*> children;
        QString displayText;
        int symbolVisualState = 0; // 0: inserted, 1: pending, 2: disabled
    };

    Node* createNode(NodeType type, int id, Node *parent);
    void clear();
    QString whatsThisForNode(const Node *node) const;
    QIcon iconForNode(const Node *node) const;
    QString buildSymbolDisplayText(const SymbolData &symbol) const;
    QModelIndex indexFromNode(Node *node) const;
    void sortChildren(Node *node);

    ProjectDataModel *m_projectDataModel = nullptr;
    QVector<Node*> m_rootNodes;
    std::vector<std::unique_ptr<Node>> m_nodeStorage;
    QHash<int, Node*> m_gaocengIndex;
    QHash<int, Node*> m_posIndex;
    QHash<int, Node*> m_equipmentIndex;
    QHash<int, Node*> m_symbolIndex;
    Node *m_defaultRoot = nullptr;
};

#endif // EQUIPMENTTREEMODEL_H
