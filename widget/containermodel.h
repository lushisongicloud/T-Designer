#ifndef CONTAINERMODEL_H
#define CONTAINERMODEL_H

#include <QAbstractItemModel>
#include <QVector>
#include "BO/containerrepository.h"

struct ContainerNode {
    ContainerEntity entity;
    ContainerNode *parent = nullptr;
    QVector<ContainerNode*> children;
    ~ContainerNode() { qDeleteAll(children); }
};

class ContainerModel : public QAbstractItemModel
{
    Q_OBJECT
public:
    explicit ContainerModel(QObject *parent = nullptr);
    ~ContainerModel() override;

    QModelIndex index(int row, int column, const QModelIndex &parent) const override;
    QModelIndex parent(const QModelIndex &child) const override;
    int rowCount(const QModelIndex &parent) const override;
    int columnCount(const QModelIndex &parent) const override { Q_UNUSED(parent); return 2; }
    QVariant data(const QModelIndex &index, int role) const override;
    QVariant headerData(int section, Qt::Orientation orientation, int role) const override;
    Qt::ItemFlags flags(const QModelIndex &index) const override;
    bool setData(const QModelIndex &index, const QVariant &value, int role) override;

    void setDatabase(const QSqlDatabase &db);
    void reload();
    bool addChild(const QModelIndex &parent, const QString &name, ContainerType type);
    bool removeAt(const QModelIndex &index);
    ContainerEntity entityForIndex(const QModelIndex &index) const;

private:
    void buildTree();
    ContainerNode *nodeFromIndex(const QModelIndex &index) const;

    ContainerRepository m_repo;
    ContainerNode *m_root;
};

#endif // CONTAINERMODEL_H
