#ifndef CONTAINERREPOSITORY_H
#define CONTAINERREPOSITORY_H

#include <QList>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QVariant>
#include <QDebug>
#include "DO/containerentity.h"

class ContainerRepository
{
public:
    explicit ContainerRepository(const QSqlDatabase &db = QSqlDatabase::database());

    bool ensureTables();

    QList<ContainerEntity> fetchRoots();
    QList<ContainerEntity> fetchChildren(int parentId);
    QList<ContainerEntity> fetchAll();
    ContainerEntity getById(int id);

    bool insert(ContainerEntity &entity);
    bool update(const ContainerEntity &entity);
    bool remove(int id);

    int componentContainerIdForEquipment(int equipmentId);
    int createComponentContainerForEquipment(int equipmentId, const QString &displayName,
                                             const QString &equipmentType, const QString &equipmentName);
    bool deleteComponentContainerForEquipment(int equipmentId);
    bool attachToParent(int containerId, int parentContainerId);

    int highestAncestorId(int containerId);
    QList<int> ancestorChainIds(int nodeId);

    static bool canContain(ContainerType parentType, ContainerType childType);

private:
    bool ensureEquipmentLinkTable();
    ContainerEntity fromQuery(const QSqlQuery &query) const;
    bool isAncestorOf(int ancestorId, int nodeId);

    QSqlDatabase m_db;
};

#endif // CONTAINERREPOSITORY_H
