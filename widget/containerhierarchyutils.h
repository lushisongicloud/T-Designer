#ifndef CONTAINERHIERARCHYUTILS_H
#define CONTAINERHIERARCHYUTILS_H

#include <QSqlDatabase>
#include <QString>
#include <QStringList>
#include <QList>
#include "BO/containerrepository.h"
#include "BO/function/functioninfo.h"

namespace ContainerHierarchy {

struct EquipmentMetadata {
    QString dt;
    QString type;
    QString name;
};

EquipmentMetadata fetchEquipmentMetadata(const QSqlDatabase &db, int equipmentId);
QString defaultComponentName(const EquipmentMetadata &meta, int equipmentId);
int ensureComponentContainer(ContainerRepository &repo, const QSqlDatabase &db, int equipmentId);
QString describeContainer(ContainerRepository &repo, const ContainerEntity &entity);
QString containerTypeTextZh(ContainerType type);
QString containerTypeTextEn(ContainerType type);
QList<ContainerType> parentCandidateTypes(ContainerType childType);
QList<ContainerType> childCandidateTypes(ContainerType parentType);
bool detachComponentContainer(ContainerRepository &repo, int componentContainerId);
bool attachComponentsToTarget(ContainerRepository &repo, const QList<int> &componentContainerIds, int targetId);

QMap<QString, FunctionInfo> fetchFunctionInfoMap(const QSqlDatabase &db);
QHash<int, QStringList> defaultFunctionMapping(const ContainerEntity &entity, const QMap<QString, FunctionInfo> &functions);

}

#endif // CONTAINERHIERARCHYUTILS_H
