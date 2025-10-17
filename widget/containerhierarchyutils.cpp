#include "widget/containerhierarchyutils.h"
#include <QSqlQuery>
#include <QVariant>
#include <QDebug>
#pragma execution_character_set("utf-8")
namespace ContainerHierarchy {

namespace {

QStringList collectComponentNames(ContainerRepository &repo, int containerId, int &total)
{
    QStringList names;
    QList<ContainerEntity> stack = repo.fetchChildren(containerId);
    while (!stack.isEmpty()) {
        ContainerEntity entity = stack.takeFirst();
        if (entity.type() == ContainerType::Component) {
            ++total;
            if (names.size() < 10) names.append(entity.name());
        } else {
            const auto children = repo.fetchChildren(entity.id());
            for (const auto &child : children) stack.append(child);
        }
    }
    return names;
}

}

EquipmentMetadata fetchEquipmentMetadata(const QSqlDatabase &db, int equipmentId)
{
    EquipmentMetadata meta;
    QSqlQuery query(db);
    query.prepare("SELECT DT,Type,Name FROM Equipment WHERE Equipment_ID=:id");
    query.bindValue(":id", equipmentId);
    if (query.exec() && query.next()) {
        meta.dt = query.value(0).toString().trimmed();
        meta.type = query.value(1).toString().trimmed();
        meta.name = query.value(2).toString().trimmed();
    }
    return meta;
}

QString defaultComponentName(const EquipmentMetadata &meta, int equipmentId)
{
    if (!meta.dt.isEmpty()) return meta.dt;
    if (!meta.name.isEmpty()) return meta.name;
    return QString("Component-%1").arg(equipmentId);
}

int ensureComponentContainer(ContainerRepository &repo, const QSqlDatabase &db, int equipmentId)
{
    EquipmentMetadata meta = fetchEquipmentMetadata(db, equipmentId);
    const QString displayName = defaultComponentName(meta, equipmentId);

    int existing = repo.componentContainerIdForEquipment(equipmentId);
    if (existing != 0) {
        ContainerEntity entity = repo.getById(existing);
        bool changed = false;
        if (!displayName.isEmpty() && entity.name() != displayName) {
            entity.setName(displayName);
            changed = true;
        }
        if (entity.equipmentId() != equipmentId) {
            entity.setEquipmentId(equipmentId);
            changed = true;
        }
        if (entity.equipmentType() != meta.type) {
            entity.setEquipmentType(meta.type);
            changed = true;
        }
        if (entity.equipmentName() != meta.name) {
            entity.setEquipmentName(meta.name);
            changed = true;
        }
        if (changed) repo.update(entity);
        return existing;
    }

    ContainerEntity entity;
    entity.setName(displayName);
    entity.setType(ContainerType::Component);
    entity.setParentId(0);
    entity.setEquipmentId(equipmentId);
    entity.setEquipmentType(meta.type);
    entity.setEquipmentName(meta.name);
    if (!repo.insert(entity)) return 0;

    QSqlQuery insertQuery(db);
    insertQuery.prepare("INSERT OR REPLACE INTO equipment_containers(equipment_id, container_id) VALUES(:eid,:cid)");
    insertQuery.bindValue(":eid", equipmentId);
    insertQuery.bindValue(":cid", entity.id());
    if (!insertQuery.exec()) {
        qWarning() << insertQuery.lastError();
        return 0;
    }
    return entity.id();
}

QString describeContainer(ContainerRepository &repo, const ContainerEntity &entity)
{
    const QString typeZh = containerTypeTextZh(entity.type());
    if (entity.type() == ContainerType::Component) {
        return QString("%1：%2").arg(typeZh, entity.name());
    }

    int total = 0;
    QStringList componentNames = collectComponentNames(repo, entity.id(), total);
    QString suffix = containerTypeTextEn(entity.type());
    if (!componentNames.isEmpty()) {
        suffix += QString("-") + componentNames.join(",");
        if (total > componentNames.size()) suffix += QString("...等共%1项").arg(total);
    }
    QString value = suffix;
    if (!entity.name().trimmed().isEmpty()) value = entity.name().trimmed() + QString("-") + suffix;
    return QString("%1：%2").arg(typeZh, value);
}

QString containerTypeTextZh(ContainerType type)
{
    switch (type) {
    case ContainerType::System: return QString("系统");
    case ContainerType::Subsystem: return QString("子系统");
    case ContainerType::LRU: return QString("LRU");
    case ContainerType::SRU: return QString("SRU");
    case ContainerType::Module: return QString("模块");
    case ContainerType::Submodule: return QString("子模块");
    case ContainerType::Component: return QString("元件");
    }
    return {};
}

QString containerTypeTextEn(ContainerType type)
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

QList<ContainerType> parentCandidateTypes(ContainerType childType)
{
    QList<ContainerType> result;
    for (int value = 0; value < static_cast<int>(childType); ++value)
        result.append(static_cast<ContainerType>(value));
    return result;
}

QList<ContainerType> childCandidateTypes(ContainerType parentType)
{
    QList<ContainerType> result;
    for (int value = static_cast<int>(parentType) + 1; value <= static_cast<int>(ContainerType::Component); ++value)
        result.append(static_cast<ContainerType>(value));
    return result;
}

bool detachComponentContainer(ContainerRepository &repo, int componentContainerId)
{
    ContainerEntity entity = repo.getById(componentContainerId);
    if (entity.id() == 0) return false;
    if (entity.parentId() == 0) return true;
    return repo.attachToParent(componentContainerId, 0);
}

}


bool ContainerHierarchy::attachComponentsToTarget(ContainerRepository &repo, const QList<int> &componentContainerIds, int targetId)
{
    bool success = true;
    for (int cid : componentContainerIds) {
        if (!repo.attachToParent(cid, targetId)) success = false;
    }
    return success;
}
