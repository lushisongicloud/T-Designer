#include "BO/containerrepository.h"

namespace {

QString typeColumnList()
{
    return QString(
        "id,name,type,parent_id,order_index,analysis_depth,"
        "interface_json,behavior_smt,fault_modes_json,tests_json,analysis_json,"
        "equipment_id,equipment_type,equipment_name");
}

}

ContainerRepository::ContainerRepository(const QSqlDatabase &db)
    : m_db(db)
{
}

bool ContainerRepository::ensureTables()
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        qWarning() << "ContainerRepository: database is not open";
        return false;
    }

    QSqlQuery q(m_db);
    q.exec("PRAGMA foreign_keys = ON");

    const char *ddl =
        "CREATE TABLE IF NOT EXISTS containers ("
        " id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " name TEXT NOT NULL,"
        " type INTEGER NOT NULL,"
        " parent_id INTEGER,"
        " order_index INTEGER DEFAULT 0,"
        " analysis_depth INTEGER DEFAULT 0,"
        " interface_json TEXT,"
        " behavior_smt TEXT,"
        " fault_modes_json TEXT,"
        " tests_json TEXT,"
        " analysis_json TEXT,"
        " equipment_id INTEGER,"
        " equipment_type TEXT,"
        " equipment_name TEXT,"
        " UNIQUE(name, parent_id),"
        " FOREIGN KEY(parent_id) REFERENCES containers(id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddl)) {
        qWarning() << "Failed to create containers table:" << q.lastError();
        return false;
    }

    if (!q.exec("CREATE INDEX IF NOT EXISTS idx_containers_parent ON containers(parent_id, order_index)")) {
        qWarning() << "Failed to create containers index:" << q.lastError();
        return false;
    }

    // ensure new columns exist when upgrading
    auto ensureColumn = [&](const QString &column, const QString &alterSql) {
        QSqlQuery pragma(m_db);
        if (!pragma.exec("PRAGMA table_info(containers)")) {
            qWarning() << "Failed to query containers schema:" << pragma.lastError();
            return false;
        }
        bool exists = false;
        while (pragma.next()) {
            if (pragma.value(1).toString().compare(column, Qt::CaseInsensitive) == 0) {
                exists = true;
                break;
            }
        }
        if (exists) return true;
        if (!q.exec(alterSql)) {
            qWarning() << "Failed to alter containers column" << column << q.lastError();
            return false;
        }
        return true;
    };

    if (!ensureColumn("tests_json", "ALTER TABLE containers ADD COLUMN tests_json TEXT")) return false;
    if (!ensureColumn("analysis_json", "ALTER TABLE containers ADD COLUMN analysis_json TEXT")) return false;
    if (!ensureColumn("equipment_id", "ALTER TABLE containers ADD COLUMN equipment_id INTEGER")) return false;
    if (!ensureColumn("equipment_type", "ALTER TABLE containers ADD COLUMN equipment_type TEXT")) return false;
    if (!ensureColumn("equipment_name", "ALTER TABLE containers ADD COLUMN equipment_name TEXT")) return false;

    return ensureEquipmentLinkTable();
}

bool ContainerRepository::ensureEquipmentLinkTable()
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;
    QSqlQuery q(m_db);
    const char *ddl =
        "CREATE TABLE IF NOT EXISTS equipment_containers ("
        " equipment_id INTEGER PRIMARY KEY,"
        " container_id INTEGER NOT NULL,"
        " FOREIGN KEY(container_id) REFERENCES containers(id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddl)) {
        qWarning() << "Failed to create equipment_containers table:" << q.lastError();
        return false;
    }
    if (!q.exec("CREATE INDEX IF NOT EXISTS idx_eq_containers_container ON equipment_containers(container_id)")) {
        qWarning() << "Failed to create equipment_containers index:" << q.lastError();
        return false;
    }
    return true;
}

QList<ContainerEntity> ContainerRepository::fetchRoots()
{
    QList<ContainerEntity> list;
    QSqlQuery q(m_db);
    if (!q.exec(QString("SELECT %1 FROM containers WHERE parent_id IS NULL ORDER BY order_index, id").arg(typeColumnList()))) {
        qWarning() << q.lastError();
        return list;
    }
    while (q.next()) list.append(fromQuery(q));
    return list;
}

QList<ContainerEntity> ContainerRepository::fetchChildren(int parentId)
{
    QList<ContainerEntity> list;
    QSqlQuery q(m_db);
    q.prepare(QString("SELECT %1 FROM containers WHERE parent_id = :pid ORDER BY order_index, id").arg(typeColumnList()));
    q.bindValue(":pid", parentId);
    if (!q.exec()) {
        qWarning() << q.lastError();
        return list;
    }
    while (q.next()) list.append(fromQuery(q));
    return list;
}

QList<ContainerEntity> ContainerRepository::fetchAll()
{
    QList<ContainerEntity> list;
    QSqlQuery q(m_db);
    if (!q.exec(QString("SELECT %1 FROM containers ORDER BY parent_id, order_index, id").arg(typeColumnList()))) {
        qWarning() << q.lastError();
        return list;
    }
    while (q.next()) list.append(fromQuery(q));
    return list;
}

ContainerEntity ContainerRepository::getById(int id)
{
    QSqlQuery q(m_db);
    q.prepare(QString("SELECT %1 FROM containers WHERE id=:id").arg(typeColumnList()));
    q.bindValue(":id", id);
    if (!q.exec() || !q.next()) return {};
    return fromQuery(q);
}

bool ContainerRepository::insert(ContainerEntity &e)
{
    QSqlQuery q(m_db);
    q.prepare("INSERT INTO containers(name,type,parent_id,order_index,analysis_depth,interface_json,behavior_smt,fault_modes_json,tests_json,analysis_json,"
              "equipment_id,equipment_type,equipment_name)"
              " VALUES(:name,:type,:parent,:order,:depth,:iface,:smt,:faults,:tests,:analysis,:eqid,:eqtype,:eqname)");
    q.bindValue(":name", e.name());
    q.bindValue(":type", static_cast<int>(e.type()));
    if (e.parentId() == 0)
        q.bindValue(":parent", QVariant(QVariant::Int));
    else
        q.bindValue(":parent", e.parentId());
    q.bindValue(":order", e.orderIndex());
    q.bindValue(":depth", e.analysisDepth());
    q.bindValue(":iface", e.interfaceJson());
    q.bindValue(":smt", e.behaviorSmt());
    q.bindValue(":faults", e.faultModesJson());
    q.bindValue(":tests", e.testsJson());
    q.bindValue(":analysis", e.analysisJson());
    if (e.equipmentId() == 0)
        q.bindValue(":eqid", QVariant(QVariant::Int));
    else
        q.bindValue(":eqid", e.equipmentId());
    q.bindValue(":eqtype", e.equipmentType());
    q.bindValue(":eqname", e.equipmentName());
    if (!q.exec()) {
        qWarning() << q.lastError();
        return false;
    }
    e.setId(q.lastInsertId().toInt());
    return true;
}

bool ContainerRepository::update(const ContainerEntity &e)
{
    QSqlQuery q(m_db);
    q.prepare("UPDATE containers SET name=:name, type=:type, parent_id=:parent, order_index=:order, analysis_depth=:depth,"
              "interface_json=:iface, behavior_smt=:smt, fault_modes_json=:faults, tests_json=:tests, analysis_json=:analysis,"
              "equipment_id=:eqid, equipment_type=:eqtype, equipment_name=:eqname WHERE id=:id");
    q.bindValue(":id", e.id());
    q.bindValue(":name", e.name());
    q.bindValue(":type", static_cast<int>(e.type()));
    if (e.parentId() == 0)
        q.bindValue(":parent", QVariant(QVariant::Int));
    else
        q.bindValue(":parent", e.parentId());
    q.bindValue(":order", e.orderIndex());
    q.bindValue(":depth", e.analysisDepth());
    q.bindValue(":iface", e.interfaceJson());
    q.bindValue(":smt", e.behaviorSmt());
    q.bindValue(":faults", e.faultModesJson());
    q.bindValue(":tests", e.testsJson());
    q.bindValue(":analysis", e.analysisJson());
    if (e.equipmentId() == 0)
        q.bindValue(":eqid", QVariant(QVariant::Int));
    else
        q.bindValue(":eqid", e.equipmentId());
    q.bindValue(":eqtype", e.equipmentType());
    q.bindValue(":eqname", e.equipmentName());
    if (!q.exec()) {
        qWarning() << q.lastError();
        return false;
    }
    return true;
}

bool ContainerRepository::remove(int id)
{
    QSqlQuery q(m_db);
    q.prepare("DELETE FROM containers WHERE id=:id");
    q.bindValue(":id", id);
    if (!q.exec()) {
        qWarning() << q.lastError();
        return false;
    }
    return true;
}

int ContainerRepository::componentContainerIdForEquipment(int equipmentId)
{
    QSqlQuery q(m_db);
    q.prepare("SELECT container_id FROM equipment_containers WHERE equipment_id=:eid");
    q.bindValue(":eid", equipmentId);
    if (!q.exec()) {
        qWarning() << q.lastError();
        return 0;
    }
    if (q.next()) return q.value(0).toInt();
    return 0;
}

int ContainerRepository::createComponentContainerForEquipment(int equipmentId, const QString &displayName,
                                                             const QString &equipmentType, const QString &equipmentName)
{
    int existing = componentContainerIdForEquipment(equipmentId);
    if (existing != 0) {
        ContainerEntity current = getById(existing);
        bool changed = false;
        if (!displayName.isEmpty() && current.name() != displayName) { current.setName(displayName); changed = true; }
        if (current.equipmentId() != equipmentId) { current.setEquipmentId(equipmentId); changed = true; }
        if (current.equipmentType() != equipmentType) { current.setEquipmentType(equipmentType); changed = true; }
        if (current.equipmentName() != equipmentName) { current.setEquipmentName(equipmentName); changed = true; }
        if (changed) update(current);
        return existing;
    }

    ContainerEntity entity;
    entity.setName(displayName);
    entity.setType(ContainerType::Component);
    entity.setParentId(0);
    entity.setEquipmentId(equipmentId);
    entity.setEquipmentType(equipmentType);
    entity.setEquipmentName(equipmentName);
    if (!insert(entity)) return 0;

    QSqlQuery q(m_db);
    q.prepare("INSERT OR REPLACE INTO equipment_containers(equipment_id, container_id) VALUES(:eid,:cid)");
    q.bindValue(":eid", equipmentId);
    q.bindValue(":cid", entity.id());
    if (!q.exec()) {
        qWarning() << q.lastError();
        return 0;
    }
    return entity.id();
}

bool ContainerRepository::deleteComponentContainerForEquipment(int equipmentId)
{
    int cid = componentContainerIdForEquipment(equipmentId);
    if (cid == 0) return true;

    QSqlQuery q(m_db);
    q.prepare("DELETE FROM equipment_containers WHERE equipment_id=:eid");
    q.bindValue(":eid", equipmentId);
    if (!q.exec()) {
        qWarning() << q.lastError();
        return false;
    }
    return remove(cid);
}

bool ContainerRepository::attachToParent(int containerId, int parentContainerId)
{
    ContainerEntity child = getById(containerId);
    if (child.id() == 0) return false;

    if (parentContainerId == 0) {
        child.setParentId(0);
        return update(child);
    }

    ContainerEntity parent = getById(parentContainerId);
    if (parent.id() == 0) return false;

    if (!canContain(parent.type(), child.type())) return false;
    if (parent.id() == child.id()) return false;
    if (isAncestorOf(parent.id(), child.id())) return false;
    if (isAncestorOf(child.id(), parent.id())) return false;

    child.setParentId(parent.id());
    return update(child);
}

int ContainerRepository::highestAncestorId(int containerId)
{
    int current = containerId;
    int lastValid = current;
    while (current != 0) {
        ContainerEntity entity = getById(current);
        if (entity.id() == 0) break;
        lastValid = entity.id();
        if (entity.parentId() == 0) break;
        current = entity.parentId();
    }
    return lastValid;
}

QList<int> ContainerRepository::ancestorChainIds(int nodeId)
{
    QList<int> chain;
    int current = nodeId;
    while (current != 0) {
        ContainerEntity entity = getById(current);
        if (entity.id() == 0) break;
        chain.prepend(entity.id());
        current = entity.parentId();
    }
    return chain;
}

bool ContainerRepository::canContain(ContainerType parentType, ContainerType childType)
{
    if (parentType == childType) return false;
    return static_cast<int>(parentType) < static_cast<int>(childType);
}

ContainerEntity ContainerRepository::fromQuery(const QSqlQuery &query) const
{
    ContainerEntity entity;
    entity.setId(query.value(0).toInt());
    entity.setName(query.value(1).toString());
    entity.setType(static_cast<ContainerType>(query.value(2).toInt()));
    entity.setParentId(query.value(3).isNull() ? 0 : query.value(3).toInt());
    entity.setOrderIndex(query.value(4).toInt());
    entity.setAnalysisDepth(query.value(5).toInt());
    entity.setInterfaceJson(query.value(6).toString());
    entity.setBehaviorSmt(query.value(7).toString());
    entity.setFaultModesJson(query.value(8).toString());
    entity.setTestsJson(query.value(9).toString());
    entity.setAnalysisJson(query.value(10).toString());
    entity.setEquipmentId(query.value(11).isNull() ? 0 : query.value(11).toInt());
    entity.setEquipmentType(query.value(12).toString());
    entity.setEquipmentName(query.value(13).toString());
    return entity;
}

bool ContainerRepository::isAncestorOf(int ancestorId, int nodeId)
{
    if (ancestorId == 0 || nodeId == 0) return false;
    if (ancestorId == nodeId) return true;
    int current = nodeId;
    while (current != 0) {
        ContainerEntity entity = getById(current);
        if (entity.id() == 0) break;
        if (entity.parentId() == ancestorId) return true;
        current = entity.parentId();
    }
    return false;
}
