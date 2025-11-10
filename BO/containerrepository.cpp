
#include "BO/containerrepository.h"

bool ContainerRepository::ensureContainerSchema()
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;

    QSqlQuery q(m_db);
    const char *ddl =
        "CREATE TABLE IF NOT EXISTS container ("
        " container_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " project_structure_id INTEGER,"
        " name TEXT NOT NULL,"
        " level TEXT NOT NULL,"
        " source_equipment_id INTEGER,"
        " auto_generated INTEGER NOT NULL DEFAULT 0,"
        " description TEXT,"
        " fault_analysis_depth TEXT,"
        " inherits_from_container_id INTEGER,"
        " order_index INTEGER DEFAULT 0,"
        " analysis_depth INTEGER DEFAULT 0,"
        " interface_json TEXT,"
        " behavior_smt TEXT,"
        " fault_modes_json TEXT,"
        " tests_json TEXT,"
        " analysis_json TEXT,"
        " created_at TEXT DEFAULT CURRENT_TIMESTAMP,"
        " updated_at TEXT DEFAULT CURRENT_TIMESTAMP"
        ")";
    if (!q.exec(ddl)) {
        qWarning() << "Failed to create container table:" << q.lastError();
        return false;
    }

    if (!q.exec("CREATE INDEX IF NOT EXISTS idx_container_project ON container(project_structure_id)")) {
        qWarning() << "Failed to create container project index:" << q.lastError();
        return false;
    }
    if (!q.exec("CREATE INDEX IF NOT EXISTS idx_container_equipment ON container(source_equipment_id)")) {
        qWarning() << "Failed to create container equipment index:" << q.lastError();
        return false;
    }

    if (!ensureColumnExists("container", "order_index", "ALTER TABLE container ADD COLUMN order_index INTEGER DEFAULT 0")) return false;
    if (!ensureColumnExists("container", "analysis_depth", "ALTER TABLE container ADD COLUMN analysis_depth INTEGER DEFAULT 0")) return false;
    if (!ensureColumnExists("container", "interface_json", "ALTER TABLE container ADD COLUMN interface_json TEXT")) return false;
    if (!ensureColumnExists("container", "behavior_smt", "ALTER TABLE container ADD COLUMN behavior_smt TEXT")) return false;
    if (!ensureColumnExists("container", "fault_modes_json", "ALTER TABLE container ADD COLUMN fault_modes_json TEXT")) return false;
    if (!ensureColumnExists("container", "tests_json", "ALTER TABLE container ADD COLUMN tests_json TEXT")) return false;
    if (!ensureColumnExists("container", "analysis_json", "ALTER TABLE container ADD COLUMN analysis_json TEXT")) return false;
    if (!ensureColumnExists("container", "updated_at", "ALTER TABLE container ADD COLUMN updated_at TEXT DEFAULT CURRENT_TIMESTAMP")) return false;

    return true;
}

bool ContainerRepository::ensureHierarchySchema()
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;

    QSqlQuery q(m_db);
    const char *ddlHierarchy =
        "CREATE TABLE IF NOT EXISTS container_hierarchy ("
        " parent_id INTEGER NOT NULL,"
        " child_id INTEGER NOT NULL,"
        " relation_type TEXT DEFAULT 'contains',"
        " PRIMARY KEY(parent_id, child_id),"
        " FOREIGN KEY(parent_id) REFERENCES container(container_id) ON DELETE CASCADE,"
        " FOREIGN KEY(child_id) REFERENCES container(container_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlHierarchy)) {
        qWarning() << "Failed to create container_hierarchy table:" << q.lastError();
        return false;
    }

    if (!q.exec("CREATE INDEX IF NOT EXISTS idx_hierarchy_child ON container_hierarchy(child_id)")) {
        qWarning() << "Failed to create hierarchy index:" << q.lastError();
        return false;
    }

    if (!ensureColumnExists("container_hierarchy", "relation_type", "ALTER TABLE container_hierarchy ADD COLUMN relation_type TEXT DEFAULT 'contains'")) return false;

    const char *ddlInterface =
        "CREATE TABLE IF NOT EXISTS container_interface ("
        " interface_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " container_id INTEGER NOT NULL,"
        " name TEXT NOT NULL,"
        " direction TEXT NOT NULL,"
        " signal_category TEXT NOT NULL,"
        " signal_subtype TEXT,"
        " physical_domain TEXT,"
        " default_unit TEXT,"
        " description TEXT,"
        " inherits_interface_id INTEGER,"
        " FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlInterface)) {
        qWarning() << "Failed to create container_interface table:" << q.lastError();
        return false;
    }

    const char *ddlBinding =
        "CREATE TABLE IF NOT EXISTS container_interface_binding ("
        " binding_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " interface_id INTEGER NOT NULL,"
        " equipment_id INTEGER,"
        " terminal_id INTEGER,"
        " connect_line_id INTEGER,"
        " binding_role TEXT,"
        " FOREIGN KEY(interface_id) REFERENCES container_interface(interface_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlBinding)) {
        qWarning() << "Failed to create container_interface_binding table:" << q.lastError();
        return false;
    }

    const char *ddlState =
        "CREATE TABLE IF NOT EXISTS container_state ("
        " state_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " container_id INTEGER NOT NULL,"
        " name TEXT NOT NULL,"
        " state_type TEXT NOT NULL,"
        " derived_from_children INTEGER NOT NULL DEFAULT 0,"
        " probability REAL,"
        " rationale TEXT,"
        " analysis_scope TEXT,"
        " FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlState)) {
        qWarning() << "Failed to create container_state table:" << q.lastError();
        return false;
    }

    const char *ddlStateBehavior =
        "CREATE TABLE IF NOT EXISTS container_state_behavior ("
        " behavior_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " state_id INTEGER NOT NULL,"
        " representation TEXT NOT NULL,"
        " expression TEXT NOT NULL,"
        " notes TEXT,"
        " FOREIGN KEY(state_id) REFERENCES container_state(state_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlStateBehavior)) {
        qWarning() << "Failed to create container_state_behavior table:" << q.lastError();
        return false;
    }

    const char *ddlStateInterface =
        "CREATE TABLE IF NOT EXISTS container_state_interface ("
        " id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " state_id INTEGER NOT NULL,"
        " interface_id INTEGER NOT NULL,"
        " constraint TEXT,"
        " FOREIGN KEY(state_id) REFERENCES container_state(state_id) ON DELETE CASCADE,"
        " FOREIGN KEY(interface_id) REFERENCES container_interface(interface_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlStateInterface)) {
        qWarning() << "Failed to create container_state_interface table:" << q.lastError();
        return false;
    }

    return true;
}

bool ContainerRepository::ensureComponentLinkSchema()
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;

    QSqlQuery q(m_db);
    const char *ddlComponent =
        "CREATE TABLE IF NOT EXISTS container_component ("
        " container_id INTEGER NOT NULL,"
        " equipment_id INTEGER NOT NULL,"
        " role TEXT,"
        " PRIMARY KEY(container_id, equipment_id),"
        " FOREIGN KEY(container_id) REFERENCES container(container_id) ON DELETE CASCADE"
        ")";
    if (!q.exec(ddlComponent)) {
        qWarning() << "Failed to create container_component table:" << q.lastError();
        return false;
    }

    if (!q.exec("CREATE INDEX IF NOT EXISTS idx_container_component_equipment ON container_component(equipment_id)")) {
        qWarning() << "Failed to create container_component index:" << q.lastError();
        return false;
    }

    return true;
}

bool ContainerRepository::ensureColumnExists(const QString &table, const QString &column, const QString &alterSql)
{
    QSqlQuery pragma(m_db);
    if (!pragma.exec(QString("PRAGMA table_info(%1)").arg(table))) {
        qWarning() << "Failed to inspect table" << table << pragma.lastError();
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

    QSqlQuery alter(m_db);
    if (!alter.exec(alterSql)) {
        qWarning() << "Failed to alter table" << table << "with" << alterSql << alter.lastError();
        return false;
    }
    return true;
}

namespace {

QString selectColumns()
{
    return QString(
        "c.container_id,"
        "c.name,"
        "c.level,"
        "COALESCE(parent_link.parent_id,0) AS parent_id,"
        "COALESCE(c.order_index,0) AS order_index,"
        "COALESCE(c.analysis_depth, CASE WHEN c.fault_analysis_depth IS NOT NULL AND c.fault_analysis_depth != '' THEN CAST(c.fault_analysis_depth AS INTEGER) ELSE 0 END) AS analysis_depth_value,"
        "c.interface_json,"
        "c.behavior_smt,"
        "c.fault_modes_json,"
        "c.tests_json,"
        "c.analysis_json,"
        "c.source_equipment_id,"
        "COALESCE(e.Type,'') AS equipment_type,"
        "COALESCE(e.Name,'') AS equipment_name,"
        "COALESCE(c.project_structure_id,0) AS project_structure_id");
}

}

QString ContainerRepository::levelFromType(ContainerType type)
{
    switch (type) {
    case ContainerType::System: return QString("system");
    case ContainerType::Subsystem: return QString("subsystem");
    case ContainerType::LRU: return QString("LRU");
    case ContainerType::SRU: return QString("SRU");
    case ContainerType::Module: return QString("module");
    case ContainerType::Submodule: return QString("submodule");
    case ContainerType::Component: return QString("component");
    }
    return QString("component");
}

ContainerType ContainerRepository::typeFromLevel(const QString &level)
{
    const QString value = level.trimmed().toLower();
    if (value == QString("system")) return ContainerType::System;
    if (value == QString("subsystem")) return ContainerType::Subsystem;
    if (value == QString("LRU")) return ContainerType::LRU;
    if (value == QString("SRU")) return ContainerType::SRU;
    if (value == QString("module")) return ContainerType::Module;
    if (value == QString("submodule")) return ContainerType::Submodule;
    return ContainerType::Component;
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

    QSqlQuery pragma(m_db);
    pragma.exec("PRAGMA foreign_keys = ON");

    if (!ensureContainerSchema()) return false;
    if (!ensureHierarchySchema()) return false;
    if (!ensureComponentLinkSchema()) return false;

    return true;
}

QList<ContainerEntity> ContainerRepository::fetchRoots()
{
    QList<ContainerEntity> list;
    QSqlQuery q(m_db);
    const QString sql = QString(
        "SELECT %1 "
        "FROM container c "
        "LEFT JOIN container_hierarchy parent_link ON parent_link.child_id = c.container_id "
        "LEFT JOIN Equipment e ON e.Equipment_ID = c.source_equipment_id "
        "WHERE parent_link.parent_id IS NULL "
        "ORDER BY c.order_index, c.container_id").arg(selectColumns());
    if (!q.exec(sql)) {
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
    q.prepare(QString(
        "SELECT %1 "
        "FROM container c "
        "JOIN container_hierarchy parent_link ON parent_link.child_id = c.container_id "
        "LEFT JOIN Equipment e ON e.Equipment_ID = c.source_equipment_id "
        "WHERE parent_link.parent_id = :pid "
        "ORDER BY c.order_index, c.container_id"
    ).arg(selectColumns()));
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
    const QString sql = QString(
        "SELECT %1 "
        "FROM container c "
        "LEFT JOIN container_hierarchy parent_link ON parent_link.child_id = c.container_id "
        "LEFT JOIN Equipment e ON e.Equipment_ID = c.source_equipment_id "
        "ORDER BY COALESCE(parent_link.parent_id,0), c.order_index, c.container_id"
    ).arg(selectColumns());
    if (!q.exec(sql)) {
        qWarning() << q.lastError();
        return list;
    }
    while (q.next()) list.append(fromQuery(q));
    return list;
}

ContainerEntity ContainerRepository::getById(int id)
{
    QSqlQuery q(m_db);
    q.prepare(QString(
        "SELECT %1 "
        "FROM container c "
        "LEFT JOIN container_hierarchy parent_link ON parent_link.child_id = c.container_id "
        "LEFT JOIN Equipment e ON e.Equipment_ID = c.source_equipment_id "
        "WHERE c.container_id = :id"
    ).arg(selectColumns()));
    q.bindValue(":id", id);
    if (!q.exec() || !q.next()) return {};
    return fromQuery(q);
}

bool ContainerRepository::insert(ContainerEntity &e)
{
    QSqlQuery q(m_db);
    const int projectStructureId = e.projectStructureId() != 0 ? e.projectStructureId() : resolveProjectStructureId(e);
    q.prepare("INSERT INTO container(project_structure_id,name,level,source_equipment_id,auto_generated,description,fault_analysis_depth,inherits_from_container_id,order_index,analysis_depth,interface_json,behavior_smt,fault_modes_json,tests_json,analysis_json) "
              "VALUES(:psid,:name,:level,:eqid,:auto,:desc,:faultDepth,:inherit,:orderIndex,:analysisDepth,:iface,:smt,:faults,:tests,:analysis)");
    if (projectStructureId == 0)
        q.bindValue(":psid", QVariant(QVariant::Int));
    else
        q.bindValue(":psid", projectStructureId);
    q.bindValue(":name", e.name());
    q.bindValue(":level", levelFromType(e.type()));
    if (e.equipmentId() == 0)
        q.bindValue(":eqid", QVariant(QVariant::Int));
    else
        q.bindValue(":eqid", e.equipmentId());
    q.bindValue(":auto", e.equipmentId() != 0 ? 1 : 0);
    QString description = e.equipmentName();
    if (description.trimmed().isEmpty())
        description = e.name();
    q.bindValue(":desc", description);
    if (e.analysisDepth() > 0)
        q.bindValue(":faultDepth", QString::number(e.analysisDepth()));
    else
        q.bindValue(":faultDepth", QVariant(QVariant::String));
    q.bindValue(":inherit", QVariant(QVariant::Int));
    q.bindValue(":orderIndex", e.orderIndex());
    q.bindValue(":analysisDepth", e.analysisDepth());
    if (e.interfaceJson().isEmpty())
        q.bindValue(":iface", QVariant(QVariant::String));
    else
        q.bindValue(":iface", e.interfaceJson());
    if (e.behaviorSmt().isEmpty())
        q.bindValue(":smt", QVariant(QVariant::String));
    else
        q.bindValue(":smt", e.behaviorSmt());
    if (e.faultModesJson().isEmpty())
        q.bindValue(":faults", QVariant(QVariant::String));
    else
        q.bindValue(":faults", e.faultModesJson());
    if (e.testsJson().isEmpty())
        q.bindValue(":tests", QVariant(QVariant::String));
    else
        q.bindValue(":tests", e.testsJson());
    if (e.analysisJson().isEmpty())
        q.bindValue(":analysis", QVariant(QVariant::String));
    else
        q.bindValue(":analysis", e.analysisJson());

    if (!q.exec()) {
        qWarning() << q.lastError();
        return false;
    }
    e.setId(q.lastInsertId().toInt());
    e.setProjectStructureId(projectStructureId);
    if (!updateNormalizedParentLink(e.id(), e.parentId())) return false;
    if (!updateNormalizedEquipmentLink(e)) return false;
    return true;
}

bool ContainerRepository::update(const ContainerEntity &e)
{
    QSqlQuery q(m_db);
    const int projectStructureId = e.projectStructureId() != 0 ? e.projectStructureId() : resolveProjectStructureId(e);
    q.prepare("UPDATE container SET project_structure_id=:psid, name=:name, level=:level, source_equipment_id=:eqid, auto_generated=:auto, description=:desc, "
              "fault_analysis_depth=:faultDepth, inherits_from_container_id=:inherit, order_index=:orderIndex, analysis_depth=:analysisDepth, "
              "interface_json=:iface, behavior_smt=:smt, fault_modes_json=:faults, tests_json=:tests, analysis_json=:analysis, updated_at=CURRENT_TIMESTAMP "
              "WHERE container_id=:id");
    q.bindValue(":id", e.id());
    if (projectStructureId == 0)
        q.bindValue(":psid", QVariant(QVariant::Int));
    else
        q.bindValue(":psid", projectStructureId);
    q.bindValue(":name", e.name());
    q.bindValue(":level", levelFromType(e.type()));
    if (e.equipmentId() == 0)
        q.bindValue(":eqid", QVariant(QVariant::Int));
    else
        q.bindValue(":eqid", e.equipmentId());
    q.bindValue(":auto", e.equipmentId() != 0 ? 1 : 0);
    QString description = e.equipmentName();
    if (description.trimmed().isEmpty())
        description = e.name();
    q.bindValue(":desc", description);
    if (e.analysisDepth() > 0)
        q.bindValue(":faultDepth", QString::number(e.analysisDepth()));
    else
        q.bindValue(":faultDepth", QVariant(QVariant::String));
    q.bindValue(":inherit", QVariant(QVariant::Int));
    q.bindValue(":orderIndex", e.orderIndex());
    q.bindValue(":analysisDepth", e.analysisDepth());
    if (e.interfaceJson().isEmpty())
        q.bindValue(":iface", QVariant(QVariant::String));
    else
        q.bindValue(":iface", e.interfaceJson());
    if (e.behaviorSmt().isEmpty())
        q.bindValue(":smt", QVariant(QVariant::String));
    else
        q.bindValue(":smt", e.behaviorSmt());
    if (e.faultModesJson().isEmpty())
        q.bindValue(":faults", QVariant(QVariant::String));
    else
        q.bindValue(":faults", e.faultModesJson());
    if (e.testsJson().isEmpty())
        q.bindValue(":tests", QVariant(QVariant::String));
    else
        q.bindValue(":tests", e.testsJson());
    if (e.analysisJson().isEmpty())
        q.bindValue(":analysis", QVariant(QVariant::String));
    else
        q.bindValue(":analysis", e.analysisJson());
    if (!q.exec()) {
        qWarning() << q.lastError();
        return false;
    }
    if (!updateNormalizedParentLink(e.id(), e.parentId())) return false;
    if (!updateNormalizedEquipmentLink(e)) return false;
    return true;
}

bool ContainerRepository::remove(int id)
{
    auto execCleanup = [&](const QString &sql, std::function<void(QSqlQuery &)> binder) -> bool {
        QSqlQuery stmt(m_db);
        stmt.prepare(sql);
        binder(stmt);
        if (!stmt.exec()) {
            qWarning() << "Container cleanup failed:" << stmt.lastError() << sql;
            return false;
        }
        return true;
    };

    bool ok = true;
    ok &= execCleanup("DELETE FROM container_state_interface WHERE state_id IN (SELECT state_id FROM container_state WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM container_state_behavior WHERE state_id IN (SELECT state_id FROM container_state WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM container_state WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM container_interface_binding WHERE interface_id IN (SELECT interface_id FROM container_interface WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM container_interface WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM container_component WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM function_io WHERE function_id IN (SELECT function_id FROM function_definition WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM function_dependency WHERE function_id IN (SELECT function_id FROM function_definition WHERE container_id=:cid) OR depends_on_function_id IN (SELECT function_id FROM function_definition WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM function_definition WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM test_fault_coverage WHERE test_id IN (SELECT test_id FROM test_definition WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM test_constraint WHERE test_id IN (SELECT test_id FROM test_definition WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM test_definition WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM analysis_requirement WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM analysis_constraint WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM test_plan_candidate_item WHERE candidate_id IN (SELECT candidate_id FROM test_plan_candidate WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM test_plan_candidate WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM diagnosis_tree_node WHERE tree_id IN (SELECT tree_id FROM diagnosis_tree WHERE container_id=:cid)", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM diagnosis_tree WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    ok &= execCleanup("DELETE FROM container_hierarchy WHERE parent_id=:pid OR child_id=:cid", [&](QSqlQuery &q) {
        q.bindValue(":pid", id);
        q.bindValue(":cid", id);
    });

    ok &= execCleanup("DELETE FROM container WHERE container_id=:cid", [&](QSqlQuery &q) { q.bindValue(":cid", id); });
    return ok;
}

int ContainerRepository::componentContainerIdForEquipment(int equipmentId)
{
    QSqlQuery q(m_db);
    q.prepare("SELECT container_id FROM container WHERE source_equipment_id=:eid ORDER BY container_id LIMIT 1");
    q.bindValue(":eid", equipmentId);
    if (!q.exec()) {
        qWarning() << q.lastError();
        return 0;
    }
    if (q.next()) return q.value(0).toInt();

    QSqlQuery link(m_db);
    link.prepare("SELECT container_id FROM container_component WHERE equipment_id=:eid ORDER BY container_id LIMIT 1");
    link.bindValue(":eid", equipmentId);
    if (!link.exec()) {
        qWarning() << link.lastError();
        return 0;
    }
    if (link.next()) return link.value(0).toInt();
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
    return entity.id();
}

bool ContainerRepository::deleteComponentContainerForEquipment(int equipmentId)
{
    int cid = componentContainerIdForEquipment(equipmentId);
    if (cid == 0) return true;

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
    entity.setType(typeFromLevel(query.value(2).toString()));
    entity.setParentId(query.value(3).toInt());
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
    entity.setProjectStructureId(query.value(14).toInt());
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


bool ContainerRepository::upsertNormalizedContainer(const ContainerEntity &entity)
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;

    QSqlQuery q(m_db);
    q.prepare("INSERT INTO container (container_id, project_structure_id, name, level, source_equipment_id, auto_generated, description, fault_analysis_depth, inherits_from_container_id) "
              "VALUES (:id,:psid,:name,:level,:eqid,:auto,:desc,:faultDepth,:inherit) "
              "ON CONFLICT(container_id) DO UPDATE SET "
              "project_structure_id=excluded.project_structure_id, "
              "name=excluded.name, "
              "level=excluded.level, "
              "source_equipment_id=excluded.source_equipment_id, "
              "auto_generated=excluded.auto_generated, "
              "description=excluded.description, "
              "fault_analysis_depth=excluded.fault_analysis_depth, "
              "inherits_from_container_id=excluded.inherits_from_container_id, "
              "updated_at=CURRENT_TIMESTAMP");
    q.bindValue(":id", entity.id());
    q.bindValue(":psid", resolveProjectStructureId(entity));
    q.bindValue(":name", entity.name());
    q.bindValue(":level", levelFromType(entity.type()));
    if (entity.equipmentId() == 0)
        q.bindValue(":eqid", QVariant(QVariant::Int));
    else
        q.bindValue(":eqid", entity.equipmentId());
    q.bindValue(":auto", entity.equipmentId() != 0 ? 1 : 0);
    QString description = entity.equipmentName();
    if (description.isEmpty()) description = entity.name();
    q.bindValue(":desc", description);
    if (entity.analysisDepth() > 0)
        q.bindValue(":faultDepth", QString::number(entity.analysisDepth()));
    else
        q.bindValue(":faultDepth", QVariant());
    q.bindValue(":inherit", QVariant(QVariant::Int));
    if (!q.exec()) {
        qWarning() << "Failed to upsert normalized container:" << q.lastError();
        return false;
    }
    return true;
}

bool ContainerRepository::updateNormalizedParentLink(int containerId, int parentContainerId)
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;

    QSqlQuery del(m_db);
    del.prepare("DELETE FROM container_hierarchy WHERE child_id=:cid");
    del.bindValue(":cid", containerId);
    if (!del.exec()) {
        qWarning() << "Failed to clear normalized parent link:" << del.lastError();
        return false;
    }

    if (parentContainerId == 0) return true;

    QSqlQuery ins(m_db);
    ins.prepare("INSERT OR REPLACE INTO container_hierarchy(parent_id, child_id, relation_type) VALUES(:pid,:cid,'contains')");
    ins.bindValue(":pid", parentContainerId);
    ins.bindValue(":cid", containerId);
    if (!ins.exec()) {
        qWarning() << "Failed to upsert normalized parent link:" << ins.lastError();
        return false;
    }
    return true;
}

bool ContainerRepository::updateNormalizedEquipmentLink(const ContainerEntity &entity)
{
    if (!m_db.isValid() || !m_db.isOpen()) return false;

    QSqlQuery del(m_db);
    del.prepare("DELETE FROM container_component WHERE container_id=:cid");
    del.bindValue(":cid", entity.id());
    if (!del.exec()) {
        qWarning() << "Failed to clear normalized equipment link:" << del.lastError();
        return false;
    }

    if (entity.equipmentId() == 0) return true;

    QSqlQuery ins(m_db);
    ins.prepare("INSERT OR REPLACE INTO container_component(container_id, equipment_id, role) VALUES(:cid,:eid,'primary')");
    ins.bindValue(":cid", entity.id());
    ins.bindValue(":eid", entity.equipmentId());
    if (!ins.exec()) {
        qWarning() << "Failed to upsert normalized equipment link:" << ins.lastError();
        return false;
    }
    return true;
}

int ContainerRepository::resolveProjectStructureId(const ContainerEntity &entity) const
{
    if (!m_db.isValid() || !m_db.isOpen()) return 0;

    if (entity.equipmentId() != 0) {
        QSqlQuery q(m_db);
        q.prepare("SELECT ProjectStructure_ID FROM Equipment WHERE Equipment_ID=:eid");
        q.bindValue(":eid", entity.equipmentId());
        if (q.exec() && q.next()) {
            return q.value(0).toInt();
        }
    }

    if (entity.parentId() != 0) {
        QSqlQuery q(m_db);
        q.prepare("SELECT project_structure_id FROM container WHERE container_id=:cid");
        q.bindValue(":cid", entity.parentId());
        if (q.exec() && q.next()) {
            return q.value(0).toInt();
        }
    }

    return 0;
}

