#include "smtrepository.h"
#include <QFileInfo>
#include <QDir>

SmtRepository::SmtRepository(const QSqlDatabase &projectDb, const QString &refModelDbPath)
    : m_projectDb(projectDb)
    , m_refModelDbPath(refModelDbPath)
    , m_refModelDbOpened(false)
{
    if (m_refModelDbPath.isEmpty()) {
        // Default to ref/Model.db
        m_refModelDbPath = QDir::currentPath() + "/ref/Model.db";
    }
}

bool SmtRepository::openRefModelDb()
{
    if (m_refModelDbOpened && m_refModelDb.isOpen()) {
        return true;
    }
    
    if (!QFileInfo::exists(m_refModelDbPath)) {
        qWarning() << "Reference Model.db not found at:" << m_refModelDbPath;
        return false;
    }
    
    QString connectionName = "RefModelDb_" + QString::number((quintptr)this);
    m_refModelDb = QSqlDatabase::addDatabase("QSQLITE", connectionName);
    m_refModelDb.setDatabaseName(m_refModelDbPath);
    
    if (!m_refModelDb.open()) {
        qWarning() << "Failed to open ref Model.db:" << m_refModelDb.lastError().text();
        return false;
    }
    
    m_refModelDbOpened = true;
    return true;
}

void SmtRepository::closeRefModelDb()
{
    if (m_refModelDbOpened && m_refModelDb.isOpen()) {
        QString connectionName = m_refModelDb.connectionName();
        m_refModelDb.close();
        QSqlDatabase::removeDatabase(connectionName);
        m_refModelDbOpened = false;
    }
}

QString SmtRepository::getComponentTemplate(const QString &componentMark, QString *errorMsg)
{
    if (!openRefModelDb()) {
        if (errorMsg) *errorMsg = "无法打开参考模型数据库";
        return QString();
    }
    
    QSqlQuery query(m_refModelDb);
    query.prepare("SELECT variable, description FROM components WHERE mark = ?");
    query.addBindValue(componentMark);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return QString();
    }
    
    if (query.next()) {
        QString variable = query.value(0).toString();
        QString description = query.value(1).toString();
        return variable + "\n" + description;
    }
    
    if (errorMsg) *errorMsg = "未找到组件模板: " + componentMark;
    return QString();
}

QString SmtRepository::getComponentVariableDeclarations(const QString &componentMark, QString *errorMsg)
{
    if (!openRefModelDb()) {
        if (errorMsg) *errorMsg = "无法打开参考模型数据库";
        return QString();
    }
    
    QSqlQuery query(m_refModelDb);
    query.prepare("SELECT variable FROM components WHERE mark = ?");
    query.addBindValue(componentMark);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return QString();
    }
    
    if (query.next()) {
        return query.value(0).toString();
    }
    
    if (errorMsg) *errorMsg = "未找到组件: " + componentMark;
    return QString();
}

QString SmtRepository::getComponentDescription(const QString &componentMark, QString *errorMsg)
{
    if (!openRefModelDb()) {
        if (errorMsg) *errorMsg = "无法打开参考模型数据库";
        return QString();
    }
    
    QSqlQuery query(m_refModelDb);
    query.prepare("SELECT description FROM components WHERE mark = ?");
    query.addBindValue(componentMark);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return QString();
    }
    
    if (query.next()) {
        return query.value(0).toString();
    }
    
    if (errorMsg) *errorMsg = "未找到组件: " + componentMark;
    return QString();
}

QString SmtRepository::getComponentFailureMode(const QString &componentMark, QString *errorMsg)
{
    if (!openRefModelDb()) {
        if (errorMsg) *errorMsg = "无法打开参考模型数据库";
        return QString();
    }
    
    QSqlQuery query(m_refModelDb);
    query.prepare("SELECT failuremode FROM components WHERE mark = ?");
    query.addBindValue(componentMark);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return QString();
    }
    
    if (query.next()) {
        return query.value(0).toString();
    }
    
    if (errorMsg) *errorMsg = "未找到组件: " + componentMark;
    return QString();
}

QString SmtRepository::getComponentSmt(int equipmentId, QString *errorMsg)
{
    if (!m_projectDb.isValid() || !m_projectDb.isOpen()) {
        if (errorMsg) *errorMsg = "项目数据库未打开";
        return QString();
    }
    
    QSqlQuery query(m_projectDb);
    query.prepare("SELECT smt_text FROM component_smt WHERE equipment_id = ?");
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return QString();
    }
    
    if (query.next()) {
        return query.value(0).toString();
    }
    
    // If not found in project DB, try to get from Equipment table and fallback to template
    QSqlQuery equipQuery(m_projectDb);
    equipQuery.prepare("SELECT Name, TModel FROM Equipment WHERE Equipment_ID = ?");
    equipQuery.addBindValue(equipmentId);
    
    if (equipQuery.exec() && equipQuery.next()) {
        QString tmodel = equipQuery.value(1).toString();
        if (!tmodel.isEmpty()) {
            // Get template from ref/Model.db
            QString tmpl = getComponentTemplate(tmodel, errorMsg);
            if (!tmpl.isEmpty()) {
                QString name = equipQuery.value(0).toString();
                // Replace placeholder %TModel% with actual instance name
                tmpl.replace("%" + tmodel + "%", name);
                return tmpl;
            }
        }
    }
    
    if (errorMsg) *errorMsg = "未找到设备SMT描述: Equipment_ID=" + QString::number(equipmentId);
    return QString();
}

QString SmtRepository::getContainerSmt(int containerId, QString *errorMsg)
{
    if (!m_projectDb.isValid() || !m_projectDb.isOpen()) {
        if (errorMsg) *errorMsg = "项目数据库未打开";
        return QString();
    }
    
    QSqlQuery query(m_projectDb);
    query.prepare("SELECT smt_text FROM component_smt WHERE container_id = ? AND model_scope = 'component'");
    query.addBindValue(containerId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return QString();
    }
    
    if (query.next()) {
        return query.value(0).toString();
    }
    
    if (errorMsg) *errorMsg = "未找到容器SMT描述: Container_ID=" + QString::number(containerId);
    return QString();
}

SmtRepository::SystemSmtData SmtRepository::getSystemSmt(int containerId, QString *errorMsg)
{
    SystemSmtData result;
    
    if (!m_projectDb.isValid() || !m_projectDb.isOpen()) {
        if (errorMsg) *errorMsg = "项目数据库未打开";
        return result;
    }
    
    QSqlQuery query(m_projectDb);
    query.prepare("SELECT def_block, connect_block, raw_block, generated_by FROM system_smt WHERE container_id = ?");
    query.addBindValue(containerId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return result;
    }
    
    if (query.next()) {
        result.defBlock = query.value(0).toString();
        result.connectBlock = query.value(1).toString();
        result.rawBlock = query.value(2).toString();
        result.generatedBy = query.value(3).toString();
        result.isValid = true;
    } else {
        if (errorMsg) *errorMsg = "未找到系统SMT描述: Container_ID=" + QString::number(containerId);
    }
    
    return result;
}

bool SmtRepository::saveComponentSmt(int equipmentId, const QString &smtText, const QString &portSignature, QString *errorMsg)
{
    if (!m_projectDb.isValid() || !m_projectDb.isOpen()) {
        if (errorMsg) *errorMsg = "项目数据库未打开";
        return false;
    }
    
    QSqlQuery query(m_projectDb);
    query.prepare(
        "INSERT OR REPLACE INTO component_smt "
        "(equipment_id, smt_text, port_signature, syntax_status, updated_at) "
        "VALUES (?, ?, ?, 'unknown', datetime('now'))"
    );
    query.addBindValue(equipmentId);
    query.addBindValue(smtText);
    query.addBindValue(portSignature);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "保存失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

bool SmtRepository::saveContainerSmt(int containerId, const QString &smtText, const QString &portSignature, QString *errorMsg)
{
    if (!m_projectDb.isValid() || !m_projectDb.isOpen()) {
        if (errorMsg) *errorMsg = "项目数据库未打开";
        return false;
    }
    
    QSqlQuery query(m_projectDb);
    query.prepare(
        "INSERT OR REPLACE INTO component_smt "
        "(container_id, model_scope, smt_text, port_signature, syntax_status, updated_at) "
        "VALUES (?, 'component', ?, ?, 'unknown', datetime('now'))"
    );
    query.addBindValue(containerId);
    query.addBindValue(smtText);
    query.addBindValue(portSignature);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "保存失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

bool SmtRepository::saveSystemSmt(int containerId, const QString &defBlock, const QString &connectBlock, const QString &rawBlock, QString *errorMsg)
{
    if (!m_projectDb.isValid() || !m_projectDb.isOpen()) {
        if (errorMsg) *errorMsg = "项目数据库未打开";
        return false;
    }
    
    QSqlQuery query(m_projectDb);
    query.prepare(
        "INSERT OR REPLACE INTO system_smt "
        "(container_id, def_block, connect_block, raw_block, generated_by, generated_at, updated_at) "
        "VALUES (?, ?, ?, ?, 'SmtRepository', datetime('now'), datetime('now'))"
    );
    query.addBindValue(containerId);
    query.addBindValue(defBlock);
    query.addBindValue(connectBlock);
    query.addBindValue(rawBlock);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "保存失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

bool SmtRepository::validateComponentSmt(const QString &smtText, QString *errorMsg)
{
    // Basic validation - check for basic SMT-LIB2 structure
    if (smtText.trimmed().isEmpty()) {
        if (errorMsg) *errorMsg = "SMT描述为空";
        return false;
    }
    
    // Check for balanced parentheses
    int balance = 0;
    for (QChar ch : smtText) {
        if (ch == '(') balance++;
        else if (ch == ')') balance--;
        if (balance < 0) {
            if (errorMsg) *errorMsg = "括号不匹配";
            return false;
        }
    }
    
    if (balance != 0) {
        if (errorMsg) *errorMsg = "括号不匹配";
        return false;
    }
    
    // More comprehensive validation can be added using SmtSyntaxChecker
    return true;
}
