#include "BO/function/functionrepository.h"

#include <QCryptographicHash>
#include <QDomDocument>
#include <QDomElement>
#include <QDomNodeList>
#include <QSqlError>
#include <QSqlRecord>
#include <QtDebug>

namespace {

QString trimmedChildText(const QDomElement &parent, const QString &tagName)
{
    return parent.firstChildElement(tagName).text().trimmed();
}

QString componentNameFromVariable(const QString &variable)
{
    if (variable.startsWith(QLatin1Char('.'))) {
        return {};
    }
    const int dotIndex = variable.indexOf(QLatin1Char('.'));
    if (dotIndex == -1) {
        return variable.trimmed();
    }
    return variable.left(dotIndex).trimmed();
}

QStringList parseDelimitedListUnique(const QString &text)
{
    QString normalized = text;
    normalized.replace(QLatin1Char('\n'), QLatin1Char(','));
    normalized.replace(QLatin1Char('\r'), QLatin1Char(','));
    const QStringList rawParts = normalized.split(QLatin1Char(','), QString::SkipEmptyParts);

    QSet<QString> seen;
    QStringList result;
    for (const QString &part : rawParts) {
        const QString trimmed = part.trimmed();
        if (trimmed.isEmpty() || seen.contains(trimmed))
            continue;
        result.append(trimmed);
        seen.insert(trimmed);
    }
    return result;
}

TestItem buildTestItem(const QDomElement &constraintElement)
{
    TestItem item;
    item.variable = constraintElement.firstChildElement(QString("variable")).text().trimmed();
    item.value = constraintElement.firstChildElement(QString("value")).text().trimmed();
    bool ok = false;
    const QString confidenceText = constraintElement.firstChildElement(QString("confidence")).text().trimmed();
    item.confidence = confidenceText.toDouble(&ok);
    if (!ok) item.confidence = 0.0;
    item.testType = constraintElement.firstChildElement(QString("type")).text().trimmed();
    item.checkState = item.testType.contains(QString("执行器")) ? Qt::Checked : Qt::Unchecked;
    return item;
}

QString elementToString(const QDomElement &element)
{
    if (element.isNull())
        return QString();
    QDomDocument doc;
    QDomNode imported = doc.importNode(element, true);
    doc.appendChild(imported);
    return doc.toString();
}

} // namespace

FunctionRepository::FunctionRepository(const QSqlDatabase &db)
    : m_db(db)
{
}

bool FunctionRepository::ensureTables()
{
    if (!m_db.isValid() || !m_db.isOpen())
        return false;

    QSqlQuery pragma(m_db);
    pragma.exec(QString("PRAGMA foreign_keys = ON"));

    if (!ensureFunctionTable())
        return false;
    if (!ensureFunctionBindingTable())
        return false;
    if (!ensureFunctionDocumentTable())
        return false;

    return true;
}

bool FunctionRepository::ensureFunctionTable()
{
    auto ensureColumn = [&](const QString &name, const QString &definition) -> bool {
        QSqlQuery info(m_db);
        if (!info.exec(QString("PRAGMA table_info(Function)"))) {
            logError(info, QString("pragma table_info Function"));
            return false;
        }
        while (info.next()) {
            if (info.value(QString("name")).toString().compare(name, Qt::CaseInsensitive) == 0)
                return true;
        }
        QSqlQuery alter(m_db);
        if (!alter.exec(QString("ALTER TABLE Function ADD COLUMN %1 %2").arg(name, definition))) {
            logError(alter, QString("alter table add column %1").arg(name));
            return false;
        }
        return true;
    };

    QSqlQuery query(m_db);
    if (!query.exec(QString(
            "CREATE TABLE IF NOT EXISTS Function ("
            " FunctionID INTEGER PRIMARY KEY,"
            " FunctionName TEXT NOT NULL,"
            " ExecsList TEXT,"
            " CmdValList TEXT,"
            " Remark TEXT,"
            " LinkText TEXT DEFAULT '',"
            " ComponentDependency TEXT DEFAULT '',"
            " AllComponents TEXT DEFAULT '',"
            " FunctionDependency TEXT DEFAULT '',"
            " PersistentFlag INTEGER DEFAULT 1,"
            " FaultProbability REAL DEFAULT 0.0)"))) {
        logError(query, QString("create Function"));
        return false;
    }

    const struct {
        const char *name;
        const char *definition;
    } requiredColumns[] = {
        {"LinkText", "TEXT DEFAULT ''"},
        {"ComponentDependency", "TEXT DEFAULT ''"},
        {"AllComponents", "TEXT DEFAULT ''"},
        {"FunctionDependency", "TEXT DEFAULT ''"},
        {"PersistentFlag", "INTEGER DEFAULT 1"},
        {"FaultProbability", "REAL DEFAULT 0.0"},
        {"VariableConfigXml", "TEXT DEFAULT ''"}
    };
    for (const auto &column : requiredColumns) {
        if (!ensureColumn(QString::fromLatin1(column.name), QString::fromLatin1(column.definition)))
            return false;
    }

    return true;
}

bool FunctionRepository::ensureFunctionBindingTable()
{
    QSqlQuery query(m_db);
    if (!query.exec(QString(
            "CREATE TABLE IF NOT EXISTS function_bindings ("
            " id INTEGER PRIMARY KEY AUTOINCREMENT,"
            " function_id INTEGER NOT NULL UNIQUE,"
            " symbol_id INTEGER NOT NULL,"
            " FOREIGN KEY(function_id) REFERENCES Function(FunctionID) ON DELETE CASCADE,"
            " FOREIGN KEY(symbol_id) REFERENCES Symbol(Symbol_ID) ON DELETE CASCADE)"))) {
        logError(query, QString("create function_bindings"));
        return false;
    }

    if (!query.exec(QString(
            "CREATE INDEX IF NOT EXISTS idx_function_bindings_symbol ON function_bindings(symbol_id)"))) {
        logError(query, QString("create index function_bindings"));
        return false;
    }
    return true;
}

bool FunctionRepository::ensureFunctionDocumentTable()
{
    QSqlQuery query(m_db);
    if (!query.exec(QString(
            "CREATE TABLE IF NOT EXISTS function_document ("
            " function_document_id INTEGER PRIMARY KEY AUTOINCREMENT,"
            " container_id INTEGER NOT NULL,"
            " xml_text TEXT NOT NULL,"
            " format_version TEXT NOT NULL DEFAULT '1.0',"
            " checksum TEXT,"
            " source_hint TEXT,"
            " metadata_json TEXT,"
            " created_at TEXT DEFAULT CURRENT_TIMESTAMP,"
            " updated_at TEXT DEFAULT CURRENT_TIMESTAMP)"))) {
        logError(query, QString("create function_document"));
        return false;
    }

    if (!query.exec(QString(
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_function_document_container ON function_document(container_id)"))) {
        logError(query, QString("create index function_document"));
        return false;
    }
    return true;
}

QList<FunctionRecord> FunctionRepository::fetchAll() const
{
    QList<FunctionRecord> list;
    if (!m_db.isOpen()) return list;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "SELECT f.FunctionID, f.FunctionName, f.CmdValList, f.ExecsList, f.Remark,"
        " f.LinkText, f.ComponentDependency, f.AllComponents, f.FunctionDependency,"
        " f.PersistentFlag, f.FaultProbability, f.VariableConfigXml,"
        " fb.symbol_id, s.Show_DT"
        " FROM Function f"
        " LEFT JOIN function_bindings fb ON fb.function_id = f.FunctionID"
        " LEFT JOIN Symbol s ON s.Symbol_ID = fb.symbol_id"
        " ORDER BY f.FunctionID"));
    if (!query.exec()) {
        logError(query, QString("fetchAll"));
        return list;
    }

    while (query.next()) {
        FunctionRecord rec;
        rec.id = query.value(0).toInt();
        rec.name = query.value(1).toString();
        rec.cmdValList = query.value(2).toString();
        rec.execsList = query.value(3).toString();
        rec.remark = query.value(4).toString();
        rec.link = query.value(5).toString();
        rec.componentDependency = query.value(6).toString();
        rec.allComponents = query.value(7).toString();
        rec.functionDependency = query.value(8).toString();
        rec.persistent = query.value(9).toBool();
        rec.faultProbability = query.value(10).toDouble();
        rec.variableConfigXml = query.value(11).toString();
        rec.symbolId = query.value(12).toInt();
        rec.symbolName = query.value(13).toString();
        list.append(rec);
    }
    return list;
}

QList<FunctionRecord> FunctionRepository::fetchBySymbol(int symbolId) const
{
    QList<FunctionRecord> list;
    if (!m_db.isOpen()) return list;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "SELECT f.FunctionID, f.FunctionName, f.CmdValList, f.ExecsList, f.Remark,"
        " f.LinkText, f.ComponentDependency, f.AllComponents, f.FunctionDependency,"
        " f.PersistentFlag, f.FaultProbability, f.VariableConfigXml,"
        " fb.symbol_id, s.Show_DT"
        " FROM Function f"
        " JOIN function_bindings fb ON fb.function_id = f.FunctionID"
        " LEFT JOIN Symbol s ON s.Symbol_ID = fb.symbol_id"
        " WHERE fb.symbol_id = :symbolId"
        " ORDER BY f.FunctionID"));
    query.bindValue(":symbolId", symbolId);
    if (!query.exec()) {
        logError(query, QString("fetchBySymbol"));
        return list;
    }

    while (query.next()) {
        FunctionRecord rec;
        rec.id = query.value(0).toInt();
        rec.name = query.value(1).toString();
        rec.cmdValList = query.value(2).toString();
        rec.execsList = query.value(3).toString();
        rec.remark = query.value(4).toString();
        rec.link = query.value(5).toString();
        rec.componentDependency = query.value(6).toString();
        rec.allComponents = query.value(7).toString();
        rec.functionDependency = query.value(8).toString();
        rec.persistent = query.value(9).toBool();
        rec.faultProbability = query.value(10).toDouble();
        rec.variableConfigXml = query.value(11).toString();
        rec.symbolId = query.value(12).toInt();
        rec.symbolName = query.value(13).toString();
        list.append(rec);
    }
    return list;
}

FunctionRecord FunctionRepository::getById(int id) const
{
    FunctionRecord rec;
    if (!m_db.isOpen() || id == 0) return rec;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "SELECT f.FunctionID, f.FunctionName, f.CmdValList, f.ExecsList, f.Remark,"
        " f.LinkText, f.ComponentDependency, f.AllComponents, f.FunctionDependency,"
        " f.PersistentFlag, f.FaultProbability, f.VariableConfigXml,"
        " fb.symbol_id, s.Show_DT"
        " FROM Function f"
        " LEFT JOIN function_bindings fb ON fb.function_id = f.FunctionID"
        " LEFT JOIN Symbol s ON s.Symbol_ID = fb.symbol_id"
        " WHERE f.FunctionID = :id"));
    query.bindValue(":id", id);
    if (!query.exec()) {
        logError(query, QString("getById"));
        return rec;
    }
    if (query.next()) {
        rec.id = query.value(0).toInt();
        rec.name = query.value(1).toString();
        rec.cmdValList = query.value(2).toString();
        rec.execsList = query.value(3).toString();
        rec.remark = query.value(4).toString();
        rec.link = query.value(5).toString();
        rec.componentDependency = query.value(6).toString();
        rec.allComponents = query.value(7).toString();
        rec.functionDependency = query.value(8).toString();
        rec.persistent = query.value(9).toBool();
        rec.faultProbability = query.value(10).toDouble();
        rec.variableConfigXml = query.value(11).toString();
        rec.symbolId = query.value(12).toInt();
        rec.symbolName = query.value(13).toString();
    }
    return rec;
}

int FunctionRepository::insert(const FunctionRecord &record)
{
    if (!m_db.isOpen()) return 0;

    int newId = record.id > 0 ? record.id : nextId();

    QSqlQuery query(m_db);
    query.prepare(QString(
        "INSERT INTO Function(FunctionID, FunctionName, ExecsList, CmdValList, Remark,"
        " LinkText, ComponentDependency, AllComponents, FunctionDependency, PersistentFlag, FaultProbability, VariableConfigXml)"
        " VALUES(:id, :name, :execs, :cmds, :remark, :link, :componentDependency, :allComponents, :functionDependency, :persistent, :faultProbability, :variableConfig)"));
    query.bindValue(":id", newId);
    query.bindValue(":name", record.name);
    query.bindValue(":execs", record.execsList);
    query.bindValue(":cmds", record.cmdValList);
    query.bindValue(":remark", record.remark);
    query.bindValue(":link", record.link);
    query.bindValue(":componentDependency", record.componentDependency);
    query.bindValue(":allComponents", record.allComponents);
    query.bindValue(":functionDependency", record.functionDependency);
    query.bindValue(":persistent", record.persistent ? 1 : 0);
    query.bindValue(":faultProbability", record.faultProbability);
    query.bindValue(":variableConfig", record.variableConfigXml);
    if (!query.exec()) {
        logError(query, QString("insert function"));
        return 0;
    }

    if (record.symbolId > 0)
        bindSymbol(newId, record.symbolId);

    return newId;
}

bool FunctionRepository::update(const FunctionRecord &record)
{
    if (!m_db.isOpen() || record.id == 0) return false;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "UPDATE Function SET FunctionName=:name, ExecsList=:execs, CmdValList=:cmds, Remark=:remark,"
        " LinkText=:link, ComponentDependency=:componentDependency, AllComponents=:allComponents,"
        " FunctionDependency=:functionDependency, PersistentFlag=:persistent, FaultProbability=:faultProbability,"
        " VariableConfigXml=:variableConfig"
        " WHERE FunctionID=:id"));
    query.bindValue(":name", record.name);
    query.bindValue(":execs", record.execsList);
    query.bindValue(":cmds", record.cmdValList);
    query.bindValue(":remark", record.remark);
    query.bindValue(":link", record.link);
    query.bindValue(":componentDependency", record.componentDependency);
    query.bindValue(":allComponents", record.allComponents);
    query.bindValue(":functionDependency", record.functionDependency);
    query.bindValue(":persistent", record.persistent ? 1 : 0);
    query.bindValue(":faultProbability", record.faultProbability);
    query.bindValue(":variableConfig", record.variableConfigXml);
    query.bindValue(":id", record.id);
    if (!query.exec()) {
        logError(query, QString("update function"));
        return false;
    }

    if (record.symbolId > 0)
        bindSymbol(record.id, record.symbolId);
    else {
        QSqlQuery remove(m_db);
        remove.prepare(QString("DELETE FROM function_bindings WHERE function_id=:fid"));
        remove.bindValue(":fid", record.id);
        remove.exec();
    }

    return true;
}

bool FunctionRepository::remove(int id)
{
    if (!m_db.isOpen() || id == 0) return false;

    // Remove bindings first
    {
        QSqlQuery query(m_db);
        query.prepare(QString("DELETE FROM function_bindings WHERE function_id=:fid"));
        query.bindValue(":fid", id);
        query.exec();
    }

    // Remove function
    {
        QSqlQuery query(m_db);
        query.prepare(QString("DELETE FROM Function WHERE FunctionID=:id"));
        query.bindValue(":id", id);
        if (!query.exec()) {
            logError(query, QString("delete function"));
            return false;
        }
    }
    return true;
}

FunctionDocumentRecord FunctionRepository::loadDocument(int containerId) const
{
    FunctionDocumentRecord record;
    if (!m_db.isOpen() || containerId <= 0)
        return record;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "SELECT function_document_id, container_id, xml_text, format_version, checksum, "
        "source_hint, metadata_json, created_at, updated_at "
        "FROM function_document WHERE container_id = :cid LIMIT 1"));
    query.bindValue(QString(":cid"), containerId);
    if (!query.exec()) {
        logError(query, QString("load function_document"));
        return record;
    }

    if (query.next()) {
        record.id = query.value(0).toInt();
        record.containerId = query.value(1).toInt();
        record.xmlText = query.value(2).toString();
        record.formatVersion = query.value(3).toString();
        record.checksum = query.value(4).toString();
        record.sourceHint = query.value(5).toString();
        record.metadataJson = query.value(6).toString();
        record.createdAt = query.value(7).toString();
        record.updatedAt = query.value(8).toString();
    } else {
        record.containerId = containerId;
    }
    return record;
}

bool FunctionRepository::saveDocument(FunctionDocumentRecord &record)
{
    if (!m_db.isOpen() || record.containerId <= 0)
        return false;

    if (record.id == 0) {
        const FunctionDocumentRecord existing = loadDocument(record.containerId);
        if (existing.id > 0) {
            record.id = existing.id;
        }
    }

    if (record.checksum.trimmed().isEmpty()) {
        record.checksum = computeChecksum(record.xmlText);
    }

    if (record.formatVersion.trimmed().isEmpty()) {
        record.formatVersion = QString("1.0");
    }

    if (record.id > 0) {
        QSqlQuery query(m_db);
        query.prepare(QString(
            "UPDATE function_document "
            "SET xml_text = :xml, format_version = :version, checksum = :checksum, "
            "source_hint = :source, metadata_json = :metadata, updated_at = CURRENT_TIMESTAMP "
            "WHERE function_document_id = :id"));
        query.bindValue(QString(":xml"), record.xmlText);
        query.bindValue(QString(":version"), record.formatVersion);
        query.bindValue(QString(":checksum"), record.checksum);
        query.bindValue(QString(":source"), record.sourceHint);
        query.bindValue(QString(":metadata"), record.metadataJson);
        query.bindValue(QString(":id"), record.id);
        if (!query.exec()) {
            logError(query, QString("update function_document"));
            return false;
        }
        return true;
    }

    QSqlQuery insert(m_db);
    insert.prepare(QString(
        "INSERT INTO function_document(container_id, xml_text, format_version, checksum, source_hint, metadata_json)"
        " VALUES(:cid, :xml, :version, :checksum, :source, :metadata)"));
    insert.bindValue(QString(":cid"), record.containerId);
    insert.bindValue(QString(":xml"), record.xmlText);
    insert.bindValue(QString(":version"), record.formatVersion);
    insert.bindValue(QString(":checksum"), record.checksum);
    insert.bindValue(QString(":source"), record.sourceHint);
    insert.bindValue(QString(":metadata"), record.metadataJson);
    if (!insert.exec()) {
        logError(insert, QString("insert function_document"));
        return false;
    }
    record.id = insert.lastInsertId().toInt();
    return record.id > 0;
}

bool FunctionRepository::deleteDocument(int containerId)
{
    if (!m_db.isOpen() || containerId <= 0)
        return false;
    QSqlQuery query(m_db);
    query.prepare(QString("DELETE FROM function_document WHERE container_id = :cid"));
    query.bindValue(QString(":cid"), containerId);
    if (!query.exec()) {
        logError(query, QString("delete function_document"));
        return false;
    }
    return true;
}

FunctionDocumentParseResult FunctionRepository::parseFunctionDocument(const QString &xml) const
{
    FunctionDocumentParseResult result;
    if (xml.trimmed().isEmpty()) {
        result.warnings.append(QString("功能 XML 内容为空"));
        return result;
    }

    QDomDocument doc;
    QString errorMsg;
    int errorLine = 0;
    int errorColumn = 0;
    if (!doc.setContent(xml, &errorMsg, &errorLine, &errorColumn)) {
        result.warnings.append(QString("解析功能 XML 失败: %1 (line %2, column %3)")
                               .arg(errorMsg).arg(errorLine).arg(errorColumn));
        return result;
    }

    QDomElement root = doc.documentElement();
    if (root.isNull()) {
        result.warnings.append(QString("功能 XML 缺少根节点"));
        return result;
    }

    QDomElement treeStruct = root.firstChildElement(QString("treestruct"));
    if (!treeStruct.isNull()) {
        QDomElement itemElement = treeStruct.firstChildElement(QString("item"));
        while (!itemElement.isNull()) {
            result.tree.append(parseTreeItem(itemElement));
            itemElement = itemElement.nextSiblingElement(QString("item"));
        }
    }

    QMap<QString, FunctionInfo> map;
    QStringList warnings;
    QDomNodeList functionNodes = root.elementsByTagName(QString("functiondefine"));
    for (int i = 0; i < functionNodes.count(); ++i) {
        const QDomElement funcElement = functionNodes.at(i).toElement();
        if (funcElement.isNull())
            continue;
        FunctionInfo info = parseFunctionElement(funcElement, warnings);
        if (info.functionName.isEmpty()) {
            warnings.append(QString("检测到未命名的功能定义。"));
            continue;
        }
        if (map.contains(info.functionName)) {
            warnings.append(QString("功能名称重复: %1，已覆盖之前的定义").arg(info.functionName));
        }
        map.insert(info.functionName, info);
    }

    result.functionMap = map;
    result.warnings = warnings;
    result.success = true;
    return result;
}

int FunctionRepository::nextId() const
{
    QSqlQuery query(m_db);
    if (!query.exec(QString("SELECT IFNULL(MAX(FunctionID),0) + 1 FROM Function")))
        return 1;
    if (query.next())
        return query.value(0).toInt();
    return 1;
}

bool FunctionRepository::bindSymbol(int functionId, int symbolId)
{
    QSqlQuery query(m_db);
    // Try update first
    query.prepare(QString("UPDATE function_bindings SET symbol_id=:sid WHERE function_id=:fid"));
    query.bindValue(":sid", symbolId);
    query.bindValue(":fid", functionId);
    if (!query.exec()) {
        logError(query, QString("bind symbol (update)"));
        return false;
    }
    
    if (query.numRowsAffected() > 0)
        return true;

    // If no rows updated, insert
    QSqlQuery insertQuery(m_db);
    insertQuery.prepare(QString("INSERT INTO function_bindings(function_id, symbol_id) VALUES(:fid,:sid)"));
    insertQuery.bindValue(":fid", functionId);
    insertQuery.bindValue(":sid", symbolId);
    if (!insertQuery.exec()) {
        logError(insertQuery, QString("bind symbol (insert)"));
        return false;
    }
    return true;
}

void FunctionRepository::logError(const QSqlQuery &query, const QString &context) const
{
    if (!query.lastError().isValid())
        return;
    qWarning() << "FunctionRepository" << context << query.lastError() << query.lastQuery();
}

QString FunctionRepository::computeChecksum(const QString &xml) const
{
    const QByteArray data = xml.toUtf8();
    const QByteArray hash = QCryptographicHash::hash(data, QCryptographicHash::Sha256);
    return QString::fromLatin1(hash.toHex());
}

FunctionTreeNode FunctionRepository::parseTreeItem(const QDomElement &element) const
{
    FunctionTreeNode node;
    node.name = element.attribute(QString("name")).trimmed();
    QDomElement child = element.firstChildElement(QString("item"));
    while (!child.isNull()) {
        node.children.append(parseTreeItem(child));
        child = child.nextSiblingElement(QString("item"));
    }
    return node;
}

FunctionInfo FunctionRepository::parseFunctionElement(const QDomElement &element, QStringList &warnings) const
{
    FunctionInfo info;
    if (element.isNull())
        return info;

    info.functionName = trimmedChildText(element, QString("name"));
    info.description = trimmedChildText(element, QString("describe"));
    info.link = trimmedChildText(element, QString("link"));
    info.linkElements = parseComponentList(info.link);

    const QDomElement dependencyElement = element.firstChildElement(QString("dependency"));
    if (!dependencyElement.isNull()) {
        info.functionDependency = dependencyElement.firstChildElement(QString("function")).text().trimmed();
        info.componentDependency = dependencyElement.firstChildElement(QString("component")).text().trimmed();
        info.allRelatedComponent = dependencyElement.firstChildElement(QString("allComponent")).text().trimmed();
    }

    info.allComponentList = parseComponentList(info.allRelatedComponent);
    if (info.allComponentList.isEmpty()) {
        const QStringList components = parseComponentList(info.componentDependency);
        if (!components.isEmpty())
            info.allComponentList = components;
    }
    if (info.allComponentList.isEmpty()) {
        info.allComponentList = info.linkElements;
    }

    const QString attribute = trimmedChildText(element, QString("attribute"));
    const QStringList attributeParts = attribute.split(QLatin1Char(','), QString::SkipEmptyParts);
    if (!attributeParts.isEmpty()) {
        info.persistent = attributeParts.at(0).trimmed() != QString("NotPersistent");
    }
    if (attributeParts.size() >= 2) {
        bool ok = false;
        const double probability = attributeParts.at(1).trimmed().toDouble(&ok);
        info.faultProbability = ok ? probability : 0.0;
    } else {
        info.faultProbability = 0.0;
    }

    info.constraintIntegrity = trimmedChildText(element, QString("constraintIntegrity"));
    if (info.constraintIntegrity.isEmpty())
        info.constraintIntegrity = QString("未检查");

    info.constraintList.clear();
    QDomElement constraintElement = element.firstChildElement(QString("constraint"));
    while (!constraintElement.isNull()) {
        info.constraintList.append(buildTestItem(constraintElement));
        constraintElement = constraintElement.nextSiblingElement(QString("constraint"));
    }

    const QString actuatorKeyword = QString("执行器");
    bool actuatorSelected = false;
    bool hasFallback = false;
    TestItem fallbackItem;
    for (const TestItem &item : info.constraintList) {
        if (!hasFallback) {
            fallbackItem = item;
            hasFallback = true;
        }
        if (!actuatorSelected && item.testType.contains(actuatorKeyword)) {
            info.actuatorConstraint = item;
            info.actuatorName = componentNameFromVariable(item.variable);
            actuatorSelected = true;
        }
    }
    if (!actuatorSelected && hasFallback) {
        info.actuatorConstraint = fallbackItem;
        info.actuatorName = componentNameFromVariable(fallbackItem.variable);
    }

    info.offlineResults.clear();
    QDomElement offlineElement = element.firstChildElement(QString("offlineSolveResult"));
    while (!offlineElement.isNull()) {
        FunctionOfflineResult entry;
        entry.componentNames = parseComponentList(offlineElement.firstChildElement(QString("componentNames")).text());
        entry.failureModes = parseComponentList(offlineElement.firstChildElement(QString("failureModes")).text());
        bool ok = false;
        entry.probability = offlineElement.firstChildElement(QString("probability")).text().trimmed().toDouble(&ok);
        if (!ok)
            entry.probability = 0.0;
        info.offlineResults.append(entry);
        offlineElement = offlineElement.nextSiblingElement(QString("offlineSolveResult"));
    }

    const QDomElement variableConfig = element.firstChildElement(QString("variableValueConfig"));
    info.variableConfigXml = elementToString(variableConfig);

    if (info.functionName.isEmpty()) {
        warnings.append(QString("检测到缺少名称的功能定义。"));
    }

    return info;
}

QStringList FunctionRepository::parseComponentList(const QString &text) const
{
    return parseDelimitedListUnique(text);
}

QString FunctionRepository::buildFunctionDocument(const QMap<QString, FunctionInfo> &functions,
                                                  const QList<FunctionTreeNode> &tree) const
{
    QDomDocument doc(QStringLiteral("root"));
    QDomElement root = doc.createElement(QStringLiteral("root"));
    doc.appendChild(root);

    if (!tree.isEmpty()) {
        QDomElement treeStruct = doc.createElement(QStringLiteral("treestruct"));
        std::function<void(const FunctionTreeNode &, QDomElement &)> addNode =
            [&](const FunctionTreeNode &node, QDomElement &parent) {
                QDomElement item = doc.createElement(QStringLiteral("item"));
                item.setAttribute(QStringLiteral("name"), node.name);
                parent.appendChild(item);
                for (const auto &child : node.children) {
                    addNode(child, item);
                }
            };
        for (const auto &n : tree) {
            addNode(n, treeStruct);
        }
        root.appendChild(treeStruct);
    }

    for (auto it = functions.cbegin(); it != functions.cend(); ++it) {
        const FunctionInfo &info = it.value();
        QDomElement fn = doc.createElement(QStringLiteral("functiondefine"));

        auto appendText = [&](const QString &tag, const QString &value) {
            QDomElement el = doc.createElement(tag);
            el.appendChild(doc.createTextNode(value));
            fn.appendChild(el);
        };

        appendText(QStringLiteral("name"), info.functionName);
        appendText(QStringLiteral("describe"), info.description);
        appendText(QStringLiteral("link"), info.link);

        QDomElement dependency = doc.createElement(QStringLiteral("dependency"));
        QDomElement depFunc = doc.createElement(QStringLiteral("function"));
        depFunc.appendChild(doc.createTextNode(info.functionDependency));
        dependency.appendChild(depFunc);
        QDomElement depComp = doc.createElement(QStringLiteral("component"));
        depComp.appendChild(doc.createTextNode(info.componentDependency));
        dependency.appendChild(depComp);
        QDomElement depAll = doc.createElement(QStringLiteral("allComponent"));
        depAll.appendChild(doc.createTextNode(info.allRelatedComponent.isEmpty() ? info.allComponentList.join(QStringLiteral(",")) : info.allRelatedComponent));
        dependency.appendChild(depAll);
        fn.appendChild(dependency);

        QString attrText = QString("%1,%2")
                               .arg(info.persistent ? QStringLiteral("Persistent") : QStringLiteral("NotPersistent"))
                               .arg(info.faultProbability, 0, 'g', 6);
        appendText(QStringLiteral("attribute"), attrText);
        appendText(QStringLiteral("constraintIntegrity"), info.constraintIntegrity.isEmpty() ? QStringLiteral("未检查") : info.constraintIntegrity);

        for (const TestItem &item : info.constraintList) {
            QDomElement c = doc.createElement(QStringLiteral("constraint"));
            auto appendChild = [&](const QString &tag, const QString &val) {
                QDomElement el = doc.createElement(tag);
                el.appendChild(doc.createTextNode(val));
                c.appendChild(el);
            };
            appendChild(QStringLiteral("variable"), item.variable);
            appendChild(QStringLiteral("value"), item.value);
            appendChild(QStringLiteral("confidence"), QString::number(item.confidence));
            appendChild(QStringLiteral("type"), item.testType);
            fn.appendChild(c);
        }

        for (const FunctionOfflineResult &offline : info.offlineResults) {
            QDomElement off = doc.createElement(QStringLiteral("offlineSolveResult"));
            appendText(QStringLiteral("componentNames"), offline.componentNames.join(QStringLiteral(",")));
            appendText(QStringLiteral("failureModes"), offline.failureModes.join(QStringLiteral(",")));
            appendText(QStringLiteral("probability"), QString::number(offline.probability, 'g', 6));
            fn.appendChild(off);
        }

        if (!info.variableConfigXml.trimmed().isEmpty()) {
            QDomDocument tmp;
            tmp.setContent(info.variableConfigXml);
            if (!tmp.documentElement().isNull()) {
                QDomNode imported = doc.importNode(tmp.documentElement(), true);
                fn.appendChild(imported);
            }
        }

        root.appendChild(fn);
    }

    return doc.toString();
}
