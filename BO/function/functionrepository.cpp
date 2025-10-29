#include "BO/function/functionrepository.h"

#include <QSqlError>
#include <QSqlRecord>
#include <QtDebug>

FunctionRepository::FunctionRepository(const QSqlDatabase &db)
    : m_db(db)
{
}

bool FunctionRepository::ensureTables()
{
    if (!m_db.isValid() || !m_db.isOpen())
        return false;

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

    QSqlQuery pragma(m_db);
    pragma.exec(QString("PRAGMA foreign_keys = ON"));

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
        {"FaultProbability", "REAL DEFAULT 0.0"}
    };
    for (const auto &column : requiredColumns) {
        if (!ensureColumn(QString::fromLatin1(column.name), QString::fromLatin1(column.definition)))
            return false;
    }

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

QList<FunctionRecord> FunctionRepository::fetchAll() const
{
    QList<FunctionRecord> list;
    if (!m_db.isOpen()) return list;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "SELECT f.FunctionID, f.FunctionName, f.CmdValList, f.ExecsList, f.Remark,"
        " f.LinkText, f.ComponentDependency, f.AllComponents, f.FunctionDependency,"
        " f.PersistentFlag, f.FaultProbability,"
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
        rec.symbolId = query.value(11).toInt();
        rec.symbolName = query.value(12).toString();
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
        " f.PersistentFlag, f.FaultProbability,"
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
        rec.symbolId = query.value(11).toInt();
        rec.symbolName = query.value(12).toString();
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
        " f.PersistentFlag, f.FaultProbability,"
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
        rec.symbolId = query.value(11).toInt();
        rec.symbolName = query.value(12).toString();
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
        " LinkText, ComponentDependency, AllComponents, FunctionDependency, PersistentFlag, FaultProbability)"
        " VALUES(:id, :name, :execs, :cmds, :remark, :link, :componentDependency, :allComponents, :functionDependency, :persistent, :faultProbability)"));
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
        " FunctionDependency=:functionDependency, PersistentFlag=:persistent, FaultProbability=:faultProbability"
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

    QSqlQuery query(m_db);
    query.prepare(QString("DELETE FROM UserTest WHERE FunctionID=:fid"));
    query.bindValue(":fid", id);
    query.exec();

    query.prepare(QString("DELETE FROM Function WHERE FunctionID=:id"));
    query.bindValue(":id", id);
    if (!query.exec()) {
        logError(query, QString("delete function"));
        return false;
    }
    return true;
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
    query.prepare(QString(
        "INSERT INTO function_bindings(function_id, symbol_id)"
        " VALUES(:fid,:sid)"
        " ON CONFLICT(function_id) DO UPDATE SET symbol_id = excluded.symbol_id"));
    query.bindValue(":fid", functionId);
    query.bindValue(":sid", symbolId);
    if (!query.exec()) {
        logError(query, QString("bind symbol"));
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

