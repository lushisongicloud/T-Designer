#include "demo_projectbuilder.h"

#include "common.h"
#include <QDir>
#include <QFile>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QMap>
#include <QHash>
#include <QSet>
#include <QStringList>
#include <QVariant>
#include <QVector>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QTextStream>
#include <QDateTime>

#include <QDomDocument>

struct DemoProjectModelAccess
{
    static QString coilTModel() { return DemoProjectBuilder::coilTModel(); }
    static QString psuTModel() { return DemoProjectBuilder::psuTModel(); }
};

namespace {

inline bool execQuery(QSqlQuery &query, const QString &sql, QString *errorMessage)
{
    if (!query.exec(sql)) {
        if (errorMessage)
            *errorMessage = QString("SQL error: %1 (%2)").arg(query.lastError().text(), sql);
        return false;
    }
    return true;
}

inline bool prepareAndExec(QSqlQuery &query, const QString &sql, const QList<QVariant> &values, QString *errorMessage)
{
    query.prepare(sql);
    for (int i = 0; i < values.size(); ++i)
        query.bindValue(i, values.at(i));
    if (!query.exec()) {
        if (errorMessage)
            *errorMessage = QString("SQL error: %1 (%2)").arg(query.lastError().text(), sql);
        return false;
    }
    return true;
}

inline QString compactJson(const QJsonObject &obj)
{
    return QString::fromUtf8(QJsonDocument(obj).toJson(QJsonDocument::Compact));
}

inline QString compactJson(const QJsonArray &arr)
{
    return QString::fromUtf8(QJsonDocument(arr).toJson(QJsonDocument::Compact));
}

inline bool upsertFunctionDefineClass(QSqlDatabase &db, const QVariantList &row, QString *errorMessage)
{
    if (row.size() != 11)
        return false;

    QSqlQuery checkQuery(db);
    checkQuery.prepare(QString("SELECT COUNT(*) FROM FunctionDefineClass WHERE FunctionDefineClass_ID = ?"));
    checkQuery.bindValue(0, row.at(0));
    if (!checkQuery.exec()) {
        if (errorMessage)
            *errorMessage = QString("SQL error: %1 (%2)").arg(checkQuery.lastError().text(), checkQuery.lastQuery());
        return false;
    }

    bool exists = false;
    if (checkQuery.next())
        exists = checkQuery.value(0).toInt() > 0;

    if (exists) {
        QSqlQuery updateQuery(db);
        updateQuery.prepare(QString(
            "UPDATE FunctionDefineClass "
            "SET ParentNo=?, Level=?, Desc=?, _Order=?, FunctionDefineName=?, FunctionDefineCode=?, DefaultSymbol=?, FuncType=?, TModel=?, TClassName=? "
            "WHERE FunctionDefineClass_ID=?"));
        for (int i = 1; i < row.size(); ++i)
            updateQuery.bindValue(i - 1, row.at(i));
        updateQuery.bindValue(10, row.at(0));
        if (!updateQuery.exec()) {
            if (errorMessage)
                *errorMessage = QString("SQL error: %1 (%2)").arg(updateQuery.lastError().text(), updateQuery.lastQuery());
            return false;
        }
    } else {
        QSqlQuery insertQuery(db);
        insertQuery.prepare(QString(
            "INSERT INTO FunctionDefineClass (FunctionDefineClass_ID, ParentNo, Level, Desc, _Order, FunctionDefineName, FunctionDefineCode, DefaultSymbol, FuncType, TModel, TClassName) "
            "VALUES (?,?,?,?,?,?,?,?,?,?,?)"));
        for (int i = 0; i < row.size(); ++i)
            insertQuery.bindValue(i, row.at(i));
        if (!insertQuery.exec()) {
            if (errorMessage)
                *errorMessage = QString("SQL error: %1 (%2)").arg(insertQuery.lastError().text(), insertQuery.lastQuery());
            return false;
        }
    }

    return true;
}

inline bool fetchTableColumns(QSqlDatabase &db, const QString &tableName, QStringList *columns, QString *errorMessage)
{
    QSqlQuery pragma(db);
    const QString pragmaSql = QString("PRAGMA table_info(%1)").arg(tableName);
    if (!pragma.exec(pragmaSql)) {
        if (errorMessage)
            *errorMessage = QString("SQL error: %1 (%2)").arg(pragma.lastError().text(), pragmaSql);
        return false;
    }

    while (pragma.next())
        columns->append(pragma.value(1).toString());

    return true;
}

struct ReferenceEquipmentRow
{
    QString equipmentId;
    QString type;
    QString name;
    QString description;
    QString partCode;
    QString orderNum;
    QString factory;
    QString tModel;
    QString structure;
    QString repairInfo;
    QString picture;
    QString mtbf;
};

struct CategoryConfig
{
    QString key;
    QString displayName;
    QString prefix;
    int digits = 2;
    int startIndex = 1;
    int count = 0;
    int projectStructureId = 0;
    QString parentContainerKey;
    int pageId = 0;
    QStringList keywords;
    QString wireCategory;
    QString wireType;
};

struct ContainerSpec
{
    int containerId = 0;
    int projectStructureId = 0;
    QString key;
    QString name;
    QString level;
    QString description;
    int parentContainerId = 0;
};

struct EquipmentInstance
{
    int equipmentId = 0;
    int symbolId = 0;
    int pageId = 0;
    QString categoryKey;
    QString mark;
};

static QList<ReferenceEquipmentRow> fetchReferenceEquipmentRows(QSqlDatabase &refDb,
                                                                const QStringList &keywords,
                                                                int limit);
static QString defaultTModelForCategory(const QString &categoryKey, const QString &mark);
static QString formatDeviceMark(const QString &prefix, int value, int digits);
static bool populateHydraulicPowerSystemData(QSqlDatabase &db, QString *errorMessage);

} // namespace

bool DemoProjectBuilder::buildDemoProject(const QString &projectDir, const QString &projectName, QString *errorMessage)
{
    QDir dir;
    if (!dir.mkpath(projectDir)) {
        if (errorMessage)
            *errorMessage = QString("无法创建目录: %1").arg(projectDir);
        return false;
    }

    const QString swProPath = projectDir + "/" + projectName + ".swPro";
    const QString dbPath = projectDir + "/" + projectName + ".db";
    const QString paramsPath = projectDir + "/test.params";
    const QString canonicalPageStem = BuildCanonicalPageName(QString("=Subsystem+Station 1"),
                                                             QString("Demo Diagram"),
                                                             QString("D1"));
    const QString dwgPath = projectDir + "/" + canonicalPageStem + ".dwg";
    const QString templatePath = QDir::cleanPath(QString("D:/SynologyDrive/Project/T_DESIGNER/templete/project.db"));
    qDebug()<<"templatePath = "<<templatePath;
    qDebug()<<"dbPath = "<<dbPath;

    QFile::remove(swProPath);
    QFile::remove(dbPath);
    QFile::remove(paramsPath);
    QFile::remove(dwgPath);
    QFile::remove(projectDir + "/D1.dwg");

    if (!QFile::exists(templatePath)) {
        if (errorMessage)
            *errorMessage = QString("模板数据库不存在: %1").arg(templatePath);
        return false;
    }

    if (!QFile::copy(templatePath, dbPath)) {
        if (errorMessage)
            *errorMessage = QString("复制模板数据库失败: %1").arg(dbPath);
        return false;
    }
    QFile::setPermissions(dbPath, QFile::permissions(templatePath));

    if (!writeSwProFile(swProPath, projectName, errorMessage))
        return false;
    if (!populateProjectDatabase(dbPath, errorMessage))
        return false;
    if (!writeTestParams(paramsPath, errorMessage))
        return false;

    // create placeholder DWG file for completeness
    QFile dwg(dwgPath);
    if (dwg.open(QIODevice::WriteOnly | QIODevice::Text)) {
        QTextStream out(&dwg);
        out << "Demo DWG placeholder generated at " << QDateTime::currentDateTime().toString(Qt::ISODate);
        dwg.close();
    }

    return true;
}

bool DemoProjectBuilder::writeSwProFile(const QString &filePath, const QString &projectName, QString *errorMessage)
{
    QFile file(filePath);
    if (!file.open(QIODevice::WriteOnly | QIODevice::Text)) {
        if (errorMessage)
            *errorMessage = QString("无法创建项目文件: %1").arg(filePath);
        return false;
    }
    file.write(projectName.toUtf8());
    file.close();
    return true;
}

bool DemoProjectBuilder::writeTestParams(const QString &filePath, QString *errorMessage)
{
    QFile file(filePath);
    if (!file.open(QIODevice::WriteOnly | QIODevice::Text)) {
        if (errorMessage)
            *errorMessage = QString("无法创建测试参数文件: %1").arg(filePath);
        return false;
    }
    QTextStream out(&file);
    out << "# Demo test parameters\n"
        << "Voltage=24V\n"
        << "Pressure=8bar\n";
    file.close();
    return true;
}

bool DemoProjectBuilder::populateProjectDatabase(const QString &dbPath, QString *errorMessage)
{
    const QString connName = QString("demo_project_builder");
    QSqlDatabase db = QSqlDatabase::addDatabase("QSQLITE", connName);
    db.setDatabaseName(dbPath);
    if (!db.open()) {
        if (errorMessage)
            *errorMessage = QString("无法创建数据库: %1").arg(db.lastError().text());
        db = QSqlDatabase();
        QSqlDatabase::removeDatabase(connName);
        return false;
    }

    auto cleanup = [&]() {
        db.close();
        db = QSqlDatabase();
        QSqlDatabase::removeDatabase(connName);
    };

    QSqlQuery query(db);

    const QStringList createStatements = {
        "CREATE TABLE IF NOT EXISTS ProjectStructure (ProjectStructure_ID INTEGER PRIMARY KEY, Structure_ID TEXT, Structure_INT TEXT, Parent_ID INTEGER, Struct_Desc TEXT)",
        "CREATE TABLE IF NOT EXISTS Equipment (Equipment_ID INTEGER PRIMARY KEY, ProjectStructure_ID INTEGER, DT TEXT, Type TEXT, Eqpt_Category TEXT, Name TEXT, Desc TEXT, PartCode TEXT, SymbRemark TEXT, OrderNum TEXT, Factory TEXT, TVariable TEXT, TModel TEXT, Structure TEXT, RepairInfo TEXT, Picture TEXT, MTBF TEXT)",
        "CREATE TABLE IF NOT EXISTS EquipmentDiagnosePara (DiagnoseParaID INTEGER PRIMARY KEY, Equipment_ID INTEGER, Name TEXT, Unit TEXT, CurValue TEXT, DefaultValue TEXT, Remark TEXT)",
        "CREATE TABLE IF NOT EXISTS Symbol (Symbol_ID INTEGER PRIMARY KEY, Equipment_ID INTEGER, Page_ID INTEGER, Symbol TEXT, Symbol_Category TEXT, Symbol_Desc TEXT, Designation TEXT, Symbol_Handle TEXT, Symbol_Remark TEXT, FunDefine TEXT, FuncType TEXT, SourceConn INTEGER, ExecConn INTEGER, SourcePrior INTEGER, InterConnect TEXT, Show_DT TEXT)",
        "CREATE TABLE IF NOT EXISTS Symb2TermInfo (Symb2TermInfo_ID INTEGER PRIMARY KEY, Symbol_ID INTEGER, ConnNum TEXT, ConnDesc TEXT)",
        "CREATE TABLE IF NOT EXISTS Page (Page_ID INTEGER PRIMARY KEY, ProjectStructure_ID INTEGER, Page_Desc TEXT, PageType TEXT, PageNum INTEGER, PageName TEXT, Scale TEXT, Border TEXT, Title TEXT, AlterTime TEXT, MD5Code TEXT)",
        "CREATE TABLE IF NOT EXISTS JXB (JXB_ID INTEGER PRIMARY KEY, ProjectStructure_ID INTEGER, Page_ID INTEGER, Cable_ID INTEGER, ConnectionNumber TEXT, ConnectionNumber_Handle TEXT, Symb1_ID TEXT, Symb2_ID TEXT, Wires_Type TEXT, Wires_Color TEXT, Wires_Diameter TEXT, Wires_Category TEXT, Symb1_Category TEXT, Symb2_Category TEXT)",
        "CREATE TABLE IF NOT EXISTS Connector (Connector_ID INTEGER PRIMARY KEY, Page_ID INTEGER, Symb_ID INTEGER)",
        "CREATE TABLE IF NOT EXISTS Link (Link_ID INTEGER PRIMARY KEY, Page_ID INTEGER)",
        "CREATE TABLE IF NOT EXISTS Wires (Wires_ID INTEGER PRIMARY KEY, Page_ID INTEGER)",
        "CREATE TABLE IF NOT EXISTS Terminal (Terminal_ID INTEGER PRIMARY KEY, TerminalStrip_ID INTEGER, Designation TEXT, ShortJumper TEXT)",
        "CREATE TABLE IF NOT EXISTS TerminalStrip (TerminalStrip_ID INTEGER PRIMARY KEY, ProjectStructure_ID INTEGER, DT TEXT)",
        "CREATE TABLE IF NOT EXISTS TerminalTerm (TerminalTerm_ID INTEGER PRIMARY KEY, Terminal_ID INTEGER, ConnNum TEXT)",
        "CREATE TABLE IF NOT EXISTS TerminalInstance (TerminalInstanceID INTEGER PRIMARY KEY, TerminalStrip_ID INTEGER, Terminal_ID INTEGER, Coordinate TEXT)",
        "CREATE TABLE IF NOT EXISTS TerminalStripDiagnosePara (DiagnoseParaID INTEGER PRIMARY KEY, TerminalStrip_ID INTEGER, Name TEXT, Unit TEXT, CurValue TEXT)",
        "CREATE TABLE IF NOT EXISTS Cable (Cable_ID INTEGER PRIMARY KEY)",
        "CREATE TABLE IF NOT EXISTS Line (Line_ID INTEGER PRIMARY KEY)",
        "CREATE TABLE IF NOT EXISTS Function (FunctionID INTEGER PRIMARY KEY, FunctionName TEXT, ExecsList TEXT, CmdValList TEXT, Remark TEXT, LinkText TEXT, ComponentDependency TEXT, AllComponents TEXT, FunctionDependency TEXT, PersistentFlag INTEGER, FaultProbability REAL)",
        "CREATE TABLE IF NOT EXISTS function_bindings (function_id INTEGER PRIMARY KEY, symbol_id INTEGER)",
        "CREATE TABLE IF NOT EXISTS FunctionDefineClass (FunctionDefineClass_ID INTEGER PRIMARY KEY, ParentNo INTEGER, Level INTEGER, Desc TEXT, _Order INTEGER, FunctionDefineName TEXT, FunctionDefineCode TEXT, DefaultSymbol TEXT, FuncType TEXT, TModel TEXT, TClassName TEXT)",
        "CREATE TABLE IF NOT EXISTS UserTest (UserTest_ID INTEGER PRIMARY KEY, FunctionID INTEGER, Name TEXT)",
        "CREATE TABLE IF NOT EXISTS containers (id INTEGER PRIMARY KEY, name TEXT, type INTEGER, parent_id INTEGER, order_index INTEGER, analysis_depth INTEGER, interface_json TEXT, behavior_smt TEXT, fault_modes_json TEXT, tests_json TEXT, analysis_json TEXT, equipment_id INTEGER, equipment_type TEXT, equipment_name TEXT)",
        "CREATE TABLE IF NOT EXISTS equipment_containers (equipment_id INTEGER PRIMARY KEY, container_id INTEGER)",
        "CREATE TABLE IF NOT EXISTS container (container_id INTEGER PRIMARY KEY AUTOINCREMENT, project_structure_id INTEGER NOT NULL, name TEXT NOT NULL, level TEXT NOT NULL, source_equipment_id INTEGER, auto_generated INTEGER NOT NULL DEFAULT 0, description TEXT, fault_analysis_depth TEXT, inherits_from_container_id INTEGER, created_at TEXT DEFAULT CURRENT_TIMESTAMP, updated_at TEXT DEFAULT CURRENT_TIMESTAMP)",
        "CREATE TABLE IF NOT EXISTS container_hierarchy (parent_id INTEGER NOT NULL, child_id INTEGER NOT NULL, relation_type TEXT DEFAULT 'contains', PRIMARY KEY (parent_id, child_id))",
        "CREATE TABLE IF NOT EXISTS container_component (container_id INTEGER NOT NULL, equipment_id INTEGER NOT NULL, role TEXT, PRIMARY KEY (container_id, equipment_id))",
        "CREATE TABLE IF NOT EXISTS container_interface (interface_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, name TEXT NOT NULL, direction TEXT NOT NULL, signal_category TEXT NOT NULL, signal_subtype TEXT, physical_domain TEXT, default_unit TEXT, description TEXT, inherits_interface_id INTEGER)",
        "CREATE TABLE IF NOT EXISTS container_interface_binding (binding_id INTEGER PRIMARY KEY AUTOINCREMENT, interface_id INTEGER NOT NULL, equipment_id INTEGER, terminal_id INTEGER, connect_line_id INTEGER, binding_role TEXT)",
        "CREATE TABLE IF NOT EXISTS container_state (state_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, name TEXT NOT NULL, state_type TEXT NOT NULL, derived_from_children INTEGER NOT NULL DEFAULT 0, probability REAL, rationale TEXT, analysis_scope TEXT)",
        "CREATE TABLE IF NOT EXISTS container_state_behavior (behavior_id INTEGER PRIMARY KEY AUTOINCREMENT, state_id INTEGER NOT NULL, representation TEXT NOT NULL, expression TEXT NOT NULL, notes TEXT)",
        "CREATE TABLE IF NOT EXISTS container_state_interface (id INTEGER PRIMARY KEY AUTOINCREMENT, state_id INTEGER NOT NULL, interface_id INTEGER NOT NULL, constraint TEXT)",
        "CREATE TABLE IF NOT EXISTS function_definition (function_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, parent_function_id INTEGER, name TEXT NOT NULL, description TEXT, requirement TEXT, expected_output TEXT, detection_rule TEXT, auto_generated INTEGER NOT NULL DEFAULT 0)",
        "CREATE TABLE IF NOT EXISTS function_io (io_id INTEGER PRIMARY KEY AUTOINCREMENT, function_id INTEGER NOT NULL, io_type TEXT NOT NULL, name TEXT NOT NULL, interface_id INTEGER, default_value TEXT, expression TEXT, description TEXT)",
        "CREATE TABLE IF NOT EXISTS function_dependency (function_id INTEGER NOT NULL, depends_on_function_id INTEGER NOT NULL, dependency_type TEXT DEFAULT 'requires', PRIMARY KEY (function_id, depends_on_function_id))",
        "CREATE TABLE IF NOT EXISTS test_definition (test_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER, function_id INTEGER, related_state_id INTEGER, test_type TEXT NOT NULL, name TEXT NOT NULL, description TEXT, auto_generated INTEGER NOT NULL DEFAULT 1, interface_id INTEGER, signal_category TEXT, expected_result TEXT, complexity INTEGER, estimated_duration REAL, estimated_cost REAL)",
        "CREATE TABLE IF NOT EXISTS test_fault_coverage (test_id INTEGER NOT NULL, state_id INTEGER NOT NULL, coverage_type TEXT NOT NULL, confidence REAL, PRIMARY KEY (test_id, state_id, coverage_type))",
        "CREATE TABLE IF NOT EXISTS test_constraint (constraint_id INTEGER PRIMARY KEY AUTOINCREMENT, test_id INTEGER NOT NULL, constraint_type TEXT NOT NULL, value TEXT, unit TEXT)",
        "CREATE TABLE IF NOT EXISTS analysis_requirement (requirement_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, metric TEXT NOT NULL, target_value REAL NOT NULL, unit TEXT DEFAULT 'ratio', notes TEXT)",
        "CREATE TABLE IF NOT EXISTS analysis_constraint (constraint_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, constraint_type TEXT NOT NULL, value TEXT, unit TEXT)",
        "CREATE TABLE IF NOT EXISTS test_plan_candidate (candidate_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, name TEXT NOT NULL, description TEXT, total_cost REAL, total_duration REAL, selection_notes TEXT)",
        "CREATE TABLE IF NOT EXISTS test_plan_candidate_item (candidate_id INTEGER NOT NULL, test_id INTEGER NOT NULL, PRIMARY KEY (candidate_id, test_id))",
        "CREATE TABLE IF NOT EXISTS diagnosis_tree (tree_id INTEGER PRIMARY KEY AUTOINCREMENT, container_id INTEGER NOT NULL, name TEXT, description TEXT)",
        "CREATE TABLE IF NOT EXISTS diagnosis_tree_node (node_id INTEGER PRIMARY KEY AUTOINCREMENT, tree_id INTEGER NOT NULL, parent_node_id INTEGER, test_id INTEGER, state_id INTEGER, outcome TEXT, comment TEXT)"
    };

    for (const QString &statement : createStatements) {
        if (!execQuery(query, statement, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QStringList tablesToReset = {
        QString("diagnosis_tree_node"),
        QString("diagnosis_tree"),
        QString("test_plan_candidate_item"),
        QString("test_plan_candidate"),
        QString("test_fault_coverage"),
        QString("test_constraint"),
        QString("test_definition"),
        QString("analysis_constraint"),
        QString("analysis_requirement"),
        QString("function_dependency"),
        QString("function_io"),
        QString("function_definition"),
        QString("container_state_interface"),
        QString("container_state_behavior"),
        QString("container_state"),
        QString("container_interface_binding"),
        QString("container_interface"),
        QString("container_component"),
        QString("container_hierarchy"),
        QString("container"),
        QString("containers"),
        QString("equipment_containers"),
        QString("UserTest"),
        QString("Function"),
        QString("function_bindings"),
        QString("JXB"),
        QString("Connector"),
        QString("Link"),
        QString("Wires"),
        QString("TerminalInstance"),
        QString("TerminalTerm"),
        QString("TerminalStripDiagnosePara"),
        QString("TerminalStrip"),
        QString("Terminal"),
        QString("Cable"),
        QString("Line"),
        QString("Symbol"),
        QString("Symb2TermInfo"),
        QString("EquipmentDiagnosePara"),
        QString("Equipment"),
        QString("Page"),
        QString("ProjectStructure"),
        QString("FunctionDefineClass")
    };

    for (const QString &table : tablesToReset) {
        const QString sql = QString("DELETE FROM %1").arg(table);
        if (!execQuery(query, sql, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QVariantList> functionDefineClasses = {
        {QVariant(1), QVariant(0), QVariant(0), QString(), QVariant(1), QString("电气工程"), QVariant(), QVariant(), QVariant(), QVariant(), QVariant()},
        {QVariant(102), QVariant(1), QVariant(1), QString(), QVariant(2), QString("线圈,触点"), QVariant(), QVariant(), QVariant(), QVariant(), QVariant()},
        {QVariant(10200), QVariant(102), QVariant(2), QString(), QVariant(1), QString("线圈"), QString("200"), QVariant(), QVariant(), QVariant(), QVariant()},
        {QVariant(1020001), QVariant(10200), QVariant(3), QString(), QVariant(1), QString("线圈,2 个连接点"), QString("200.1"), QVariant(), QString("接线端口"), coilBaseTModel(), QString("KA_xq")},
        {QVariant(102000100), QVariant(1020001), QVariant(4), QString(), QVariant(1), QString("线圈,常规"), QString("200.1.0"), QString("SPS_M_K-1"), QString("接线端口"), coilTModel(), QString("NewKA_xq")},
        {QVariant(117), QVariant(1), QVariant(1), QString(), QVariant(17), QString("elecPort"), QVariant(), QVariant(), QVariant(), elecPortTModel(), QString("elecPort")},
        {QVariant(107), QVariant(1), QVariant(1), QString(), QVariant(6), QString("电源,发电机"), QVariant(), QVariant(), QVariant(), QVariant(), QVariant()},
        {QVariant(10700), QVariant(107), QVariant(2), QString(), QVariant(1), QString("电压源"), QString("700"), QVariant(), QVariant(), QVariant(), QVariant()},
        {QVariant(1070099), QVariant(10700), QVariant(3), QString(), QVariant(2), QString("电压源,可变"), QString("700.99"), QVariant(), QVariant(), QVariant(), QVariant()},
        {QVariant(107009901), QVariant(1070099), QVariant(4), QString(), QVariant(1), QString("电压源,可变"), QString("700.99.1"), QString("SPS_M_BAT-1"), QVariant(), psuTModel(), QString("DC24VSource")}
    };

    for (const QVariantList &row : functionDefineClasses) {
        if (!upsertFunctionDefineClass(db, row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    if (!db.transaction()) {
        if (errorMessage)
            *errorMessage = QString("无法开启数据库事务: %1").arg(db.lastError().text());
        cleanup();
        return false;
    }

    if (!populateHydraulicPowerSystemData(db, errorMessage)) {
        db.rollback();
        cleanup();
        return false;
    }

    if (!db.commit()) {
        if (errorMessage)
            *errorMessage = QString("数据库提交失败: %1").arg(db.lastError().text());
        cleanup();
        return false;
    }

    cleanup();
    return true;
}

namespace {

QString formatDeviceMark(const QString &prefix, int value, int digits)
{
    return prefix + QString::number(value).rightJustified(digits, QLatin1Char('0'));
}

QString defaultTModelForCategory(const QString &categoryKey, const QString &mark)
{
    if (categoryKey == QString("relay") || categoryKey == QString("contactor"))
        return DemoProjectModelAccess::coilTModel();
    if (categoryKey == QString("breaker"))
        return DemoProjectModelAccess::psuTModel();
    return QString("component %1_%2 { state nominal; }").arg(categoryKey, mark);
}

QList<ReferenceEquipmentRow> fetchReferenceEquipmentRows(QSqlDatabase &refDb,
                                                         const QStringList &keywords,
                                                         int limit)
{
    QList<ReferenceEquipmentRow> rows;
    if (limit <= 0)
        return rows;

    const QString selectPrefix = QString(
        "SELECT Equipment_ID, Type, Name, \"Desc\", PartCode, OrderNum, Factory_ID, TModel, Structure, RepairInfo, Picture, MTBF FROM Equipment");
    QSet<QString> seen;

    auto fetchWithSql = [&](const QString &sql) {
        QSqlQuery refQuery(refDb);
        if (!refQuery.exec(sql))
            return;
        while (refQuery.next()) {
            const QString equipmentId = refQuery.value(0).toString();
            if (seen.contains(equipmentId))
                continue;
            ReferenceEquipmentRow row;
            row.equipmentId = equipmentId;
            row.type = refQuery.value(1).toString();
            row.name = refQuery.value(2).toString();
            row.description = refQuery.value(3).toString();
            row.partCode = refQuery.value(4).toString();
            row.orderNum = refQuery.value(5).toString();
            row.factory = refQuery.value(6).toString();
            row.tModel = refQuery.value(7).toString();
            row.structure = refQuery.value(8).toString();
            row.repairInfo = refQuery.value(9).toString();
            row.picture = refQuery.value(10).toString();
            row.mtbf = refQuery.value(11).toString();
            rows.append(row);
            seen.insert(equipmentId);
            if (rows.size() >= limit)
                return;
        }
    };

    bool matchedKeyword = false;
    for (const QString &keyword : keywords) {
        const QString trimmed = keyword.trimmed();
        if (trimmed.isEmpty())
            continue;
        matchedKeyword = true;
        QString sanitized = trimmed;
        sanitized.replace('\'', QString("''"));
        const QString sql = QString("%1 WHERE (Name LIKE '%%2%%' OR \"Desc\" LIKE '%%2%%') ORDER BY Equipment_ID LIMIT %3")
                                .arg(selectPrefix)
                                .arg(sanitized)
                                .arg(limit);
        fetchWithSql(sql);
        if (rows.size() >= limit)
            break;
    }

    if (!matchedKeyword || rows.isEmpty()) {
        const QString sql = QString("%1 ORDER BY Equipment_ID LIMIT %2").arg(selectPrefix).arg(limit);
        fetchWithSql(sql);
    }

    return rows;
}

bool populateHydraulicPowerSystemData(QSqlDatabase &db, QString *errorMessage)
{
    QSqlQuery query(db);

    const int structRoot = 2001;
    const int structControlCabinet = 2002;
    const int structDistribution = 2003;
    const int structHydraulic = 2004;
    const int structSensor = 2005;
    const int structPump1 = 2006;
    const int structPump2 = 2007;
    const int structPump3 = 2008;
    const int structPump4 = 2009;
    const int structPlcRack = 2010;
    const int structActuatorBay = 2011;
    const int structInterface = 2012;
    const int structLocalOps = 2013;
    const int structNetwork = 2014;
    const int structAmplifier = 2015;

    const QList<QList<QVariant>> projectStructures = {
        {structRoot, QString("1"), QString("集中油源动力系统"), 0, QString("集中油源动力系统根节点")},
        {structControlCabinet, QString("3"), QString("油源动力系统控制柜"), structRoot, QString("控制柜")},
        {structDistribution, QString("3"), QString("配电系统"), structRoot, QString("配电与电源滤波")},
        {structHydraulic, QString("3"), QString("液压泵站"), structRoot, QString("液压泵站总成")},
        {structSensor, QString("5"), QString("传感器网络"), structRoot, QString("传感器层")},
        {structPump1, QString("6"), QString("1#收放系统供油回路"), structHydraulic, QString("为1#收放系统供油")},
        {structPump2, QString("6"), QString("2#收放系统供油回路"), structHydraulic, QString("为2#收放系统供油")},
        {structPump3, QString("6"), QString("3#收放系统供油回路"), structHydraulic, QString("为3#收放系统供油")},
        {structPump4, QString("6"), QString("4#收放系统供油回路"), structHydraulic, QString("为4#收放系统供油")},
        {structPlcRack, QString("5"), QString("PLC机柜"), structControlCabinet, QString("PLC1/PLC2 机柜")},
        {structActuatorBay, QString("5"), QString("执行机构区"), structHydraulic, QString("比例电磁铁与电磁阀")},
        {structInterface, QString("5"), QString("MTA接口模块"), structControlCabinet, QString("接口模块区")},
        {structLocalOps, QString("5"), QString("本地操作单元"), structControlCabinet, QString("本地操作单元")},
        {structNetwork, QString("5"), QString("控制网络"), structControlCabinet, QString("主/从控制网络")},
        {structAmplifier, QString("5"), QString("放大板区"), structDistribution, QString("信号放大板区")}
    };

    for (const auto &row : projectStructures) {
        if (!prepareAndExec(query,
                            "INSERT INTO ProjectStructure (ProjectStructure_ID, Structure_ID, Structure_INT, Parent_ID, Struct_Desc) VALUES (?,?,?,?,?)",
                            row,
                            errorMessage)) {
            return false;
        }
    }

    const QString alterTime = QDateTime::currentDateTime().toString(QString("yyyy-MM-dd hh:mm:ss"));
    const int pageControl = 3101;
    const int pageDistribution = 3102;
    const int pageHydraulic = 3103;
    const int pageSensor = 3104;
    const int pageNetwork = 3105;

    const QList<QList<QVariant>> pages = {
        {pageControl, structControlCabinet, QString("控制柜主回路"), QString("原理图"), 1, QString("CC-01"), QString("1:20"), QString("A2 594x420"), QString("油源动力控制柜"), alterTime, QString()},
        {pageDistribution, structDistribution, QString("配电系统"), QString("原理图"), 2, QString("PD-01"), QString("1:25"), QString("A2 594x420"), QString("配电系统"), alterTime, QString()},
        {pageHydraulic, structHydraulic, QString("液压泵站"), QString("原理图"), 3, QString("HY-01"), QString("1:15"), QString("A1 841x594"), QString("液压泵站"), alterTime, QString()},
        {pageSensor, structSensor, QString("传感器网络"), QString("I/O图"), 4, QString("SN-01"), QString("1:40"), QString("A3 420x297"), QString("传感器网络"), alterTime, QString()},
        {pageNetwork, structNetwork, QString("控制网络"), QString("联接图"), 5, QString("NET-01"), QString("1:30"), QString("A3 420x297"), QString("控制网络"), alterTime, QString()}
    };

    for (const auto &row : pages) {
        if (!prepareAndExec(query,
                            "INSERT INTO Page (Page_ID, ProjectStructure_ID, Page_Desc, PageType, PageNum, PageName, Scale, Border, Title, AlterTime, MD5Code) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                            row,
                            errorMessage)) {
            return false;
        }
    }

    const QList<ContainerSpec> baseContainers = {
        {1, structRoot, QString("root"), QString("集中油源动力系统"), QString("system"), QString("系统根容器"), 0},
        {2, structControlCabinet, QString("control_cabinet"), QString("控制柜"), QString("subsystem"), QString("控制柜母线"), 1},
        {3, structDistribution, QString("distribution"), QString("配电系统"), QString("subsystem"), QString("配电主体"), 1},
        {4, structHydraulic, QString("hydraulic_pump"), QString("液压泵站"), QString("subsystem"), QString("液压泵站容器"), 1},
        {5, structSensor, QString("sensor_array"), QString("传感器网络"), QString("subsystem"), QString("传感器列阵"), 1},
        {6, structPlcRack, QString("plc_rack"), QString("PLC机柜"), QString("subsystem"), QString("PLC1/PLC2 柜"), 2},
        {7, structActuatorBay, QString("actuator_bay"), QString("执行机构区"), QString("subsystem"), QString("执行机构列阵"), 4},
        {8, structNetwork, QString("network_segment"), QString("控制网络"), QString("subsystem"), QString("主/从网络"), 2},
        {9, structInterface, QString("interface_zone"), QString("接口模块区"), QString("subsystem"), QString("MTA 接口模块区"), 2},
        {10, structAmplifier, QString("amplifier_panel"), QString("放大板区"), QString("subsystem"), QString("信号放大板"), 3}
    };

    QHash<QString, int> containerIdByKey;
    int maxContainerId = 0;
    for (const ContainerSpec &spec : baseContainers) {
        QVariantList row = {
            spec.containerId,
            spec.projectStructureId,
            spec.name,
            spec.level,
            QVariant(),
            1,
            spec.description,
            QVariant(),
            QVariant()
        };
        if (!prepareAndExec(query,
                            "INSERT INTO container (container_id, project_structure_id, name, level, source_equipment_id, auto_generated, description, fault_analysis_depth, inherits_from_container_id) VALUES (?,?,?,?,?,?,?,?,?)",
                            row,
                            errorMessage)) {
            return false;
        }
        containerIdByKey.insert(spec.key, spec.containerId);
        maxContainerId = qMax(maxContainerId, spec.containerId);
        if (spec.parentContainerId > 0) {
            QVariantList hierarchyRow = {spec.parentContainerId, spec.containerId, QString("contains")};
            if (!prepareAndExec(query,
                                "INSERT INTO container_hierarchy (parent_id, child_id, relation_type) VALUES (?,?,?)",
                                hierarchyRow,
                                errorMessage)) {
                return false;
            }
        }
    }

    const QString refConnName = QString("ldmain_reference_connection");
    QSqlDatabase refDb = QSqlDatabase::addDatabase(QString("QSQLITE"), refConnName);
    refDb.setDatabaseName(QDir::cleanPath(QString("ref/LdMainData.db")));
    if (!refDb.open()) {
        if (errorMessage)
            *errorMessage = QString("无法打开器件库 ref/LdMainData.db: %1").arg(refDb.lastError().text());
        refDb = QSqlDatabase();
        QSqlDatabase::removeDatabase(refConnName);
        return false;
    }

    auto closeReferenceDb = [&]() {
        refDb.close();
        refDb = QSqlDatabase();
        QSqlDatabase::removeDatabase(refConnName);
    };

    const QList<CategoryConfig> categories = {
        {QString("relay"), QString("继电器"), QString("KA"), 2, 1, 520, structControlCabinet, QString("control_cabinet"), pageControl, {QString("继电器"), QString("relay")}, QString("控制线"), QString("control")},
        {QString("contactor"), QString("接触器"), QString("KM"), 2, 1, 420, structControlCabinet, QString("control_cabinet"), pageControl, {QString("接触器"), QString("contactor")}, QString("动力线"), QString("power")},
        {QString("breaker"), QString("断路器"), QString("QF"), 2, 1, 420, structDistribution, QString("distribution"), pageDistribution, {QString("断路器"), QString("breaker")}, QString("动力线"), QString("power")},
        {QString("solenoid"), QString("电磁阀"), QString("YV"), 3, 101, 460, structHydraulic, QString("hydraulic_pump"), pageHydraulic, {QString("阀"), QString("solenoid")}, QString("动力线"), QString("hydraulic-control")},
        {QString("switch_sensor"), QString("开关型传感器"), QString("SQ"), 3, 101, 420, structSensor, QString("sensor_array"), pageSensor, {QString("开关"), QString("switch")}, QString("信号线"), QString("digital-signal")},
        {QString("analog_sensor"), QString("模拟量传感器"), QString("SA"), 3, 101, 360, structSensor, QString("sensor_array"), pageSensor, {QString("sensor"), QString("传感器")}, QString("信号线"), QString("analog-signal")},
        {QString("proportional_solenoid"), QString("比例电磁铁"), QString("BT"), 3, 101, 260, structActuatorBay, QString("actuator_bay"), pageHydraulic, {QString("比例"), QString("伺服")}, QString("动力线"), QString("hydraulic-control")},
        {QString("filter"), QString("电源滤波器"), QString("PF"), 2, 1, 200, structDistribution, QString("distribution"), pageDistribution, {QString("滤波"), QString("filter")}, QString("动力线"), QString("power")},
        {QString("plc"), QString("PLC"), QString("PLC"), 2, 1, 160, structPlcRack, QString("plc_rack"), pageControl, {QString("PLC"), QString("controller")}, QString("控制线"), QString("control")},
        {QString("meter"), QString("电表"), QString("EM"), 2, 1, 160, structDistribution, QString("distribution"), pageDistribution, {QString("Sensor"), QString("meter")}, QString("信号线"), QString("monitor")},
        {QString("amplifier"), QString("放大板"), QString("AM"), 2, 1, 150, structAmplifier, QString("amplifier_panel"), pageControl, {QString("放大"), QString("amplifier")}, QString("控制线"), QString("control")},
        {QString("network_module"), QString("网络模块"), QString("NET"), 2, 1, 160, structNetwork, QString("network_segment"), pageNetwork, {QString("模块"), QString("module")}, QString("信号线"), QString("network")}
    };

    QHash<QString, QList<ReferenceEquipmentRow>> referenceByCategory;
    for (const CategoryConfig &config : categories) {
        const int fetchLimit = qMax(5, qMin(config.count, 30));
        QList<ReferenceEquipmentRow> refs = fetchReferenceEquipmentRows(refDb, config.keywords, fetchLimit);
        if (refs.isEmpty())
            refs = fetchReferenceEquipmentRows(refDb, QStringList(), 10);
        if (refs.isEmpty()) {
            ReferenceEquipmentRow fallback;
            fallback.name = config.displayName;
            fallback.description = QString("%1 预置元件").arg(config.displayName);
            fallback.factory = QString("T-Designer");
            refs.append(fallback);
        }
        referenceByCategory.insert(config.key, refs);
    }

    closeReferenceDb();

    QVector<EquipmentInstance> instances;
    instances.reserve(4000);
    QHash<QString, QVector<int>> categoryIndexes;

    int nextEquipmentId = 1;
    int nextContainerId = maxContainerId + 1;
    int nextSymbolId = 1;
    int nextSymbTermId = 1;
    int nextConnectLineId = 1;

    auto insertEquipmentInstance = [&](const CategoryConfig &config, int sequenceIndex, const ReferenceEquipmentRow &refRow) -> bool {
        const int equipmentId = nextEquipmentId++;
        const int baseValue = config.startIndex + sequenceIndex;
        const QString mark = formatDeviceMark(config.prefix, baseValue, config.digits);
        QVariantList equipmentRow = {
            equipmentId,
            config.projectStructureId,
            mark,
            refRow.type.isEmpty() ? config.displayName : refRow.type,
            QString("普通元件"),
            refRow.name.isEmpty() ? config.displayName : refRow.name,
            refRow.description,
            refRow.partCode.isEmpty() ? QString("%1-%2").arg(config.prefix).arg(baseValue) : refRow.partCode,
            config.displayName,
            refRow.orderNum.isEmpty() ? QString::number(baseValue) : refRow.orderNum,
            refRow.factory.isEmpty() ? QString("T-Designer") : refRow.factory,
            QString("%1.signal").arg(mark),
            refRow.tModel.isEmpty() ? defaultTModelForCategory(config.key, mark) : refRow.tModel,
            refRow.structure,
            refRow.repairInfo,
            refRow.picture,
            refRow.mtbf
        };
        if (!prepareAndExec(query,
                            "INSERT INTO Equipment (Equipment_ID, ProjectStructure_ID, DT, Type, Eqpt_Category, Name, Desc, PartCode, SymbRemark, OrderNum, Factory, TVariable, TModel, Structure, RepairInfo, Picture, MTBF) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            equipmentRow,
                            errorMessage)) {
            return false;
        }

        const int containerId = nextContainerId++;
        const int parentContainerId = containerIdByKey.value(config.parentContainerKey, containerIdByKey.value(QString("root")));
        QVariantList containerRow = {
            containerId,
            config.projectStructureId,
            mark,
            QString("component"),
            equipmentId,
            1,
            QString("%1 %2").arg(config.displayName, mark),
            QVariant(),
            QVariant()
        };
        if (!prepareAndExec(query,
                            "INSERT INTO container (container_id, project_structure_id, name, level, source_equipment_id, auto_generated, description, fault_analysis_depth, inherits_from_container_id) VALUES (?,?,?,?,?,?,?,?,?)",
                            containerRow,
                            errorMessage)) {
            return false;
        }

        QVariantList componentRow = {containerId, equipmentId, QString("primary")};
        if (!prepareAndExec(query,
                            "INSERT INTO container_component (container_id, equipment_id, role) VALUES (?,?,?)",
                            componentRow,
                            errorMessage)) {
            return false;
        }

        QVariantList equipmentContainerRow = {equipmentId, containerId};
        if (!prepareAndExec(query,
                            "INSERT INTO equipment_containers (equipment_id, container_id) VALUES (?,?)",
                            equipmentContainerRow,
                            errorMessage)) {
            return false;
        }

        QVariantList hierarchyRow = {parentContainerId, containerId, QString("contains")};
        if (!prepareAndExec(query,
                            "INSERT INTO container_hierarchy (parent_id, child_id, relation_type) VALUES (?,?,?)",
                            hierarchyRow,
                            errorMessage)) {
            return false;
        }

        const int symbolId = nextSymbolId++;
        QVariantList symbolRow = {
            symbolId,
            equipmentId,
            config.pageId,
            QString("SYM_%1").arg(mark),
            config.displayName,
            refRow.description.isEmpty() ? config.displayName : refRow.description,
            mark,
            QString("HANDLE_%1").arg(symbolId),
            QString("%1 接线符号").arg(mark),
            config.key,
            config.displayName,
            1,
            1,
            1,
            QString("NET-%1").arg(config.key.toUpper()),
            mark
        };
        if (!prepareAndExec(query,
                            "INSERT INTO Symbol (Symbol_ID, Equipment_ID, Page_ID, Symbol, Symbol_Category, Symbol_Desc, Designation, Symbol_Handle, Symbol_Remark, FunDefine, FuncType, SourceConn, ExecConn, SourcePrior, InterConnect, Show_DT) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            symbolRow,
                            errorMessage)) {
            return false;
        }

        const QStringList directions = {QString("向上"), QString("向下")};
        for (int portIndex = 0; portIndex < 2; ++portIndex) {
            QVariantList termRow = {
                nextSymbTermId++,
                symbolId,
                QString::number(portIndex + 1),
                QString::number(portIndex + 1),
                directions.at(portIndex),
                0,
                QString("%1 端口%2").arg(mark).arg(portIndex + 1)
            };
            if (!prepareAndExec(query,
                                "INSERT INTO Symb2TermInfo (Symb2TermInfo_ID, Symbol_ID, ConnNum_Logic, ConnNum, ConnDirection, Internal, ConnDesc) VALUES (?,?,?,?,?,?,?)",
                                termRow,
                                errorMessage)) {
                return false;
            }
        }

        EquipmentInstance instance;
        instance.equipmentId = equipmentId;
        instance.symbolId = symbolId;
        instance.pageId = config.pageId;
        instance.categoryKey = config.key;
        instance.mark = mark;
        const int instanceIndex = instances.size();
        instances.append(instance);
        categoryIndexes[config.key].append(instanceIndex);
        return true;
    };

    for (const CategoryConfig &config : categories) {
        const QList<ReferenceEquipmentRow> refs = referenceByCategory.value(config.key);
        if (refs.isEmpty())
            continue;
        for (int i = 0; i < config.count; ++i) {
            const ReferenceEquipmentRow &refRow = refs.at(i % refs.size());
            if (!insertEquipmentInstance(config, i, refRow))
                return false;
        }
    }

    const QStringList wireColors = {QString("RD"), QString("BU"), QString("BK"), QString("YE"), QString("GN"), QString("WH")};
    auto addConnection = [&](const EquipmentInstance &from, const EquipmentInstance &to, const QString &wireType, const QString &wireCategory) -> bool {
        const QString connectionNumber = QString("CL-%1").arg(nextConnectLineId, 6, 10, QLatin1Char('0'));
        const QString equipotential = QString::number((nextConnectLineId % 20) + 1);
        const QString color = wireColors.at((nextConnectLineId + from.symbolId + to.symbolId) % wireColors.size());
        QVariantList row = {
            nextConnectLineId++,
            from.pageId,
            QString(),
            equipotential,
            connectionNumber,
            QString("HND-%1").arg(connectionNumber),
            QString("%1:%2").arg(from.symbolId).arg(1),
            QString("%1:%2").arg(to.symbolId).arg(2),
            wireType,
            color,
            QString("2.5mm2"),
            wireCategory,
            QString("component"),
            QString("component")
        };
        return prepareAndExec(query,
                              "INSERT INTO ConnectLine (ConnectLine_ID, Page_ID, Cable_ID, Equipotential_Num, ConnectionNumber, ConnectionNumber_Handle, Symb1_ID, Symb2_ID, Wires_Type, Wires_Color, Wires_Diameter, Wires_Category, Symb1_Category, Symb2_Category) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                              row,
                              errorMessage);
    };

    auto connectChain = [&](const QString &categoryKey, const QString &wireType, const QString &wireCategory) -> bool {
        const QVector<int> indexes = categoryIndexes.value(categoryKey);
        for (int i = 0; i + 1 < indexes.size(); ++i) {
            const EquipmentInstance &from = instances.at(indexes.at(i));
            const EquipmentInstance &to = instances.at(indexes.at(i + 1));
            if (!addConnection(from, to, wireType, wireCategory))
                return false;
        }
        return true;
    };

    for (const CategoryConfig &config : categories) {
        if (!connectChain(config.key, config.wireType, config.wireCategory))
            return false;
    }

    auto connectGroups = [&](const QString &fromKey, const QString &toKey, int limit, const QString &wireType, const QString &wireCategory) -> bool {
        const QVector<int> fromIndexes = categoryIndexes.value(fromKey);
        const QVector<int> toIndexes = categoryIndexes.value(toKey);
        if (fromIndexes.isEmpty() || toIndexes.isEmpty())
            return true;
        const int pairCount = qMin(limit, qMin(fromIndexes.size(), toIndexes.size()));
        for (int i = 0; i < pairCount; ++i) {
            const EquipmentInstance &from = instances.at(fromIndexes.at(i));
            const EquipmentInstance &to = instances.at(toIndexes.at(i % toIndexes.size()));
            if (!addConnection(from, to, wireType, wireCategory))
                return false;
        }
        return true;
    };

    if (!connectGroups(QString("analog_sensor"), QString("plc"), 200, QString("analog-signal"), QString("信号线")))
        return false;
    if (!connectGroups(QString("switch_sensor"), QString("plc"), 200, QString("digital-signal"), QString("控制线")))
        return false;
    if (!connectGroups(QString("relay"), QString("contactor"), 200, QString("control"), QString("控制线")))
        return false;
    if (!connectGroups(QString("solenoid"), QString("proportional_solenoid"), 200, QString("hydraulic-control"), QString("动力线")))
        return false;
    if (!connectGroups(QString("filter"), QString("breaker"), 120, QString("power"), QString("动力线")))
        return false;
    if (!connectGroups(QString("network_module"), QString("plc"), 120, QString("network"), QString("信号线")))
        return false;

    QStringList functionColumns;
    if (!fetchTableColumns(db, QString("Function"), &functionColumns, errorMessage))
        return false;

    const QStringList functionColumnPriority = {
        QString("FunctionID"),
        QString("FunctionName"),
        QString("ExecsList"),
        QString("CmdValList"),
        QString("UserTest"),
        QString("Remark"),
        QString("LinkText"),
        QString("ComponentDependency"),
        QString("AllComponents"),
        QString("FunctionDependency"),
        QString("PersistentFlag"),
        QString("FaultProbability")
    };

    auto insertFunctionRow = [&](const QVariantMap &row) -> bool {
        QStringList insertColumns;
        QVariantList values;
        for (const QString &column : functionColumnPriority) {
            if (functionColumns.contains(column)) {
                insertColumns.append(column);
                values.append(row.value(column));
            }
        }
        if (insertColumns.isEmpty())
            return true;
        QStringList placeholders;
        for (int i = 0; i < insertColumns.size(); ++i)
            placeholders.append(QString("?"));
        const QString sql = QString("INSERT INTO Function (%1) VALUES (%2)")
                                .arg(insertColumns.join(QString(", ")), placeholders.join(QString(", ")));
        return prepareAndExec(query, sql, values, errorMessage);
    };

    auto gatherMarks = [&](const QString &categoryKey, int cap) -> QStringList {
        QStringList marks;
        const QVector<int> indexes = categoryIndexes.value(categoryKey);
        for (int idx : indexes) {
            marks.append(instances.at(idx).mark);
            if (marks.size() >= cap)
                break;
        }
        return marks;
    };

    QStringList solenoidMarks = gatherMarks(QString("solenoid"), 6);
    QStringList btMarks = gatherMarks(QString("proportional_solenoid"), 4);
    QStringList func1Components = solenoidMarks;
    func1Components.append(btMarks);
    QVariantMap func1;
    func1.insert(QString("FunctionID"), 1);
    func1.insert(QString("FunctionName"), QString("液压泵站供油链路"));
    func1.insert(QString("ExecsList"), func1Components.join(QString(",")));
    func1.insert(QString("CmdValList"), QString("BT链路=调节;YV链路=导通"));
    func1.insert(QString("Remark"), QString("泵站向1#~4#收放系统持续供油"));
    func1.insert(QString("LinkText"), QString("液压泵站->执行机构"));
    func1.insert(QString("ComponentDependency"), func1Components.join(QString(",")));
    func1.insert(QString("AllComponents"), func1Components.join(QString(",")));
    func1.insert(QString("FunctionDependency"), QString());
    func1.insert(QString("PersistentFlag"), 1);
    func1.insert(QString("FaultProbability"), 0.025);

    QStringList relayMarks = gatherMarks(QString("relay"), 6);
    QStringList contactorMarks = gatherMarks(QString("contactor"), 6);
    QStringList plcMarks = gatherMarks(QString("plc"), 4);
    QStringList func2Components = relayMarks;
    func2Components.append(contactorMarks);
    func2Components.append(plcMarks);
    QVariantMap func2;
    func2.insert(QString("FunctionID"), 2);
    func2.insert(QString("FunctionName"), QString("控制柜冗余联锁"));
    func2.insert(QString("ExecsList"), func2Components.join(QString(",")));
    func2.insert(QString("CmdValList"), QString("PLC主备=互联;KM=闭合"));
    func2.insert(QString("Remark"), QString("控制柜完成软启、加热和电机启动信号分配"));
    func2.insert(QString("LinkText"), QString("控制柜->配电->泵站"));
    func2.insert(QString("ComponentDependency"), func2Components.join(QString(",")));
    func2.insert(QString("AllComponents"), func2Components.join(QString(",")));
    func2.insert(QString("FunctionDependency"), QString("液压泵站供油链路"));
    func2.insert(QString("PersistentFlag"), 1);
    func2.insert(QString("FaultProbability"), 0.02);

    QStringList sqMarks = gatherMarks(QString("switch_sensor"), 8);
    QStringList saMarks = gatherMarks(QString("analog_sensor"), 8);
    QStringList func3Components = sqMarks;
    func3Components.append(saMarks);
    QVariantMap func3;
    func3.insert(QString("FunctionID"), 3);
    func3.insert(QString("FunctionName"), QString("传感器网络监测"));
    func3.insert(QString("ExecsList"), func3Components.join(QString(",")));
    func3.insert(QString("CmdValList"), QString("液位/压力/温度=实时采集"));
    func3.insert(QString("Remark"), QString("对污染度、水分、油品及液位进行监测"));
    func3.insert(QString("LinkText"), QString("传感器->PLC->控制网"));
    func3.insert(QString("ComponentDependency"), func3Components.join(QString(",")));
    func3.insert(QString("AllComponents"), func3Components.join(QString(",")));
    func3.insert(QString("FunctionDependency"), QString("控制柜冗余联锁"));
    func3.insert(QString("PersistentFlag"), 0);
    func3.insert(QString("FaultProbability"), 0.03);

    const QList<QVariantMap> functions = {func1, func2, func3};
    for (const QVariantMap &row : functions) {
        if (!insertFunctionRow(row))
            return false;
    }

    return true;
}

} // namespace

QString DemoProjectBuilder::containerPortsJson(const QString &equipmentTag,
                                              const QString &outPort,
                                              const QString &outCategory,
                                              const QString &inPort,
                                              const QString &inCategory)
{
    QJsonArray ports;
    if (!inPort.isEmpty()) {
        QJsonObject in;
        in.insert(QString("name"), equipmentTag + "." + inPort);
        in.insert(QString("category"), inCategory);
        in.insert(QString("direction"), QString("input"));
        ports.append(in);
    }
    QJsonObject out;
    out.insert(QString("name"), equipmentTag + "." + outPort);
    out.insert(QString("category"), outCategory);
    out.insert(QString("direction"), QString("output"));
    ports.append(out);
    return compactJson(ports);
}

QString DemoProjectBuilder::coilBaseTModel()
{
    static const char model[] =
        "class KA_xq {\r\n"
        "\r\n"
        "    ModeType mode;\r\n"
        "    onOffState cmdIn;\r\n"
        "    Resistance Res;\r\n"
        "    onOffState xqActivatedLed;\r\n"
        "    onOffState cmdOut;\r\n"
        "\r\n"
        "    enum ModeType {nominal, malFunction, unknownFault};\r\n"
        "\r\n"
        "    stateVector [mode];\r\n"
        "\r\n"
        "    {\r\n"
        "        if (cmdIn = on) {\r\n"
        "            xqActivatedLed = on;\r\n"
        "        }\r\n"
        "        if (cmdIn = off) {\r\n"
        "            xqActivatedLed = off;\r\n"
        "        }\r\n"
        "        switch (mode) {\r\n"
        "            case nominal:\r\n"
        "                if (cmdIn = on) {\r\n"
        "                    cmdOut = on;\r\n"
        "                    Res = nominal;\r\n"
        "                }\r\n"
        "                if (cmdIn = off) {\r\n"
        "                    cmdOut = off;\r\n"
        "                    Res = nominal;\r\n"
        "                }\r\n"
        "            case malFunction:\r\n"
        "                cmdOut = off;\r\n"
        "                Res != nominal;\r\n"
        "            case unknownFault:\r\n"
        "        }\r\n"
        "    }\r\n"
        "\r\n"
        "    failure toMalFunction(*, malFunction, 2.0e-5) {\r\n"
        "    }\r\n"
        "    failure toUnknownFault(*, unknownFault, 1.0e-7) {\r\n"
        "    }\r\n"
        "}\r\n";
    return QString::fromUtf8(model);
}

QString DemoProjectBuilder::coilTModel()
{
    static const char model[] =
        "class NewKA_xq {\r\n"
        "\r\n"
        "    ModeType mode;\r\n"
        "    onOffState xqActivatedLed;\r\n"
        "    onOffState cmdOut;\r\n"
        "    resistance innerR;\r\n"
        "    elecPort ePort_in;\r\n"
        "\r\n"
        "    enum ModeType {nominal, blown, shorted, unknownFault};\r\n"
        "\r\n"
        "    stateVector [mode];\r\n"
        "\r\n"
        "    {\r\n"
        "        ePort_in.R = innerR;\r\n"
        "        ePort_in.appliance_U_I();\r\n"
        "        if (ePort_in.I = middle) {\r\n"
        "            xqActivatedLed = on;\r\n"
        "        }\r\n"
        "        if (ePort_in.I = none) {\r\n"
        "            xqActivatedLed = off;\r\n"
        "        }\r\n"
        "        switch (mode) {\r\n"
        "            case nominal:\r\n"
        "                innerR = middle;\r\n"
        "                if (ePort_in.I = middle) {\r\n"
        "                    cmdOut = on;\r\n"
        "                }\r\n"
        "                if (ePort_in.I != middle) {\r\n"
        "                    cmdOut = off;\r\n"
        "                }\r\n"
        "            case blown:\r\n"
        "                innerR = infinite;\r\n"
        "                cmdOut = off;\r\n"
        "            case shorted:\r\n"
        "                innerR = none;\r\n"
        "                cmdOut = off;\r\n"
        "            case unknownFault:\r\n"
        "        }\r\n"
        "    }\r\n"
        "\r\n"
        "    failure toBlown(*, blown, 2.0e-5) {\r\n"
        "    }\r\n"
        "    failure toShorted(*, shorted, 1.0e-5) {\r\n"
        "    }\r\n"
        "    failure toUnknownFault(*, unknownFault, 1.0e-8) {\r\n"
        "    }\r\n"
        "}\r\n";
    return QString::fromUtf8(model);
}

QString DemoProjectBuilder::elecPortTModel()
{
    static const char model[] =
        "class elecPort {\r\n"
        "\r\n"
        "    current I;\r\n"
        "    voltage U;\r\n"
        "    resistance R;\r\n"
        "\r\n"
        "    relation ePort_init() {\r\n"
        "        I = none;\r\n"
        "        U = none;\r\n"
        "    }\r\n"
        "    relation highRes_U_I() {\r\n"
        "        appliance_U_I();\r\n"
        "    }\r\n"
        "    relation appliance_U_I() {\r\n"
        "        if (R = none) {\r\n"
        "            U = none;\r\n"
        "        }\r\n"
        "        if (R = infinite) {\r\n"
        "            I = none;\r\n"
        "        }\r\n"
        "        if ((U = none & \r\n"
        "            R != none)) {\r\n"
        "            I = none;\r\n"
        "        }\r\n"
        "        if ((U = middle & \r\n"
        "            R = middle)) {\r\n"
        "            I = middle;\r\n"
        "        }\r\n"
        "        if ((U = middle & \r\n"
        "            R = high)) {\r\n"
        "            I = low;\r\n"
        "        }\r\n"
        "        if ((U = middle & \r\n"
        "            R = low)) {\r\n"
        "            I = high;\r\n"
        "        }\r\n"
        "        if ((U = low & \r\n"
        "            R = middle)) {\r\n"
        "            I = low;\r\n"
        "        }\r\n"
        "        if ((U = low & \r\n"
        "            R = high)) {\r\n"
        "            I = low;\r\n"
        "        }\r\n"
        "        if ((U = high & \r\n"
        "            R = low)) {\r\n"
        "            I = high;\r\n"
        "        }\r\n"
        "        if ((U = high & \r\n"
        "            R = middle)) {\r\n"
        "            I = high;\r\n"
        "        }\r\n"
        "    }\r\n"
        "}\r\n";
    return QString::fromUtf8(model);
}

QString DemoProjectBuilder::psuTModel()
{
    static const char model[] =
        "class DC24VSource {\r\n"
        "\r\n"
        "    ModeType mode;\r\n"
        "    supplyState supplyStatus;\r\n"
        "    elecPort port_pos;\r\n"
        "    elecPort port_neg;\r\n"
        "\r\n"
        "    enum ModeType {nominal, openCircuit, shortCircuit, unknownFault};\r\n"
        "    enum supplyState {energized, deEnergized, shorted};\r\n"
        "\r\n"
        "    stateVector [mode];\r\n"
        "\r\n"
        "    {\r\n"
        "        port_pos.appliance_U_I();\r\n"
        "        port_neg.appliance_U_I();\r\n"
        "        switch (mode) {\r\n"
        "            case nominal:\r\n"
        "                supplyStatus = energized;\r\n"
        "            case openCircuit:\r\n"
        "                supplyStatus = deEnergized;\r\n"
        "            case shortCircuit:\r\n"
        "                supplyStatus = shorted;\r\n"
        "            case unknownFault:\r\n"
        "        }\r\n"
        "    }\r\n"
        "\r\n"
        "    failure toOpenCircuit(*, openCircuit, 1.0e-5) {\r\n"
        "    }\r\n"
        "    failure toShortCircuit(*, shortCircuit, 1.0e-5) {\r\n"
        "    }\r\n"
        "    failure toUnknownFault(*, unknownFault, 1.0e-8) {\r\n"
        "    }\r\n"
        "}\r\n";
    return QString::fromUtf8(model);
}

QString DemoProjectBuilder::psuBehaviorJson()
{
    QJsonObject normal;
    normal.insert(QString("id"), QString("psu_normal"));
    normal.insert(QString("name"), QString("PSU 正常"));
    normal.insert(QString("type"), QString("normal"));
    normal.insert(QString("probability"), 0.0);
    normal.insert(QString("constraints"), QJsonArray{QString("PSU-1.Vout=24V")});

    QJsonObject fault;
    fault.insert(QString("id"), QString("psu_failure"));
    fault.insert(QString("name"), QString("PSU 输出失效"));
    fault.insert(QString("type"), QString("fault"));
    fault.insert(QString("probability"), 0.01);
    fault.insert(QString("constraints"), QJsonArray{QString("PSU-1.Vout=0V")});

    QJsonObject behavior;
    behavior.insert(QString("normal"), normal);
    behavior.insert(QString("faults"), QJsonArray{fault});
    return compactJson(behavior);
}

QString DemoProjectBuilder::actuatorBehaviorJson()
{
    QJsonObject normal;
    normal.insert(QString("id"), QString("act_normal"));
    normal.insert(QString("name"), QString("执行器正常"));
    normal.insert(QString("type"), QString("normal"));
    normal.insert(QString("probability"), 0.0);
    normal.insert(QString("constraints"), QJsonArray{QString("ACT-1.Pressure=8bar")});

    QJsonObject fault;
    fault.insert(QString("id"), QString("act_stuck"));
    fault.insert(QString("name"), QString("执行器卡滞"));
    fault.insert(QString("type"), QString("fault"));
    fault.insert(QString("probability"), 0.02);
    fault.insert(QString("constraints"), QJsonArray{QString("ACT-1.Pressure=0bar")});

    QJsonObject behavior;
    behavior.insert(QString("normal"), normal);
    behavior.insert(QString("faults"), QJsonArray{fault});
    return compactJson(behavior);
}

QString DemoProjectBuilder::subsystemBehaviorJson()
{
    QJsonObject normal;
    normal.insert(QString("id"), QString("sub_normal"));
    normal.insert(QString("name"), QString("子系统正常"));
    normal.insert(QString("type"), QString("normal"));
    normal.insert(QString("probability"), 0.0);

    QJsonObject behavior;
    behavior.insert(QString("normal"), normal);
    behavior.insert(QString("faults"), QJsonArray());
    return compactJson(behavior);
}

QStringList DemoProjectBuilder::demoTestJsonList()
{
    auto makeTest = [](const QString &id, const QString &category, const QString &name, const QString &target, const QStringList &faults, double cost, double duration, const QVariantMap &metrics = QVariantMap()) {
        QJsonObject obj;
        obj.insert(QString("id"), id);
        obj.insert(QString("category"), category);
        obj.insert(QString("name"), name);
        obj.insert(QString("description"), QString("演示生成的测试"));
        obj.insert(QString("targetId"), target);
        obj.insert(QString("detectableFaults"), QJsonArray::fromStringList(faults));
        obj.insert(QString("isolatableFaults"), QJsonArray::fromStringList(faults));
        obj.insert(QString("estimatedCost"), cost);
        obj.insert(QString("estimatedDuration"), duration);
        if (!metrics.isEmpty())
            obj.insert(QString("metrics"), QJsonObject::fromVariantMap(metrics));
        return obj;
    };

    QStringList list;
    QVariantMap signalMetrics;
    signalMetrics.insert(QString("direction"), QString("output"));
    signalMetrics.insert(QString("unit"), QString("V"));
    const QJsonObject signalTest = makeTest(QString("signal:3:PSU-1.Vout"), QString("signal"), QString("PSU 输出电压检测"), QString("PSU-1.Vout"), {QString("psu_failure")}, 1.0, 1.0, signalMetrics);

    QVariantMap functionMetrics;
    functionMetrics.insert(QString("requiredInputs"), QJsonArray{QString("PSU-1.Vout")});
    functionMetrics.insert(QString("actuators"), QJsonArray{QString("ACT-1.Pressure")});
    const QJsonObject functionTest = makeTest(QString("function:4:DeliverPressure"), QString("function"), QString("DeliverPressure 功能测试"), QString("DeliverPressure"), {QString("psu_failure"), QString("act_stuck")}, 2.0, 2.0, functionMetrics);

    QVariantMap faultMetrics;
    faultMetrics.insert(QString("sourceContainers"), QJsonArray{4});
    const QJsonObject faultTest = makeTest(QString("fault:4:act_stuck"), QString("faultMode"), QString("执行器卡滞诊断"), QString("act_stuck"), {QString("act_stuck")}, 3.0, 3.0, faultMetrics);

    list << compactJson(QJsonArray{signalTest});
    list << compactJson(QJsonArray{functionTest, faultTest});

    return list;
}

QString DemoProjectBuilder::demoFunctionXml()
{
    QDomDocument doc;
    QDomElement root = doc.createElement(QString("root"));
    doc.appendChild(root);

    QDomElement treeStruct = doc.createElement(QString("treestruct"));
    root.appendChild(treeStruct);

    QDomElement item = doc.createElement(QString("item"));
    item.setAttribute(QString("name"), QString("DeliverPressure"));
    treeStruct.appendChild(item);

    QDomElement functionElement = doc.createElement(QString("functiondefine"));
    root.appendChild(functionElement);

    auto appendTextElement = [&](const QString &tag, const QString &text) {
        QDomElement e = doc.createElement(tag);
        e.appendChild(doc.createTextNode(text));
        functionElement.appendChild(e);
        return e;
    };

    appendTextElement(QString("name"), QString("DeliverPressure"));
    appendTextElement(QString("link"), QString("PSU-1.Vout,ACT-1.Pressure"));

    QDomElement dependency = doc.createElement(QString("dependency"));
    functionElement.appendChild(dependency);
    QDomElement funcDep = doc.createElement(QString("function"));
    funcDep.appendChild(doc.createTextNode(QString()));
    dependency.appendChild(funcDep);
    QDomElement compDep = doc.createElement(QString("component"));
    compDep.appendChild(doc.createTextNode(QString("PSU-1,ACT-1")));
    dependency.appendChild(compDep);
    QDomElement allComp = doc.createElement(QString("allComponent"));
    allComp.appendChild(doc.createTextNode(QString("PSU-1,ACT-1")));
    dependency.appendChild(allComp);

    appendTextElement(QString("describe"), QString("PSU 为执行器提供稳定压力"));
    appendTextElement(QString("attribute"), QString("Persistent,0.01"));

    auto addConstraint = [&](const QString &variable, const QString &value, const QString &type) {
        QDomElement constraint = doc.createElement(QString("constraint"));
        QDomElement var = doc.createElement(QString("variable"));
        var.appendChild(doc.createTextNode(variable));
        constraint.appendChild(var);
        QDomElement val = doc.createElement(QString("value"));
        val.appendChild(doc.createTextNode(value));
        constraint.appendChild(val);
        QDomElement confidence = doc.createElement(QString("confidence"));
        confidence.appendChild(doc.createTextNode(QString("1")));
        constraint.appendChild(confidence);
        QDomElement typeElement = doc.createElement(QString("type"));
        typeElement.appendChild(doc.createTextNode(type));
        constraint.appendChild(typeElement);
        functionElement.appendChild(constraint);
    };

    addConstraint(QString("PSU-1.Vout"), QString("24V"), QString("一般变量"));
    addConstraint(QString("ACT-1.Pressure"), QString("8bar"), QString("功能执行器"));

    return doc.toString();
}
