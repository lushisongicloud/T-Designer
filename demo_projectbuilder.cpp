#include "demo_projectbuilder.h"

#include "common.h"
#include <QDir>
#include <QFile>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QMap>
#include <QStringList>
#include <QVariant>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QTextStream>
#include <QDateTime>

#include <QDomDocument>

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

    // Insert project structure entries
    const QList<QList<QVariant>> projectStructures = {
        {1001, QString("1"), QString("Demo System"), 0, QString("演示项目根节点")},
        {1002, QString("3"), QString("Subsystem"), 1001, QString("演示子系统")},
        {1003, QString("5"), QString("Station 1"), 1002, QString("演示位置")},
        {1004, QString("6"), QString("Demo Diagram"), 1003, QString("演示图纸分组")}
    };
    for (const auto &row : projectStructures) {
        if (!prepareAndExec(query,
                            "INSERT INTO ProjectStructure (ProjectStructure_ID, Structure_ID, Structure_INT, Parent_ID, Struct_Desc) VALUES (?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    // Equipment entries
    const QList<QList<QVariant>> equipments = {
        {1,
         1003,
         QString("PSU-1"),
         QString("Power"),
         QString("普通元件"),
         QString("Power Supply"),
         QString("提供24V稳压输出"),
         QString("PSU001"),
         QString("SPS_M_BAT-1"),
         QString("1"),
         QString("DemoWorks"),
         QString("PSU-1.Vout"),
         psuTModel(),
         QString("107009901"),
         QString(),
         QString(),
         QString("120000")},
        {2,
         1003,
         QString("ACT-1"),
         QString("Actuator"),
         QString("普通元件"),
         QString("Hydraulic Actuator"),
         QString("输出8bar液压压力"),
         QString("ACT001"),
         QString("SPS_M_K-1"),
         QString("2"),
         QString("DemoWorks"),
         QString("ACT-1.Cmd"),
         coilTModel(),
         QString("102000100"),
         QString(),
         QString(),
         QString("90000")}
    };
    for (const auto &row : equipments) {
        if (!prepareAndExec(query,
                            "INSERT INTO Equipment (Equipment_ID, ProjectStructure_ID, DT, Type, Eqpt_Category, Name, Desc, PartCode, SymbRemark, OrderNum, Factory, TVariable, TModel, Structure, RepairInfo, Picture, MTBF) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> diagnoseParas = {
        {1, 1, QString("Vout"), QString("V"), QString("24"), QString("24"), QString("输出电压")},
        {2, 2, QString("Pressure"), QString("bar"), QString("8"), QString("8"), QString("输出压力")}
    };
    for (const auto &row : diagnoseParas) {
        if (!prepareAndExec(query,
                            "INSERT INTO EquipmentDiagnosePara (DiagnoseParaID, Equipment_ID, Name, Unit, CurValue, DefaultValue, Remark) VALUES (?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> symbols = {
        {1,
         1,
         1,
         QString("SPS_M_BAT-1"),
         QString("电源,发电机"),
         QString("电压源子块"),
         QString("PSU"),
         QString(),
         QString("107009901"),
         QString("电压源,可变"),
         QString("source"),
         1,
         0,
         1,
         QString(),
         QString("PSU-1.Vout")},
        {2,
         2,
         1,
         QString("SPS_M_K-1"),
         QString("线圈,触点"),
         QString("执行器线圈子块"),
         QString("ACT"),
         QString(),
         QString("102000100"),
         QString("线圈,常规"),
         QString("actuator"),
         0,
         1,
         1,
         QString(),
         QString("ACT-1.Cmd")}
    };
    for (const auto &row : symbols) {
        if (!prepareAndExec(query,
                            "INSERT INTO Symbol (Symbol_ID, Equipment_ID, Page_ID, Symbol, Symbol_Category, Symbol_Desc, Designation, Symbol_Handle, Symbol_Remark, FunDefine, FuncType, SourceConn, ExecConn, SourcePrior, InterConnect, Show_DT) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QVariantList> symbTerms = {
        {1, 1, QString("1"), QString("P"), QString(), QVariant(0), QString("正极端子")},
        {2, 1, QString("2"), QString("N"), QString(), QVariant(0), QString("负极端子")},
        {3, 2, QString("1"), QString("A1"), QString(), QVariant(0), QString("线圈入口")},
        {4, 2, QString("2"), QString("A2"), QString(), QVariant(0), QString("线圈返回")}
    };
    for (const QVariantList &row : symbTerms) {
        if (!prepareAndExec(query,
                            "INSERT INTO Symb2TermInfo (Symb2TermInfo_ID, Symbol_ID, ConnNum_Logic, ConnNum, ConnDirection, Internal, ConnDesc) VALUES (?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QString alterTime = QDateTime::currentDateTime().toString(QString("yyyy-MM-dd hh:mm:ss"));
    const QList<QList<QVariant>> pages = {
        {1,
         1004,
         QString("Demo diagram for workflow"),
         QString("原理图"),
         1,
         QString("D1"),
         QString("1:1"),
         QString("A3:420x297"),
         QString("Demo Diagram"),
         alterTime,
         QString()}
    };
    for (const auto &row : pages) {
        if (!prepareAndExec(query,
                            "INSERT INTO Page (Page_ID, ProjectStructure_ID, Page_Desc, PageType, PageNum, PageName, Scale, Border, Title, AlterTime, MD5Code) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    QStringList functionColumns;
    if (!fetchTableColumns(db, QString("Function"), &functionColumns, errorMessage)) {
        cleanup();
        return false;
    }

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

    QVariantMap functionRow;
    functionRow.insert(QString("FunctionID"), QVariant(1));
    functionRow.insert(QString("FunctionName"), QString("DeliverPressure"));
    functionRow.insert(QString("ExecsList"), QString("ACT-1.Pressure"));
    functionRow.insert(QString("CmdValList"), QString("PSU-1.Vout=24V"));
    functionRow.insert(QString("UserTest"), QString());
    functionRow.insert(QString("Remark"), QString("演示功能: 电源驱动执行器"));
    functionRow.insert(QString("LinkText"), QString("PSU-1.Vout,ACT-1.Pressure"));
    functionRow.insert(QString("ComponentDependency"), QString("PSU-1,ACT-1"));
    functionRow.insert(QString("AllComponents"), QString("PSU-1,ACT-1"));
    functionRow.insert(QString("FunctionDependency"), QString());
    functionRow.insert(QString("PersistentFlag"), QVariant(1));
    functionRow.insert(QString("FaultProbability"), QVariant(0.01));

    QStringList functionInsertColumns;
    QVariantList functionInsertValues;
    for (const QString &column : functionColumnPriority) {
        if (functionColumns.contains(column)) {
            functionInsertColumns.append(column);
            functionInsertValues.append(functionRow.value(column));
        }
    }

    if (!functionInsertColumns.contains(QString("FunctionID")) || !functionInsertColumns.contains(QString("FunctionName"))) {
        if (errorMessage)
            *errorMessage = QString("函数表缺少必要字段");
        cleanup();
        return false;
    }

    QStringList placeholders;
    for (int i = 0; i < functionInsertColumns.size(); ++i)
        placeholders.append(QString("?"));

    const QString functionInsertSql = QString("INSERT INTO Function (%1) VALUES (%2)")
                                           .arg(functionInsertColumns.join(", "), placeholders.join(", "));
    if (!prepareAndExec(query, functionInsertSql, functionInsertValues, errorMessage)) {
        cleanup();
        return false;
    }

    // Populate normalized container schema
    const QList<QList<QVariant>> containerRows = {
        {1, 1001, QString("Demo System"), QString("system"), QVariant(), 0, QString("演示项目根节点"), QVariant(), QVariant()},
        {2, 1002, QString("Subsystem"), QString("subsystem"), QVariant(), 0, QString("液压演示子系统"), QVariant(), QVariant()},
        {3, 1003, QString("PSU-1"), QString("component"), 1, 1, QString("Power Supply container"), QVariant(), QVariant()},
        {4, 1003, QString("ACT-1"), QString("component"), 2, 1, QString("Hydraulic actuator container"), QVariant(), QVariant()}
    };
    for (const auto &row : containerRows) {
        if (!prepareAndExec(query,
                            "INSERT INTO container (container_id, project_structure_id, name, level, source_equipment_id, auto_generated, description, fault_analysis_depth, inherits_from_container_id) "
                            "VALUES (?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> containerHierarchy = {
        {1, 2, QString("contains")},
        {2, 3, QString("contains")},
        {2, 4, QString("contains")}
    };
    for (const auto &row : containerHierarchy) {
        if (!prepareAndExec(query,
                            "INSERT INTO container_hierarchy (parent_id, child_id, relation_type) VALUES (?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> containerComponents = {
        {3, 1, QString("primary")},
        {4, 2, QString("primary")}
    };
    for (const auto &row : containerComponents) {
        if (!prepareAndExec(query,
                            "INSERT INTO container_component (container_id, equipment_id, role) VALUES (?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> containerInterfaces = {
        {1, 3, QString("PSU-1.Vout"), QString("out"), QString("electric"), QString("voltage"), QString("electrical"), QString("V"), QString("PSU 输出电压"), QVariant()},
        {2, 4, QString("ACT-1.Supply"), QString("in"), QString("hydraulic"), QString("pressure"), QString("hydraulic"), QString("bar"), QString("执行器端口供压"), QVariant()},
        {3, 4, QString("ACT-1.Pressure"), QString("out"), QString("hydraulic"), QString("pressure"), QString("hydraulic"), QString("bar"), QString("执行器输出压力"), QVariant()},
        {4, 2, QString("Subsystem.Pressure"), QString("out"), QString("hydraulic"), QString("pressure"), QString("hydraulic"), QString("bar"), QString("子系统对外输出"), QVariant()}
    };
    for (const auto &row : containerInterfaces) {
        if (!prepareAndExec(query,
                            "INSERT INTO container_interface (interface_id, container_id, name, direction, signal_category, signal_subtype, physical_domain, default_unit, description, inherits_interface_id) "
                            "VALUES (?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> containerStates = {
        {1, 3, QString("PSU 正常"), QString("normal"), 0, 0.99, QString("输出稳定在 24V"), QVariant()},
        {2, 3, QString("PSU 输出失效"), QString("fault"), 0, 0.01, QString("输出降为 0V"), QVariant()},
        {3, 4, QString("执行器正常"), QString("normal"), 0, 0.98, QString("输出 8bar 压力"), QVariant()},
        {4, 4, QString("执行器卡滞"), QString("fault"), 0, 0.02, QString("输出压力为 0bar"), QVariant()},
        {5, 2, QString("子系统正常"), QString("normal"), 1, QVariant(), QString("聚合子级正常状态"), QString("component")},
        {6, 2, QString("子系统故障"), QString("fault"), 1, QVariant(), QString("聚合子级故障状态"), QString("component")}
    };
    for (const auto &row : containerStates) {
        if (!prepareAndExec(query,
                            "INSERT INTO container_state (state_id, container_id, name, state_type, derived_from_children, probability, rationale, analysis_scope) "
                            "VALUES (?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> stateBehaviors = {
        {1, 1, QString("expr"), QString("PSU-1.Vout = 24"), QString()},
        {2, 2, QString("expr"), QString("PSU-1.Vout = 0"), QString()},
        {3, 3, QString("expr"), QString("ACT-1.Pressure = 8"), QString()},
        {4, 4, QString("expr"), QString("ACT-1.Pressure = 0"), QString()},
        {5, 5, QString("expr"), QString("Subsystem.Pressure = 8"), QString()},
        {6, 6, QString("expr"), QString("Subsystem.Pressure = 0"), QString()}
    };
    for (const auto &row : stateBehaviors) {
        if (!prepareAndExec(query,
                            "INSERT INTO container_state_behavior (behavior_id, state_id, representation, expression, notes) VALUES (?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    QStringList stateInterfaceColumns;
    if (!fetchTableColumns(db, QString("container_state_interface"), &stateInterfaceColumns, errorMessage)) {
        cleanup();
        return false;
    }

    const QStringList stateInterfacePriority = {
        QString("id"),
        QString("state_id"),
        QString("interface_id"),
        QString("constraint")
    };

    const QList<QVariantMap> stateInterfaceRows = {
        QVariantMap{{QString("id"), QVariant(1)}, {QString("state_id"), QVariant(1)}, {QString("interface_id"), QVariant(1)}, {QString("constraint"), QString("PSU-1.Vout=24V")}},
        QVariantMap{{QString("id"), QVariant(2)}, {QString("state_id"), QVariant(2)}, {QString("interface_id"), QVariant(1)}, {QString("constraint"), QString("PSU-1.Vout=0V")}},
        QVariantMap{{QString("id"), QVariant(3)}, {QString("state_id"), QVariant(3)}, {QString("interface_id"), QVariant(3)}, {QString("constraint"), QString("ACT-1.Pressure=8bar")}},
        QVariantMap{{QString("id"), QVariant(4)}, {QString("state_id"), QVariant(4)}, {QString("interface_id"), QVariant(3)}, {QString("constraint"), QString("ACT-1.Pressure=0bar")}},
        QVariantMap{{QString("id"), QVariant(5)}, {QString("state_id"), QVariant(5)}, {QString("interface_id"), QVariant(4)}, {QString("constraint"), QString("Subsystem.Pressure=8bar")}},
        QVariantMap{{QString("id"), QVariant(6)}, {QString("state_id"), QVariant(6)}, {QString("interface_id"), QVariant(4)}, {QString("constraint"), QString("Subsystem.Pressure=0bar")}}
    };

    for (const QVariantMap &row : stateInterfaceRows) {
        QStringList insertColumns;
        QVariantList insertValues;
        for (const QString &column : stateInterfacePriority) {
            if (stateInterfaceColumns.contains(column) && row.contains(column)) {
                insertColumns.append(column);
                insertValues.append(row.value(column));
            }
        }

        if (!insertColumns.contains(QString("state_id")) || !insertColumns.contains(QString("interface_id"))) {
            if (errorMessage)
                *errorMessage = QString("状态接口表缺少必要字段");
            cleanup();
            return false;
        }

        QStringList placeholders;
        for (int i = 0; i < insertColumns.size(); ++i)
            placeholders.append(QString("?"));

        const QString sql = QString("INSERT INTO container_state_interface (%1) VALUES (%2)")
                                .arg(insertColumns.join(", "), placeholders.join(", "));

        if (!prepareAndExec(query, sql, insertValues, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> functionDefinitions = {
        {1, 2, QVariant(), QString("DeliverPressure"), QString("PSU 提供能量驱动执行器输出压力"), QString("当输入电压满足要求时，应输出 8bar 压力"), QString("Subsystem.Pressure=8bar"), QString("PSU-1.Vout >= 20"), 0}
    };
    for (const auto &row : functionDefinitions) {
        if (!prepareAndExec(query,
                            "INSERT INTO function_definition (function_id, container_id, parent_function_id, name, description, requirement, expected_output, detection_rule, auto_generated) "
                            "VALUES (?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> functionIoRows = {
        {1, 1, QString("input"), QString("SupplyVoltage"), 1, QVariant(), QString("PSU-1.Vout"), QString("来自电源的输出电压")},
        {2, 1, QString("output"), QString("SubsystemPressure"), 4, QVariant(), QString("Subsystem.Pressure"), QString("期望输出压力")}
    };
    for (const auto &row : functionIoRows) {
        if (!prepareAndExec(query,
                            "INSERT INTO function_io (io_id, function_id, io_type, name, interface_id, default_value, expression, description) "
                            "VALUES (?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> testDefinitions = {
        {1, 3, QVariant(), QVariant(), QString("signal"), QString("PSU 输出电压测试"), QString("测量 PSU 输出是否稳定"), 1, 1, QString("electric"), QString("Vout=24V"), 1, 0.5, 100.0},
        {2, 4, QVariant(), QVariant(), QString("signal"), QString("执行器压力测试"), QString("测量执行器输出压力"), 1, 3, QString("hydraulic"), QString("Pressure=8bar"), 1, 0.7, 120.0},
        {3, 2, 1, QVariant(), QString("function"), QString("系统功能验证"), QString("验证 DeliverPressure 功能的整体表现"), 1, QVariant(), QString("functional"), QString("Subsystem.Pressure=8bar"), 2, 1.5, 250.0},
        {4, 3, QVariant(), 2, QString("fault-mode"), QString("PSU 故障诊断"), QString("定位 PSU 输出失效的故障模式"), 0, 1, QString("electric"), QString("输出降至 0V"), 2, 0.9, 180.0}
    };
    for (const auto &row : testDefinitions) {
        if (!prepareAndExec(query,
                            "INSERT INTO test_definition (test_id, container_id, function_id, related_state_id, test_type, name, description, auto_generated, interface_id, signal_category, expected_result, complexity, estimated_duration, estimated_cost) "
                            "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> testCoverage = {
        {1, 2, QString("detect"), 0.95},
        {2, 4, QString("detect"), 0.93},
        {3, 6, QString("detect"), 0.90},
        {4, 2, QString("isolate"), 0.80}
    };
    for (const auto &row : testCoverage) {
        if (!prepareAndExec(query,
                            "INSERT INTO test_fault_coverage (test_id, state_id, coverage_type, confidence) VALUES (?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> testConstraints = {
        {1, 1, QString("setup_time"), QString("0.2"), QString("hour")},
        {2, 2, QString("setup_time"), QString("0.3"), QString("hour")},
        {3, 3, QString("team_size"), QString("3"), QString("person")}
    };
    for (const auto &row : testConstraints) {
        if (!prepareAndExec(query,
                            "INSERT INTO test_constraint (constraint_id, test_id, constraint_type, value, unit) VALUES (?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> analysisRequirements = {
        {1, 2, QString("detection_rate"), 0.90, QString("ratio"), QString("子系统检测率目标")},
        {2, 2, QString("isolation_rate"), 0.75, QString("ratio"), QString("子系统隔离率目标")},
        {3, 1, QString("detection_rate"), 0.85, QString("ratio"), QString("系统层级检测率")}
    };
    for (const auto &row : analysisRequirements) {
        if (!prepareAndExec(query,
                            "INSERT INTO analysis_requirement (requirement_id, container_id, metric, target_value, unit, notes) VALUES (?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> analysisConstraints = {
        {1, 2, QString("max_duration"), QString("3"), QString("hour")},
        {2, 2, QString("max_cost"), QString("800"), QString("USD")}
    };
    for (const auto &row : analysisConstraints) {
        if (!prepareAndExec(query,
                            "INSERT INTO analysis_constraint (constraint_id, container_id, constraint_type, value, unit) VALUES (?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> testPlanCandidates = {
        {1, 2, QString("基础测试方案"), QString("满足指标的最小测试集合"), 320.0, 2.0, QString("自动生成示例")}
    };
    for (const auto &row : testPlanCandidates) {
        if (!prepareAndExec(query,
                            "INSERT INTO test_plan_candidate (candidate_id, container_id, name, description, total_cost, total_duration, selection_notes) "
                            "VALUES (?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> testPlanItems = {
        {1, 1},
        {1, 2},
        {1, 3}
    };
    for (const auto &row : testPlanItems) {
        if (!prepareAndExec(query,
                            "INSERT INTO test_plan_candidate_item (candidate_id, test_id) VALUES (?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> diagnosisTrees = {
        {1, 2, QString("Demo Diagnosis Tree"), QString("基于候选测试集生成的示例决策树")}
    };
    for (const auto &row : diagnosisTrees) {
        if (!prepareAndExec(query,
                            "INSERT INTO diagnosis_tree (tree_id, container_id, name, description) VALUES (?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> diagnosisNodes = {
        {1, 1, QVariant(), 1, QVariant(), QString("root"), QString("执行 PSU 输出电压测试")},
        {2, 1, 1, QVariant(), 5, QString("pass"), QString("测试通过，判定子系统正常")},
        {3, 1, 1, 4, QVariant(), QString("fail"), QString("测试失败，执行故障模式测试")},
        {4, 1, 3, QVariant(), 2, QString("isolate"), QString("确认 PSU 输出失效")}
    };
    for (const auto &row : diagnosisNodes) {
        if (!prepareAndExec(query,
                            "INSERT INTO diagnosis_tree_node (node_id, tree_id, parent_node_id, test_id, state_id, outcome, comment) VALUES (?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QStringList testsJson = demoTestJsonList();

    const QList<QList<QVariant>> containers = {
        {1, QString("Demo System"), 0, QVariant(), 0, 0, compactJson(QJsonArray()), QString(), subsystemBehaviorJson(), QString(), QString(), QVariant(), QString("System"), QString("Demo System")},
        {2, QString("Subsystem"), 1, 1, 0, 0, compactJson(QJsonArray()), QString(), subsystemBehaviorJson(), QString(), QString(), QVariant(), QString("Subsystem"), QString("Hydraulics")},
        {3, QString("PSU-1"), 6, 2, 0, 0, containerPortsJson(QString("PSU-1"), QString("Vout"), QString("power")), QString(), psuBehaviorJson(), testsJson.at(0), QString(), 1, QString("Power"), QString("Power Supply")},
        {4, QString("ACT-1"), 6, 2, 1, 0, containerPortsJson(QString("ACT-1"), QString("Pressure"), QString("hydraulic"), QString("Supply"), QString("hydraulic")), QString(), actuatorBehaviorJson(), testsJson.at(1), QString(), 2, QString("Actuator"), QString("Hydraulic Actuator")}
    };
    for (const auto &row : containers) {
        if (!prepareAndExec(query,
                            "INSERT INTO containers (id, name, type, parent_id, order_index, analysis_depth, interface_json, behavior_smt, fault_modes_json, tests_json, analysis_json, equipment_id, equipment_type, equipment_name) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> equipmentContainers = {
        {1, 3},
        {2, 4}
    };
    for (const auto &row : equipmentContainers) {
        if (!prepareAndExec(query,
                            "INSERT OR REPLACE INTO equipment_containers (equipment_id, container_id) VALUES (?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    cleanup();
    return true;
}

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


