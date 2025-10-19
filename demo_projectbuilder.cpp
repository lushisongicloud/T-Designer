#include "demo_projectbuilder.h"

#include <QDir>
#include <QFile>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QVariant>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QTextStream>
#include <QDateTime>

#include <QDomDocument>
#pragma execution_character_set("utf-8")
namespace {

inline bool execQuery(QSqlQuery &query, const QString &sql, QString *errorMessage)
{
    if (!query.exec(sql)) {
        if (errorMessage)
            *errorMessage = QStringLiteral("SQL error: %1 (%2)").arg(query.lastError().text(), sql);
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
            *errorMessage = QStringLiteral("SQL error: %1 (%2)").arg(query.lastError().text(), sql);
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

} // namespace

bool DemoProjectBuilder::buildDemoProject(const QString &projectDir, const QString &projectName, QString *errorMessage)
{
    QDir dir;
    if (!dir.mkpath(projectDir)) {
        if (errorMessage)
            *errorMessage = QStringLiteral("无法创建目录: %1").arg(projectDir);
        return false;
    }

    const QString swProPath = projectDir + "/" + projectName + ".swPro";
    const QString dbPath = projectDir + "/" + projectName + ".db";
    const QString modelPath = projectDir + "/Model.db";
    const QString paramsPath = projectDir + "/test.params";
    const QString dwgPath = projectDir + "/DemoDiagram.dwg";

    QFile::remove(swProPath);
    QFile::remove(dbPath);
    QFile::remove(modelPath);
    QFile::remove(paramsPath);
    QFile::remove(dwgPath);

    if (!writeSwProFile(swProPath, projectName, errorMessage))
        return false;
    if (!buildProjectDatabase(dbPath, errorMessage))
        return false;
    if (!buildModelDatabase(modelPath, errorMessage))
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
            *errorMessage = QStringLiteral("无法创建项目文件: %1").arg(filePath);
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
            *errorMessage = QStringLiteral("无法创建测试参数文件: %1").arg(filePath);
        return false;
    }
    QTextStream out(&file);
    out << "# Demo test parameters\n"
        << "Voltage=24V\n"
        << "Pressure=8bar\n";
    file.close();
    return true;
}

bool DemoProjectBuilder::buildProjectDatabase(const QString &dbPath, QString *errorMessage)
{
    const QString connName = QStringLiteral("demo_project_builder");
    QSqlDatabase db = QSqlDatabase::addDatabase("QSQLITE", connName);
    db.setDatabaseName(dbPath);
    if (!db.open()) {
        if (errorMessage)
            *errorMessage = QStringLiteral("无法创建数据库: %1").arg(db.lastError().text());
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
        "CREATE TABLE IF NOT EXISTS Page (Page_ID INTEGER PRIMARY KEY, ProjectStructure_ID INTEGER, PageType TEXT, Structure_ID TEXT, PageName TEXT)",
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
        "CREATE TABLE IF NOT EXISTS equipment_containers (equipment_id INTEGER PRIMARY KEY, container_id INTEGER)"
    };

    for (const QString &statement : createStatements) {
        if (!execQuery(query, statement, errorMessage)) {
            cleanup();
            return false;
        }
    }

    // Insert project structure entries
    const QList<QList<QVariant>> projectStructures = {
        {1001, QStringLiteral("1"), QStringLiteral("Demo System"), 0, QStringLiteral("演示项目根节点")},
        {1002, QStringLiteral("3"), QStringLiteral("Subsystem"), 1001, QStringLiteral("演示子系统")},
        {1003, QStringLiteral("5"), QStringLiteral("Station 1"), 1002, QStringLiteral("演示位置")},
        {1004, QStringLiteral("6"), QStringLiteral("Demo Diagram"), 1003, QStringLiteral("演示图纸")}
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
        {1, 1003, QStringLiteral("PSU-1"), QStringLiteral("Power"), QStringLiteral("普通元件"), QStringLiteral("Power Supply"), QStringLiteral("提供24V稳压输出"), QStringLiteral("PSU001"), QString(), QStringLiteral("1"), QStringLiteral("DemoWorks"), QString(), QStringLiteral("class PSU"), QString(), QString(), QString(), QStringLiteral("120000")},
        {2, 1003, QStringLiteral("ACT-1"), QStringLiteral("Actuator"), QStringLiteral("普通元件"), QStringLiteral("Hydraulic Actuator"), QStringLiteral("输出8bar液压压力"), QStringLiteral("ACT001"), QString(), QStringLiteral("2"), QStringLiteral("DemoWorks"), QString(), QStringLiteral("class ACT"), QString(), QString(), QString(), QStringLiteral("90000")}
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
        {1, 1, QStringLiteral("Vout"), QStringLiteral("V"), QStringLiteral("24"), QStringLiteral("24"), QStringLiteral("输出电压")},
        {2, 2, QStringLiteral("Pressure"), QStringLiteral("bar"), QStringLiteral("8"), QStringLiteral("8"), QStringLiteral("输出压力")}
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
        {1, 1, 1, QStringLiteral("PSU"), QStringLiteral("0"), QStringLiteral("电源模块"), QStringLiteral("PSU"), QString(), QString(), QStringLiteral(""), QStringLiteral("source"), 1, 0, 1, QString(), QStringLiteral("PSU-1.Supply")},
        {2, 2, 1, QStringLiteral("ACT"), QStringLiteral("0"), QStringLiteral("执行器模块"), QStringLiteral("ACT"), QString(), QString(), QStringLiteral(""), QStringLiteral("actuator"), 0, 1, 1, QString(), QStringLiteral("ACT-1.Deliver")}
    };
    for (const auto &row : symbols) {
        if (!prepareAndExec(query,
                            "INSERT INTO Symbol (Symbol_ID, Equipment_ID, Page_ID, Symbol, Symbol_Category, Symbol_Desc, Designation, Symbol_Handle, Symbol_Remark, FunDefine, FuncType, SourceConn, ExecConn, SourcePrior, InterConnect, Show_DT) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> symbTerms = {
        {1, 1, QStringLiteral("Vin"), QStringLiteral("供电输入")},
        {2, 1, QStringLiteral("Vout"), QStringLiteral("稳压输出")},
        {3, 2, QStringLiteral("Supply"), QStringLiteral("供油接口")},
        {4, 2, QStringLiteral("Pressure"), QStringLiteral("压力输出")}
    };
    for (const auto &row : symbTerms) {
        if (!prepareAndExec(query,
                            "INSERT INTO Symb2TermInfo (Symb2TermInfo_ID, Symbol_ID, ConnNum, ConnDesc) VALUES (?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> pages = {
        {1, 1004, QStringLiteral("原理图"), QStringLiteral("6"), QStringLiteral("DemoDiagram")}
    };
    for (const auto &row : pages) {
        if (!prepareAndExec(query,
                            "INSERT INTO Page (Page_ID, ProjectStructure_ID, PageType, Structure_ID, PageName) VALUES (?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> jxbs = {
        {1, 1003, 1, QVariant(), QStringLiteral("L1"), QString(), QStringLiteral("2"), QStringLiteral("4"), QStringLiteral("Round"), QStringLiteral("Red"), QStringLiteral("2.5"), QStringLiteral("Power"), QStringLiteral("0"), QStringLiteral("0")}
    };
    for (const auto &row : jxbs) {
        if (!prepareAndExec(query,
                            "INSERT INTO JXB (JXB_ID, ProjectStructure_ID, Page_ID, Cable_ID, ConnectionNumber, ConnectionNumber_Handle, Symb1_ID, Symb2_ID, Wires_Type, Wires_Color, Wires_Diameter, Wires_Category, Symb1_Category, Symb2_Category) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> functions = {
        {1, QStringLiteral("DeliverPressure"), QStringLiteral("ACT-1.Pressure"), QStringLiteral("PSU-1.Vout=24V"), QStringLiteral("演示功能: 电源驱动执行器"), QStringLiteral("PSU-1.Vout,ACT-1.Pressure"), QStringLiteral("PSU-1,ACT-1"), QStringLiteral("PSU-1,ACT-1"), QString(), 1, 0.01}
    };
    for (const auto &row : functions) {
        if (!prepareAndExec(query,
                            "INSERT INTO Function (FunctionID, FunctionName, ExecsList, CmdValList, Remark, LinkText, ComponentDependency, AllComponents, FunctionDependency, PersistentFlag, FaultProbability) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    if (!prepareAndExec(query,
                        "INSERT INTO function_bindings (function_id, symbol_id) VALUES (?,?)",
                        {1, 2}, errorMessage)) {
        cleanup();
        return false;
    }

    const QStringList testsJson = demoTestJsonList();

    const QList<QList<QVariant>> containers = {
        {1, QStringLiteral("Demo System"), 0, 0, 0, 0, compactJson(QJsonArray()), QString(), subsystemBehaviorJson(), QString(), QString(), QVariant(), QStringLiteral("System"), QStringLiteral("Demo System")},
        {2, QStringLiteral("Subsystem"), 1, 1, 0, 0, compactJson(QJsonArray()), QString(), subsystemBehaviorJson(), QString(), QString(), QVariant(), QStringLiteral("Subsystem"), QStringLiteral("Hydraulics")},
        {3, QStringLiteral("PSU-1"), 6, 2, 0, 0, containerPortsJson(QStringLiteral("PSU-1"), QStringLiteral("Vout"), QStringLiteral("power")), QString(), psuBehaviorJson(), testsJson.at(0), QString(), 1, QStringLiteral("Power"), QStringLiteral("Power Supply")},
        {4, QStringLiteral("ACT-1"), 6, 2, 1, 0, containerPortsJson(QStringLiteral("ACT-1"), QStringLiteral("Pressure"), QStringLiteral("hydraulic"), QStringLiteral("Supply"), QStringLiteral("hydraulic")), QString(), actuatorBehaviorJson(), testsJson.at(1), QString(), 2, QStringLiteral("Actuator"), QStringLiteral("Hydraulic Actuator")}
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
        in.insert(QStringLiteral("name"), equipmentTag + "." + inPort);
        in.insert(QStringLiteral("category"), inCategory);
        in.insert(QStringLiteral("direction"), QStringLiteral("input"));
        ports.append(in);
    }
    QJsonObject out;
    out.insert(QStringLiteral("name"), equipmentTag + "." + outPort);
    out.insert(QStringLiteral("category"), outCategory);
    out.insert(QStringLiteral("direction"), QStringLiteral("output"));
    ports.append(out);
    return compactJson(ports);
}

QString DemoProjectBuilder::psuBehaviorJson()
{
    QJsonObject normal;
    normal.insert(QStringLiteral("id"), QStringLiteral("psu_normal"));
    normal.insert(QStringLiteral("name"), QStringLiteral("PSU 正常"));
    normal.insert(QStringLiteral("type"), QStringLiteral("normal"));
    normal.insert(QStringLiteral("probability"), 0.0);
    normal.insert(QStringLiteral("constraints"), QJsonArray{QStringLiteral("PSU-1.Vout=24V")});

    QJsonObject fault;
    fault.insert(QStringLiteral("id"), QStringLiteral("psu_failure"));
    fault.insert(QStringLiteral("name"), QStringLiteral("PSU 输出失效"));
    fault.insert(QStringLiteral("type"), QStringLiteral("fault"));
    fault.insert(QStringLiteral("probability"), 0.01);
    fault.insert(QStringLiteral("constraints"), QJsonArray{QStringLiteral("PSU-1.Vout=0V")});

    QJsonObject behavior;
    behavior.insert(QStringLiteral("normal"), normal);
    behavior.insert(QStringLiteral("faults"), QJsonArray{fault});
    return compactJson(behavior);
}

QString DemoProjectBuilder::actuatorBehaviorJson()
{
    QJsonObject normal;
    normal.insert(QStringLiteral("id"), QStringLiteral("act_normal"));
    normal.insert(QStringLiteral("name"), QStringLiteral("执行器正常"));
    normal.insert(QStringLiteral("type"), QStringLiteral("normal"));
    normal.insert(QStringLiteral("probability"), 0.0);
    normal.insert(QStringLiteral("constraints"), QJsonArray{QStringLiteral("ACT-1.Pressure=8bar")});

    QJsonObject fault;
    fault.insert(QStringLiteral("id"), QStringLiteral("act_stuck"));
    fault.insert(QStringLiteral("name"), QStringLiteral("执行器卡滞"));
    fault.insert(QStringLiteral("type"), QStringLiteral("fault"));
    fault.insert(QStringLiteral("probability"), 0.02);
    fault.insert(QStringLiteral("constraints"), QJsonArray{QStringLiteral("ACT-1.Pressure=0bar")});

    QJsonObject behavior;
    behavior.insert(QStringLiteral("normal"), normal);
    behavior.insert(QStringLiteral("faults"), QJsonArray{fault});
    return compactJson(behavior);
}

QString DemoProjectBuilder::subsystemBehaviorJson()
{
    QJsonObject normal;
    normal.insert(QStringLiteral("id"), QStringLiteral("sub_normal"));
    normal.insert(QStringLiteral("name"), QStringLiteral("子系统正常"));
    normal.insert(QStringLiteral("type"), QStringLiteral("normal"));
    normal.insert(QStringLiteral("probability"), 0.0);

    QJsonObject behavior;
    behavior.insert(QStringLiteral("normal"), normal);
    behavior.insert(QStringLiteral("faults"), QJsonArray());
    return compactJson(behavior);
}

QStringList DemoProjectBuilder::demoTestJsonList()
{
    auto makeTest = [](const QString &id, const QString &category, const QString &name, const QString &target, const QStringList &faults, double cost, double duration, const QVariantMap &metrics = QVariantMap()) {
        QJsonObject obj;
        obj.insert(QStringLiteral("id"), id);
        obj.insert(QStringLiteral("category"), category);
        obj.insert(QStringLiteral("name"), name);
        obj.insert(QStringLiteral("description"), QStringLiteral("演示生成的测试"));
        obj.insert(QStringLiteral("targetId"), target);
        obj.insert(QStringLiteral("detectableFaults"), QJsonArray::fromStringList(faults));
        obj.insert(QStringLiteral("isolatableFaults"), QJsonArray::fromStringList(faults));
        obj.insert(QStringLiteral("estimatedCost"), cost);
        obj.insert(QStringLiteral("estimatedDuration"), duration);
        if (!metrics.isEmpty())
            obj.insert(QStringLiteral("metrics"), QJsonObject::fromVariantMap(metrics));
        return obj;
    };

    QStringList list;
    QVariantMap signalMetrics;
    signalMetrics.insert(QStringLiteral("direction"), QStringLiteral("output"));
    signalMetrics.insert(QStringLiteral("unit"), QStringLiteral("V"));
    const QJsonObject signalTest = makeTest(QStringLiteral("signal:3:PSU-1.Vout"), QStringLiteral("signal"), QStringLiteral("PSU 输出电压检测"), QStringLiteral("PSU-1.Vout"), {QStringLiteral("psu_failure")}, 1.0, 1.0, signalMetrics);

    QVariantMap functionMetrics;
    functionMetrics.insert(QStringLiteral("requiredInputs"), QJsonArray{QStringLiteral("PSU-1.Vout")});
    functionMetrics.insert(QStringLiteral("actuators"), QJsonArray{QStringLiteral("ACT-1.Pressure")});
    const QJsonObject functionTest = makeTest(QStringLiteral("function:4:DeliverPressure"), QStringLiteral("function"), QStringLiteral("DeliverPressure 功能测试"), QStringLiteral("DeliverPressure"), {QStringLiteral("psu_failure"), QStringLiteral("act_stuck")}, 2.0, 2.0, functionMetrics);

    QVariantMap faultMetrics;
    faultMetrics.insert(QStringLiteral("sourceContainers"), QJsonArray{4});
    const QJsonObject faultTest = makeTest(QStringLiteral("fault:4:act_stuck"), QStringLiteral("faultMode"), QStringLiteral("执行器卡滞诊断"), QStringLiteral("act_stuck"), {QStringLiteral("act_stuck")}, 3.0, 3.0, faultMetrics);

    list << compactJson(QJsonArray{signalTest});
    list << compactJson(QJsonArray{functionTest, faultTest});

    return list;
}

QString DemoProjectBuilder::demoFunctionXml()
{
    QDomDocument doc;
    QDomElement root = doc.createElement(QStringLiteral("root"));
    doc.appendChild(root);

    QDomElement treeStruct = doc.createElement(QStringLiteral("treestruct"));
    root.appendChild(treeStruct);

    QDomElement item = doc.createElement(QStringLiteral("item"));
    item.setAttribute(QStringLiteral("name"), QStringLiteral("DeliverPressure"));
    treeStruct.appendChild(item);

    QDomElement functionElement = doc.createElement(QStringLiteral("functiondefine"));
    root.appendChild(functionElement);

    auto appendTextElement = [&](const QString &tag, const QString &text) {
        QDomElement e = doc.createElement(tag);
        e.appendChild(doc.createTextNode(text));
        functionElement.appendChild(e);
        return e;
    };

    appendTextElement(QStringLiteral("name"), QStringLiteral("DeliverPressure"));
    appendTextElement(QStringLiteral("link"), QStringLiteral("PSU-1.Vout,ACT-1.Pressure"));

    QDomElement dependency = doc.createElement(QStringLiteral("dependency"));
    functionElement.appendChild(dependency);
    QDomElement funcDep = doc.createElement(QStringLiteral("function"));
    funcDep.appendChild(doc.createTextNode(QString()));
    dependency.appendChild(funcDep);
    QDomElement compDep = doc.createElement(QStringLiteral("component"));
    compDep.appendChild(doc.createTextNode(QStringLiteral("PSU-1,ACT-1")));
    dependency.appendChild(compDep);
    QDomElement allComp = doc.createElement(QStringLiteral("allComponent"));
    allComp.appendChild(doc.createTextNode(QStringLiteral("PSU-1,ACT-1")));
    dependency.appendChild(allComp);

    appendTextElement(QStringLiteral("describe"), QStringLiteral("PSU 为执行器提供稳定压力"));
    appendTextElement(QStringLiteral("attribute"), QStringLiteral("Persistent,0.01"));

    auto addConstraint = [&](const QString &variable, const QString &value, const QString &type) {
        QDomElement constraint = doc.createElement(QStringLiteral("constraint"));
        QDomElement var = doc.createElement(QStringLiteral("variable"));
        var.appendChild(doc.createTextNode(variable));
        constraint.appendChild(var);
        QDomElement val = doc.createElement(QStringLiteral("value"));
        val.appendChild(doc.createTextNode(value));
        constraint.appendChild(val);
        QDomElement confidence = doc.createElement(QStringLiteral("confidence"));
        confidence.appendChild(doc.createTextNode(QStringLiteral("1")));
        constraint.appendChild(confidence);
        QDomElement typeElement = doc.createElement(QStringLiteral("type"));
        typeElement.appendChild(doc.createTextNode(type));
        constraint.appendChild(typeElement);
        functionElement.appendChild(constraint);
    };

    addConstraint(QStringLiteral("PSU-1.Vout"), QStringLiteral("24V"), QStringLiteral("一般变量"));
    addConstraint(QStringLiteral("ACT-1.Pressure"), QStringLiteral("8bar"), QStringLiteral("功能执行器"));

    return doc.toString();
}

bool DemoProjectBuilder::buildModelDatabase(const QString &dbPath, QString *errorMessage)
{
    const QString connName = QStringLiteral("demo_model_builder");
    QSqlDatabase db = QSqlDatabase::addDatabase("QSQLITE", connName);
    db.setDatabaseName(dbPath);
    if (!db.open()) {
        if (errorMessage)
            *errorMessage = QStringLiteral("无法创建模型数据库: %1").arg(db.lastError().text());
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
        "CREATE TABLE IF NOT EXISTS components (id INTEGER PRIMARY KEY, type TEXT, mark TEXT, parameter TEXT, variable TEXT, description TEXT, failuremode TEXT)",
        "CREATE TABLE IF NOT EXISTS parameters (id INTEGER PRIMARY KEY, componentId INTEGER, name TEXT, defaultValue TEXT)",
        "CREATE TABLE IF NOT EXISTS models (id INTEGER PRIMARY KEY, name TEXT, systemDescription TEXT, testDiscription TEXT, connectNodes TEXT, functionDescription TEXT)"
    };

    for (const QString &statement : createStatements) {
        if (!execQuery(query, statement, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> components = {
        {1, QStringLiteral("Power"), QStringLiteral("PSU-1"), QStringLiteral("Vin=24,Load=5"), QStringLiteral("Vout"), QStringLiteral("24V 电源"), QStringLiteral("psu_failure")},
        {2, QStringLiteral("Actuator"), QStringLiteral("ACT-1"), QStringLiteral("Pressure=8"), QStringLiteral("Pressure"), QStringLiteral("8bar 执行器"), QStringLiteral("act_stuck")}
    };
    for (const auto &row : components) {
        if (!prepareAndExec(query,
                            "INSERT INTO components (id, type, mark, parameter, variable, description, failuremode) VALUES (?,?,?,?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QList<QList<QVariant>> parameters = {
        {1, 1, QStringLiteral("Vin"), QStringLiteral("24")},
        {2, 1, QStringLiteral("Load"), QStringLiteral("5")},
        {3, 2, QStringLiteral("Pressure"), QStringLiteral("8")}
    };
    for (const auto &row : parameters) {
        if (!prepareAndExec(query,
                            "INSERT INTO parameters (id, componentId, name, defaultValue) VALUES (?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QString systemDescription = QStringLiteral(
        "DEF BEGIN\n"
        "PSU-1 supply\n"
        "ACT-1 actuator\n"
        "DEF END\n\n"
        "connect2e(PSU-1.Vout,ACT-1.Supply)\n");

    const QString functionDescription = demoFunctionXml();

    if (!prepareAndExec(query,
                        "INSERT INTO models (id, name, systemDescription, testDiscription, connectNodes, functionDescription) VALUES (?,?,?,?,?,?)",
                        {1, QStringLiteral("QBT"), systemDescription, QString(), QStringLiteral("PSU-1.Vout->ACT-1.Supply"), functionDescription},
                        errorMessage)) {
        cleanup();
        return false;
    }

    cleanup();
    return true;
}
