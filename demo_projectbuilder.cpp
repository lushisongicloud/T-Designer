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

bool DemoProjectBuilder::buildProjectDatabase(const QString &dbPath, QString *errorMessage)
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
        {1001, QString("1"), QString("Demo System"), 0, QString("演示项目根节点")},
        {1002, QString("3"), QString("Subsystem"), 1001, QString("演示子系统")},
        {1003, QString("5"), QString("Station 1"), 1002, QString("演示位置")},
        {1004, QString("6"), QString("Demo Diagram"), 1003, QString("演示图纸")}
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
        {1, 1003, QString("PSU-1"), QString("Power"), QString("普通元件"), QString("Power Supply"), QString("提供24V稳压输出"), QString("PSU001"), QString(), QString("1"), QString("DemoWorks"), QString(), QString("class PSU"), QString(), QString(), QString(), QString("120000")},
        {2, 1003, QString("ACT-1"), QString("Actuator"), QString("普通元件"), QString("Hydraulic Actuator"), QString("输出8bar液压压力"), QString("ACT001"), QString(), QString("2"), QString("DemoWorks"), QString(), QString("class ACT"), QString(), QString(), QString(), QString("90000")}
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
        {1, 1, 1, QString("PSU"), QString("0"), QString("电源模块"), QString("PSU"), QString(), QString(), QString(""), QString("source"), 1, 0, 1, QString(), QString("PSU-1.Supply")},
        {2, 2, 1, QString("ACT"), QString("0"), QString("执行器模块"), QString("ACT"), QString(), QString(), QString(""), QString("actuator"), 0, 1, 1, QString(), QString("ACT-1.Deliver")}
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
        {1, 1, QString("Vin"), QString("供电输入")},
        {2, 1, QString("Vout"), QString("稳压输出")},
        {3, 2, QString("Supply"), QString("供油接口")},
        {4, 2, QString("Pressure"), QString("压力输出")}
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
        {1, 1004, QString("原理图"), QString("6"), QString("DemoDiagram")}
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
        {1, 1003, 1, QVariant(), QString("L1"), QString(), QString("2"), QString("4"), QString("Round"), QString("Red"), QString("2.5"), QString("Power"), QString("0"), QString("0")}
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
        {1, QString("DeliverPressure"), QString("ACT-1.Pressure"), QString("PSU-1.Vout=24V"), QString("演示功能: 电源驱动执行器"), QString("PSU-1.Vout,ACT-1.Pressure"), QString("PSU-1,ACT-1"), QString("PSU-1,ACT-1"), QString(), 1, 0.01}
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
        {1, QString("Demo System"), 0, 0, 0, 0, compactJson(QJsonArray()), QString(), subsystemBehaviorJson(), QString(), QString(), QVariant(), QString("System"), QString("Demo System")},
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

bool DemoProjectBuilder::buildModelDatabase(const QString &dbPath, QString *errorMessage)
{
    const QString connName = QString("demo_model_builder");
    QSqlDatabase db = QSqlDatabase::addDatabase("QSQLITE", connName);
    db.setDatabaseName(dbPath);
    if (!db.open()) {
        if (errorMessage)
            *errorMessage = QString("无法创建模型数据库: %1").arg(db.lastError().text());
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
        {1, QString("Power"), QString("PSU-1"), QString("Vin=24,Load=5"), QString("Vout"), QString("24V 电源"), QString("psu_failure")},
        {2, QString("Actuator"), QString("ACT-1"), QString("Pressure=8"), QString("Pressure"), QString("8bar 执行器"), QString("act_stuck")}
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
        {1, 1, QString("Vin"), QString("24")},
        {2, 1, QString("Load"), QString("5")},
        {3, 2, QString("Pressure"), QString("8")}
    };
    for (const auto &row : parameters) {
        if (!prepareAndExec(query,
                            "INSERT INTO parameters (id, componentId, name, defaultValue) VALUES (?,?,?,?)",
                            row, errorMessage)) {
            cleanup();
            return false;
        }
    }

    const QString systemDescription = QString(
        "DEF BEGIN\n"
        "PSU-1 supply\n"
        "ACT-1 actuator\n"
        "DEF END\n\n"
        "connect2e(PSU-1.Vout,ACT-1.Supply)\n");

    const QString functionDescription = demoFunctionXml();

    if (!prepareAndExec(query,
                        "INSERT INTO models (id, name, systemDescription, testDiscription, connectNodes, functionDescription) VALUES (?,?,?,?,?,?)",
                        {1, QString("QBT"), systemDescription, QString(), QString("PSU-1.Vout->ACT-1.Supply"), functionDescription},
                        errorMessage)) {
        cleanup();
        return false;
    }

    cleanup();
    return true;
}
