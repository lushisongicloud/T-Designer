#include "BO/test/dmatrixservice.h"

#include <QDateTime>
#include <QDir>
#include <QFile>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QSqlQuery>
#include <QSqlError>
#include <QVariant>
#include <QtDebug>
#include <cmath>
#include <limits>

#include "widget/containerhierarchyutils.h"
#include "BO/function/functionrepository.h"
#include "BO/systementity.h"
#include "DO/model.h"
#include "testability/smt_facade.h"
#include "testability/function_catalog.h"

using namespace testability;

namespace {

QString defaultMetadataPath(const QString &projectDir, const QString &projectName)
{
    if (projectDir.isEmpty() || projectName.isEmpty())
        return QString();
    return QDir(projectDir).filePath(QString("%1.json").arg(projectName));
}

QString defaultCsvPath(const QString &projectDir, const QString &projectName)
{
    if (projectDir.isEmpty() || projectName.isEmpty())
        return QString();
    return QDir(projectDir).filePath(QString("%1.csv").arg(projectName));
}

bool ensureBuiltinMacroFamilies(const QSqlDatabase &db)
{
    if (!db.isOpen())
        return false;
    QSqlQuery count(db);
    if (count.exec(QString("SELECT COUNT(1) FROM sqlite_master WHERE type='table' AND name='port_connect_macro_family'"))
        && count.next() && count.value(0).toInt() == 0) {
        return false;
    }

    QSqlQuery exists(db);
    exists.exec(QString("SELECT COUNT(1) FROM port_connect_macro_family WHERE is_builtin = 1"));
    if (exists.next() && exists.value(0).toInt() > 0) {
        return true;
    }

    auto makeMacros = [](const QString &domain) {
        QJsonArray arr;
        auto add = [&](int arity, const QString &name, const QString &expansion) {
            QJsonObject obj;
            obj.insert(QString("arity"), arity);
            obj.insert(QString("macro_name"), name);
            obj.insert(QString("expansion"), expansion);
            arr.append(obj);
        };
        if (domain == QString("electric")) {
            add(2, QString("connect2e"), QString("(assert (= (+ %1.i %2.i) 0)) (assert (= %1.u %2.u))"));
            add(3, QString("connect3e"), QString("(assert (= (+ %1.i %2.i %3.i) 0)) (assert (= %1.u %2.u %3.u))"));
        } else if (domain == QString("hydraulic")) {
            add(2, QString("connect2h"), QString("(assert (= (+ %1.q %2.q) 0)) (assert (= %1.p %2.p))"));
            add(3, QString("connect3h"), QString("(assert (= (+ %1.q %2.q %3.q) 0)) (assert (= %1.p %2.p %3.p))"));
        } else if (domain == QString("mechanical")) {
            add(2, QString("connect2m"), QString("(assert (= (+ %1.F %2.F) 0)) (assert (= %1.M %2.M))"));
            add(3, QString("connect3m"), QString("(assert (= (+ %1.F %2.F %3.F) 0)) (assert (= %1.M %2.M %3.M))"));
        }
        return arr;
    };

    struct BuiltinFamily {
        QString name;
        QString domain;
        QString description;
    };
    const QVector<BuiltinFamily> families = {
        {QString("electric-connect"), QString("electric"), QString("电气连接宏族")},
        {QString("hydraulic-connect"), QString("hydraulic"), QString("液压连接宏族")},
        {QString("mechanical-connect"), QString("mechanical"), QString("机械连接宏族")}
    };

    for (const auto &fam : families) {
        QSqlQuery ins(db);
        ins.prepare(QString("INSERT OR IGNORE INTO port_connect_macro_family(family_name, domain, description, is_builtin, macros_json) "
                                   "VALUES(:name, :domain, :desc, 1, :json)"));
        ins.bindValue(QString(":name"), fam.name);
        ins.bindValue(QString(":domain"), fam.domain);
        ins.bindValue(QString(":desc"), fam.description);
        ins.bindValue(QString(":json"), QString::fromUtf8(QJsonDocument(makeMacros(fam.domain)).toJson(QJsonDocument::Compact)));
        ins.exec();
    }
    return true;
}

double optionalDouble(const QJsonObject &obj, const QString &key)
{
    const QJsonValue value = obj.value(key);
    if (value.isDouble()) {
        return value.toDouble();
    }
    if (value.isString()) {
        bool ok = false;
        double d = value.toString().toDouble(&ok);
        return ok ? d : std::numeric_limits<double>::quiet_NaN();
    }
    return std::numeric_limits<double>::quiet_NaN();
}

void insertIfFinite(QJsonObject &obj, const QString &key, double value)
{
    if (std::isfinite(value)) {
        obj.insert(key, value);
    }
}

} // namespace

DMatrixService::DMatrixService(const QSqlDatabase &db)
    : m_db(db)
{
}

QString DMatrixService::loadFunctionDescriptionFromModels(const QString &projectName) const
{
    if (!m_db.isOpen()) {
        return QString();
    }

    QString tableName;
    QSqlQuery check(m_db);
    if (!check.exec(QString("SELECT name FROM sqlite_master WHERE type='table' AND name IN ('models','model') LIMIT 1"))) {
        qWarning() << "DMatrixService failed to inspect models table" << check.lastError();
        return QString();
    }
    if (check.next()) {
        tableName = check.value(0).toString();
    }
    if (tableName.isEmpty()) {
        return QString();
    }

    auto loadByName = [&](const QString &name) -> QString {
        if (name.trimmed().isEmpty()) {
            return QString();
        }
        QSqlQuery query(m_db);
        query.prepare(QString("SELECT functionDescription FROM %1 WHERE name = :name LIMIT 1").arg(tableName));
        query.bindValue(QString(":name"), name.trimmed());
        if (!query.exec()) {
            qWarning() << "DMatrixService failed to load functionDescription for model" << name << query.lastError();
            return QString();
        }
        if (query.next()) {
            return query.value(0).toString();
        }
        return QString();
    };

    QString description = loadByName(projectName);
    if (description.trimmed().isEmpty()) {
        QSqlQuery any(m_db);
        if (any.exec(QString("SELECT functionDescription FROM %1 LIMIT 1").arg(tableName)) && any.next()) {
            description = any.value(0).toString();
        }
    }
    return description;
}

QMap<QString, FunctionInfo> DMatrixService::loadFunctionInfoMap(const QString &projectName) const
{
    const QString description = loadFunctionDescriptionFromModels(projectName);
    if (description.trimmed().isEmpty()) {
        return {};
    }
    const QMap<QString, FunctionInfo> functionMap = testability::FunctionCatalog::parse(description);
    if (functionMap.isEmpty()) {
        qWarning() << "DMatrixService parsed empty function map from models.functionDescription";
    } else {
        qDebug().noquote() << "[DMatrixService] loaded functionDescription from models, functions:"
                           << functionMap.keys();
    }
    return functionMap;
}

bool DMatrixService::ensureTable() const
{
    if (!m_db.isOpen()) return false;
    QSqlQuery query(m_db);
    if (!query.exec(QString(
            "CREATE TABLE IF NOT EXISTS dmatrix_meta ("
            " dmatrix_meta_id INTEGER PRIMARY KEY AUTOINCREMENT,"
            " container_id INTEGER NOT NULL,"
            " result_json TEXT NOT NULL,"
            " options_json TEXT NOT NULL,"
            " state_json TEXT,"
            " csv_path TEXT,"
            " checksum TEXT,"
            " is_active INTEGER NOT NULL DEFAULT 1,"
            " created_at TEXT DEFAULT CURRENT_TIMESTAMP,"
            " updated_at TEXT DEFAULT CURRENT_TIMESTAMP"
            ")"))) {
        qWarning() << "DMatrixService ensureTable failed" << query.lastError();
        return false;
    }
    QSqlQuery index(m_db);
    index.exec(QString("CREATE INDEX IF NOT EXISTS idx_dmatrix_container ON dmatrix_meta(container_id, is_active)"));
    ensureBuiltinMacroFamilies(m_db);
    return true;
}

static bool fillVector(const QJsonArray &array, QVector<bool> *out)
{
    if (!out) return false;
    QVector<bool> result;
    result.reserve(array.size());
    for (const auto &val : array) {
        result.append(val.toBool(true));
    }
    *out = result;
    return true;
}

QString DMatrixService::serializeState(const QVector<bool> &faultEnabled,
                                       const QVector<bool> &testEnabled)
{
    QJsonObject obj;
    QJsonArray faults;
    for (bool v : faultEnabled)
        faults.append(v);
    QJsonArray tests;
    for (bool v : testEnabled)
        tests.append(v);
    obj.insert(QString("faultEnabled"), faults);
    obj.insert(QString("testEnabled"), tests);
    return QString::fromUtf8(QJsonDocument(obj).toJson(QJsonDocument::Compact));
}

bool DMatrixService::parseState(const QString &json,
                                QVector<bool> *faultEnabled,
                                QVector<bool> *testEnabled)
{
    if (json.trimmed().isEmpty())
        return false;
    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (doc.isNull() || !doc.isObject()) {
        return false;
    }
    const QJsonObject obj = doc.object();
    if (faultEnabled) {
        fillVector(obj.value(QString("faultEnabled")).toArray(), faultEnabled);
    }
    if (testEnabled) {
        fillVector(obj.value(QString("testEnabled")).toArray(), testEnabled);
    }
    return true;
}

DMatrixBuildOptions DMatrixService::parseOptions(const QString &json) const
{
    DMatrixBuildOptions opts;
    if (json.trimmed().isEmpty())
        return opts;
    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (doc.isNull() || !doc.isObject()) {
        return opts;
    }
    const QJsonObject obj = doc.object();
    opts.mode = static_cast<DetectMode>(obj.value(QString("mode")).toInt(static_cast<int>(DetectMode::Guaranteed)));
    opts.timeoutMs = obj.value(QString("timeoutMs")).toInt(-1);
    opts.autoRange = obj.value(QString("autoRange")).toBool(true);
    opts.fallbackToTemplate = obj.value(QString("fallbackToTemplate")).toBool(true);
    opts.rangeTolerance = obj.value(QString("rangeTolerance")).toDouble(0.05);
    opts.searchMaxAbs = obj.value(QString("searchMaxAbs")).toDouble(10000.0);
    opts.includeFunctionInputs = obj.value(QString("includeFunctionInputs")).toBool(true);
    opts.outputDirectory = obj.value(QString("outputDirectory")).toString();
    return opts;
}

QString DMatrixService::serializeOptions(const DMatrixBuildOptions &options) const
{
    QJsonObject obj;
    obj.insert(QString("mode"), static_cast<int>(options.mode));
    obj.insert(QString("timeoutMs"), options.timeoutMs);
    obj.insert(QString("autoRange"), options.autoRange);
    obj.insert(QString("fallbackToTemplate"), options.fallbackToTemplate);
    obj.insert(QString("rangeTolerance"), options.rangeTolerance);
    obj.insert(QString("searchMaxAbs"), options.searchMaxAbs);
    obj.insert(QString("includeFunctionInputs"), options.includeFunctionInputs);
    obj.insert(QString("outputDirectory"), options.outputDirectory);
    return QString::fromUtf8(QJsonDocument(obj).toJson(QJsonDocument::Compact));
}

bool DMatrixService::parseMetadata(const QString &json, DMatrixBuildResult *result) const
{
    if (!result) return false;
    result->faults.clear();
    result->tests.clear();
    result->cells.clear();

    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (doc.isNull() || !doc.isObject()) {
        qWarning() << "DMatrixService parseMetadata failed" << error.errorString();
        return false;
    }
    const QJsonObject root = doc.object();
    const QJsonArray faultsArray = root.value(QString("faults")).toArray();
    for (const auto &val : faultsArray) {
        const QJsonObject obj = val.toObject();
        FaultDefinition fault;
        fault.id = obj.value(QString("id")).toString();
        fault.name = obj.value(QString("name")).toString();
        const QJsonValue kindVal = obj.value(QString("kind"));
        if (kindVal.isString()) {
            const QString kindStr = kindVal.toString().toLower();
            if (kindStr == QStringLiteral("component")) {
                fault.kind = FaultKind::Component;
            } else {
                fault.kind = FaultKind::Function;
            }
        } else {
            fault.kind = static_cast<FaultKind>(kindVal.toInt(static_cast<int>(FaultKind::Function)));
        }
        fault.relatedFunction = obj.value(QString("relatedFunction")).toString();
        fault.componentName = obj.value(QString("componentName")).toString();
        fault.failureModeName = obj.value(QString("failureModeName")).toString();
        const QJsonArray inputs = obj.value(QString("inputAssertions")).toArray();
        for (const auto &i : inputs) fault.inputAssertions.append(i.toString());
        const QJsonArray faultA = obj.value(QString("faultAssertions")).toArray();
        for (const auto &i : faultA) fault.faultAssertions.append(i.toString());
        const QJsonArray actuators = obj.value(QString("actuatorAssertions")).toArray();
        for (const auto &i : actuators) fault.actuatorAssertions.append(i.toString());
        fault.enabled = obj.value(QString("enabled")).toBool(true);
        result->faults.append(fault);
    }

    const QJsonArray testsArray = root.value(QString("tests")).toArray();
    for (const auto &val : testsArray) {
        const QJsonObject obj = val.toObject();
        TestDefinition test;
        test.id = obj.value(QString("id")).toString();
        test.name = obj.value(QString("name")).toString();
        const QJsonValue kindVal = obj.value(QString("kind"));
        if (kindVal.isString()) {
            const QString kindStr = kindVal.toString().toLower();
            if (kindStr == QStringLiteral("function")) {
                test.kind = TestKind::Function;
            } else if (kindStr == QStringLiteral("mode")) {
                test.kind = TestKind::Mode;
            } else {
                test.kind = TestKind::Signal;
            }
        } else {
            test.kind = static_cast<TestKind>(kindVal.toInt(static_cast<int>(TestKind::Signal)));
        }
        test.relatedFunction = obj.value(QString("relatedFunction")).toString();
        test.componentName = obj.value(QString("componentName")).toString();
        test.failureModeName = obj.value(QString("failureModeName")).toString();
        test.predicate = obj.value(QString("predicate")).toString();
        test.negatedPredicate = obj.value(QString("negatedPredicate")).toString();
        test.description = obj.value(QString("description")).toString();
        test.note = obj.value(QString("note")).toString();
        const QString remark = obj.value(QString("remark")).toString();
        if (test.note.isEmpty() && !remark.isEmpty()) {
            test.note = remark;
        }
        test.complexity = optionalDouble(obj, QStringLiteral("complexity"));
        test.cost = optionalDouble(obj, QStringLiteral("cost"));
        test.duration = optionalDouble(obj, QStringLiteral("duration"));
        test.successRate = optionalDouble(obj, QStringLiteral("successRate"));
        test.signalVariable = obj.value(QString("signalVariable")).toString();
        test.enabled = obj.value(QString("enabled")).toBool(true);
        result->tests.append(test);
    }

    const QJsonArray cellRows = root.value(QString("cells")).toArray();
    result->cells.resize(result->faults.size());
    for (int i = 0; i < cellRows.size() && i < result->faults.size(); ++i) {
        const QJsonArray row = cellRows.at(i).toArray();
        QVector<DetectabilityResult> rowVec;
        rowVec.reserve(result->tests.size());
        for (int j = 0; j < row.size() && j < result->tests.size(); ++j) {
            const QJsonObject obj = row.at(j).toObject();
            DetectabilityResult cell;
            cell.normalSat = obj.value(QString("normalSat")).toBool();
            cell.faultSat = obj.value(QString("faultSat")).toBool();
            cell.normalPassSat = obj.value(QString("normalPassSat")).toBool();
            cell.faultFailSat = obj.value(QString("faultFailSat")).toBool();
            cell.guaranteed = obj.value(QString("guaranteed")).toBool();
            cell.detected = obj.value(QString("detected")).toBool();
            cell.method = obj.value(QString("method")).toString();
            cell.detail = obj.value(QString("detail")).toString();
            rowVec.append(cell);
        }
        // pad if necessary
        while (rowVec.size() < result->tests.size()) {
            rowVec.append(DetectabilityResult());
        }
        result->cells[i] = rowVec;
    }
    // pad missing rows
    while (result->cells.size() < result->faults.size()) {
        QVector<DetectabilityResult> empty;
        empty.resize(result->tests.size());
        result->cells.append(empty);
    }
    return true;
}

QString DMatrixService::serializeMetadata(const DMatrixBuildResult &result,
                                          const DMatrixBuildOptions &options,
                                          const QString &csvPath,
                                          const QString &modelName,
                                          const QString &metadataPath) const
{
    QJsonObject metadata;
    QJsonArray faultsArray;
    for (const FaultDefinition &fault : result.faults) {
        QJsonObject obj;
        obj["id"] = fault.id;
        obj["name"] = fault.name;
        obj["kind"] = static_cast<int>(fault.kind);
        obj["relatedFunction"] = fault.relatedFunction;
        obj["componentName"] = fault.componentName;
        obj["failureModeName"] = fault.failureModeName;
        obj["inputAssertions"] = QJsonArray::fromStringList(fault.inputAssertions);
        obj["faultAssertions"] = QJsonArray::fromStringList(fault.faultAssertions);
        obj["actuatorAssertions"] = QJsonArray::fromStringList(fault.actuatorAssertions);
        obj["enabled"] = fault.enabled;
        faultsArray.append(obj);
    }
    metadata["faults"] = faultsArray;

    QJsonArray testsArray;
    for (const TestDefinition &test : result.tests) {
        QJsonObject obj;
        obj["id"] = test.id;
        obj["name"] = test.name;
        obj["kind"] = static_cast<int>(test.kind);
        obj["relatedFunction"] = test.relatedFunction;
        obj["componentName"] = test.componentName;
        obj["failureModeName"] = test.failureModeName;
        obj["predicate"] = test.predicate;
        obj["negatedPredicate"] = test.negatedPredicate;
        if (!test.description.isEmpty()) {
            obj["description"] = test.description;
        }
        obj["note"] = test.note;
        obj["remark"] = test.note;
        insertIfFinite(obj, QStringLiteral("complexity"), test.complexity);
        insertIfFinite(obj, QStringLiteral("cost"), test.cost);
        insertIfFinite(obj, QStringLiteral("duration"), test.duration);
        insertIfFinite(obj, QStringLiteral("successRate"), test.successRate);
        obj["signalVariable"] = test.signalVariable;
        obj["enabled"] = test.enabled;
        testsArray.append(obj);
    }
    metadata["tests"] = testsArray;

    QJsonArray rows;
    for (int i = 0; i < result.faults.size(); ++i) {
        QJsonArray row;
        if (i < result.cells.size()) {
            for (int j = 0; j < result.tests.size(); ++j) {
                DetectabilityResult cell;
                if (j < result.cells.at(i).size()) {
                    cell = result.cells.at(i).at(j);
                }
                QJsonObject obj;
                obj["normalSat"] = cell.normalSat;
                obj["faultSat"] = cell.faultSat;
                obj["normalPassSat"] = cell.normalPassSat;
                obj["faultFailSat"] = cell.faultFailSat;
                obj["guaranteed"] = cell.guaranteed;
                obj["detected"] = cell.detected;
                obj["method"] = cell.method;
                obj["detail"] = cell.detail;
                row.append(obj);
            }
        }
        rows.append(row);
    }
    metadata["cells"] = rows;

    QJsonObject optionsObj;
    optionsObj["mode"] = static_cast<int>(options.mode);
    optionsObj["timeoutMs"] = options.timeoutMs;
    optionsObj["autoRange"] = options.autoRange;
    optionsObj["fallbackToTemplate"] = options.fallbackToTemplate;
    optionsObj["rangeTolerance"] = options.rangeTolerance;
    optionsObj["searchMaxAbs"] = options.searchMaxAbs;
    optionsObj["includeFunctionInputs"] = options.includeFunctionInputs;
    metadata["options"] = optionsObj;

    metadata["modelName"] = modelName;
    metadata["generatedAt"] = QDateTime::currentDateTime().toString(Qt::ISODate);
    metadata["csvPath"] = csvPath;
    metadata["metadataPath"] = metadataPath;

    return QString::fromUtf8(QJsonDocument(metadata).toJson(QJsonDocument::Indented));
}

QString DMatrixService::readFile(const QString &path) const
{
    QFile f(path);
    if (!f.open(QIODevice::ReadOnly | QIODevice::Text))
        return QString();
    return QString::fromUtf8(f.readAll());
}

QString DMatrixService::relativeToProject(const QString &projectDir, const QString &path) const
{
    if (projectDir.isEmpty() || path.isEmpty())
        return path;
    QDir dir(projectDir);
    return dir.relativeFilePath(path);
}

QString DMatrixService::absoluteFromProject(const QString &projectDir, const QString &path) const
{
    if (projectDir.isEmpty() || path.isEmpty())
        return path;
    QDir dir(projectDir);
    return dir.absoluteFilePath(path);
}

void DMatrixService::deactivateOld(int containerId) const
{
    QSqlQuery query(m_db);
    query.prepare(QString("UPDATE dmatrix_meta SET is_active=0 WHERE container_id=:cid"));
    query.bindValue(QString(":cid"), containerId);
    query.exec();
}

DMatrixLoadResult DMatrixService::loadLatest(int containerId,
                                             const QString &projectDir,
                                             const QString &projectName) const
{
    DMatrixLoadResult load;
    if (!m_db.isOpen() || containerId <= 0)
        return load;

    QSqlQuery query(m_db);
    query.prepare(QString(
        "SELECT result_json, options_json, state_json, csv_path "
        "FROM dmatrix_meta WHERE container_id = :cid AND is_active = 1 "
        "ORDER BY updated_at DESC, dmatrix_meta_id DESC LIMIT 1"));
    query.bindValue(QString(":cid"), containerId);
    if (!query.exec()) {
        qWarning() << "DMatrixService loadLatest failed" << query.lastError();
        return load;
    }
    if (!query.next()) {
        return load;
    }

    const QString resultJson = query.value(0).toString();
    const QString optionsJson = query.value(1).toString();
    load.stateJson = query.value(2).toString();
    const QString csvPathRel = query.value(3).toString();

    load.options = parseOptions(optionsJson);
    load.csvPath = absoluteFromProject(projectDir, csvPathRel);
    load.metadataPath = defaultMetadataPath(projectDir, projectName);

    if (!parseMetadata(resultJson, &load.result)) {
        return load;
    }

    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(resultJson.toUtf8(), &error);
    if (error.error == QJsonParseError::NoError && doc.isObject()) {
        const QJsonObject obj = doc.object();
        const QString metaPathJson = obj.value(QString("metadataPath")).toString();
        if (!metaPathJson.isEmpty())
            load.metadataPath = absoluteFromProject(projectDir, metaPathJson);
        const QString csvPathJson = obj.value(QString("csvPath")).toString();
        if (!csvPathJson.isEmpty())
            load.csvPath = absoluteFromProject(projectDir, csvPathJson);
    }

    load.found = true;
    return load;
}

bool DMatrixService::saveResult(int containerId,
                                const DMatrixBuildResult &result,
                                const DMatrixBuildOptions &options,
                                const QString &csvPath,
                                const QString &metadataPath,
                                const QString &stateJson) const
{
    if (!m_db.isOpen() || containerId <= 0) return false;
    const QString optionsJson = serializeOptions(options);
    const QString resultJson = serializeMetadata(result, options, csvPath, QString(), metadataPath);

    deactivateOld(containerId);

    QSqlQuery insert(m_db);
    insert.prepare(QString(
        "INSERT INTO dmatrix_meta(container_id, result_json, options_json, state_json, csv_path, is_active, updated_at) "
        "VALUES(:cid, :result, :options, :state, :csv, 1, CURRENT_TIMESTAMP)"));
    insert.bindValue(QString(":cid"), containerId);
    insert.bindValue(QString(":result"), resultJson);
    insert.bindValue(QString(":options"), optionsJson);
    insert.bindValue(QString(":state"), stateJson);
    insert.bindValue(QString(":csv"), csvPath);
    if (!insert.exec()) {
        qWarning() << "DMatrixService saveResult failed" << insert.lastError();
        return false;
    }
    return true;
}

bool DMatrixService::saveState(int containerId,
                               const QString &stateJson,
                               const QString &metadataPath,
                               const QString &csvPath) const
{
    if (!m_db.isOpen() || containerId <= 0)
        return false;
    QSqlQuery query(m_db);
    query.prepare(QString(
        "UPDATE dmatrix_meta SET state_json=:state, "
        "csv_path=COALESCE(:csv, csv_path), "
        "updated_at=CURRENT_TIMESTAMP WHERE container_id=:cid AND is_active=1"));
    query.bindValue(QString(":state"), stateJson);
    query.bindValue(QString(":csv"), csvPath);
    query.bindValue(QString(":cid"), containerId);
    if (!query.exec()) {
        qWarning() << "DMatrixService saveState failed" << query.lastError();
        return false;
    }
    return true;
}

bool DMatrixService::buildAndPersist(SystemEntity *systemEntity,
                                     const QString &systemDescription,
                                     int containerId,
                                     const QString &projectDir,
                                     const QString &projectName,
                                     const DMatrixBuildOptions &options,
                                     DMatrixBuildResult *outResult,
                                     QString *metadataPathOut,
                                     QString *csvPathOut,
                                     QString *errorMessage) const
{
    if (!systemEntity || !m_db.isOpen()) {
        if (errorMessage) *errorMessage = QString("系统实体或数据库不可用");
        return false;
    }
    if (!ensureTable()) {
        if (errorMessage) *errorMessage = QString("dmatrix_meta 表不可用");
        return false;
    }

    // 准备功能定义：优先使用 models.functionDescription，与 T-Solver 对齐
    QMap<QString, FunctionInfo> functionMap = loadFunctionInfoMap(projectName);
    if (functionMap.isEmpty()) {
        FunctionRepository repo(m_db);
        repo.ensureTables();
        FunctionDocumentRecord doc = repo.loadDocument(containerId);
        if (doc.id > 0 && !doc.xmlText.trimmed().isEmpty()) {
            const FunctionDocumentParseResult parsed = repo.parseFunctionDocument(doc.xmlText);
            functionMap = parsed.functionMap;
        }
    }
    if (functionMap.isEmpty()) {
        functionMap = ContainerHierarchy::fetchFunctionInfoMap(m_db);
    }

    testability::DMatrixBuilder builder(systemEntity);
    builder.setFunctionInfoMap(functionMap);

    SmtFacade smt = SmtFacade::fromSystemDescription(*systemEntity, systemDescription);

    QVector<FaultDefinition> faults = builder.collectFunctionFaults();
    const QVector<FaultDefinition> modeFaults = builder.collectComponentModeFaults(smt);
    faults += modeFaults;
    QVector<TestDefinition> tests = builder.collectFunctionTests();
    tests += builder.collectModeTests(smt);
    tests += builder.collectSignalTests(smt, options);

    DMatrixBuildResult result = builder.buildDMatrix(faults, tests, smt, options);

    const QString outputDir = options.outputDirectory.isEmpty() ? projectDir : options.outputDirectory;
    QString csvPath;
    QString metadataPath;
    builder.exportDMatrix(result, projectName, options, outputDir, &csvPath, &metadataPath);

    // 同步一份工程同名 JSON
    const QString projectMetadataPath = defaultMetadataPath(projectDir, projectName);
    const QString metadataContent = readFile(metadataPath);
    if (!metadataContent.isEmpty() && !projectMetadataPath.isEmpty()) {
        // 确保项目目录存在
        QDir projDir(QFileInfo(projectMetadataPath).absolutePath());
        if (!projDir.exists()) {
            qDebug() << "Creating project metadata directory:" << projDir.absolutePath();
            if (!projDir.mkpath(QString("."))) {
                qWarning() << "Failed to create project metadata directory:" << projDir.absolutePath();
            }
        }
        QFile f(projectMetadataPath);
        if (f.open(QIODevice::WriteOnly | QIODevice::Text)) {
            f.write(metadataContent.toUtf8());
            f.close();
            metadataPath = projectMetadataPath;
        }
    }
    // 同步 CSV (可选)
    const QString projectCsvPath = defaultCsvPath(projectDir, projectName);
    if (!csvPath.isEmpty() && !projectCsvPath.isEmpty()) {
        // 确保项目目录存在
        QDir projDir(QFileInfo(projectCsvPath).absolutePath());
        if (!projDir.exists()) {
            qDebug() << "Creating project CSV directory:" << projDir.absolutePath();
            if (!projDir.mkpath(QString("."))) {
                qWarning() << "Failed to create project CSV directory:" << projDir.absolutePath();
            }
        }
        QFile::remove(projectCsvPath);
        QFile::copy(csvPath, projectCsvPath);
        csvPath = projectCsvPath;
    }

    const QString stateJson = serializeState(result.faults.size() ? QVector<bool>(result.faults.size(), true) : QVector<bool>(),
                                             result.tests.size() ? QVector<bool>(result.tests.size(), true) : QVector<bool>());

    // 存库：路径保存相对值
    saveResult(containerId, result, options,
               relativeToProject(projectDir, csvPath),
               relativeToProject(projectDir, metadataPath),
               stateJson);

    if (outResult) *outResult = result;
    if (metadataPathOut) *metadataPathOut = metadataPath;
    if (csvPathOut) *csvPathOut = csvPath;
    return true;
}
