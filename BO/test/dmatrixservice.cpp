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

#include "widget/containerhierarchyutils.h"
#include "BO/function/functionrepository.h"
#include "BO/systementity.h"
#include "DO/model.h"
#include "testability/smt_facade.h"

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
    if (count.exec(QStringLiteral("SELECT COUNT(1) FROM sqlite_master WHERE type='table' AND name='port_connect_macro_family'"))
        && count.next() && count.value(0).toInt() == 0) {
        return false;
    }

    QSqlQuery exists(db);
    exists.exec(QStringLiteral("SELECT COUNT(1) FROM port_connect_macro_family WHERE is_builtin = 1"));
    if (exists.next() && exists.value(0).toInt() > 0) {
        return true;
    }

    auto makeMacros = [](const QString &domain) {
        QJsonArray arr;
        auto add = [&](int arity, const QString &name, const QString &expansion) {
            QJsonObject obj;
            obj.insert(QStringLiteral("arity"), arity);
            obj.insert(QStringLiteral("macro_name"), name);
            obj.insert(QStringLiteral("expansion"), expansion);
            arr.append(obj);
        };
        if (domain == QStringLiteral("electric")) {
            add(2, QStringLiteral("connect2e"), QStringLiteral("(assert (= (+ %1.i %2.i) 0)) (assert (= %1.u %2.u))"));
            add(3, QStringLiteral("connect3e"), QStringLiteral("(assert (= (+ %1.i %2.i %3.i) 0)) (assert (= %1.u %2.u %3.u))"));
        } else if (domain == QStringLiteral("hydraulic")) {
            add(2, QStringLiteral("connect2h"), QStringLiteral("(assert (= (+ %1.q %2.q) 0)) (assert (= %1.p %2.p))"));
            add(3, QStringLiteral("connect3h"), QStringLiteral("(assert (= (+ %1.q %2.q %3.q) 0)) (assert (= %1.p %2.p %3.p))"));
        } else if (domain == QStringLiteral("mechanical")) {
            add(2, QStringLiteral("connect2m"), QStringLiteral("(assert (= (+ %1.F %2.F) 0)) (assert (= %1.M %2.M))"));
            add(3, QStringLiteral("connect3m"), QStringLiteral("(assert (= (+ %1.F %2.F %3.F) 0)) (assert (= %1.M %2.M %3.M))"));
        }
        return arr;
    };

    struct BuiltinFamily {
        QString name;
        QString domain;
        QString description;
    };
    const QVector<BuiltinFamily> families = {
        {QStringLiteral("electric-connect"), QStringLiteral("electric"), QStringLiteral("电气连接宏族")},
        {QStringLiteral("hydraulic-connect"), QStringLiteral("hydraulic"), QStringLiteral("液压连接宏族")},
        {QStringLiteral("mechanical-connect"), QStringLiteral("mechanical"), QStringLiteral("机械连接宏族")}
    };

    for (const auto &fam : families) {
        QSqlQuery ins(db);
        ins.prepare(QStringLiteral("INSERT OR IGNORE INTO port_connect_macro_family(family_name, domain, description, is_builtin, macros_json) "
                                   "VALUES(:name, :domain, :desc, 1, :json)"));
        ins.bindValue(QStringLiteral(":name"), fam.name);
        ins.bindValue(QStringLiteral(":domain"), fam.domain);
        ins.bindValue(QStringLiteral(":desc"), fam.description);
        ins.bindValue(QStringLiteral(":json"), QString::fromUtf8(QJsonDocument(makeMacros(fam.domain)).toJson(QJsonDocument::Compact)));
        ins.exec();
    }
    return true;
}

} // namespace

DMatrixService::DMatrixService(const QSqlDatabase &db)
    : m_db(db)
{
}

bool DMatrixService::ensureTable() const
{
    if (!m_db.isOpen()) return false;
    QSqlQuery query(m_db);
    if (!query.exec(QStringLiteral(
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
    index.exec(QStringLiteral("CREATE INDEX IF NOT EXISTS idx_dmatrix_container ON dmatrix_meta(container_id, is_active)"));
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
    obj.insert(QStringLiteral("faultEnabled"), faults);
    obj.insert(QStringLiteral("testEnabled"), tests);
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
        fillVector(obj.value(QStringLiteral("faultEnabled")).toArray(), faultEnabled);
    }
    if (testEnabled) {
        fillVector(obj.value(QStringLiteral("testEnabled")).toArray(), testEnabled);
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
    opts.mode = static_cast<DetectMode>(obj.value(QStringLiteral("mode")).toInt(static_cast<int>(DetectMode::Guaranteed)));
    opts.timeoutMs = obj.value(QStringLiteral("timeoutMs")).toInt(-1);
    opts.autoRange = obj.value(QStringLiteral("autoRange")).toBool(true);
    opts.fallbackToTemplate = obj.value(QStringLiteral("fallbackToTemplate")).toBool(true);
    opts.rangeTolerance = obj.value(QStringLiteral("rangeTolerance")).toDouble(0.05);
    opts.searchMaxAbs = obj.value(QStringLiteral("searchMaxAbs")).toDouble(10000.0);
    opts.includeFunctionInputs = obj.value(QStringLiteral("includeFunctionInputs")).toBool(true);
    opts.outputDirectory = obj.value(QStringLiteral("outputDirectory")).toString();
    return opts;
}

QString DMatrixService::serializeOptions(const DMatrixBuildOptions &options) const
{
    QJsonObject obj;
    obj.insert(QStringLiteral("mode"), static_cast<int>(options.mode));
    obj.insert(QStringLiteral("timeoutMs"), options.timeoutMs);
    obj.insert(QStringLiteral("autoRange"), options.autoRange);
    obj.insert(QStringLiteral("fallbackToTemplate"), options.fallbackToTemplate);
    obj.insert(QStringLiteral("rangeTolerance"), options.rangeTolerance);
    obj.insert(QStringLiteral("searchMaxAbs"), options.searchMaxAbs);
    obj.insert(QStringLiteral("includeFunctionInputs"), options.includeFunctionInputs);
    obj.insert(QStringLiteral("outputDirectory"), options.outputDirectory);
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
    const QJsonArray faultsArray = root.value(QStringLiteral("faults")).toArray();
    for (const auto &val : faultsArray) {
        const QJsonObject obj = val.toObject();
        FaultDefinition fault;
        fault.id = obj.value(QStringLiteral("id")).toString();
        fault.name = obj.value(QStringLiteral("name")).toString();
        fault.kind = static_cast<FaultKind>(obj.value(QStringLiteral("kind")).toInt(static_cast<int>(FaultKind::Function)));
        fault.relatedFunction = obj.value(QStringLiteral("relatedFunction")).toString();
        fault.componentName = obj.value(QStringLiteral("componentName")).toString();
        fault.failureModeName = obj.value(QStringLiteral("failureModeName")).toString();
        const QJsonArray inputs = obj.value(QStringLiteral("inputAssertions")).toArray();
        for (const auto &i : inputs) fault.inputAssertions.append(i.toString());
        const QJsonArray faultA = obj.value(QStringLiteral("faultAssertions")).toArray();
        for (const auto &i : faultA) fault.faultAssertions.append(i.toString());
        const QJsonArray actuators = obj.value(QStringLiteral("actuatorAssertions")).toArray();
        for (const auto &i : actuators) fault.actuatorAssertions.append(i.toString());
        fault.enabled = obj.value(QStringLiteral("enabled")).toBool(true);
        result->faults.append(fault);
    }

    const QJsonArray testsArray = root.value(QStringLiteral("tests")).toArray();
    for (const auto &val : testsArray) {
        const QJsonObject obj = val.toObject();
        TestDefinition test;
        test.id = obj.value(QStringLiteral("id")).toString();
        test.name = obj.value(QStringLiteral("name")).toString();
        test.kind = static_cast<TestKind>(obj.value(QStringLiteral("kind")).toInt(static_cast<int>(TestKind::Signal)));
        test.relatedFunction = obj.value(QStringLiteral("relatedFunction")).toString();
        test.componentName = obj.value(QStringLiteral("componentName")).toString();
        test.failureModeName = obj.value(QStringLiteral("failureModeName")).toString();
        test.predicate = obj.value(QStringLiteral("predicate")).toString();
        test.negatedPredicate = obj.value(QStringLiteral("negatedPredicate")).toString();
        test.note = obj.value(QStringLiteral("note")).toString();
        test.signalVariable = obj.value(QStringLiteral("signalVariable")).toString();
        test.enabled = obj.value(QStringLiteral("enabled")).toBool(true);
        result->tests.append(test);
    }

    const QJsonArray cellRows = root.value(QStringLiteral("cells")).toArray();
    result->cells.resize(result->faults.size());
    for (int i = 0; i < cellRows.size() && i < result->faults.size(); ++i) {
        const QJsonArray row = cellRows.at(i).toArray();
        QVector<DetectabilityResult> rowVec;
        rowVec.reserve(result->tests.size());
        for (int j = 0; j < row.size() && j < result->tests.size(); ++j) {
            const QJsonObject obj = row.at(j).toObject();
            DetectabilityResult cell;
            cell.normalSat = obj.value(QStringLiteral("normalSat")).toBool();
            cell.faultSat = obj.value(QStringLiteral("faultSat")).toBool();
            cell.normalPassSat = obj.value(QStringLiteral("normalPassSat")).toBool();
            cell.faultFailSat = obj.value(QStringLiteral("faultFailSat")).toBool();
            cell.guaranteed = obj.value(QStringLiteral("guaranteed")).toBool();
            cell.detected = obj.value(QStringLiteral("detected")).toBool();
            cell.method = obj.value(QStringLiteral("method")).toString();
            cell.detail = obj.value(QStringLiteral("detail")).toString();
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
        obj["note"] = test.note;
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
    query.prepare(QStringLiteral("UPDATE dmatrix_meta SET is_active=0 WHERE container_id=:cid"));
    query.bindValue(QStringLiteral(":cid"), containerId);
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
    query.prepare(QStringLiteral(
        "SELECT result_json, options_json, state_json, csv_path "
        "FROM dmatrix_meta WHERE container_id = :cid AND is_active = 1 "
        "ORDER BY updated_at DESC, dmatrix_meta_id DESC LIMIT 1"));
    query.bindValue(QStringLiteral(":cid"), containerId);
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
        const QString metaPathJson = obj.value(QStringLiteral("metadataPath")).toString();
        if (!metaPathJson.isEmpty())
            load.metadataPath = absoluteFromProject(projectDir, metaPathJson);
        const QString csvPathJson = obj.value(QStringLiteral("csvPath")).toString();
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
    insert.prepare(QStringLiteral(
        "INSERT INTO dmatrix_meta(container_id, result_json, options_json, state_json, csv_path, is_active, updated_at) "
        "VALUES(:cid, :result, :options, :state, :csv, 1, CURRENT_TIMESTAMP)"));
    insert.bindValue(QStringLiteral(":cid"), containerId);
    insert.bindValue(QStringLiteral(":result"), resultJson);
    insert.bindValue(QStringLiteral(":options"), optionsJson);
    insert.bindValue(QStringLiteral(":state"), stateJson);
    insert.bindValue(QStringLiteral(":csv"), csvPath);
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
    query.prepare(QStringLiteral(
        "UPDATE dmatrix_meta SET state_json=:state, "
        "csv_path=COALESCE(:csv, csv_path), "
        "updated_at=CURRENT_TIMESTAMP WHERE container_id=:cid AND is_active=1"));
    query.bindValue(QStringLiteral(":state"), stateJson);
    query.bindValue(QStringLiteral(":csv"), csvPath);
    query.bindValue(QStringLiteral(":cid"), containerId);
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
        if (errorMessage) *errorMessage = QStringLiteral("系统实体或数据库不可用");
        return false;
    }
    if (!ensureTable()) {
        if (errorMessage) *errorMessage = QStringLiteral("dmatrix_meta 表不可用");
        return false;
    }

    // 准备功能定义
    FunctionRepository repo(m_db);
    repo.ensureTables();
    QMap<QString, FunctionInfo> functionMap;
    FunctionDocumentRecord doc = repo.loadDocument(containerId);
    if (doc.id > 0 && !doc.xmlText.trimmed().isEmpty()) {
        const FunctionDocumentParseResult parsed = repo.parseFunctionDocument(doc.xmlText);
        functionMap = parsed.functionMap;
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
