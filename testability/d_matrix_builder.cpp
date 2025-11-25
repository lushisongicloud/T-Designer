#include "d_matrix_builder.h"

#include <QtConcurrent>
#include <QDateTime>
#include <QDebug>
#include <QDir>
#include <QFile>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QMutexLocker>
#include <QRegularExpression>
#include <QSet>
#include <QStringList>
#include <QTextStream>

#include <algorithm>
#include <cmath>
#include <functional>

#include "BO/systementity.h"
#include "DO/model.h"
#include "testability/constraint_utils.h"

namespace testability {
namespace {

struct NumericInterval
{
    double lower = 0.0;
    double upper = 0.0;

    bool isValid() const
    {
        return std::isfinite(lower) && std::isfinite(upper) && lower <= upper;
    }
};

QString sanitizeId(const QString &prefix, const QString &name)
{
    QString sanitized = name;
    sanitized.replace(QRegularExpression("[^A-Za-z0-9_]+"), "_");
    sanitized.remove(QRegularExpression("^_+"));
    sanitized.remove(QRegularExpression("_+$"));
    if (sanitized.isEmpty()) {
        sanitized = QString("id");
    }
    const QString hashSuffix = QString::number(qHash(name), 16);
    return prefix + sanitized + QString("_") + hashSuffix;
}

QStringList splitTrimmed(const QString &text, QChar delimiter)
{
    QStringList result;
    const QStringList parts = text.split(delimiter, QString::KeepEmptyParts);
    for (const QString &part : parts) {
        const QString trimmed = part.trimmed();
        if (!trimmed.isEmpty()) {
            result.append(trimmed);
        }
    }
    return result;
}

bool parseIntervalToken(const QString &text, NumericInterval *interval)
{
    if (!interval) {
        return false;
    }
    static const QRegularExpression re(QString("^\\s*([\\[(])\\s*([-+]?\\d+(?:\\.\\d+)?(?:[eE][-+]?\\d+)?)\\s*,\\s*([-+]?\\d+(?:\\.\\d+)?(?:[eE][-+]?\\d+)?)\\s*([\\])])\\s*$"));
    QRegularExpressionMatch match = re.match(text);
    if (!match.hasMatch()) {
        return false;
    }
    bool okLower = false;
    bool okUpper = false;
    const double lower = match.captured(2).toDouble(&okLower);
    const double upper = match.captured(3).toDouble(&okUpper);
    if (!okLower || !okUpper) {
        return false;
    }
    interval->lower = std::min(lower, upper);
    interval->upper = std::max(lower, upper);
    return interval->isValid();
}

bool isBooleanToken(const QString &text, QString *normalized = nullptr)
{
    const QString lowered = text.trimmed().toLower();
    if (lowered == QStringLiteral("true")) {
        if (normalized) {
            *normalized = QStringLiteral("true");
        }
        return true;
    }
    if (lowered == QStringLiteral("false")) {
        if (normalized) {
            *normalized = QStringLiteral("false");
        }
        return true;
    }
    return false;
}

struct RangeParseResult
{
    bool valid = false;
    bool isBoolean = false;
    QVector<NumericInterval> intervals;
    QSet<QString> boolValues;
};

RangeParseResult parseRangeText(const QString &text)
{
    RangeParseResult result;
    const QStringList tokens = splitTrimmed(text, QLatin1Char(';'));
    if (tokens.isEmpty()) {
        return result;
    }

    QVector<NumericInterval> numericIntervals;
    QSet<QString> booleanValues;
    bool hasNumeric = false;
    bool hasBoolean = false;

    for (const QString &token : tokens) {
        QString normalizedBool;
        if (isBooleanToken(token, &normalizedBool)) {
            hasBoolean = true;
            booleanValues.insert(normalizedBool);
            continue;
        }

        NumericInterval interval;
        if (parseIntervalToken(token, &interval)) {
            hasNumeric = true;
            numericIntervals.append(interval);
            continue;
        }

        return RangeParseResult();
    }

    if (hasBoolean && hasNumeric) {
        return RangeParseResult();
    }
    if (hasBoolean) {
        result.valid = true;
        result.isBoolean = true;
        result.boolValues = booleanValues;
        return result;
    }
    if (hasNumeric) {
        result.valid = true;
        result.isBoolean = false;
        result.intervals = numericIntervals;
        return result;
    }
    return result;
}

QVector<NumericInterval> mergeIntervals(QVector<NumericInterval> intervals)
{
    if (intervals.isEmpty()) {
        return intervals;
    }
    std::sort(intervals.begin(), intervals.end(), [](const NumericInterval &a, const NumericInterval &b) {
        if (a.lower == b.lower) {
            return a.upper < b.upper;
        }
        return a.lower < b.lower;
    });

    QVector<NumericInterval> merged;
    merged.reserve(intervals.size());
    NumericInterval current = intervals.first();
    for (int i = 1; i < intervals.size(); ++i) {
        const NumericInterval &next = intervals.at(i);
        if (next.lower <= current.upper) {
            current.upper = std::max(current.upper, next.upper);
        } else {
            merged.append(current);
            current = next;
        }
    }
    merged.append(current);
    return merged;
}

QVector<NumericInterval> intersectIntervals(const QVector<NumericInterval> &lhs,
                                            const QVector<NumericInterval> &rhs)
{
    QVector<NumericInterval> result;
    for (const NumericInterval &a : lhs) {
        for (const NumericInterval &b : rhs) {
            NumericInterval intersection;
            intersection.lower = std::max(a.lower, b.lower);
            intersection.upper = std::min(a.upper, b.upper);
            if (intersection.isValid()) {
                result.append(intersection);
            }
        }
    }
    return result;
}

bool contains(const QVector<NumericInterval> &intervals, double value)
{
    for (const NumericInterval &interval : intervals) {
        if (value >= interval.lower && value <= interval.upper) {
            return true;
        }
    }
    return false;
}

QString formatInterval(const NumericInterval &interval)
{
    return QString("[%1, %2]").arg(interval.lower).arg(interval.upper);
}

QStringList negateAssertions(const QStringList &assertions)
{
    QStringList result;
    result.reserve(assertions.size());
    for (const QString &expr : assertions) {
        result.append(QStringLiteral("(assert (not %1))").arg(expr));
    }
    return result;
}

QList<ComponentOverride> toComponentOverrides(const QList<FailureMode::ModeOverride> &overrides)
{
    QList<ComponentOverride> list;
    list.reserve(overrides.size());
    for (const auto &ov : overrides) {
        ComponentOverride co;
        co.componentName = ov.componentName;
        co.assertions = ov.assertions;
        co.replaceNormal = ov.replaceNormal;
        list.append(co);
    }
    return list;
}

} // namespace

DMatrixBuilder::DMatrixBuilder(SystemEntity *entity)
    : systemEntity(entity)
{
}

void DMatrixBuilder::setFunctionInfoMap(const QMap<QString, FunctionInfo> &map)
{
    functionInfoMap = map;
}

QVector<FaultDefinition> DMatrixBuilder::collectFunctionFaults() const
{
    QVector<FaultDefinition> faults;
    faults.reserve(functionInfoMap.size());

    for (auto it = functionInfoMap.cbegin(); it != functionInfoMap.cend(); ++it) {
        const FunctionInfo &info = it.value();
        if (info.actuatorConstraint.variable.isEmpty()) {
            qDebug().noquote() << "[DMatrix] skip function fault due to missing actuator:" << info.functionName;
            continue;
        }
        if (info.constraintIntegrity == QStringLiteral("不完整") || info.constraintIntegrity == QStringLiteral("不正确")) {
            qDebug().noquote() << "[DMatrix] skip function fault due to invalid integrity:" << info.functionName;
            continue;
        }

        FaultDefinition fault;
        fault.kind = FaultKind::Function;
        fault.id = sanitizeId(QStringLiteral("func_fault_"), info.functionName);
        fault.name = QStringLiteral("故障_") + info.functionName;
        fault.relatedFunction = info.functionName;
        fault.inputAssertions = toAssertions(info.constraintList);
        fault.faultAssertions = negateAssertions(QStringList() << QStringLiteral("(assert %1)").arg(info.actuatorConstraint.variable));
        fault.actuatorAssertions = QStringList() << QStringLiteral("(assert %1)").arg(info.actuatorConstraint.variable);
        fault.constraintIntegrity = info.constraintIntegrity;
        fault.linkElements = info.linkElements;
        fault.relatedComponents = info.allComponentList;
        fault.offlineModeMap = info.actuatorConstraint.offlineModeMap;
        if (!fault.id.isEmpty()) {
            faults.append(fault);
        }
        qDebug().noquote() << "[DMatrix] collectFunctionFaults:" << info.functionName;
    }
    qDebug().noquote() << "[DMatrix] total function faults:" << faults.size();
    return faults;
}

QVector<FaultDefinition> DMatrixBuilder::collectComponentModeFaults(const SmtFacade &smt) const
{
    QVector<FaultDefinition> faults;

    for (const auto &component : smt.fragments().components) {
        if (component.failureModes.isEmpty())
            continue;
        for (const FailureMode &mode : component.failureModes) {
            if (mode.name.trimmed().isEmpty())
                continue;
            FaultDefinition fault;
            fault.kind = FaultKind::Component;
            fault.id = sanitizeId(QStringLiteral("mode_fault_"), component.name + QStringLiteral("_") + mode.name);
            fault.name = QStringLiteral("故障_%1/%2").arg(component.name, mode.name);
            fault.componentName = component.name;
            fault.failureModeName = mode.name;
            fault.relatedComponents = QStringList() << component.name;
            fault.inputAssertions = QStringList();
            fault.faultAssertions = QStringList() << QStringLiteral("(assert %1)").arg(mode.describe.trimmed());
            fault.overrides = toComponentOverrides(mode.overrides);
            faults.append(fault);
        }
    }
    qDebug().noquote() << "[DMatrix] total component-mode faults:" << faults.size();
    return faults;
}

QVector<TestDefinition> DMatrixBuilder::collectFunctionTests() const
{
    QVector<TestDefinition> tests;
    tests.reserve(functionInfoMap.size());

    for (auto it = functionInfoMap.cbegin(); it != functionInfoMap.cend(); ++it) {
        const FunctionInfo &info = it.value();
        if (info.constraintIntegrity == QStringLiteral("不完整") || info.constraintIntegrity == QStringLiteral("不正确")) {
            qDebug().noquote() << "[DMatrix] collectFunctionTests skip (invalid integrity)" << info.functionName;
            continue;
        }
        if (info.actuatorConstraint.variable.isEmpty()) {
            qDebug().noquote() << "[DMatrix] collectFunctionTests skip (no actuator)" << info.functionName;
            continue;
        }
        TestDefinition test;
        test.kind = TestKind::Function;
        test.id = sanitizeId(QStringLiteral("test_func_"), info.functionName);
        test.name = QStringLiteral("测试_%1").arg(info.functionName);
        test.relatedFunction = info.functionName;
        test.sourceItem = info.actuatorConstraint;
        test.predicate = QStringLiteral("(assert %1)").arg(info.actuatorConstraint.variable);
        test.negatedPredicate = QStringLiteral("(assert (not %1))").arg(info.actuatorConstraint.variable);
        test.signalVariable = info.actuatorConstraint.variable;
        tests.append(test);
        qDebug().noquote() << "[DMatrix] function test" << info.functionName << "->" << test.id;
    }
    qDebug().noquote() << "[DMatrix] total function tests:" << tests.size();
    return tests;
}

QVector<TestDefinition> DMatrixBuilder::collectModeTests(const SmtFacade &smt) const
{
    QVector<TestDefinition> tests;

    for (const auto &component : smt.fragments().components) {
        if (component.failureModes.isEmpty())
            continue;
        for (const FailureMode &mode : component.failureModes) {
            if (mode.name.trimmed().isEmpty())
                continue;
            TestDefinition test;
            test.kind = TestKind::Mode;
        test.id = sanitizeId(QStringLiteral("test_mode_"), component.name + QStringLiteral("_") + mode.name);
        test.name = QStringLiteral("测试_%1/%2").arg(component.name, mode.name);
        test.componentName = component.name;
        test.failureModeName = mode.name;
        test.overrides = toComponentOverrides(mode.overrides);
        test.predicate = QStringLiteral("(assert %1)").arg(mode.describe.trimmed());
        test.negatedPredicate = QStringLiteral("(assert (not %1))").arg(mode.describe.trimmed());
        tests.append(test);
    }
}
    qDebug().noquote() << "[DMatrix] total mode tests:" << tests.size();
    return tests;
}

QVector<TestDefinition> DMatrixBuilder::collectSignalTests(const SmtFacade &smt,
                                                          const DMatrixBuildOptions &options) const
{
    QVector<TestDefinition> tests;

    QSet<QString> visited;
    for (const auto &component : smt.fragments().components) {
        for (const auto &mode : component.failureModes) {
            const auto overrides = toComponentOverrides(mode.overrides);
            for (const auto &overrideItem : overrides) {
                for (const QString &assertion : overrideItem.assertions) {
                    const QString trimmed = assertion.trimmed();
                    static const QRegularExpression re(QStringLiteral("\\(assert\\s+(.+)\\)"));
                    const QRegularExpressionMatch match = re.match(trimmed);
                    if (!match.hasMatch())
                        continue;
                    const QString predicate = match.captured(1).trimmed();

                    static const QRegularExpression eqRe(QStringLiteral("^\\(=\\s+(.+?)\\s+([-+]?\\d+(?:\\.\\d+)?)\\)$"));
                    const QRegularExpressionMatch eqMatch = eqRe.match(predicate);
                    if (!eqMatch.hasMatch())
                        continue;
                    const QString variable = eqMatch.captured(1).trimmed();
                    const double value = eqMatch.captured(2).toDouble();
                    if (std::abs(value) > options.searchMaxAbs)
                        continue;

                    if (visited.contains(variable))
                        continue;
                    visited.insert(variable);

                    TestDefinition test;
                    test.kind = TestKind::Signal;
                    test.id = sanitizeId(QStringLiteral("test_signal_"), variable);
                    test.name = QStringLiteral("信号_%1").arg(variable);
                    test.signalVariable = variable;
                    test.predicate = QStringLiteral("(assert (= %1 %2))").arg(variable).arg(value);
                    test.negatedPredicate = QStringLiteral("(assert (not (= %1 %2)))").arg(variable).arg(value);
                    const QString sourceComponent = overrideItem.componentName.isEmpty() ? component.name : overrideItem.componentName;
                    test.note = QStringLiteral("来自器件覆盖: %1").arg(sourceComponent);
                    tests.append(test);
                }
            }
        }
    }
    qDebug().noquote() << "[DMatrix] total signal tests:" << tests.size();
    return tests;
}

DetectabilityResult DMatrixBuilder::detectability(const FaultDefinition &fault,
                                                  const TestDefinition &test,
                                                  DetectMode mode,
                                                  const SmtFacade &smt,
                                                  const DMatrixBuildOptions &options,
                                                  int timeoutMs) const
{
    DetectabilityResult result;
    QStringList faultExtra;
    QStringList normalExtra;
    QList<ComponentOverride> overrides = fault.overrides;

    if (test.kind == TestKind::Function) {
        normalExtra.append(test.predicate);
        faultExtra.append(test.negatedPredicate);
        faultExtra.append(fault.faultAssertions);
    } else if (test.kind == TestKind::Mode) {
        faultExtra.append(fault.faultAssertions);
        faultExtra.append(test.predicate);
        normalExtra.append(test.negatedPredicate);
    } else if (test.kind == TestKind::Signal) {
        if (fault.kind == FaultKind::Function) {
            faultExtra.append(fault.faultAssertions);
        } else {
            overrides.append(test.overrides);
        }
        faultExtra.append(test.predicate);
        normalExtra.append(test.negatedPredicate);
    }

    QString faultCode = smt.buildFaultCode(fault.inputAssertions + faultExtra, overrides);
    QString normalCode = smt.buildNormalCode(normalExtra);

    result.normalSat = isSatCached(smt, normalCode, timeoutMs);
    result.faultSat = isSatCached(smt, faultCode, timeoutMs);

    if (mode == DetectMode::Guaranteed) {
        result.normalPassSat = result.normalSat;
        result.faultFailSat = result.faultSat;
        result.guaranteed = result.normalSat && !result.faultSat;
        result.detected = result.guaranteed;
        result.method = QStringLiteral("guaranteed");
    } else {
        result.normalPassSat = result.normalSat;
        result.faultFailSat = result.faultSat;
        result.detected = result.normalSat && !result.faultSat;
        result.guaranteed = result.detected;
        result.method = QStringLiteral("exists");
    }

    if (!result.normalSat || !result.faultSat) {
        if (!result.normalSat && !result.faultSat) {
            result.detail = QStringLiteral("正常/故障模型均不可满足");
        } else if (!result.normalSat) {
            result.detail = QStringLiteral("正常模型不可满足");
        } else {
            result.detail = QStringLiteral("故障模型不可满足");
        }
    }
    return result;
}

DMatrixBuildResult DMatrixBuilder::buildDMatrix(const QVector<FaultDefinition> &faults,
                                                const QVector<TestDefinition> &tests,
                                                const SmtFacade &smt,
                                                const DMatrixBuildOptions &options) const
{
    DMatrixBuildResult result;
    result.faults = faults;
    result.tests = tests;
    result.cells.resize(faults.size());
    for (int i = 0; i < faults.size(); ++i) {
        result.cells[i].resize(tests.size());
    }

    const int timeoutMs = options.timeoutMs;
    auto worker = [&](int faultIndex, int testIndex) {
        const FaultDefinition &fault = faults.at(faultIndex);
        const TestDefinition &test = tests.at(testIndex);
        return detectability(fault, test, options.mode, smt, options, timeoutMs);
    };

    QList<QFuture<void>> futures;
    for (int i = 0; i < faults.size(); ++i) {
        for (int j = 0; j < tests.size(); ++j) {
            QFuture<void> future = QtConcurrent::run([&, i, j]() {
                result.cells[i][j] = worker(i, j);
            });
            futures.append(future);
        }
    }
    for (auto &f : futures) {
        f.waitForFinished();
    }

    clearSatCache();
    return result;
}

bool DMatrixBuilder::exportDMatrix(const DMatrixBuildResult &result,
                                   const QString &modelName,
                                   const DMatrixBuildOptions &options,
                                   const QString &outputDir,
                                   QString *csvPath,
                                   QString *metadataPath) const
{
    QDir dir(outputDir.isEmpty() ? QDir::current() : QDir(outputDir));
    if (!dir.exists(QStringLiteral("DMatrix"))) {
        dir.mkdir(QStringLiteral("DMatrix"));
    }
    dir.cd(QStringLiteral("DMatrix"));

    const QString dateTag = QDateTime::currentDateTime().toString(QStringLiteral("yyyyMMdd_hhmmss"));
    const QString baseName = modelName.isEmpty() ? QStringLiteral("dmatrix") : modelName;
    const QString csvFile = dir.filePath(QString("%1_%2.csv").arg(baseName, dateTag));
    const QString metadataFile = dir.filePath(QString("%1_%2.json").arg(baseName, dateTag));

    QFile file(csvFile);
    if (!file.open(QIODevice::WriteOnly | QIODevice::Text)) {
        qWarning() << "Failed to open CSV for writing:" << csvFile;
        return false;
    }

    QTextStream out(&file);
    out.setCodec("UTF-8");
    out << "Test/Fault";
    for (const FaultDefinition &fault : result.faults) {
        out << "," << fault.name;
    }
    out << "\n";
    for (int j = 0; j < result.tests.size(); ++j) {
        out << result.tests.at(j).name;
        for (int i = 0; i < result.faults.size(); ++i) {
            const DetectabilityResult &cell = result.cells.at(i).at(j);
            out << "," << (cell.detected ? "1" : "0");
        }
        out << "\n";
    }
    file.close();

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
        testsArray.append(obj);
    }
    metadata["tests"] = testsArray;

    QJsonArray rows;
    for (int i = 0; i < result.faults.size(); ++i) {
        QJsonArray row;
        for (int j = 0; j < result.tests.size(); ++j) {
            const DetectabilityResult &cell = result.cells.at(i).at(j);
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
    metadata["csvPath"] = csvFile;

    QFile metaFile(metadataFile);
    if (!metaFile.open(QIODevice::WriteOnly | QIODevice::Text)) {
        qWarning() << "Failed to open metadata file:" << metadataFile;
        return false;
    }
    metaFile.write(QJsonDocument(metadata).toJson(QJsonDocument::Indented));
    metaFile.close();

    if (csvPath)
        *csvPath = csvFile;
    if (metadataPath)
        *metadataPath = metadataFile;

    return true;
}

QStringList DMatrixBuilder::toAssertions(const QList<TestItem> &items) const
{
    QStringList assertions;
    assertions.reserve(items.size());
    for (const TestItem &item : items) {
        const QString variable = item.variable.trimmed();
        if (variable.isEmpty())
            continue;
        const QString value = item.value.trimmed();
        if (value.isEmpty())
            continue;

        if (value.startsWith(QStringLiteral("smt("), Qt::CaseInsensitive)) {
            const QString trimmed = value.mid(4, value.length() - 5);
            assertions.append(QStringLiteral("(assert %1)").arg(trimmed));
            continue;
        }

        QString normalizedBool;
        if (isBooleanToken(value, &normalizedBool)) {
            assertions.append(QStringLiteral("(assert (= %1 %2))").arg(variable, normalizedBool));
            continue;
        }

        RangeParseResult parsed = parseRangeText(value);
        if (parsed.valid && !parsed.isBoolean) {
            QVector<NumericInterval> intervals = mergeIntervals(parsed.intervals);
            for (const NumericInterval &interval : intervals) {
                assertions.append(createRangePredicate(variable, interval.lower, interval.upper));
            }
            continue;
        }

        if (parsed.valid && parsed.isBoolean) {
            QStringList boolVals = parsed.boolValues.values();
            if (boolVals.size() == 1) {
                assertions.append(QStringLiteral("(assert (= %1 %2))").arg(variable, boolVals.first()));
            } else {
                assertions.append(QStringLiteral("(assert (or (= %1 true) (= %1 false)))").arg(variable));
            }
            continue;
        }

        static const QRegularExpression re(QStringLiteral(R"(^\s*(>|>=|<|<=|=)\s*(-?\d+(?:\.\d+)?)\s*$)"));
        const QRegularExpressionMatch match = re.match(value);
        if (match.hasMatch()) {
            const QString op = match.captured(1);
            const QString val = match.captured(2);
            assertions.append(QStringLiteral("(assert (%1 %2 %3))").arg(op, variable, val));
            continue;
        }

        assertions.append(QStringLiteral("(assert (= %1 %2))").arg(variable, value));
    }
    return assertions;
}

QString DMatrixBuilder::createRangePredicate(const QString &expression, double lower, double upper) const
{
    if (lower == upper) {
        return QStringLiteral("(assert (= %1 %2))").arg(expression).arg(formatDouble(lower));
    }
    return QStringLiteral("(assert (and (>= %1 %2) (<= %1 %3)))")
        .arg(expression)
        .arg(formatDouble(lower))
        .arg(formatDouble(upper));
}

QString DMatrixBuilder::formatDouble(double value) const
{
    if (std::isnan(value)) return QStringLiteral("nan");
    if (std::isinf(value)) return value > 0 ? QStringLiteral("inf") : QStringLiteral("-inf");
    return QString::number(value, 'g', 10);
}

bool DMatrixBuilder::isSatCached(const SmtFacade &smt, const QString &code, int timeoutMs) const
{
    QMutexLocker locker(&satCacheMutex);
    const QString key = QString::number(qHash(code));
    auto it = satCache.find(key);
    if (it != satCache.end()) {
        return it.value();
    }
    locker.unlock();

    const bool sat = smt.isSat(code, timeoutMs);

    locker.relock();
    satCache.insert(key, sat);
    return sat;
}

void DMatrixBuilder::clearSatCache() const
{
    QMutexLocker locker(&satCacheMutex);
    satCache.clear();
}

} // namespace testability
