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
#include "mainwindow.h"
#include "testability/constraint_utils.h"

namespace testability {

// 匿名命名空间，内部使用的辅助结构和函数
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
    if (lowered == QString("true")) {
        if (normalized) {
            *normalized = QString("true");
        }
        return true;
    }
    if (lowered == QString("false")) {
        if (normalized) {
            *normalized = QString("false");
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
                if (intersection.lower < intersection.upper) {
                    result.append(intersection);
                } else if (intersection.lower == intersection.upper) {
                    // 针对点区间，保留为零长度，后续长度计算会得到0
                    result.append(intersection);
                }
            }
        }
    }
    return mergeIntervals(result);
}

double totalLength(const QVector<NumericInterval> &intervals)
{
    double sum = 0.0;
    for (const NumericInterval &interval : intervals) {
        sum += std::max(0.0, interval.upper - interval.lower);
    }
    return sum;
}

QString intervalsToString(const QVector<NumericInterval> &intervals)
{
    QStringList parts;
    for (const NumericInterval &interval : intervals) {
        parts.append(QString("[%1,%2]")
                     .arg(QString::number(interval.lower, 'g', 12),
                          QString::number(interval.upper, 'g', 12)));
    }
    return parts.join(QString(";"));
}

QStringList orderedBooleanValues(const QSet<QString> &boolValues)
{
    QStringList ordered;
    if (boolValues.contains(QString("true"))) {
        ordered.append(QString("true"));
    }
    if (boolValues.contains(QString("false"))) {
        ordered.append(QString("false"));
    }
    for (const QString &value : boolValues) {
        if (!ordered.contains(value)) {
            ordered.append(value);
        }
    }
    return ordered;
}

QString boolValuesToString(const QSet<QString> &boolValues)
{
    const QStringList ordered = orderedBooleanValues(boolValues);
    return ordered.join(QString(";"));
}

QString createBooleanPredicate(const QString &expression,
                               const QSet<QString> &boolValues)
{
    const QStringList ordered = orderedBooleanValues(boolValues);
    if (ordered.isEmpty()) {
        return QString();
    }
    if (ordered.size() == 1) {
        return QString("(= %1 %2)").arg(expression, ordered.first());
    }
    QStringList terms;
    for (const QString &value : ordered) {
        terms.append(QString("(= %1 %2)").arg(expression, value));
    }
    return QString("(or %1)").arg(terms.join(QString(" ")));
}

void insertIfFinite(QJsonObject &obj, const QString &key, double value)
{
    if (std::isfinite(value)) {
        obj.insert(key, value);
    }
}

QSet<QString> parseDependencyList(const QString &dependencyText)
{
    QSet<QString> dependencies;
    const QStringList rows = splitTrimmed(dependencyText, QLatin1Char(';'));
    for (const QString &row : rows) {
        const QStringList parts = row.split(',', QString::KeepEmptyParts);
        if (parts.size() < 2) {
            continue;
        }
        const QString functionName = parts.at(1).trimmed();
        if (!functionName.isEmpty()) {
            dependencies.insert(functionName);
        }
    }
    return dependencies;
}

QSet<QString> resolveDependencyClosure(const QMap<QString, FunctionInfo> &map,
                                       const QString &functionName,
                                       QSet<QString> *visiting = nullptr)
{
    if (!visiting) {
        QSet<QString> stack;
        return resolveDependencyClosure(map, functionName, &stack);
    }
    if (visiting->contains(functionName)) {
        return {};
    }
    visiting->insert(functionName);

    QSet<QString> closure;
    const auto it = map.constFind(functionName);
    if (it == map.constEnd()) {
        visiting->remove(functionName);
        return closure;
    }

    const QSet<QString> direct = parseDependencyList(it.value().functionDependency);
    for (const QString &dep : direct) {
        if (dep.trimmed().isEmpty() || dep == functionName) {
            continue;
        }
        closure.insert(dep);
        closure.unite(resolveDependencyClosure(map, dep, visiting));
    }

    visiting->remove(functionName);
    return closure;
}

QHash<QString, QSet<QString>> buildOfflineModeMap(const QVector<FunctionOfflineResult> &entries)
{
    QHash<QString, QSet<QString>> map;
    for (const FunctionOfflineResult &entry : entries) {
        const QStringList components = entry.componentNames;
        const QStringList modes = entry.failureModes;
        if (components.isEmpty()) {
            continue;
        }
        if (modes.isEmpty()) {
            for (const QString &component : components) {
                const QString trimmed = component.trimmed();
                if (!trimmed.isEmpty()) {
                    map[trimmed];
                }
            }
            continue;
        }
        if (components.size() == modes.size()) {
            for (int i = 0; i < components.size(); ++i) {
                const QString component = components.at(i).trimmed();
                const QString mode = modes.at(i).trimmed();
                if (!component.isEmpty() && !mode.isEmpty()) {
                    map[component].insert(mode);
                }
            }
            continue;
        }
        if (modes.size() == 1) {
            const QString mode = modes.first().trimmed();
            if (mode.isEmpty()) {
                continue;
            }
            for (const QString &component : components) {
                const QString trimmed = component.trimmed();
                if (!trimmed.isEmpty()) {
                    map[trimmed].insert(mode);
                }
            }
            continue;
        }
        for (const QString &component : components) {
            const QString trimmedComponent = component.trimmed();
            if (trimmedComponent.isEmpty()) {
                continue;
            }
            for (const QString &mode : modes) {
                const QString trimmedMode = mode.trimmed();
                if (!trimmedMode.isEmpty()) {
                    map[trimmedComponent].insert(trimmedMode);
                }
            }
        }
    }
    return map;
}

bool componentMatchesScope(const QStringList &elements, const QString &componentName)
{
    if (componentName.trimmed().isEmpty()) {
        return false;
    }
    for (const QString &item : elements) {
        const QString trimmed = item.trimmed();
        if (trimmed.isEmpty()) {
            continue;
        }
        if (!QString::compare(trimmed, componentName, Qt::CaseInsensitive)) {
            return true;
        }
        const int dotIndex = trimmed.indexOf('.');
        if (dotIndex > 0) {
            const QString prefix = trimmed.left(dotIndex);
            if (!QString::compare(prefix, componentName, Qt::CaseInsensitive)) {
                return true;
            }
        }
    }
    return false;
}

QString testKindToString(TestKind kind)
{
    switch (kind) {
    case TestKind::Signal:
        return QString("signal");
    case TestKind::Function:
        return QString("function");
    case TestKind::Mode:
        return QString("mode");
    }
    return QString("unknown");
}

QString faultKindToString(FaultKind kind)
{
    switch (kind) {
    case FaultKind::Function:
        return QString("function");
    case FaultKind::Component:
        return QString("component");
    }
    return QString("unknown");
}

QString detectModeToString(DetectMode mode)
{
    switch (mode) {
    case DetectMode::Guaranteed:
        return QString("guaranteed");
    case DetectMode::Exists:
        return QString("exists");
    }
    return QString("unknown");
}

} // namespace

/**
 * @brief D矩阵构建器构造函数
 * @param entity 系统实体指针
 */
DMatrixBuilder::DMatrixBuilder(SystemEntity *entity)
    : systemEntity(entity)
{
}

/**
 * @brief 设置函数信息映射
 * @param map 函数信息映射表
 */
void DMatrixBuilder::setFunctionInfoMap(const QMap<QString, FunctionInfo> &map)
{
    functionInfoMap = map;
}

/**
 * @brief 收集函数故障定义
 * 根据函数信息生成对应的故障定义
 * @return 故障定义向量
 */
QVector<FaultDefinition> DMatrixBuilder::collectFunctionFaults() const
{
    QVector<FaultDefinition> faults;
    if (!systemEntity) {
        return faults;
    }

    for (auto it = functionInfoMap.constBegin(); it != functionInfoMap.constEnd(); ++it) {
        const FunctionInfo &info = it.value();
        if (info.constraintIntegrity.trimmed() == QString("不正确")) {
            qDebug().noquote() << "[DMatrix] skip function fault due to invalid integrity:" << info.functionName;
            continue;
        }
        qDebug().noquote() << "[DMatrix] collectFunctionFaults:" << info.functionName;
        qDebug().noquote() << "  actuator variable=" << info.actuatorConstraint.variable
                           << " value=" << info.actuatorConstraint.value
                           << " type=" << info.actuatorConstraint.testType;
        FaultDefinition fault;
        fault.id = sanitizeId(QString("func."), info.functionName);
        // 故障名增加前缀，保留原功能名中的下划线等字符
        fault.name = QString("故障_%1").arg(info.functionName);
        fault.kind = FaultKind::Function;
        fault.relatedFunction = info.functionName;
        fault.constraintIntegrity = info.constraintIntegrity.trimmed();
        fault.linkElements = info.linkElements;
        fault.relatedComponents = info.allComponentList;
        fault.offlineModeMap = buildOfflineModeMap(info.offlineResults);
        fault.dependencyClosure = resolveDependencyClosure(functionInfoMap, info.functionName);
        qDebug().noquote() << "  allComponents =" << fault.relatedComponents;

        QList<TestItem> inputItems;
        TestItem actuatorItem = info.actuatorConstraint;

        // 分离输入项和执行器项
        for (const auto &item : info.constraintList) {
            if (!actuatorItem.variable.isEmpty()
                && item.variable == actuatorItem.variable
                && item.value == actuatorItem.value) {
                continue;
            }
            inputItems.append(item);
        }

        fault.inputAssertions = toAssertions(inputItems);
        if (fault.inputAssertions.isEmpty()) {
            qDebug().noquote() << "  WARN inputAssertions empty for" << info.functionName;
        }

        // 如果有执行器项，则生成故障断言
        if (!actuatorItem.variable.isEmpty()) {
            fault.actuatorAssertions = toAssertions({actuatorItem});
            TestItem negated = actuatorItem;
            negated.value = negateRange(actuatorItem.value);
            QStringList faultAssertList = toAssertions({negated});
            fault.faultAssertions = faultAssertList;
            if (faultAssertList.isEmpty()) {
                qDebug().noquote() << "  WARN faultAssertions empty after negate for" << info.functionName;
            } else {
                qDebug().noquote() << "  faultAssertions size=" << faultAssertList.size()
                                   << " first=" << faultAssertList.value(0);
                if (!info.actuatorName.isEmpty()) {
                    // 通过组件 override 在故障模型中替换掉执行器所属组件的正常约束，
                    // 仅保留失效断言，便于“存在”模式搜索可行的故障状态。
                    ComponentOverride override;
                    override.componentName = info.actuatorName;
                    override.assertions = faultAssertList;
                    override.replaceNormal = true;
                    fault.overrides.append(override);
                }
            }
        } else {
            qDebug().noquote() << "  WARN actuatorItem missing for" << info.functionName;
        }

        faults.append(fault);
    }

    return faults;
}

QVector<FaultDefinition> DMatrixBuilder::collectComponentModeFaults(const SmtFacade &smt) const
{
    QVector<FaultDefinition> faults;
    const auto &components = smt.fragments().components;
    for (const auto &component : components) {
        const QString componentName = component.name.trimmed();
        if (componentName.isEmpty()) {
            continue;
        }
        qDebug().noquote() << "[DMatrix] collectComponentModeFaults component" << componentName
                           << "modeCandidates=" << component.failureModes.size();
        for (const FailureMode &mode : component.failureModes) {
            const QString modeName = mode.name.trimmed();
            const QString describe = mode.describe.trimmed();
            if (modeName.isEmpty() || describe.isEmpty()) {
                qDebug().noquote() << "  skip mode entry for faults nameEmpty=" << modeName.isEmpty()
                                   << "describeEmpty=" << describe.isEmpty();
                continue;
            }

            FaultDefinition fault;
            fault.id = sanitizeId(QString("comp."), componentName + QString(".") + modeName);
            // 器件故障模式故障名增加前缀，区分测试/故障
            fault.name = QString("故障_%1/%2").arg(componentName, modeName);
            fault.kind = FaultKind::Component;
            fault.componentName = componentName;
            fault.failureModeName = modeName;
            fault.relatedComponents = QStringList{componentName};
            fault.enabled = true;

            faults.append(fault);
            qDebug().noquote() << "  added component-mode fault" << fault.id
                               << "component=" << fault.componentName
                               << "mode=" << fault.failureModeName;
        }
    }
    qDebug().noquote() << "[DMatrix] total component-mode faults:" << faults.size();
    return faults;
}

/**
 * @brief 收集函数测试定义
 * 根据函数信息生成对应的测试定义
 * @return 测试定义向量
 */
QVector<TestDefinition> DMatrixBuilder::collectFunctionTests() const
{
    QVector<TestDefinition> tests;
    if (!systemEntity) {
        return tests;
    }

    for (auto it = functionInfoMap.constBegin(); it != functionInfoMap.constEnd(); ++it) {
        const FunctionInfo &info = it.value();
        if (info.constraintIntegrity.trimmed() == QString("不正确")) {
            qDebug().noquote() << "[DMatrix] collectFunctionTests skip (invalid integrity)" << info.functionName;
            continue;
        }
        // 如果没有执行器约束则跳过
        if (info.actuatorConstraint.variable.isEmpty()) {
            qDebug().noquote() << "[DMatrix] collectFunctionTests skip (no actuator)"
                               << info.functionName;
            continue;
        }

        TestDefinition test;
        test.id = sanitizeId(QString("func."), info.functionName);
        // 功能测试名增加前缀，避免与功能名混淆
        test.name = QString("测试_%1").arg(info.functionName);
        test.kind = TestKind::Function;
        test.sourceItem = info.actuatorConstraint;
        test.relatedFunction = info.functionName;

        // 生成正向断言
        QStringList positive = toAssertions({info.actuatorConstraint});
        if (!positive.isEmpty()) {
            test.predicate = positive.first();
        }
        qDebug().noquote() << "[DMatrix] function test" << info.functionName
                           << " predicate=" << test.predicate;

        // 生成反向断言
        TestItem negated = info.actuatorConstraint;
        negated.value = negateRange(info.actuatorConstraint.value);
        QStringList negative = toAssertions({negated});
        if (!negative.isEmpty()) {
            test.negatedPredicate = negative.first();
        }
        qDebug().noquote() << "  negatedPredicate=" << test.negatedPredicate;

        test.note = QString("function");
        tests.append(test);
    }

    return tests;
}

QVector<TestDefinition> DMatrixBuilder::collectModeTests(const SmtFacade &smt) const
{
    QVector<TestDefinition> tests;
    const auto &components = smt.fragments().components;
    for (const auto &component : components) {
        qDebug().noquote() << "[DMatrix] collectModeTests component" << component.name
                           << "modeCandidates=" << component.failureModes.size();
        for (const FailureMode &mode : component.failureModes) {
            const QString modeName = mode.name.trimmed();
            const QString describe = mode.describe.trimmed();
            if (modeName.isEmpty() || describe.isEmpty()) {
                qDebug().noquote() << "  skip mode entry nameEmpty=" << modeName.isEmpty()
                                   << "describeEmpty=" << describe.isEmpty();
                continue;
            }

            TestDefinition test;
            test.id = sanitizeId(QString("mode."), component.name + QString(".") + modeName);
            // 故障模式测试名增加前缀，与器件故障模式故障名对称
            test.name = QString("测试_%1/%2").arg(component.name, modeName);
            test.kind = TestKind::Mode;
            test.componentName = component.name;
            test.failureModeName = modeName;

            ComponentOverride override;
            override.componentName = component.name;
            override.assertions = QStringList{describe};
            override.replaceNormal = true;
            test.overrides.append(override);

            test.sourceItem.variable = component.name;
            test.sourceItem.value = modeName;
            test.sourceItem.testType = QString("故障模式");
            test.note = QString("mode:%1").arg(modeName);

            tests.append(test);
            qDebug().noquote() << "  added mode test" << test.id
                               << "component=" << test.componentName
                               << "mode=" << test.failureModeName;
        }
    }
    qDebug().noquote() << "[DMatrix] total mode tests:" << tests.size();
    return tests;
}

/**
 * @brief 收集信号测试定义
 * 根据功能变量配置生成信号测试定义
 * @param smt SMT求解器接口（当前实现未使用）
 * @param options 构建选项
 * @return 测试定义向量
 */
QVector<TestDefinition> DMatrixBuilder::collectSignalTests(const SmtFacade &smt,
                                                          const DMatrixBuildOptions &options) const
{
    Q_UNUSED(smt);
    QVector<TestDefinition> tests;
    if (!systemEntity) {
        return tests;
    }

    struct AggregatedSignal
    {
        QString variable;
        QVector<NumericInterval> intervals;
        QString typeKey;
        QSet<QString> functions;
        bool isBoolean = false;
        QSet<QString> boolValues;
    };

    QHash<QString, AggregatedSignal> aggregated;

    for (auto it = functionInfoMap.constBegin(); it != functionInfoMap.constEnd(); ++it) {
        const FunctionInfo &info = it.value();
        if (info.constraintIntegrity.trimmed() == QString("不正确")) {
            continue;
        }
        if (info.variableConfig.isEmpty()) {
            continue;
        }

        QSet<QString> constraintVariables;
        for (const TestItem &item : info.constraintList) {
            const QString variable = item.variable.trimmed();
            if (variable.isEmpty()) {
                continue;
            }
            if (!info.actuatorConstraint.variable.isEmpty()
                && variable == info.actuatorConstraint.variable.trimmed()) {
                continue;
            }
            constraintVariables.insert(variable);
        }

        const QStringList variables = info.variableConfig.variableNames();
        for (const QString &variable : variables) {
            const QString trimmedVariable = variable.trimmed();
            if (trimmedVariable.isEmpty()) {
                continue;
            }
            if (!options.includeFunctionInputs && constraintVariables.contains(trimmedVariable)) {
                continue;
            }

            const functionvalues::VariableEntry entry = info.variableConfig.entry(trimmedVariable);
            const QString rangeText = entry.valueRange.trimmed();
            if (rangeText.isEmpty()) {
                continue;
            }

            RangeParseResult parsedRange = parseRangeText(rangeText);
            if (!parsedRange.valid) {
                continue;
            }

            AggregatedSignal &agg = aggregated[trimmedVariable];
            if (agg.variable.isEmpty()) {
                agg.variable = trimmedVariable;
            }
            agg.functions.insert(info.functionName);

            if (parsedRange.isBoolean) {
                if (!agg.isBoolean && !agg.intervals.isEmpty()) {
                    continue;
                }
                agg.isBoolean = true;
                agg.boolValues.unite(parsedRange.boolValues);
                if (agg.typeKey.isEmpty()) {
                    if (!entry.type.trimmed().isEmpty()) {
                        agg.typeKey = entry.type.trimmed();
                    } else {
                        agg.typeKey = QString("Bool");
                    }
                }
                continue;
            }

            QVector<NumericInterval> intervals = mergeIntervals(parsedRange.intervals);
            if (intervals.isEmpty()) {
                continue;
            }

            if (agg.isBoolean) {
                continue;
            }

            if (agg.intervals.isEmpty()) {
                agg.intervals = intervals;
            } else {
                QVector<NumericInterval> combined = agg.intervals;
                combined += intervals;
                agg.intervals = mergeIntervals(combined);
            }
            if (agg.typeKey.isEmpty()) {
                if (!entry.type.trimmed().isEmpty()) {
                    agg.typeKey = entry.type.trimmed();
                } else {
                    const QString declType = systemEntity->obsVarsMap.value(trimmedVariable);
                    agg.typeKey = rangeconfig::VariableRangeConfig::inferTypeKey(trimmedVariable, declType);
                }
            }
        }
    }

    for (auto it = aggregated.constBegin(); it != aggregated.constEnd(); ++it) {
        const AggregatedSignal &agg = it.value();
        if (agg.isBoolean) {
            if (agg.boolValues.isEmpty()) {
                continue;
            }
            const QString valueText = boolValuesToString(agg.boolValues);

            TestDefinition test;
            test.id = sanitizeId(QString("sig."), agg.variable);
            test.name = agg.variable;
            test.kind = TestKind::Signal;
            test.signalVariable = agg.variable;
            test.sourceItem.variable = agg.variable;
            test.sourceItem.value = valueText;
            test.sourceItem.confidence = 1.0;
            test.sourceItem.testType = QString("信号");
            test.note = test.sourceItem.value;
            test.predicate = createBooleanPredicate(agg.variable, agg.boolValues);

            tests.append(test);
            continue;
        }

        if (agg.intervals.isEmpty()) {
            continue;
        }

        const QVector<NumericInterval> mergedIntervals = mergeIntervals(agg.intervals);

        TestDefinition test;
        test.id = sanitizeId(QString("sig."), agg.variable);
        test.name = agg.variable;
        test.kind = TestKind::Signal;
        test.signalVariable = agg.variable;
        test.sourceItem.variable = agg.variable;
        test.sourceItem.value = intervalsToString(mergedIntervals);
        test.sourceItem.confidence = 1.0;
        test.sourceItem.testType = QString("信号");
        test.note = test.sourceItem.value;

        QStringList predicates;
        for (const NumericInterval &interval : mergedIntervals) {
            predicates.append(createRangePredicate(agg.variable,
                                                   interval.lower,
                                                   interval.upper));
        }
        if (!predicates.isEmpty()) {
            if (predicates.size() == 1) {
                test.predicate = predicates.first();
            } else {
                test.predicate = QString("(or %1)").arg(predicates.join(QString(" ")));
            }
        }

        tests.append(test);
    }

    return tests;
}

/**
 * @brief 计算故障可检测性
 * 判断在给定测试下故障是否可检测
 * @param fault 故障定义
 * @param test 测试定义
 * @param mode 检测模式
 * @param smt SMT求解器接口
 * @param timeoutMs 超时时间(毫秒)
 * @return 可检测性结果
 */
DetectabilityResult DMatrixBuilder::detectability(const FaultDefinition &fault,
                                                  const TestDefinition &test,
                                                  DetectMode mode,
                                                  const SmtFacade &smt,
                                                  const DMatrixBuildOptions &options,
                                                  int timeoutMs) const
{
    DetectabilityResult result;

    auto finalize = [&](bool detected) {
        result.detected = detected;
        if (mode == DetectMode::Guaranteed) {
            result.guaranteed = detected;
        } else {
            result.guaranteed = false;
        }
        return result;
    };

    // 器件故障模式相关判定优先处理
    if (fault.kind == FaultKind::Component) {
        // 1) 故障模式测试 vs 器件故障模式：直接一一对应
        if (test.kind == TestKind::Mode) {
            result.method = QString("模式测试");
            const QString faultComp = fault.componentName.trimmed();
            const QString faultMode = fault.failureModeName.trimmed();
            const QString testComp = test.componentName.trimmed();
            const QString testMode = test.failureModeName.trimmed();
            if (faultComp.isEmpty() || faultMode.isEmpty()
                || testComp.isEmpty() || testMode.isEmpty()) {
                result.detail = QString("组件或故障模式信息不完整");
                return finalize(false);
            }
            const bool matched = (QString::compare(faultComp, testComp, Qt::CaseInsensitive) == 0)
                                 && (faultMode == testMode);
            result.detail = matched ? QString("测试直接对应器件故障模式")
                                    : QString("测试与该器件故障模式不匹配");
            return finalize(matched);
        }

        // 2) 功能测试 vs 器件故障模式：复用原“故障模式测试×功能故障”的判定语义
        if (test.kind == TestKind::Function) {
            result.method = QString("功能测试");
            if (test.relatedFunction.trimmed().isEmpty()) {
                result.detail = QString("测试未绑定功能");
                return finalize(false);
            }

            const auto infoIt = functionInfoMap.constFind(test.relatedFunction);
            if (infoIt == functionInfoMap.constEnd()) {
                result.detail = QString("未找到功能定义");
                return finalize(false);
            }
            const FunctionInfo &info = infoIt.value();

            const QStringList scope = info.allComponentList.isEmpty() ? info.linkElements
                                                                      : info.allComponentList;
            qDebug().noquote() << "[DMatrix][FuncDetect-CompFault] function=" << info.functionName
                               << "componentScope=" << scope
                               << "targetComponent=" << fault.componentName
                               << "mode=" << fault.failureModeName;
            if (!componentMatchesScope(scope, fault.componentName)) {
                if (info.allComponentList.isEmpty()) {
                    result.detail = QString("组件不在功能链路内");
                    qDebug().noquote() << "  skip because component not in link";
                } else {
                    result.detail = QString("组件不在全部相关器件内");
                    qDebug().noquote() << "  skip because component not in all components";
                }
                return finalize(false);
            }

            // 若功能约束完整，优先使用离线求解结果
            if (info.constraintIntegrity.trimmed() == QString("完整")) {
                const QHash<QString, QSet<QString>> offlineMap = buildOfflineModeMap(info.offlineResults);
                const QSet<QString> modes = offlineMap.value(fault.componentName);
                const bool detected = modes.contains(fault.failureModeName);
                QStringList modeList = modes.values();
                modeList.sort();
                qDebug().noquote() << "  offline modes for component" << fault.componentName
                                   << ":" << modeList
                                   << "detected=" << detected;
                result.detail = detected ? QString("离线求解包含故障模式")
                                         : QString("离线求解未覆盖该故障模式");
                return finalize(detected);
            }

            // 否则在功能约束 + 器件故障模式注入下，通过SMT判定
            QList<TestItem> inputItems;
            TestItem actuatorItem = info.actuatorConstraint;
            for (const auto &item : info.constraintList) {
                if (!actuatorItem.variable.isEmpty()
                    && item.variable == actuatorItem.variable
                    && item.value == actuatorItem.value) {
                    continue;
                }
                inputItems.append(item);
            }

            QStringList inputAssertions = toAssertions(inputItems);
            QStringList actuatorAssertions;
            if (!actuatorItem.variable.isEmpty()) {
                actuatorAssertions = toAssertions({actuatorItem});
            }

            QStringList positive = inputAssertions;
            positive.append(actuatorAssertions);
            if (positive.isEmpty()) {
                result.detail = QString("缺少执行器正向约束，无法验证");
                qDebug().noquote() << "  skip because positive assertions empty (component fault)";
                return finalize(false);
            }

            // 查找器件故障模式的约束描述
            QString modeDescribe;
            const auto &components = smt.fragments().components;
            for (const auto &compBlock : components) {
                if (QString::compare(compBlock.name.trimmed(),
                                     fault.componentName.trimmed(),
                                     Qt::CaseInsensitive) != 0) {
                    continue;
                }
                for (const FailureMode &modeEntry : compBlock.failureModes) {
                    const QString modeName = modeEntry.name.trimmed();
                    if (modeName == fault.failureModeName.trimmed()) {
                        modeDescribe = modeEntry.describe.trimmed();
                        break;
                    }
                }
                if (!modeDescribe.isEmpty()) {
                    break;
                }
            }

            if (modeDescribe.trimmed().isEmpty()) {
                result.detail = QString("未找到器件故障模式描述，无法验证");
                return finalize(false);
            }

            ComponentOverride override;
            override.componentName = fault.componentName;
            override.assertions = QStringList{modeDescribe};
            override.replaceNormal = true;
            QList<ComponentOverride> overrides;
            overrides.append(override);

            const QString code = smt.buildFaultCode(QStringList(), overrides, positive);
            const bool sat = isSatCached(smt, code, timeoutMs);
            result.faultSat = sat;
            qDebug().noquote() << "[DMatrix][FuncDetect-CompFault] SAT query result sat=" << sat;
            result.detail = sat ? QString("模式成立时仍可满足功能输出")
                                 : QString("模式导致功能输出矛盾");
            return finalize(!sat);
        }

        if (test.kind == TestKind::Signal) {
            result.method = QString("信号测试");
            result.detail = QString("暂不支持对器件故障模式的信号测试判定");
            return finalize(false);
        }
    }

    if (test.kind == TestKind::Mode) {
        result.method = QString("模式测试");
        qDebug().noquote() << "[DMatrix][ModeDetect] fault" << fault.id
                           << "function=" << fault.relatedFunction
                           << "integrity=" << fault.constraintIntegrity
                           << "test=" << test.id
                           << "component=" << test.componentName
                           << "mode=" << test.failureModeName;
        const QStringList scope = fault.relatedComponents.isEmpty() ? fault.linkElements
                                                                    : fault.relatedComponents;
        qDebug().noquote() << "  component scope =" << scope;
        if (!componentMatchesScope(scope, test.componentName)) {
            if (fault.relatedComponents.isEmpty()) {
                result.detail = QString("组件不在功能链路内");
                qDebug().noquote() << "  skip because component not in link";
            } else {
                result.detail = QString("组件不在全部相关器件内");
                qDebug().noquote() << "  skip because component not in all components";
            }
            return finalize(false);
        }

        if (fault.constraintIntegrity.trimmed() == QString("完整")) {
            const QSet<QString> modes = fault.offlineModeMap.value(test.componentName);
            const bool detected = modes.contains(test.failureModeName);
            QStringList modeList = modes.values();
            modeList.sort();
            qDebug().noquote() << "  offline modes for component" << test.componentName
                               << ":" << modeList
                               << "detected=" << detected;
            result.detail = detected ? QString("离线求解包含故障模式")
                                     : QString("离线求解未覆盖该故障模式");
            return finalize(detected);
        }

        QStringList positive = fault.inputAssertions;
        positive.append(fault.actuatorAssertions);
        if (positive.isEmpty()) {
            result.detail = QString("缺少执行器正向约束，无法验证");
            qDebug().noquote() << "  skip because positive assertions empty";
            return finalize(false);
        }

        const QString code = smt.buildFaultCode(QStringList(), test.overrides, positive);
        const bool sat = isSatCached(smt, code, timeoutMs);
        result.faultSat = sat;
        qDebug().noquote() << "  SAT query result sat=" << sat;
        result.detail = sat ? QString("模式成立时仍可满足功能输出")
                             : QString("模式导致功能输出矛盾");
        return finalize(!sat);
    }

    if (test.kind == TestKind::Function) {
        result.method = QString("功能测试");
        if (test.relatedFunction.trimmed().isEmpty()) {
            result.detail = QString("测试未绑定功能");
            return finalize(false);
        }
        QSet<QString> coverage = resolveDependencyClosure(functionInfoMap, test.relatedFunction);
        coverage.insert(test.relatedFunction);
        const bool detected = coverage.contains(fault.relatedFunction);
        result.detail = detected ? QString("功能依赖覆盖目标故障")
                                 : QString("功能依赖未覆盖目标故障");
        return finalize(detected);
    }

    if (test.kind == TestKind::Signal) {
        result.method = QString("信号测试");
        const auto infoIt = functionInfoMap.constFind(fault.relatedFunction);
        if (infoIt == functionInfoMap.constEnd()) {
            result.detail = QString("未找到功能定义");
            return finalize(false);
        }
        const FunctionInfo &info = infoIt.value();
        if (!info.variableConfig.contains(test.signalVariable)) {
            qDebug().noquote() << "[DMatrix] signal variable missing from config"
                               << test.signalVariable
                               << "function=" << fault.relatedFunction
                               << "config keys=" << info.variableConfig.variableNames();
            result.detail = QString("变量未在功能中配置");
            return finalize(false);
        }
        const functionvalues::VariableEntry entry = info.variableConfig.entry(test.signalVariable);
        const QString rangeText = entry.valueRange.trimmed();
        if (rangeText.isEmpty()) {
            result.detail = QString("功能未配置取值区间");
            return finalize(false);
        }
        RangeParseResult parsedRange = parseRangeText(rangeText);
        if (!parsedRange.valid) {
            result.detail = QString("功能取值区间无效");
            return finalize(false);
        }

        if (parsedRange.isBoolean) {
            const QSet<QString> feasibleBools = parsedRange.boolValues;
            if (feasibleBools.isEmpty()) {
                result.detail = QString("功能取值区间无效");
                return finalize(false);
            }

            double diffRatio = feasibleBools.size() == 1 ? 0.5 : 0.0;
            result.metric = diffRatio;

            const double tolerance = options.rangeTolerance;
            const double upperBound = 1.0 - tolerance;
            const bool detected = diffRatio > tolerance && diffRatio <= upperBound;
            result.detail = QString("布尔取值差异比例=%1").arg(diffRatio, 0, 'f', 3);
            return finalize(detected);
        }

        QVector<NumericInterval> feasible = mergeIntervals(parsedRange.intervals);
        if (feasible.isEmpty()) {
            result.detail = QString("功能取值区间无效");
            return finalize(false);
        }

        QString typeKey = entry.type.trimmed();
        if (typeKey.isEmpty()) {
            const QString declType = systemEntity->obsVarsMap.value(test.signalVariable);
            typeKey = rangeconfig::VariableRangeConfig::inferTypeKey(test.signalVariable, declType);
        }
        const rangeconfig::RangeValue rangeValue = systemEntity->variableRangeConfigRef().effectiveRange(typeKey, test.signalVariable);
        NumericInterval globalInterval;
        globalInterval.lower = rangeValue.lower;
        globalInterval.upper = rangeValue.upper;
        if (!globalInterval.isValid()) {
            result.detail = QString("全局取值范围无效");
            return finalize(false);
        }
        QVector<NumericInterval> globalIntervals{globalInterval};
        const double globalLength = totalLength(globalIntervals);
        if (globalLength <= 0.0) {
            result.detail = QString("全局取值范围长度为0");
            return finalize(false);
        }

        const QVector<NumericInterval> overlap = intersectIntervals(globalIntervals, feasible);
        const double overlapLength = totalLength(overlap);
        double diffRatio = (globalLength - overlapLength) / globalLength;
        if (diffRatio < 0.0) {
            diffRatio = 0.0;
        }
        if (diffRatio > 1.0) {
            diffRatio = 1.0;
        }
        result.metric = diffRatio;

        const double tolerance = options.rangeTolerance;
        const double upperBound = 1.0 - tolerance;
        const bool detected = diffRatio > tolerance && diffRatio <= upperBound;
        result.detail = QString("区间差异比例=%1").arg(diffRatio, 0, 'f', 3);
        return finalize(detected);
    }

    result.detail = QString("未知测试类型");
    return finalize(false);
}

/**
 * @brief 构建D矩阵
 * 计算所有故障和测试之间的可检测性关系，构建D矩阵
 * @param faults 故障定义向量
 * @param tests 测试定义向量
 * @param smt SMT求解器接口
 * @param options 构建选项
 * @return D矩阵构建结果
 */
DMatrixBuildResult DMatrixBuilder::buildDMatrix(const QVector<FaultDefinition> &faults,
                                                const QVector<TestDefinition> &tests,
                                                const SmtFacade &smt,
                                                const DMatrixBuildOptions &options) const
{
    DMatrixBuildResult result;
    result.faults = faults;
    result.tests = tests;
    result.cells.resize(faults.size());
    for (auto &row : result.cells) {
        row.resize(tests.size());
    }

    clearSatCache();

    // 定义任务结构体
    struct Task {
        int faultIndex;
        int testIndex;
    };

    // 创建任务列表
    QVector<Task> tasks;
    tasks.reserve(faults.size() * tests.size());
    for (int fi = 0; fi < faults.size(); ++fi) {
        for (int ti = 0; ti < tests.size(); ++ti) {
            tasks.append({fi, ti});
        }
    }

    // 并行计算所有任务
    QtConcurrent::blockingMap(tasks, [&](const Task &task) {
        DetectabilityResult cell = detectability(faults.at(task.faultIndex),
                                                 tests.at(task.testIndex),
                                                 options.mode,
                                                 smt,
                                                 options,
                                                 options.timeoutMs);
        result.cells[task.faultIndex][task.testIndex] = cell;
    });

    return result;
}

/**
 * @brief 导出D矩阵
 * 将D矩阵结果导出为CSV文件和JSON元数据文件
 * @param result D矩阵构建结果
 * @param modelName 模型名称
 * @param options 构建选项
 * @param outputDir 输出目录
 * @param csvPath CSV文件路径输出参数
 * @param metadataPath 元数据文件路径输出参数
 * @return 导出成功返回true，否则返回false
 */
bool DMatrixBuilder::exportDMatrix(const DMatrixBuildResult &result,
                                   const QString &modelName,
                                   const DMatrixBuildOptions &options,
                                   const QString &outputDir,
                                   QString *csvPath,
                                   QString *metadataPath) const
{
    QDir dir(outputDir);
    if (outputDir.isEmpty()) {
        dir = QDir(QDir::currentPath());
        if (!dir.exists(QString("docs"))) {
            dir.mkdir(QString("docs"));
        }
        dir.cd(QString("docs"));
        if (!dir.exists(QString("DMatrix"))) {
            dir.mkdir(QString("DMatrix"));
        }
        dir.cd(QString("DMatrix"));
    } else if (!dir.exists()) {
        if (!dir.mkpath(QString("."))) {
            return false;
        }
    }

    QString sanitizedModel = modelName;
    sanitizedModel.replace(QRegularExpression("[^A-Za-z0-9_\\-]+"), "_");
    if (sanitizedModel.isEmpty()) {
        sanitizedModel = QString("model");
    }

    QString timestamp = QDateTime::currentDateTimeUtc().toString(QString("yyyyMMdd_HHmmss"));
    QString csvFileName = QString("%1_%2.csv").arg(sanitizedModel, timestamp);
    QString metaFileName = QString("%1_%2.json").arg(sanitizedModel, timestamp);

    QFile csvFile(dir.filePath(csvFileName));
    if (!csvFile.open(QIODevice::WriteOnly | QIODevice::Text)) {
        return false;
    }

    // CSV字段引用函数
    auto quote = [](const QString &text) {
        QString escaped = text;
        escaped.replace('"', "\"\"");
        return QString("\"%1\"").arg(escaped);
    };

    QTextStream csvStream(&csvFile);
    csvStream << quote(QString("测试/故障"));
    for (const auto &fault : result.faults) {
        csvStream << ',' << quote(fault.id);
    }
    csvStream << '\n';

    for (int ti = 0; ti < result.tests.size(); ++ti) {
        const auto &test = result.tests.at(ti);
        csvStream << quote(test.id);
        for (int fi = 0; fi < result.faults.size(); ++fi) {
            const auto &cell = result.cells.at(fi).at(ti);
            csvStream << ',' << (cell.detected ? '1' : '0');
        }
        csvStream << '\n';
    }
    csvStream.flush();
    csvFile.close();

    QFile metaFile(dir.filePath(metaFileName));
    if (!metaFile.open(QIODevice::WriteOnly | QIODevice::Text)) {
        return false;
    }

    QJsonObject meta;
    meta.insert(QString("model"), modelName);
    meta.insert(QString("timestamp"), timestamp);
    meta.insert(QString("mode"), detectModeToString(options.mode));
    meta.insert(QString("timeoutMs"), options.timeoutMs);
    meta.insert(QString("autoRange"), options.autoRange);
    meta.insert(QString("fallbackToTemplate"), options.fallbackToTemplate);
    meta.insert(QString("rangeTolerance"), options.rangeTolerance);
    meta.insert(QString("searchMaxAbs"), options.searchMaxAbs);
    meta.insert(QString("includeFunctionInputs"), options.includeFunctionInputs);

    QJsonArray faultsArray;
    for (const auto &fault : result.faults) {
        QJsonObject obj;
        obj.insert(QString("id"), fault.id);
        obj.insert(QString("name"), fault.name);
        obj.insert(QString("kind"), faultKindToString(fault.kind));
        obj.insert(QString("function"), fault.relatedFunction);
        obj.insert(QString("component"), fault.componentName);
        obj.insert(QString("failureMode"), fault.failureModeName);
        obj.insert(QString("constraintIntegrity"), fault.constraintIntegrity);
        obj.insert(QString("linkElements"), QJsonArray::fromStringList(fault.linkElements));
        obj.insert(QString("relatedComponents"), QJsonArray::fromStringList(fault.relatedComponents));
        obj.insert(QString("inputAssertions"), QJsonArray::fromStringList(fault.inputAssertions));
        obj.insert(QString("faultAssertions"), QJsonArray::fromStringList(fault.faultAssertions));
        obj.insert(QString("actuatorAssertions"), QJsonArray::fromStringList(fault.actuatorAssertions));
        QStringList dependencyList;
        for (auto it = fault.dependencyClosure.constBegin(); it != fault.dependencyClosure.constEnd(); ++it) {
            dependencyList.append(*it);
        }
        obj.insert(QString("dependencyClosure"), QJsonArray::fromStringList(dependencyList));
        obj.insert(QString("enabled"), fault.enabled);

        QJsonObject offlineObj;
        for (auto offlineIt = fault.offlineModeMap.constBegin(); offlineIt != fault.offlineModeMap.constEnd(); ++offlineIt) {
            offlineObj.insert(offlineIt.key(), QJsonArray::fromStringList(offlineIt.value().toList()));
        }
        obj.insert(QString("offlineModes"), offlineObj);
        faultsArray.append(obj);
    }
    meta.insert(QString("faults"), faultsArray);

    QJsonArray testsArray;
    for (const auto &test : result.tests) {
        QJsonObject obj;
        obj.insert(QString("id"), test.id);
        obj.insert(QString("name"), test.name);
        obj.insert(QString("kind"), testKindToString(test.kind));
        obj.insert(QString("predicate"), test.predicate);
        obj.insert(QString("negatedPredicate"), test.negatedPredicate);
        obj.insert(QString("sourceVariable"), test.sourceItem.variable);
        obj.insert(QString("sourceValue"), test.sourceItem.value);
        if (!test.description.isEmpty()) {
            obj.insert(QString("description"), test.description);
        }
        obj.insert(QString("note"), test.note);
        obj.insert(QString("remark"), test.note);
        insertIfFinite(obj, QStringLiteral("complexity"), test.complexity);
        insertIfFinite(obj, QStringLiteral("cost"), test.cost);
        insertIfFinite(obj, QStringLiteral("duration"), test.duration);
        insertIfFinite(obj, QStringLiteral("successRate"), test.successRate);
        obj.insert(QString("relatedFunction"), test.relatedFunction);
        obj.insert(QString("component"), test.componentName);
        obj.insert(QString("failureMode"), test.failureModeName);
        obj.insert(QString("signalVariable"), test.signalVariable);
        obj.insert(QString("enabled"), test.enabled);
        testsArray.append(obj);
    }
    meta.insert(QString("tests"), testsArray);

    QJsonArray cellMetadata;
    for (int fi = 0; fi < result.faults.size(); ++fi) {
        const QString faultId = result.faults.at(fi).id;
        for (int ti = 0; ti < result.tests.size(); ++ti) {
            const QString testId = result.tests.at(ti).id;
            const auto &cell = result.cells.at(fi).at(ti);
            QJsonObject entry;
            entry.insert(QString("faultId"), faultId);
            entry.insert(QString("testId"), testId);
            entry.insert(QString("detected"), cell.detected);
            entry.insert(QString("guaranteed"), cell.guaranteed);
            if (!cell.method.trimmed().isEmpty()) {
                entry.insert(QString("method"), cell.method);
            }
            if (!cell.detail.trimmed().isEmpty()) {
                entry.insert(QString("detail"), cell.detail);
            }
            if (!std::isnan(cell.metric)) {
                entry.insert(QString("metric"), cell.metric);
            }
            cellMetadata.append(entry);
        }
    }
    meta.insert(QString("cellMetadata"), cellMetadata);

    QJsonArray summaryArray;
    for (int fi = 0; fi < result.faults.size(); ++fi) {
        int detectedCount = 0;
        for (int ti = 0; ti < result.tests.size(); ++ti) {
            if (result.cells.at(fi).at(ti).detected) {
                ++detectedCount;
            }
        }
        QJsonObject obj;
        obj.insert(QString("faultId"), result.faults.at(fi).id);
        obj.insert(QString("detected"), detectedCount);
        obj.insert(QString("totalTests"), result.tests.size());
        summaryArray.append(obj);
    }
    meta.insert(QString("faultSummary"), summaryArray);

    metaFile.write(QJsonDocument(meta).toJson(QJsonDocument::Indented));
    metaFile.close();

    if (csvPath) {
        *csvPath = dir.filePath(csvFileName);
    }
    if (metadataPath) {
        *metadataPath = dir.filePath(metaFileName);
    }
    return true;
}

/**
 * @brief 转换为断言
 * 将测试项列表转换为断言字符串列表
 * @param items 测试项列表
 * @return 断言字符串列表
 */
QStringList DMatrixBuilder::toAssertions(const QList<TestItem> &items) const
{
    QStringList assertions;
    if (!systemEntity) {
        return assertions;
    }

    QList<TestItem> mutableItems = items;
    QList<obsEntity> entities = systemEntity->buildObsEntityList(mutableItems);
    for (const auto &entity : entities) {
        assertions.append(entity.getDescription());
    }
    return assertions;
}

/**
 * @brief 创建范围断言
 * 创建表示变量在指定范围内的SMT-LIB断言
 * @param expression 变量表达式
 * @param lower 下界
 * @param upper 上界
 * @return 范围断言字符串
 */
QString DMatrixBuilder::createRangePredicate(const QString &expression,
                                             double lower,
                                             double upper) const
{
    return QString("(and (>= %1 %2) (<= %1 %3))")
        .arg(expression,
             formatDouble(lower),
             formatDouble(upper));
}

/**
 * @brief 格式化双精度浮点数
 * 将双精度浮点数格式化为字符串，处理接近零的情况
 * @param value 数值
 * @return 格式化后的字符串
 */
QString DMatrixBuilder::formatDouble(double value) const
{
    if (std::fabs(value) < 1e-12) {
        value = 0.0;
    }
    QString text = QString::number(value, 'f', 12);
    if (text.contains(QLatin1Char('.'))) {
        while (text.endsWith(QLatin1Char('0'))) {
            text.chop(1);
        }
        if (text.endsWith(QLatin1Char('.'))) {
            text.chop(1);
        }
    }
    if (text == QLatin1String("-0")) {
        text = QString("0");
    }
    if (text.isEmpty()) {
        text = QString("0");
    }
    return text;
}

/**
 * @brief 检查SAT缓存
 * 检查代码是否在SAT缓存中，如果不在则调用SMT求解器并缓存结果
 * @param smt SMT求解器接口
 * @param code SMT-LIB代码
 * @param timeoutMs 超时时间(毫秒)
 * @return 如果可满足返回true，否则返回false
 */
bool DMatrixBuilder::isSatCached(const SmtFacade &smt,
                                 const QString &code,
                                 int timeoutMs) const
{
    {
        QMutexLocker locker(&satCacheMutex);
        auto it = satCache.constFind(code);
        if (it != satCache.constEnd()) {
            return it.value();
        }
    }

    bool sat = smt.isSat(code, timeoutMs);
    {
        QMutexLocker locker(&satCacheMutex);
        satCache.insert(code, sat);
    }
    return sat;
}

/**
 * @brief 清除SAT缓存
 * 清空SAT结果缓存
 */
void DMatrixBuilder::clearSatCache() const
{
    QMutexLocker locker(&satCacheMutex);
    satCache.clear();
}

} // namespace testability
