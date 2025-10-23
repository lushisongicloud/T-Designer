#include "BO/test/testgeneratorservice.h"

#include <QVariant>
#include <QVariantList>
#include <QtGlobal>

TestGeneratorService::TestGeneratorService(ContainerRepository &repository,
                                           BehaviorAggregator &aggregator,
                                           FunctionDependencyResolver &dependencyResolver)
    : m_repository(repository)
    , m_aggregator(aggregator)
    , m_dependencyResolver(dependencyResolver)
{
}

void TestGeneratorService::setFunctionMap(const QMap<QString, FunctionInfo> &functions)
{
    m_functions = functions;
    m_dependencyResolver.setDefinitions(m_functions);
}

void TestGeneratorService::setContainerFunctions(const QHash<int, QStringList> &mapping)
{
    m_containerFunctions = mapping;
}

QVector<GeneratedTest> TestGeneratorService::generateForContainer(int containerId, bool persist)
{
    AggregationResult aggregated = m_aggregator.aggregate(containerId);
    ContainerData container = aggregated.container;

    QVector<GeneratedTest> tests;
    tests << generateSignalTests(container);
    tests << generateFunctionTests(containerId, container);
    tests << generateFaultTests(container);

    container.setTests(tests);
    if (persist)
        m_repository.update(container.entity());

    return tests;
}

QVector<GeneratedTest> TestGeneratorService::generateSignalTests(const ContainerData &container) const
{
    QVector<GeneratedTest> tests;
    const QString containerName = container.entity().name();
    const BehaviorSpec &behavior = container.behavior();

    for (const ContainerPort &port : container.ports()) {
        GeneratedTest test;
        test.category = TestCategory::Signal;
        test.id = QString("signal:%1:%2").arg(container.entity().id()).arg(port.name);
        test.name = QString("%1%2信号检测").arg(containerName.isEmpty() ? QString("容器") : containerName,
                                                 port.name.isEmpty() ? QString() : QString("/") + port.name);
        test.description = QString("根据接口模型自动生成的信号类测试");
        test.targetId = port.name;
        QVariantMap metrics;
        metrics.insert(QString("direction"), portDirectionToString(port.direction));
        if (!port.category.isEmpty()) metrics.insert(QString("category"), port.category);
        if (!port.quantity.isEmpty()) metrics.insert(QString("quantity"), port.quantity);
        if (!port.unit.isEmpty()) metrics.insert(QString("unit"), port.unit);
        if (!port.bounds.isEmpty()) metrics.insert(QString("bounds"), port.bounds);
        test.metrics = metrics;
        test.estimatedCost = 1.0;
        test.estimatedDuration = 1.0;

        QStringList tokens;
        tokens << port.name << port.alias << port.signalId;
        tokens.removeAll(QString());
        const QStringList faults = faultsReferencing(behavior, tokens);
        test.detectableFaults = faults;
        test.isolatableFaults = faults;
        tests.append(test);
    }
    return tests;
}

QVector<GeneratedTest> TestGeneratorService::generateFunctionTests(int containerId, const ContainerData &container) const
{
    QVector<GeneratedTest> tests;
    const QStringList functionNames = m_containerFunctions.value(containerId);
    if (functionNames.isEmpty()) return tests;

    for (const QString &functionName : functionNames) {
        auto it = m_functions.find(functionName);
        if (it == m_functions.end()) continue;

        FunctionDependencyResolver::ResolvedFunction resolved = m_dependencyResolver.resolve(functionName);

        GeneratedTest test;
        test.category = TestCategory::Function;
        test.id = QString("function:%1:%2").arg(container.entity().id()).arg(functionName);
        test.name = functionName + QString(" 功能测试");
        test.description = QString("根据功能依赖关系自动生成的功能类测试");
        test.targetId = functionName;

        QStringList prerequisites = resolved.evaluationOrder;
        prerequisites.removeAll(functionName);
        test.prerequisites = prerequisites;

        test.metrics.insert(QString("requiredInputs"), QStringList(resolved.requiredInputs.values()));
        test.metrics.insert(QString("dependencyFunctions"), QStringList(resolved.dependencyFunctions.values()));
        test.metrics.insert(QString("actuators"), QStringList(resolved.actuatorVariables.values()));
        test.estimatedCost = 2.0;
        test.estimatedDuration = 2.0;

        QStringList tokens = QStringList(resolved.requiredInputs.values());
        tokens.append(QStringList(resolved.actuatorVariables.values()));
        tokens.append(functionName);
        tokens.removeAll(QString());

        const QStringList faults = faultsReferencing(container.behavior(), tokens);
        test.detectableFaults = faults;
        test.isolatableFaults = faults;
        tests.append(test);
    }

    return tests;
}

QVector<GeneratedTest> TestGeneratorService::generateFaultTests(const ContainerData &container) const
{
    QVector<GeneratedTest> tests;
    const BehaviorSpec &behavior = container.behavior();
    QStringList allFaultIds;

    for (const BehaviorMode &mode : behavior.faultModes) {
        GeneratedTest test;
        test.category = TestCategory::FaultMode;
        const QString modeId = mode.modeId.isEmpty() ? QString("fault-%1").arg(container.entity().id()) : mode.modeId;
        test.id = QString("fault:%1:%2").arg(container.entity().id()).arg(modeId);
        test.name = mode.displayName.isEmpty() ? modeId : mode.displayName;
        test.description = QString("针对故障模式的虚拟测试");
        test.targetId = modeId;
        test.detectableFaults = QStringList{modeId};
        test.isolatableFaults = QStringList{modeId};
        if (!mode.sourceContainers.isEmpty()) {
            QVariantList sources;
            for (int sid : mode.sourceContainers) sources.append(sid);
            test.metrics.insert(QString("sourceContainers"), sources);
        }
        if (mode.probability > 0.0)
            test.metrics.insert(QString("probability"), mode.probability);
        test.estimatedCost = 3.0;
        test.estimatedDuration = 3.0;
        tests.append(test);
        allFaultIds.append(modeId);
    }

    allFaultIds.removeDuplicates();
    if (!allFaultIds.isEmpty()) {
        GeneratedTest normal;
        normal.category = TestCategory::FaultMode;
        normal.id = QString("fault:%1:normal").arg(container.entity().id());
        normal.name = QString("正常判别");
        normal.description = QString("验证容器是否处于正常模式的虚拟测试");
        normal.targetId = behavior.normalMode.modeId.isEmpty() ? QString("normal") : behavior.normalMode.modeId;
        normal.detectableFaults = allFaultIds;
        normal.estimatedCost = 2.5;
        normal.estimatedDuration = 2.5;
        tests.prepend(normal);
    }

    return tests;
}

QStringList TestGeneratorService::faultsReferencing(const BehaviorSpec &behavior, const QStringList &tokens) const
{
    QStringList matched;
    for (const BehaviorMode &mode : behavior.faultModes) {
        bool hit = false;
        for (const QString &token : tokens) {
            if (token.isEmpty()) continue;
            for (const QString &constraint : mode.constraints) {
                if (constraint.contains(token, Qt::CaseInsensitive)) {
                    hit = true;
                    break;
                }
            }
            if (!hit) {
                for (auto it = mode.annotations.constBegin(); it != mode.annotations.constEnd(); ++it) {
                    const QString value = it.value().toString();
                    if (value.contains(token, Qt::CaseInsensitive)) {
                        hit = true;
                        break;
                    }
                }
            }
            if (hit) break;
        }
        if (hit) matched.append(mode.modeId);
    }
    matched.removeAll(QString());
    matched.removeDuplicates();
    return matched;
}
