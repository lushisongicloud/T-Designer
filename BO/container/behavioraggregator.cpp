#include "BO/container/behavioraggregator.h"

#include <algorithm>
#include <QSet>
#include <QVariantList>

#include "BO/behavior/z3simplifier.h"

BehaviorAggregator::BehaviorAggregator(Loader loader, ChildrenFetcher childrenFetcher)
    : m_loader(std::move(loader))
    , m_childrenFetcher(std::move(childrenFetcher))
{
}

AggregationResult BehaviorAggregator::aggregate(int containerId, const AggregationOptions &options) const
{
    if (!m_loader) return {};
    ContainerEntity entity = m_loader(containerId);
    if (entity.id() == 0) return {};
    return aggregate(entity, options);
}

AggregationResult BehaviorAggregator::aggregate(const ContainerEntity &entity, const AggregationOptions &options) const
{
    AggregationResult result;
    const QList<ContainerEntity> children = m_childrenFetcher ? m_childrenFetcher(entity.id()) : QList<ContainerEntity>();
    if (children.isEmpty()) {
        result.container = ContainerData(entity);
        return result;
    }

    QList<AggregationResult> childResults;
    childResults.reserve(children.size());
    for (const ContainerEntity &child : children)
        childResults.append(aggregate(child, options));

    return combine(entity, children, childResults, options);
}

AggregationResult BehaviorAggregator::combine(const ContainerEntity &entity,
                                              const QList<ContainerEntity> &children,
                                              const QList<AggregationResult> &childResults,
                                              const AggregationOptions &options) const
{
    AggregationResult result;
    ContainerData aggregated(entity);

    if (children.size() == 1 && options.inheritSingleChild) {
        const AggregationResult &childResult = childResults.first();
        aggregated.setPorts(childResult.container.ports());
        aggregated.setBehavior(childResult.container.behavior());
        aggregated.setBehaviorSmt(childResult.container.behaviorSmt());
        result.container = aggregated;
        result.contributions = childResult.contributions;
        FaultContribution contribution;
        contribution.sourceContainerId = children.first().id();
        contribution.sourceName = children.first().name();
        for (const BehaviorMode &mode : childResult.container.behavior().faultModes)
            contribution.propagatedModes.append(mode.modeId);
        result.contributions.append(contribution);
        result.warnings = childResult.warnings;
        return result;
    }

    QVector<ContainerPort> ports;
    ports.reserve(children.size() * 4);
    QStringList smtClauses;
    QStringList warnings;
    QVector<FaultContribution> contributions;
    contributions.reserve(children.size());

    BehaviorSpec behaviorSpec;
    behaviorSpec.normalMode.modeType = BehaviorModeType::Normal;
    behaviorSpec.normalMode.modeId = entity.name().isEmpty()
            ? QString("%1.normal").arg(entity.id())
            : entity.name() + QString(".normal");
    behaviorSpec.normalMode.displayName = entity.name().isEmpty()
            ? QString("Container %1 正常").arg(entity.id())
            : entity.name() + QString(" 正常");
    behaviorSpec.normalMode.sourceContainers.append(entity.id());

    QSet<QString> seenPortNames;

    for (int index = 0; index < children.size(); ++index) {
        const ContainerEntity &childEntity = children.at(index);
        const AggregationResult &childResult = childResults.at(index);

        for (const ContainerPort &childPort : childResult.container.ports()) {
            ContainerPort parentPort = childPort;
            parentPort.sourceContainerId = childEntity.id();
            parentPort.name = qualifiedPortName(childEntity, childPort, options.prefixChildPortNames);
            if (seenPortNames.contains(parentPort.name)) {
                warnings.append(QString("端口名称冲突: %1").arg(parentPort.name));
                continue;
            }
            seenPortNames.insert(parentPort.name);
            ports.append(parentPort);
        }

        const BehaviorSpec &childBehavior = childResult.container.behavior();
        for (const QString &constraint : childBehavior.normalMode.constraints) {
            if (constraint.trimmed().isEmpty()) continue;
            if (childEntity.name().isEmpty())
                behaviorSpec.normalMode.constraints.append(constraint);
            else
                behaviorSpec.normalMode.constraints.append(QString("[%1] %2").arg(childEntity.name(), constraint));
        }

        FaultContribution contribution;
        contribution.sourceContainerId = childEntity.id();
        contribution.sourceName = childEntity.name();

        for (const BehaviorMode &mode : childBehavior.faultModes) {
            BehaviorMode derived = mode;
            derived.sourceContainers.prepend(childEntity.id());
            if (childEntity.name().isEmpty()) {
                if (derived.modeId.isEmpty())
                    derived.modeId = QString("fault-%1").arg(childEntity.id());
                if (derived.displayName.isEmpty())
                    derived.displayName = QString("容器%1故障").arg(childEntity.id());
            } else {
                if (derived.modeId.isEmpty())
                    derived.modeId = childEntity.name() + QString(".fault");
                else
                    derived.modeId = QString("%1/%2").arg(childEntity.name(), derived.modeId);
                if (derived.displayName.isEmpty())
                    derived.displayName = childEntity.name() + QString(" 故障");
                else
                    derived.displayName = childEntity.name() + QString(".") + derived.displayName;
            }
            behaviorSpec.faultModes.append(derived);
            contribution.propagatedModes.append(derived.modeId);
        }

        contributions.append(contribution);

        const QString clause = childResult.container.behaviorSmt().trimmed();
        if (!clause.isEmpty())
            smtClauses.append(clause);

        result.warnings << childResult.warnings;
    }

    aggregated.setPorts(ports);

    QString simplifiedExpression;
    if (!smtClauses.isEmpty()) {
        Z3Simplifier simplifier;
        Z3SimplificationResult simplification = simplifier.simplifyConjunction(smtClauses);
        if (simplification.success) {
            simplifiedExpression = simplification.simplifiedExpression;
            result.simplificationLog = simplification.log;
        } else {
            warnings.append(QString("Z3 化简失败，使用原始表达式聚合"));
            if (smtClauses.size() == 1)
                simplifiedExpression = smtClauses.first();
            else
                simplifiedExpression = QString("(and %1)").arg(smtClauses.join(QChar(' ')));
        }
    }

    if (!simplifiedExpression.isEmpty())
        aggregated.setBehaviorSmt(simplifiedExpression);
    else
        aggregated.setBehaviorSmt(QString());

    if (children.size() > 1) {
        BehaviorMode aggregatedFault;
        aggregatedFault.modeType = BehaviorModeType::DerivedFault;
        if (entity.name().isEmpty())
            aggregatedFault.modeId = QString("container-%1.fault").arg(entity.id());
        else
            aggregatedFault.modeId = entity.name() + QString(".fault");
        aggregatedFault.displayName = entity.name().isEmpty()
                ? QString("容器%1故障").arg(entity.id())
                : entity.name() + QString(" 故障");
        if (!aggregated.behaviorSmt().trimmed().isEmpty())
            aggregatedFault.constraints.append(QString("(not %1)").arg(aggregated.behaviorSmt()));
        aggregatedFault.sourceContainers.append(entity.id());
        QVariantList childIds;
        for (const ContainerEntity &childEntity : children)
            childIds.append(childEntity.id());
        aggregatedFault.annotations.insert(QString("children"), childIds);
        aggregatedFault.annotations.insert(QString("aggregated"), true);
        behaviorSpec.faultModes.prepend(aggregatedFault);
    }

    aggregated.setBehavior(behaviorSpec);

    result.container = aggregated;
    result.contributions = contributions;
    result.warnings << warnings;
    result.warnings.erase(std::remove_if(result.warnings.begin(), result.warnings.end(),
                                         [](const QString &value) { return value.trimmed().isEmpty(); }),
                          result.warnings.end());

    return result;
}

QString BehaviorAggregator::qualifiedPortName(const ContainerEntity &child,
                                              const ContainerPort &port,
                                              bool prefixChildName)
{
    if (!prefixChildName || child.name().isEmpty() || port.name.isEmpty())
        return port.name;
    return child.name() + QString(".") + port.name;
}
