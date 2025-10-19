#ifndef BEHAVIORAGGREGATOR_H
#define BEHAVIORAGGREGATOR_H

#include <functional>
#include <QList>
#include <QStringList>
#include <QVector>

#include "BO/container/containerdata.h"

struct FaultContribution {
    int sourceContainerId = 0;
    QString sourceName;
    QStringList propagatedModes;
};

struct AggregationOptions {
    bool inheritSingleChild = true;
    bool prefixChildPortNames = true;
};

struct AggregationResult {
    ContainerData container;
    QVector<FaultContribution> contributions;
    QStringList warnings;
};

class BehaviorAggregator
{
public:
    using Loader = std::function<ContainerEntity(int)>;
    using ChildrenFetcher = std::function<QList<ContainerEntity>(int)>;

    BehaviorAggregator(Loader loader, ChildrenFetcher childrenFetcher);

    AggregationResult aggregate(int containerId, const AggregationOptions &options = {}) const;

private:
    AggregationResult aggregate(const ContainerEntity &entity, const AggregationOptions &options) const;
    AggregationResult combine(const ContainerEntity &entity,
                              const QList<ContainerEntity> &children,
                              const QList<AggregationResult> &childResults,
                              const AggregationOptions &options) const;

    static QString qualifiedPortName(const ContainerEntity &child,
                                     const ContainerPort &port,
                                     bool prefixChildName);

    Loader m_loader;
    ChildrenFetcher m_childrenFetcher;
};

#endif // BEHAVIORAGGREGATOR_H
