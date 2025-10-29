#ifndef TESTGENERATORSERVICE_H
#define TESTGENERATORSERVICE_H

#include <QHash>
#include <QMap>
#include <QStringList>
#include <QVector>

#include "BO/container/containerdata.h"
#include "BO/container/behavioraggregator.h"
#include "BO/function/functiondependencyresolver.h"
#include "BO/function/functioninfo.h"
#include "BO/test/testdefinition.h"
#include "BO/containerrepository.h"

class TestGeneratorService
{
public:
    TestGeneratorService(ContainerRepository &repository,
                         BehaviorAggregator &aggregator,
                         FunctionDependencyResolver &dependencyResolver);

    void setFunctionMap(const QMap<QString, FunctionInfo> &functions);
    void setContainerFunctions(const QHash<int, QStringList> &mapping);

    QVector<GeneratedTest> generateForContainer(int containerId, bool persist = true);

private:
    QVector<GeneratedTest> generateSignalTests(const ContainerData &container) const;
    QVector<GeneratedTest> generateFunctionTests(int containerId, const ContainerData &container) const;
    QVector<GeneratedTest> generateFaultTests(const ContainerData &container) const;
    QStringList faultsReferencing(const BehaviorSpec &behavior, const QStringList &tokens) const;

    ContainerRepository &m_repository;
    BehaviorAggregator &m_aggregator;
    FunctionDependencyResolver &m_dependencyResolver;
    QMap<QString, FunctionInfo> m_functions;
    QHash<int, QStringList> m_containerFunctions;
};

#endif // TESTGENERATORSERVICE_H
