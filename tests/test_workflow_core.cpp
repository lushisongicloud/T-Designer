#include <QtTest>

#include "BO/componententity.h"
#include "BO/container/containerdata.h"
#include "BO/container/behavioraggregator.h"
#include "BO/behavior/z3simplifier.h"
#include "BO/function/functiondependencyresolver.h"
#include "BO/function/tmodelvalidator.h"
#include "BO/test/testgeneratorservice.h"
#include "BO/test/diagnosticmatrixbuilder.h"
#include <QSqlDatabase>

class WorkflowCoreTest : public QObject
{
    Q_OBJECT
private slots:
    void containerData_roundTrip();
    void functionDependencyResolver_simpleChain();
    void behaviorAggregator_mergeChildren();
    void testGeneratorService_generatesTests();
    void tmodelValidator_mapsPorts();
    void z3Simplifier_simplifiesConjunction();
    void z3Simplifier_detectsUnsat();
};

void WorkflowCoreTest::containerData_roundTrip()
{
    ContainerEntity entity;
    entity.setId(1);
    entity.setName(QStringLiteral("Parent"));

    ContainerData data(entity);

    ContainerPort port;
    port.name = QStringLiteral("Vin");
    port.category = QStringLiteral("electrical");
    port.quantity = QStringLiteral("voltage");
    port.direction = PortDirection::Input;
    port.unit = QStringLiteral("V");
    port.bounds.insert(QStringLiteral("min"), -5.0);
    port.bounds.insert(QStringLiteral("max"), 5.0);
    data.setPorts({port});

    BehaviorMode normal;
    normal.modeId = QStringLiteral("Parent.normal");
    normal.displayName = QStringLiteral("Parent Normal");
    normal.modeType = BehaviorModeType::Normal;
    normal.constraints.append(QStringLiteral("Vin >= -5 && Vin <= 5"));

    BehaviorMode fault;
    fault.modeId = QStringLiteral("Parent.open");
    fault.displayName = QStringLiteral("Open Fault");
    fault.modeType = BehaviorModeType::Fault;
    fault.probability = 0.2;
    fault.constraints.append(QStringLiteral("Vin > 5"));

    BehaviorSpec behavior;
    behavior.normalMode = normal;
    behavior.faultModes.append(fault);
    data.setBehavior(behavior);
    data.setBehaviorSmt(QStringLiteral("(assert (and (>= Vin -5) (<= Vin 5)))"));

    ContainerData roundTrip(data.entity());
    QCOMPARE(roundTrip.ports().size(), 1);
    QCOMPARE(roundTrip.ports().first().name, QStringLiteral("Vin"));
    QCOMPARE(roundTrip.ports().first().unit, QStringLiteral("V"));
    QCOMPARE(roundTrip.behavior().faultModes.size(), 1);
    QCOMPARE(roundTrip.behavior().faultModes.first().modeId, QStringLiteral("Parent.open"));
    QCOMPARE(roundTrip.behaviorSmt(), QStringLiteral("(assert (and (>= Vin -5) (<= Vin 5)))"));
}

void WorkflowCoreTest::functionDependencyResolver_simpleChain()
{
    FunctionInfo funcA;
    funcA.functionName = QStringLiteral("A");
    TestItem aInput;
    aInput.variable = QStringLiteral("InputA");
    aInput.testType = QStringLiteral("一般变量");
    funcA.constraintList.append(aInput);
    funcA.actuatorConstraint.variable = QStringLiteral("ActuatorA");

    FunctionInfo funcB;
    funcB.functionName = QStringLiteral("B");
    TestItem bInput;
    bInput.variable = QStringLiteral("InputB");
    bInput.testType = QStringLiteral("一般变量");
    funcB.constraintList.append(bInput);
    funcB.actuatorConstraint.variable = QStringLiteral("ActuatorB");
    funcB.functionDependency = QStringLiteral(",A,");

    FunctionInfo funcC;
    funcC.functionName = QStringLiteral("C");
    funcC.functionDependency = QStringLiteral(",B,");
    funcC.actuatorConstraint.variable = QStringLiteral("ActuatorC");

    QMap<QString, FunctionInfo> definitions;
    definitions.insert(funcA.functionName, funcA);
    definitions.insert(funcB.functionName, funcB);
    definitions.insert(funcC.functionName, funcC);

    FunctionDependencyResolver resolver(definitions);
    auto resolved = resolver.resolve(QStringLiteral("C"));

    QCOMPARE(resolved.dependencyFunctions.contains(QStringLiteral("B")), true);
    QCOMPARE(resolved.dependencyFunctions.contains(QStringLiteral("A")), true);
    QCOMPARE(resolved.requiredInputs.contains(QStringLiteral("InputA")), true);
    QCOMPARE(resolved.requiredInputs.contains(QStringLiteral("InputB")), true);
    QCOMPARE(resolved.actuatorVariables.contains(QStringLiteral("ActuatorC")), true);
    QCOMPARE(resolved.actuatorVariables.contains(QStringLiteral("ActuatorB")), false);
    QCOMPARE(resolved.evaluationOrder.last(), QStringLiteral("C"));
    QCOMPARE(resolved.evaluationOrder.first(), QStringLiteral("A"));
    QCOMPARE(resolved.warnings.isEmpty(), true);
}

void WorkflowCoreTest::behaviorAggregator_mergeChildren()
{
    ContainerEntity parent;
    parent.setId(1);
    parent.setName(QStringLiteral("Parent"));

    ContainerEntity childA;
    childA.setId(2);
    childA.setName(QStringLiteral("ChildA"));

    ContainerEntity childB;
    childB.setId(3);
    childB.setName(QStringLiteral("ChildB"));

    ContainerData childAData(childA);
    ContainerPort portA;
    portA.name = QStringLiteral("Sensor");
    portA.direction = PortDirection::Input;
    childAData.setPorts({portA});
    BehaviorMode childANormal;
    childANormal.modeId = QStringLiteral("ChildA.normal");
    childANormal.modeType = BehaviorModeType::Normal;
    childANormal.constraints.append(QStringLiteral("Sensor >= 0"));
    BehaviorMode childAFault;
    childAFault.modeId = QStringLiteral("ChildA.open");
    childAFault.modeType = BehaviorModeType::Fault;
    childAFault.displayName = QStringLiteral("Open");
    BehaviorSpec childASpec;
    childASpec.normalMode = childANormal;
    childASpec.faultModes.append(childAFault);
    childAData.setBehavior(childASpec);
    childAData.setBehaviorSmt(QStringLiteral("(>= Sensor 0)"));

    ContainerData childBData(childB);
    ContainerPort portB;
    portB.name = QStringLiteral("Output");
    portB.direction = PortDirection::Output;
    childBData.setPorts({portB});
    BehaviorMode childBNormal;
    childBNormal.modeId = QStringLiteral("ChildB.normal");
    childBNormal.modeType = BehaviorModeType::Normal;
    childBNormal.constraints.append(QStringLiteral("Output <= 10"));
    BehaviorMode childBFault;
    childBFault.modeId = QStringLiteral("ChildB.short");
    childBFault.modeType = BehaviorModeType::Fault;
    childBFault.displayName = QStringLiteral("Short");
    BehaviorSpec childBSpec;
    childBSpec.normalMode = childBNormal;
    childBSpec.faultModes.append(childBFault);
    childBData.setBehavior(childBSpec);
    childBData.setBehaviorSmt(QStringLiteral("(<= Output 10)"));

    QMap<int, ContainerEntity> entityMap;
    entityMap.insert(parent.id(), parent);
    entityMap.insert(childA.id(), childAData.entity());
    entityMap.insert(childB.id(), childBData.entity());

    QHash<int, QList<int>> adjacency;
    adjacency.insert(parent.id(), {childA.id(), childB.id()});

    BehaviorAggregator::Loader loader = [entityMap](int id) -> ContainerEntity {
        return entityMap.value(id);
    };

    BehaviorAggregator::ChildrenFetcher fetcher = [entityMap, adjacency](int id) -> QList<ContainerEntity> {
        QList<ContainerEntity> children;
        for (int childId : adjacency.value(id))
            children.append(entityMap.value(childId));
        return children;
    };

    BehaviorAggregator aggregator(loader, fetcher);
    AggregationResult aggregated = aggregator.aggregate(parent.id());

    QCOMPARE(aggregated.container.ports().size(), 2);
    QCOMPARE(aggregated.container.ports().first().sourceContainerId, childA.id());
    QCOMPARE(aggregated.container.ports().last().sourceContainerId, childB.id());
    QCOMPARE(aggregated.container.behavior().faultModes.size(), 3);
    const BehaviorMode &aggregatedFault = aggregated.container.behavior().faultModes.at(0);
    QCOMPARE(aggregatedFault.modeId, QStringLiteral("Parent.fault"));
    QVERIFY(!aggregatedFault.constraints.isEmpty());
    QVERIFY(aggregatedFault.constraints.first().startsWith(QStringLiteral("(not ")));
    const BehaviorMode &childFaultA = aggregated.container.behavior().faultModes.at(1);
    const BehaviorMode &childFaultB = aggregated.container.behavior().faultModes.at(2);
    QCOMPARE(childFaultA.modeId.contains(QStringLiteral("ChildA")), true);
    QCOMPARE(childFaultB.modeId.contains(QStringLiteral("ChildB")), true);
    QCOMPARE(aggregated.container.behavior().normalMode.constraints.size(), 2);
    QCOMPARE(aggregated.container.behaviorSmt(), QStringLiteral("(and (>= Sensor 0) (<= Output 10))"));
    QVERIFY(!aggregated.simplificationLog.isEmpty());
    QVERIFY(aggregated.warnings.isEmpty());
}
void WorkflowCoreTest::testGeneratorService_generatesTests()
{
    {
        QSqlDatabase db = QSqlDatabase::addDatabase("QSQLITE", "generator_test");
        db.setDatabaseName(":memory:");
        QVERIFY(db.open());

        {
            ContainerRepository repo(db);
            QVERIFY(repo.ensureTables());

            ContainerEntity parent;
            parent.setName(QStringLiteral("Parent"));
            parent.setType(ContainerType::Module);
            QVERIFY(repo.insert(parent));

            ContainerEntity childA;
            childA.setName(QStringLiteral("ChildA"));
            childA.setType(ContainerType::Component);
            ContainerData childAData(childA);
            ContainerPort portA;
            portA.name = QStringLiteral("Sensor");
            portA.direction = PortDirection::Input;
            childAData.setPorts({portA});
            BehaviorMode childANormal;
            childANormal.modeId = QStringLiteral("ChildA.normal");
            childANormal.constraints.append(QStringLiteral("Sensor >= 0"));
            BehaviorMode childAFault;
            childAFault.modeId = QStringLiteral("ChildA.open");
            childAFault.modeType = BehaviorModeType::Fault;
            childAFault.constraints.append(QStringLiteral("Sensor < 0"));
            BehaviorSpec childASpec;
            childASpec.normalMode = childANormal;
            childASpec.faultModes.append(childAFault);
            childAData.setBehavior(childASpec);
            QVERIFY(repo.insert(childAData.entity()));
            childAData.entity().setParentId(parent.id());
            QVERIFY(repo.update(childAData.entity()));

            ContainerEntity childB;
            childB.setName(QStringLiteral("ChildB"));
            childB.setType(ContainerType::Component);
            ContainerData childBData(childB);
            ContainerPort portB;
            portB.name = QStringLiteral("Output");
            portB.direction = PortDirection::Output;
            childBData.setPorts({portB});
            BehaviorMode childBNormal;
            childBNormal.modeId = QStringLiteral("ChildB.normal");
            childBNormal.constraints.append(QStringLiteral("Output <= 10"));
            BehaviorMode childBFault;
            childBFault.modeId = QStringLiteral("ChildB.short");
            childBFault.modeType = BehaviorModeType::Fault;
            childBFault.constraints.append(QStringLiteral("Output > 10"));
            BehaviorSpec childBSpec;
            childBSpec.normalMode = childBNormal;
            childBSpec.faultModes.append(childBFault);
            childBData.setBehavior(childBSpec);
            QVERIFY(repo.insert(childBData.entity()));
            childBData.entity().setParentId(parent.id());
            QVERIFY(repo.update(childBData.entity()));

            BehaviorAggregator aggregator(
                [&](int id) { return repo.getById(id); },
                [&](int id) { return repo.fetchChildren(id); });

            FunctionDependencyResolver resolver;
            TestGeneratorService service(repo, aggregator, resolver);

            FunctionInfo funcA;
            funcA.functionName = QStringLiteral("FuncA");
            TestItem aInput;
            aInput.variable = QStringLiteral("Sensor");
            aInput.testType = QStringLiteral("一般变量");
            funcA.constraintList.append(aInput);
            funcA.actuatorConstraint.variable = QStringLiteral("ActuatorA");

            FunctionInfo funcB;
            funcB.functionName = QStringLiteral("FuncB");
            funcB.functionDependency = QStringLiteral(",FuncA,");
            TestItem bInput;
            bInput.variable = QStringLiteral("Output");
            bInput.testType = QStringLiteral("一般变量");
            funcB.constraintList.append(bInput);
            funcB.actuatorConstraint.variable = QStringLiteral("ActuatorB");

            QMap<QString, FunctionInfo> functions;
            functions.insert(funcA.functionName, funcA);
            functions.insert(funcB.functionName, funcB);
            service.setFunctionMap(functions);

            QHash<int, QStringList> mapping;
            mapping.insert(parent.id(), QStringList{QStringLiteral("FuncB")});
            service.setContainerFunctions(mapping);

            QVector<GeneratedTest> tests = service.generateForContainer(parent.id());
            ContainerData parentData(repo.getById(parent.id()));
            DiagnosticMatrixBuilder builder;
            builder.rebuild(parentData);
            CoverageStats stats = builder.coverageStats();
            QCOMPARE(stats.totalTests, tests.size());
            QCOMPARE(stats.totalFaults, 2);
            auto containsFault = [&](const QString &needle) {
                for (const QString &fid : stats.detectedFaults) {
                    if (fid.contains(needle)) return true;
                }
                return false;
            };
            QVERIFY(containsFault(QStringLiteral("ChildA")));
            QVERIFY(containsFault(QStringLiteral("ChildB")));
            QStringList candidateTests = builder.candidateTests(0.5);
            QVERIFY(!candidateTests.isEmpty());
            auto decisionTree = builder.buildDecisionTree();
            QVERIFY(decisionTree);
            QVERIFY(!decisionTree->testId.isEmpty() || decisionTree->isLeaf);
            QVERIFY(tests.size() >= 4);
            QStringList categories;
            for (const GeneratedTest &test : tests)
                categories.append(testCategoryToString(test.category));
            QVERIFY(categories.contains(QStringLiteral("signal")));
            QVERIFY(categories.contains(QStringLiteral("function")));
            QVERIFY(categories.contains(QStringLiteral("faultMode")));

            ContainerEntity persisted = repo.getById(parent.id());
            QVERIFY(!persisted.testsJson().isEmpty());

            db.close();
        }
    }
    QSqlDatabase::removeDatabase(QStringLiteral("generator_test"));
}

void WorkflowCoreTest::tmodelValidator_mapsPorts()
{
    QList<PortInfo> ports;
    PortInfo port1;
    port1.connNum = QStringLiteral("1");
    port1.symbolId = QStringLiteral("S1");
    port1.symb2TermInfoId = QStringLiteral("10");
    ports.append(port1);
    PortInfo port2;
    port2.connNum = QStringLiteral("2");
    port2.symbolId = QStringLiteral("S1");
    port2.symb2TermInfoId = QStringLiteral("11");
    ports.append(port2);

    const QString tmodel = QStringLiteral(
        "(declare-fun %FU%.1.u () Real)\n"
        "(declare-fun %FU%.1.i () Real)\n"
        "(declare-fun FU1.2.u () Real)\n"
        "(declare-fun FU1.2.i () Real)\n"
        "(assert (= %FU%.1.u FU1.2.u))\n"
        "(assert (= %FU%.1.i (* -1 FU1.2.i)))");

    TModelValidator validator;
    TModelValidationResult result = validator.validate(tmodel, ports);
    QVERIFY(result.isValid());
    QCOMPARE(result.bindings.size(), 2);
    for (const PortVariableBinding &binding : result.bindings) {
        QVERIFY(binding.declaredDirections.contains(QStringLiteral("u")));
        QVERIFY(binding.declaredDirections.contains(QStringLiteral("i")));
    }

    const QString invalidModel = QStringLiteral(
        "(declare-fun %FU%.1.u () Real)\n"
        "(declare-fun %FU%.3.u () Real)");
    result = validator.validate(invalidModel, ports);
    QVERIFY(!result.isValid());
    QVERIFY(result.missingDeclarations.contains(QStringLiteral("1.i")));
    bool orphanFound = false;
    for (const QString &token : result.undefinedVariables) {
        if (token.contains(QStringLiteral("%FU%.3.u"))) {
            orphanFound = true;
            break;
        }
    }
    QVERIFY(orphanFound);

    ports.clear();
    PortInfo mechanicalPort;
    mechanicalPort.connNum = QStringLiteral("A1");
    mechanicalPort.functionBlock = QStringLiteral("Actuator");
    mechanicalPort.portType = QStringLiteral("mechanical");
    ports.append(mechanicalPort);

    const QString mechanicalModel = QStringLiteral(
        "(declare-fun %M%.Actuator.A1.F () Real)");
    result = validator.validate(mechanicalModel, ports);
    QVERIFY(!result.isValid());
    QVERIFY(result.missingDeclarations.contains(QStringLiteral("Actuator.A1.v/n/x")));
}

void WorkflowCoreTest::z3Simplifier_simplifiesConjunction()
{
    Z3Simplifier simplifier;
    QStringList expressions;
    expressions << QStringLiteral("(= a 1)") << QStringLiteral("(= b (+ a 1))");
    Z3SimplificationResult result = simplifier.simplifyConjunction(expressions);
    QVERIFY(result.success);
    QVERIFY(result.simplifiedExpression.contains(QStringLiteral("(= a 1)")));
    QVERIFY(result.simplifiedExpression.contains(QStringLiteral("b")));
    QVERIFY(result.log.contains(QStringLiteral("化简后")));
}

void WorkflowCoreTest::z3Simplifier_detectsUnsat()
{
    Z3Simplifier simplifier;
    QStringList assertions;
    assertions << QStringLiteral("(= x 1)") << QStringLiteral("(= x 2)");
    QVERIFY(simplifier.isUnsat(assertions));
    QStringList satAssertions;
    satAssertions << QStringLiteral("(= x 1)") << QStringLiteral("(= y 2)");
    QVERIFY(!simplifier.isUnsat(satAssertions));
}


QTEST_MAIN(WorkflowCoreTest)
#include "test_workflow_core.moc"
