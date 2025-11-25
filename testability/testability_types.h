#ifndef TESTABILITY_TESTABILITY_TYPES_H
#define TESTABILITY_TESTABILITY_TYPES_H

#include <QString>
#include <QStringList>
#include <QVector>
#include <QHash>
#include <QSet>
#include <limits>

#include "BO/componententity.h"

namespace testability {

enum class TestKind {
    Signal,
    Function,
    Mode
};

enum class FaultKind {
    Function,
    Component
};

enum class DetectMode {
    Guaranteed,
    Exists
};

struct ComponentOverride {
    QString componentName;
    QStringList assertions;
    bool replaceNormal = true;
};

struct TestDefinition {
    QString id;
    QString name;
    TestKind kind = TestKind::Signal;
    TestItem sourceItem;
    QString predicate;
    QString negatedPredicate;
    QString note;
    QString relatedFunction;
    QString componentName;
    QString failureModeName;
    QList<ComponentOverride> overrides;
    QString signalVariable;
    bool enabled = true;
};

struct FaultDefinition {
    QString id;
    QString name;
    FaultKind kind = FaultKind::Function;
    QString relatedFunction;
    QString componentName;
    QString failureModeName;
    QStringList inputAssertions;
    QStringList faultAssertions;
    QList<ComponentOverride> overrides;
    QString constraintIntegrity;
    QStringList linkElements;
    QStringList relatedComponents;
    QHash<QString, QSet<QString>> offlineModeMap;
    QStringList actuatorAssertions;
    QSet<QString> dependencyClosure;
    bool enabled = true;
};

struct DetectabilityResult {
    bool normalSat = false;
    bool faultSat = false;
    bool normalPassSat = false;
    bool faultFailSat = false;
    bool guaranteed = false;
    bool detected = false;
    QString method;
    QString detail;
    bool skipped = false;
    double metric = std::numeric_limits<double>::quiet_NaN();
};

struct ModelFragments {
    struct ComponentBlock {
        QString name;
        QString normalAssertions;
        QList<FailureMode> failureModes;
    };

    QString prefixCode;
    QVector<ComponentBlock> components;
};

struct DMatrixBuildOptions {
    DetectMode mode = DetectMode::Guaranteed;
    int timeoutMs = -1;
    bool autoRange = true;
    bool fallbackToTemplate = true;
    double rangeTolerance = 0.05;
    double searchMaxAbs = 10000.0;
    QString outputDirectory;
    bool includeFunctionInputs = true;
};

struct DMatrixBuildResult {
    QVector<FaultDefinition> faults;
    QVector<TestDefinition> tests;
    QVector<QVector<DetectabilityResult>> cells;
};

} // namespace testability

#endif // TESTABILITY_TESTABILITY_TYPES_H
