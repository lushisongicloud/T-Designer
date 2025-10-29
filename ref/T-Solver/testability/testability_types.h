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
    QString predicate;       // SMT (assert ...)
    QString negatedPredicate; // SMT (assert ...)
    QString note;            // 描述来源/区间信息
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
    QStringList inputAssertions;   // 输入约束
    QStringList faultAssertions;   // 故障特定约束（如执行器取反）
    QList<ComponentOverride> overrides; // 器件故障注入
    QString constraintIntegrity;
    QStringList linkElements;
    QStringList relatedComponents;
    QHash<QString, QSet<QString>> offlineModeMap;
    QStringList actuatorAssertions;
    QSet<QString> dependencyClosure;
    bool enabled = true;
};

struct DetectabilityResult {
    bool normalSat = false;   // 正常模型 + Fail_t 是否 SAT
    bool faultSat = false;    // 故障模型 + P_t 是否 SAT
    bool normalPassSat = false; // 正常模型 + P_t 是否 SAT
    bool faultFailSat = false;  // 故障模型 + Fail_t 是否 SAT
    bool guaranteed = false;    // 是否满足 guaranteed 判定
    bool detected = false;      // 当前模式下是否判为可检测
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

    QString prefixCode; // 变量声明 + 连接约束
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
    QVector<QVector<DetectabilityResult>> cells; // 行=故障，列=测试
};

} // namespace testability

#endif // TESTABILITY_TESTABILITY_TYPES_H
