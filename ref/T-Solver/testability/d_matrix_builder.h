#ifndef TESTABILITY_D_MATRIX_BUILDER_H
#define TESTABILITY_D_MATRIX_BUILDER_H

#include <QMap>
#include <QHash>
#include <QMutex>

#include "BO/systementity.h"
#include "testability/testability_types.h"
#include "testability/smt_facade.h"

namespace testability {

class DMatrixBuilder
{
public:
    explicit DMatrixBuilder(SystemEntity *entity);

    void setFunctionInfoMap(const QMap<QString, FunctionInfo> &map);

    QVector<FaultDefinition> collectFunctionFaults() const;
    QVector<TestDefinition> collectFunctionTests() const;
    QVector<TestDefinition> collectModeTests(const SmtFacade &smt) const;
    QVector<TestDefinition> collectSignalTests(const SmtFacade &smt,
                                              const DMatrixBuildOptions &options) const;

    DetectabilityResult detectability(const FaultDefinition &fault,
                                      const TestDefinition &test,
                                      DetectMode mode,
                                      const SmtFacade &smt,
                                      const DMatrixBuildOptions &options,
                                      int timeoutMs = -1) const;

    DMatrixBuildResult buildDMatrix(const QVector<FaultDefinition> &faults,
                                    const QVector<TestDefinition> &tests,
                                    const SmtFacade &smt,
                                    const DMatrixBuildOptions &options) const;

    bool exportDMatrix(const DMatrixBuildResult &result,
                       const QString &modelName,
                       const DMatrixBuildOptions &options,
                       const QString &outputDir = QString(),
                       QString *csvPath = nullptr,
                       QString *metadataPath = nullptr) const;

private:
    QStringList toAssertions(const QList<TestItem> &items) const;
    QString createRangePredicate(const QString &expression,
                                 double lower,
                                 double upper) const;
    QString formatDouble(double value) const;
    bool isSatCached(const SmtFacade &smt,
                     const QString &code,
                     int timeoutMs) const;
    void clearSatCache() const;

    SystemEntity *systemEntity = nullptr;
    QMap<QString, FunctionInfo> functionInfoMap;
    mutable QMutex satCacheMutex;
    mutable QHash<QString, bool> satCache;
};

} // namespace testability

#endif // TESTABILITY_D_MATRIX_BUILDER_H
