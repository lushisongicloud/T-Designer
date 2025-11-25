#ifndef BO_TEST_DMATRIXSERVICE_H
#define BO_TEST_DMATRIXSERVICE_H

#include <QSqlDatabase>
#include <QString>
#include <QVector>

#include "testability/d_matrix_builder.h"
#include "testability/testability_types.h"

class SystemEntity;

struct DMatrixLoadResult {
    bool found = false;
    testability::DMatrixBuildResult result;
    testability::DMatrixBuildOptions options;
    QString csvPath;
    QString metadataPath;
    QString stateJson;
};

class DMatrixService
{
public:
    explicit DMatrixService(const QSqlDatabase &db);

    bool ensureTable() const;

    DMatrixLoadResult loadLatest(int containerId,
                                 const QString &projectDir = QString(),
                                 const QString &projectName = QString()) const;

    bool saveResult(int containerId,
                    const testability::DMatrixBuildResult &result,
                    const testability::DMatrixBuildOptions &options,
                    const QString &csvPath,
                    const QString &metadataPath,
                    const QString &stateJson = QString()) const;

    bool saveState(int containerId,
                   const QString &stateJson,
                   const QString &metadataPath = QString(),
                   const QString &csvPath = QString()) const;

    bool buildAndPersist(SystemEntity *systemEntity,
                         const QString &systemDescription,
                         int containerId,
                         const QString &projectDir,
                         const QString &projectName,
                         const testability::DMatrixBuildOptions &options,
                         testability::DMatrixBuildResult *outResult,
                         QString *metadataPathOut,
                         QString *csvPathOut,
                         QString *errorMessage) const;

    static QString serializeState(const QVector<bool> &faultEnabled,
                                  const QVector<bool> &testEnabled);
    static bool parseState(const QString &json,
                           QVector<bool> *faultEnabled,
                           QVector<bool> *testEnabled);

private:
    testability::DMatrixBuildOptions parseOptions(const QString &json) const;
    QString serializeOptions(const testability::DMatrixBuildOptions &options) const;
    bool parseMetadata(const QString &json, testability::DMatrixBuildResult *result) const;
    QString serializeMetadata(const testability::DMatrixBuildResult &result,
                              const testability::DMatrixBuildOptions &options,
                              const QString &csvPath,
                              const QString &modelName,
                              const QString &metadataPath) const;
    QString readFile(const QString &path) const;
    QString relativeToProject(const QString &projectDir, const QString &path) const;
    QString absoluteFromProject(const QString &projectDir, const QString &path) const;
    void deactivateOld(int containerId) const;
    QString loadFunctionDescriptionFromModels(const QString &projectName) const;
    QMap<QString, FunctionInfo> loadFunctionInfoMap(const QString &projectName) const;

    QSqlDatabase m_db;
};

#endif // BO_TEST_DMATRIXSERVICE_H
