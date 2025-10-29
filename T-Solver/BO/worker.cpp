#include "worker.h"
#include "systementity.h"

Worker::Worker(SystemEntity& entity) : systemEntity(entity) {}

void Worker::workerSolve(const QString& modelDescription, const QList<TestItem>& testItemList, int truncateMode) {
    systemEntity.completeSolve(modelDescription, testItemList, truncateMode);
}
