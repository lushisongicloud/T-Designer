// worker.h

#ifndef WORKER_H
#define WORKER_H

#include <QObject>
#include "BO/componententity.h"

class SystemEntity;  // Forward declaration

class Worker : public QObject {
    Q_OBJECT
private:
    SystemEntity& systemEntity;
public:
    Worker(SystemEntity& entity);

public slots:
    void workerSolve(const QString& modelDescription, const QList<TestItem>& testItemList, int truncateMode);
};

#endif // WORKER_H
