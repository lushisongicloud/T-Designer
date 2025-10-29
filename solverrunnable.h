#ifndef SOLVERRUNNABLE_H
#define SOLVERRUNNABLE_H

#include <QMutex>
#include <QRunnable>
#include "z3solverthread.h"

bool z3Solve(QString logic);

class SolverRunnable : public QRunnable
{
public:
    SolverRunnable(const QString &code, int index, QVector<int> &excludedIndexes, QMutex &mutex);

    void run() override;

private:
    QString m_code;
    int m_index;
    QVector<int> &m_excludedIndexes;
    QMutex &m_mutex;
};

#endif // SOLVERRUNNABLE_H
