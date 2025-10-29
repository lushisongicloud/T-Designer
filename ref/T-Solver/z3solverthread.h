#ifndef Z3SOLVERTHREAD_H
#define Z3SOLVERTHREAD_H

#include <QThread>
#include <QDebug>
#include <QTime>
#include <QMutex>
#include <z3++.h>
#include "BO/componententity.h"
#include <QRunnable>


class Z3SolverThread:public QThread
{

    Q_OBJECT
public:
    explicit Z3SolverThread(QObject *parent = 0);
    ~Z3SolverThread();

    bool z3Solve(const QString &logic, int timeoutMs = -1);

    bool isSuperSet(QList<ComponentEntity> set, QList<ComponentEntity> superSet);

    QString code;

    bool ans;


signals:
    void compute_finish();

protected:
    //QThread的虚函数
    //线程处理函数
    //不能直接调用，通过start()间接调用
    void run();
};
#endif // Z3SOLVERTHREAD_H
