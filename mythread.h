#ifndef MYTHREAD_H
#define MYTHREAD_H
#include <QThread>
#include "BO/componententity.h"
#include <z3++.h>
#include <QTime>
#include "z3solverthread.h"
class Mythread:public QThread
{
    Q_OBJECT
public:
    Mythread(QObject *parent,int TaskType);
    int TaskType;
protected:
    virtual void run();
    virtual void stop();
private:
    volatile bool stopped;
signals:
    void CommandThreadEnd();
};

#endif // MYTHREAD_H



