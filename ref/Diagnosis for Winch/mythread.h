#ifndef MYTHREAD_H
#define MYTHREAD_H
#include <QThread>
#include "DataTransManage/mk2cpu_datatransthread.h"
class Mythread:public QThread
{
    Q_OBJECT
public:
    Mythread(QObject *parent,int ThreadType);


protected:
    virtual void run();
    virtual void stop();
private:
    volatile bool stopped;
    int m_ThreadID;// 0:udp
};

#endif // MYTHREAD_H



