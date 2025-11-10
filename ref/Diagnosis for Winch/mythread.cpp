#include "mythread.h"
#include <qdebug.h>
#include <QDateTime>
#include <qfile.h>
#include <qdir.h>
#include "Data_Save.h"
Mythread::Mythread(QObject *parent,int ThreadType):
    QThread(parent){

  m_ThreadID=ThreadType;
}

void Mythread::stop() {
    stopped = true;

}


void Mythread::run() {
    stopped = true;
    if(m_ThreadID == 0)
    {
        StartRevUDP();
        while(1)
        {
          RevUdp();
          msleep(200);
        }
    }
    if (m_ThreadID == 1)//PLC SAVE THREAD
            SaveThread();
}
