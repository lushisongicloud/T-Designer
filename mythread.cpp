#include "mythread.h"
#include <qdebug.h>
extern void CommandAndUpdateCandidateConflictList();
extern void SolveByType(int Type);
Mythread::Mythread(QObject *parent,int TaskType):
    QThread(parent){
    this->TaskType=TaskType;
}

void Mythread::stop() {
    stopped = true;
}

void Mythread::run() {
    stopped = false;
    if(TaskType==0) CommandAndUpdateCandidateConflictList();
    if(TaskType==1) SolveByType(0);
    if(TaskType==2) SolveByType(1);
    if(TaskType==3) SolveByType(2);
    if(TaskType==0) emit CommandThreadEnd();
}
