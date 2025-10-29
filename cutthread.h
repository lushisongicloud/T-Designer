#ifndef CUTTHREAD_H
#define CUTTHREAD_H

#include <QThread>
#include <QVector>
#include <QTime>
#include <QDebug>
#include <QQueue>
#include "graphlisthead.h"

class CutThread :public QThread
{
    Q_OBJECT
public:
    CutThread(int TaskType);        //0代表发任务管理员，1代表计算工人

    ~CutThread();

    void SetTotleCount(int count) {this->TotolCount = count;}

    void SetNumList(QList<QVector<int>>* list){num_list = list;}

    void SetVNodes(VNode* v){vexs = v;}

    void SetThreadCount(int count);

    void SetWorkNumCount(int num){work_num_count = num; WorkResult.fill(false,num);}

    QList<QVector<int>> copy_num_list;  //最终结果
    QList<QVector<int>> original_copy_num_list; // 原始数据

//    bool WorkResult;

protected:
    void run() Q_DECL_OVERRIDE;  //线程任务

private:

    //发牌员用的
    int TaskType;

    int TotolCount;

    int StartPos;

    int ThreadCount;

    VNode* vexs;

    QList<QVector<int>>* num_list;

    QVector<CutThread*> work_thread;

    //工作线程用的
    int work_num_count;
    QQueue<int> vexQ;
    QVector<bool> visit;
    QVector<bool> WorkResult;


private:
    void DistributeTasks();     //分配任务
    void ProcessResult();      //计算完一次，处理结果

    void WorkTasks();           //计算任务
    void WrokTasksProcessResult();

    bool _IsAComboConnect(const QVector<int>& num_list);                       //判断一个组合是否是连接在一起的

};

#endif // CUTTHREAD_H
