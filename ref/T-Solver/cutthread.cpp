#include "cutthread.h"

CutThread::CutThread(int TaskType)
{
    this->TaskType = TaskType;
    StartPos = 0;
}

CutThread::~CutThread()
{
    for(int i=0; i<ThreadCount; i++)
        delete[] work_thread[i];
}


void CutThread::SetThreadCount(int count)
{
    ThreadCount = count;
    for(int i=0; i<count; i++)
    {
        CutThread* new_thread = new CutThread(1);
        new_thread->SetNumList(num_list);
        new_thread->SetVNodes(vexs);
        work_thread.append(new_thread);
    }
}

void CutThread::run()
{//线程任务
    if(TaskType==0) DistributeTasks();
    if(TaskType==1) WorkTasks();

//    if(TaskType==0) emit CommandThreadEnd();

    exit();
}

void CutThread::WorkTasks()
{
    QTime timer;
    timer.restart();

    int origin = work_num_count;
    for(int i=0; i<work_num_count; i++)
    {

        if(!_IsAComboConnect(original_copy_num_list.at(i)))
        {
            WorkResult[i] = false;
        }
        else
            WorkResult[i] = true;

    }

    WrokTasksProcessResult();

    qDebug()<<"thread_time"<<origin<<timer.elapsed();

}

void CutThread::WrokTasksProcessResult()
{
    copy_num_list.clear();

    for(int i=0; i<work_num_count; i++)
    {
        if(WorkResult.at(i))
            copy_num_list.append(std::move(original_copy_num_list.at(i)));
    }

    original_copy_num_list.clear();
    WorkResult.clear();
}

void CutThread::ProcessResult()
{
    num_list->clear();
    int total_count = 0;

    for(int i=0; i<ThreadCount; i++)
        total_count = total_count + work_thread[i]->copy_num_list.count();

    num_list->reserve(total_count);

    for(int i=0; i<ThreadCount; i++)
    {
        num_list->append(std::move(work_thread[i]->copy_num_list));
        work_thread[i]->copy_num_list.clear();
    }
}

void CutThread::DistributeTasks()
{
    bool isFirst = true;
    QTime timer;
    while(true)
    {
        int piece = TotolCount/ThreadCount;

        if(isFirst)
        {
            timer.restart();
            for(int i=0; i<ThreadCount; i++)
            {

                if(i!=ThreadCount-1)
                {
                    work_thread[i]->SetWorkNumCount(piece);
                    work_thread[i]->original_copy_num_list.reserve(piece);
                    for(int j=0; j<piece; j++)
                        work_thread[i]->original_copy_num_list.append(num_list->at(StartPos+j));
                    work_thread[i]->start();
                    StartPos = piece + StartPos;
                }
                else
                {
                    work_thread[i]->SetWorkNumCount(TotolCount-StartPos);
                    work_thread[i]->original_copy_num_list.reserve(TotolCount-StartPos);

                    for(int j=0; j<TotolCount-StartPos; j++)
                        work_thread[i]->original_copy_num_list.append(num_list->at(StartPos+j));
                    work_thread[i]->start();
                }

            }

            qDebug()<<"allocate thread"<<timer.elapsed();
            isFirst = false;
            timer.restart();
        }


        //有一个没有停止就跳出
        bool isAllStop = false;
        for(int i=0; i<ThreadCount; i++)
        {
            if(!work_thread[i]->isFinished())
                break;
            if(i == ThreadCount-1)
                isAllStop = true;
        }

        if(isAllStop)
        {
            qDebug()<<"work_time"<<timer.elapsed();
            timer.restart();
            ProcessResult();
            qDebug()<<"back_process_time"<<timer.elapsed();
            break;
        }
    }
}

bool CutThread::_IsAComboConnect(const QVector<int>& num_list)
{
    int original_count = num_list.count();
    if(original_count < 2)
        return true;

    visit.fill(false, original_count);

    //3.1.初始化队列
//    QQueue<int> vexQ;
    //3.2.访问开始顶点，并标记访问、入队
    vexQ.enqueue(num_list.at(0));
    visit[0] = true;
    //3.3.出队，并遍历邻接顶点（下一层次），访问后入队
    ArcNode * p = nullptr;
    int adjVex = 0;
    int index = 0;
    int visit_node_count = 1;

    //遍历邻接顶点
    bool isFindOne = false;

    while (!vexQ.isEmpty())
    {
        index = vexQ.dequeue();
        p = this->vexs[index].first;
        isFindOne = false;

        while (p != nullptr)
        {
            adjVex = p->adjVex;
            for(int m=0; m<original_count; m++)
            {
                if(adjVex == num_list[m])
                {
                    isFindOne = true;
                    if(!visit.at(m))
                    {
                        visit[m] =true;
                        visit_node_count++;
                        vexQ.enqueue(adjVex);
                        break;
                    }
                    else
                        break;
                }
            }

            p = p->next;

        }

        if(!isFindOne)      //如果一个都没找到，说明有个点所连接的点全都不在num_list中，直接跳出false
            return false;

//        if(visit_node_count == original_count)
//            return true;
    }


    if(visit_node_count != original_count)
        return false;


    return true;

}
