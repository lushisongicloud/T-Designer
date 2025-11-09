#include "detector2_datatransthread.h"
#include <QDebug>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern RuleVariablePool m_RuleVariablePool;
extern QMutex mutex;

Detector2_DataTrans::Detector2_DataTrans(myQSqlDatabase *TMATE_Database):
    m_Database(TMATE_Database)
{

}

void Detector2_DataTransThread::stopThread()//停止线程
{
    m_stop=true;
}

void Detector2_DataTransThread::run()//线程运行主程序
{
    m_stop=false;//启动线程时令m_stop=false
    while(!m_stop)//循环主体
    {
        //延时200ms
        msleep(200);

        //产生随机数
        qsrand(static_cast<unsigned int>(QTime(0, 0, 0, 0).secsTo(QTime::currentTime())));
        Derect2 = static_cast<double>((qrand() % 100))/(static_cast<double>((qrand() % 50))+50);//产生0-2的随机数

        //加锁实现对m_RuleVariablePool写操作的线程互斥
        mutex.lock();
        //变量控制实现5个写线程和1个诊断线程的顺序执行，即当m_RuleVariablePool.GetCurrentStep()==1时本线程进行写操作，写完之后将Step置2
        if(m_RuleVariablePool.GetCurrentStep()==1){
            //qDebug()<<"GetCurrentStep=1";
            m_RuleVariablePool.SetVariableValue("Detector2",Derect2);
            m_RuleVariablePool.SetCurrentStep(2);
            //qDebug()<<"Detector2_DataTransThread  "<<QThread::currentThreadId()<<"  Set Value "<<Derect2;
        }
        mutex.unlock();
    }
    exit(0);//退出线程循环
}
