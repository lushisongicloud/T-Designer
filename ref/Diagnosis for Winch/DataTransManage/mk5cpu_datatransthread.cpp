#include "mk5cpu_datatransthread.h"
#include <QDebug>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern RuleVariablePool m_RuleVariablePool;
extern QMutex mutex;

MK5CPU_DataTransThread::MK5CPU_DataTransThread()
{
}

void MK5CPU_DataTransThread::stopThread()//停止线程
{
    m_stop=true;
}

void MK5CPU_DataTransThread::run()//线程运行主程序
{
    m_stop=false;//启动线程时令m_stop=false
    while(!m_stop)//循环主体
    {
        //延时200ms
        msleep(200);

        //产生随机数
        qsrand(static_cast<unsigned int>(QTime(0, 0, 0).secsTo(QTime::currentTime())));
        MK5CPU = (qrand() % 2);

        //加锁实现对m_RuleVariablePool写操作的线程互斥
        mutex.lock();
        //变量控制实现5个写线程和1个诊断线程的顺序执行，即当m_RuleVariablePool.GetCurrentStep()==4时本线程进行写操作，写完之后将Step置5
        if(m_RuleVariablePool.GetCurrentStep()==4){
            //qDebug()<<"GetCurrentStep=4";
            m_RuleVariablePool.SetVariableValue("MK5CPU",MK5CPU);
            m_RuleVariablePool.SetCurrentStep(5);
            qDebug()<<"SetCurrentStep(5)";
            //qDebug()<<"MK5CPU_DataTransThread  "<<QThread::currentThreadId()<<"  Set Value "<<MK5CPU;
        }
        mutex.unlock();
    }
    exit(0);//退出线程循环
}
