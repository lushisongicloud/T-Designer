#include "diagnosis.h"
#include <QDebug>
#include "rulepool.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern RuleVariablePool m_RuleVariablePool;
extern RulePool m_RulePool;
extern QMutex mutex;

Diagnosis::Diagnosis()
{

}

void Diagnosis::stopThread()//停止线程
{
    m_stop=true;
}

void Diagnosis::run()//线程运行主程序
{
    m_stop=false;//启动线程时令m_stop=false
    while(!m_stop)//循环主体
    {
        msleep(180);
        mutex.lock();
        //if(m_RuleVariablePool.GetCurrentStep()==5){
            //qDebug()<<"GetCurrentStep=5";
            //qDebug()<<"Diagnosis  诊断开始 "<<QThread::currentThreadId();
            //m_RuleVariablePool.show();

            //发射基础信号值更新信号用于更新界面和图像数据显示
            emit newBasicSignalUpdate();

            //启动规则循环检测
           m_RulePool.StartRuleDetection(m_RuleVariablePool);

            //打印检测结果
            //m_RuleVariablePool.show();

            //QVector<DataBase::Signal> FaliureError = m_RuleVariablePool.GetFaliureError();
            //QVector<DataBase::Signal> LastFaliureError = m_RuleVariablePool.GetFaliureError();

            //QVector<DataBase::Signal> WarnningError = m_RuleVariablePool.GetWarnningError();
            //QVector<DataBase::Signal> LastWarnningError = m_RuleVariablePool.GetWarnningError();
            QVector<DataBase::Signal> signal = m_RuleVariablePool.FindChangeSignal();
            if(signal.size()>0)  emit  newFaliureError(signal); //检测警告或故障的变化情况


            /*
            if(FaliureError.size()!=0||WarnningError.size()!=0){

                //停止检测
                //m_RuleVariablePool.SetCurrentStep(6);

                //触发故障报警
                if(FaliureError.size()!=0){
                    //发射故障报警信号
                    emit  newFaliureError();
                    qDebug()<<"检测有故障";
                }

                //触发警告报警
                if(WarnningError.size()!=0){
                    //发射预警报警信号
                    emit  newWarnningError();
                    qDebug()<<"检测有警告";
                }
            }
            */

            //一轮循环检测完之后，设置所有规则未检测，以进行下一轮检测
            m_RulePool.SetAllRuleUnused();
            //设置所有变量未检测,以进行下一轮检测
            m_RuleVariablePool.SetAllUnchecked();

            //测试用，将停止线程循环检测
            //m_RuleVariablePool.SetCurrentStep(6);

            //qDebug()<<"诊断解析结束"<<endl;
        //}
        mutex.unlock();

    }
    exit(0);//退出线程循环
}
