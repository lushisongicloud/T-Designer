#ifndef RULEVARIABLEPOOL_H
#define RULEVARIABLEPOOL_H

#include "myqsqldatabase.h"

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-9
 * Description:故障诊断变量池
**************************************************/

class RuleVariablePool
{
public:
    RuleVariablePool();

private:

    //变量池
    QMap<QString,DataBase::Signal> m_Signals;

    //数据库指针
    myQSqlDatabase *m_Database = nullptr;

    //为了使各线程有序
    int CurrentStep = 0;

public:

    //设置变量池当前所在步骤
    void SetCurrentStep(int cur){CurrentStep = cur;}

    //获取变量池当前所在步骤
    int GetCurrentStep(){return CurrentStep;}

    //设置数据库指针
    void SetDatabase(myQSqlDatabase *TMATE_Database){m_Database = TMATE_Database;}

    //设置INT或ENUM类型变量的值
    bool SetVariableValue(QString VariableName,int Value);

    //设置DOUBLE类型的值
    bool SetVariableValue(QString VariableName,double Value);

    //设置BOOL类型的值
    bool SetVariableValue(QString VariableName,bool Value);

    //设置报警/故障对应的信号ID
    void SetSignalRecordID(QString VariableName,int RecordID);

    //初始化中间变量、报警变量和故障变量
    bool InitVariableVector();

    //设置所有变量未初始化
    void SetAllUnchecked();

    //检测变量池是否包含变量
    bool isContainVariable(QString VariableName);

    //获取所有变量信息
    DataBase::Signal GetVariable(QString VariableName);

    //获取报警信息
    QVector<DataBase::Signal> GetWarnningError();

    //获取故障信息
    QVector<DataBase::Signal> GetFaliureError();

    //获取上一次报警信息
    QVector<DataBase::Signal> GetLastWarnningError();

    //获取上一次故障信息
    QVector<DataBase::Signal> GetLastFaliureError();

    //寻找实时报警或故障
    QVector<DataBase::Signal> FindRealtimeAlarmOrFaliure();

    //获取基础信号值
    QVector<DataBase::Signal> GetBasicSignalVector();

    //获取基础信号值
    QMap<QString,DataBase::Signal> GetBasicSignalMap();

    //打印所有变量值
    void show();

    //寻找有变化的报警或故障
    QVector<DataBase::Signal> FindChangeSignal();

    //寻找分机对应的报警变量列表
    QVector<DataBase::Signal> GetAlarmSignalVector(QString SignalPos);

};

#endif // RULEVARIABLEPOOL_H
