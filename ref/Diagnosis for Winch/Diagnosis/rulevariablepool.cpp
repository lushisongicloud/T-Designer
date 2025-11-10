#include "rulevariablepool.h"


#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

RuleVariablePool::RuleVariablePool()
{

}

bool RuleVariablePool::SetVariableValue(QString VariableName, int Value)
{
    //若变量池不包含该变量则返回false
    if(m_Signals.find(VariableName)==m_Signals.end())
        return false;

    //若变量的类型不为INT或ENUM返回false
    if(m_Signals[VariableName].valueType!="INT"&&m_Signals[VariableName].valueType!="ENUM")
        return false;

    m_Signals[VariableName].LastValue=m_Signals[VariableName].value;

    //按照变量类型给联合体的变量赋值
    if(m_Signals[VariableName].valueType=="INT")
    m_Signals[VariableName].value.INT = Value;

    if(m_Signals[VariableName].valueType=="ENUM")
    m_Signals[VariableName].value.ENUM = Value;

    //将变量是否更新定为true
    m_Signals[VariableName].isChecked = true;


    return true;
}

bool RuleVariablePool::SetVariableValue(QString VariableName, double Value)
{
    //若变量池不包含该变量则返回false
    if(m_Signals.find(VariableName)==m_Signals.end())
        return false;

    //若变量的类型不为DOUBLE返回false
    if(m_Signals[VariableName].valueType!="DOUBLE")
        return false;

    m_Signals[VariableName].LastValue=m_Signals[VariableName].value;
    //按照变量类型给联合体的变量赋值
    m_Signals[VariableName].value.DOUBLE = Value;

    //将变量是否更新定为true
    m_Signals[VariableName].isChecked = true;

    return true;
}

bool RuleVariablePool::SetVariableValue(QString VariableName, bool Value)
{
    //若变量池不包含该变量则返回false
    if(m_Signals.find(VariableName)==m_Signals.end())
        return false;

    //若变量的类型不为BOOL返回false
    if(m_Signals[VariableName].valueType!="BOOL")
        return false;

    //m_Signals[VariableName].LastValue=m_Signals[VariableName].value;
    //按照变量类型给联合体的变量赋值
    m_Signals[VariableName].value.BOOL = Value;

    //将变量是否更新定为true
    m_Signals[VariableName].isChecked = true;

    //qDebug()<<"m_Signals["<<VariableName<<"]="<<Value;
    return true;
}

bool RuleVariablePool::InitVariableVector()
{
    //检测是否给数据库指针赋值
    if(m_Database==nullptr)
        return false;

    //获取数据库所有信号
    QVector<DataBase::Str_Signal> Signals =  m_Database->SelectSignalsInforFromSignalBaseTable("","ALL");

    //清空原信号MAP
    m_Signals.clear();

    //初始化信号池
    for(int i=0;i<Signals.size();i++){
        m_Signals[Signals[i].Name].Name = Signals[i].Name;
        m_Signals[Signals[i].Name].isChecked = false;
        m_Signals[Signals[i].Name].signalType = Signals[i].SignalType;
        m_Signals[Signals[i].Name].unit = Signals[i].Unit;
        m_Signals[Signals[i].Name].valueType = Signals[i].DataType;
        m_Signals[Signals[i].Name].SignalPos = Signals[i].SignalPos;
        m_Signals[Signals[i].Name].Detail = Signals[i].Detail;
        m_Signals[Signals[i].Name].MultiPos = Signals[i].MultiPos;
        m_Signals[Signals[i].Name].Note = Signals[i].Note;
        m_Signals[Signals[i].Name].AnalysisResult =Signals[i].AnalysisResult;
        m_Signals[Signals[i].Name].DisplayPosx =Signals[i].DisplayPosx;
        m_Signals[Signals[i].Name].DisplayPosy =Signals[i].DisplayPosy;
        //qDebug()<<m_Signals[Signals[i].Name].SignalPos;
    }
    return true;
}

void RuleVariablePool::SetAllUnchecked()
{
    //设置所有变量为未定
    //for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
    //    m.value().isChecked = false;
    //}

    //设置当前变量池步骤为0
    CurrentStep = 0;
}

void RuleVariablePool::SetSignalRecordID(QString VariableName,int RecordID)
{
    m_Signals[VariableName].RecordID = RecordID;
}

bool RuleVariablePool::isContainVariable(QString VariableName)
{
    return m_Signals.find(VariableName)!=m_Signals.end();
}

DataBase::Signal RuleVariablePool::GetVariable(QString VariableName)
{
    DataBase::Signal ans;
    if(m_Signals.find(VariableName)!=m_Signals.end()){
        ans = m_Signals[VariableName];
    }
    return ans;
}

QVector<DataBase::Signal> RuleVariablePool::GetWarnningError()
{
    QVector<DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if(m.value().signalType=="报警信号"&&m.value().valueType=="BOOL"&&m.value().value.BOOL == true){
            ans.push_back(m.value());
        }
    }
    return ans;
}

QVector<DataBase::Signal> RuleVariablePool::GetLastWarnningError()
{
    QVector<DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if(m.value().signalType=="报警信号"&&m.value().valueType=="BOOL"&&m.value().LastValue.BOOL == true){
            ans.push_back(m.value());
        }
    }
    return ans;
}

QVector<DataBase::Signal> RuleVariablePool::GetFaliureError()
{
    QVector<DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if(m.value().signalType=="故障信号"&&m.value().valueType=="BOOL"&&m.value().value.BOOL == true){
            ans.push_back(m.value());
        }
    }
    return ans;
}

QVector<DataBase::Signal> RuleVariablePool::GetLastFaliureError()
{
    QVector<DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if(m.value().signalType=="故障信号"&&m.value().valueType=="BOOL"&&m.value().LastValue.BOOL == true){
            ans.push_back(m.value());
        }
    }
    return ans;
}

//寻找有变化的报警或故障
QVector<DataBase::Signal> RuleVariablePool::FindChangeSignal()
{
    QVector<DataBase::Signal> ans;

    for(auto m=m_Signals.begin();m!=m_Signals.end();m++){
        //qDebug()<<"m_Signals"<<m.value().value.BOOL<<m.value().LastValue.BOOL;
        if((m.value().signalType=="故障信号")&&(m.value().valueType=="BOOL")&&(m.value().value.BOOL!=m.value().LastValue.BOOL))
            ans.push_back(m.value());
        if((m.value().signalType=="报警信号")&&(m.value().valueType=="BOOL")&&(m.value().value.BOOL!=m.value().LastValue.BOOL))
            ans.push_back(m.value());
        m.value().LastValue=m.value().value;
    }
    return ans;
}

//寻找实时报警或故障
QVector<DataBase::Signal> RuleVariablePool::FindRealtimeAlarmOrFaliure()
{
    QVector<DataBase::Signal> ans;

    for(auto m=m_Signals.begin();m!=m_Signals.end();m++){
        //qDebug()<<"m_Signals"<<m.value().value.BOOL<<m.value().LastValue.BOOL;
        if(m.value().signalType=="故障信号"&&m.value().valueType=="BOOL"&&m.value().value.BOOL==true)
            ans.push_back(m.value());
        if(m.value().signalType=="报警信号"&&m.value().valueType=="BOOL"&&m.value().value.BOOL==true)
            ans.push_back(m.value());
    }
    return ans;
}

QMap<QString,DataBase::Signal> RuleVariablePool::GetBasicSignalMap()
{
    QMap<QString,DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if(m.value().signalType=="基础信号"){
            ans[m.key()] = m.value();
        }
    }
    return ans;
}

QVector<DataBase::Signal> RuleVariablePool::GetBasicSignalVector()
{
    QVector<DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if(m.value().signalType=="基础信号"){
            ans.push_back(m.value());
        }
    }
    return ans;
}

QVector<DataBase::Signal> RuleVariablePool::GetAlarmSignalVector(QString SignalPos)
{
    QVector<DataBase::Signal> ans;
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        if((m.value().signalType=="报警信号"||m.value().signalType=="故障信号")&&(m.value().SignalPos==SignalPos)){
            ans.push_back(m.value());
        }
    }
    return ans;
}

void RuleVariablePool::show()
{
    for(auto m = m_Signals.begin();m!=m_Signals.end();m++){
        qDebug()<<m.key();
        if(m.value().valueType=="INT"){
            qDebug()<<m.value().value.INT;
        }
        if(m.value().valueType=="ENUM"){
            qDebug()<<m.value().value.ENUM;
        }
        if(m.value().valueType=="BOOL"){
            qDebug()<<m.value().value.BOOL;
        }
        if(m.value().valueType=="DOUBLE"){
            qDebug()<<m.value().value.DOUBLE;
        }
        qDebug()<<"isChecked:"<<m.value().isChecked<<endl;
    }
}
