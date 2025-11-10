#ifndef MYQSQLDATABASE_H
#define MYQSQLDATABASE_H

#include <QtSql>
#include <QTableWidget>

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:包含数据库的所有操作函数和所有结构变量定义
**************************************************/

namespace DataBase{

typedef struct{
    int Operating_ID;//用户ID
    QString Operating_user; //用户名
    QString Operating_PSW; //用户密码
    int Operating_limit;//操作权限
    QDateTime  LoginTime;//上次登录时间
}Str_account;

typedef struct{
    QString Name;//连接名称
    QString IP;//连接IP
    QString Port;//连接端口
}Str_communication;

typedef struct{
    QString Name = "";//变量名称
    QString SignalType = "中间信号";//信号类型
    QString DataType = "BOOL";//变量类型
    QString Unit = "NULL";//变量单位
    QString SignalPos ="";
    QString Note = "";
    QString Detail = "";
    QStringList MultiPos;
    QStringList AnalysisResult;
    int DisplayPosx=0;
    int DisplayPosy=0;

}Str_Signal;

typedef struct{
    QString Name = "";//规则名称
    bool State = true;//规则状态
    QString Editor = "";//规则编辑人
    QString Description = "";//规则描述
    QString Condition = "";//规则条件
    QString ResultThen = "";//规则Then结果
    QString ResultElse = "";//规则else结果
//    QString Position = "";//报警/提示位置
//    QString ShowStr = "";//显示的报警内容
    double DurTime =0;
    QString RulePos = "";
}Str_Rule;

typedef struct{
    int ID=0;
    QString Name = "";//规则名称
    bool State = false;//规则状态
    QString Editor = "";//规则编辑人
    QString Description = "";//规则描述
    QString TaskParaList= "";
    QString WarnParaList= "";
}Str_WarnRule;

typedef union {
     int INT;//INT类型变量值
     double DOUBLE;//DOUBLE类型变量值
     bool BOOL;//BOOLT类型变量值
     int ENUM;//ENUM类型变量值
}union_value;

typedef struct{
    QString Name = "";//信号名称
    union_value value;//信号值
    QString signalType = "中间信号";//信号类型
    QString valueType = "BOOL";//变量类型
    QString unit = "NULL";//单位
    QString SignalPos ="";
    QString Note = "";
    QString Detail = "";
    QStringList MultiPos;
    bool isChecked = false;//是否确定
    union_value LastValue;//上一次信号值
    int RecordID;//报警、故障记录ID
    QDateTime RecordStartDateTime;
    QDateTime RecordFinishDateTime;
    QString MultiPosMannulSet;
    QStringList AnalysisResult;
    int DisplayPosx=0;
    int DisplayPosy=0;
}Signal;

typedef struct{
    QString WarnTaskName = "";//信号名称
    QString TaskPara = "";//任务标志变量及值  参数1=值,参数2=值，。。。
    QString WarnPara = "";//预警变量及值  参数1=值,参数2=值，。。。
    int RecordID;//报警、故障记录ID
    QDateTime RecordStartDateTime;
    QDateTime RecordFinishDateTime;
}WarnRecord;
}

class myQSqlDatabase
{
private:
    QString m_strFilePath = "C:/Users/KR510/Desktop/ControllablePitchPropeller.db3";//数据库文件

    QSqlDatabase database;//TMATE数据库链接
    QSqlQuery qsQuery;//TMATE数据库选择模型

    QString SelectSqlStatement;//选择语句
    //QString InsertSqlStatement;//插入语句
    QString UpdateSqlStatement;//更新语句
    QString DeleteSqlStatement;//删除语句
private:

    //数据库连接函数
    void TMATEconnect();

public:
    myQSqlDatabase(QString FilePath);

    //获取操作SQL语句的类指针
    QSqlQuery *getQSqlQuery(){return &qsQuery;}

    //返回数据库是否正确连接
    bool isopen(){return database.isOpen();}

    //返回数据库最后一次执行错误
    QSqlError Error(){return database.lastError();}

    //根据连接名查询连接IP和Port,若不存在该连接名则返回DataBase::Str_communication结构中Name=""
    DataBase::Str_communication SelectCommunicationInforFromCommunicationConfigTable(QString CommunicationName);

    //更新连接名对应的连接IP和Port,若不存在该连接名则返回false
    bool UpdateCommunicationInforToCommunicationConfigTable(DataBase::Str_communication Communication);


    ///////////////////////////////////////////////////
    /////AccountTable  操作相关
    ///////////////////////////////////////////////////

    //根据用户名和权限级别查询账号并返回结果  level=0查询所有结果，level=1为管理员，level=2为普通用户,其中user为模糊查询
    QVector<DataBase::Str_account> SelectAccountsInforFromAccountTable(QString user,int level);

    //根据用户名精确查询账户
    DataBase::Str_account SelectAccountFromAccountTable(QString user);

    //根据用户名查询用户密码，若未查询到则返回""
    QString SelectPasswordsFromAccountTable(QString user);

    //修改用户名对应的用户密码
    bool UpdateAccountPasswords(QString UserName,QString Passwords);

    //删除用户名对应的账户
    bool DeleteAccountFromAccountTable(QString UserName);

    //查询账户是否存在
    bool IsAccountExist(QString UserName);

    //更新账户权限
    bool UpdateAccountLimit(QString UserName,int Limit);

    //添加账户
    bool InsertAccountToAccounttable(DataBase::Str_account account);

    ///////////////////////////////////////////////////
    /////SignalBaseTable  操作相关
    ///////////////////////////////////////////////////

    //根据变量名和信号类型查询信号并返回结果,其中Name为模糊查询
    QVector<DataBase::Str_Signal> SelectSignalsInforFromSignalBaseTable(QString Name,QString SignalType);

    //根据变量名精确查询变量
    DataBase::Str_Signal SelectSignalFromSignalBaseTable(QString signalName);

    //根据变量名查询变量是否存在
    bool  IsSignalExist(QString SignalName);

    //添加变量
    bool InsertSignalToSignalBaseTable(DataBase::Str_Signal signal);

    //删除变量名对应的变量
    bool DeleteSignalFromSignalBaseTable(QString SignalName);

    //更新账户权限
    bool UpdateSignalToSignalBaseTable(DataBase::Str_Signal OraginSignal,DataBase::Str_Signal UpdateSignal);


    ///////////////////////////////////////////////////
    /////RuleBase  操作相关
    ///////////////////////////////////////////////////

    //根据变量名和信号类型查询信号并返回结果,其中Name为模糊查询,State为-1代表查询所有状态
    QVector<DataBase::Str_Rule> SelectRulesInforFromRuleBaseTable(QString Name, QString SignalPos,int State);

    QVector<DataBase::Str_WarnRule> SelectWarnRulesInforFromRuleBaseTable(QString Name,int State);

    //根据规则名精确查询规则
    DataBase::Str_Rule SelectRuleFromRuleBaseTable(QString Name);

    bool CheckIfTaskParaExist(DataBase::Str_WarnRule);

    //根据规则名精确查询规则
    DataBase::Str_WarnRule SelectWarnRuleFromWarnBaseTable(QString Name);

    //更新规则信息
    bool UpdateRuleToRuleBaseTable(DataBase::Str_Rule OraginRule,DataBase::Str_Rule UpdateRule);

    bool UpdateWarnRuleToRuleBaseTable(DataBase::Str_WarnRule OraginRule, DataBase::Str_WarnRule UpdateRule);

    //设置规则是否禁用
    bool UpdateRuleForbidden(QString RuleName,bool state);

    bool UpdateWarnRuleForbidden(QString RuleName, bool state);

    //删除规则名对应的规则
    bool DeleteRuleFromRuleBaseTable(QString RuleName);

    bool DeleteWarnRuleFromRuleBaseTable(QString RuleName);

    //添加规则
    bool InsertRuleToRuleBaseTable(DataBase::Str_Rule Rule);

    bool InsertWarnRuleToRuleBaseTable(DataBase::Str_WarnRule Rule);

    //根据规则名查询规则是否存在
    bool  IsRuleExist(QString RuleName);

    ///////////////////////////////////////////////////
    /////FailureRecord  操作相关
    ///////////////////////////////////////////////////

    //记录新故障或报警
    int InsertFailToFailureRecord(QString FailSignalName,QString SignalPos);

    int InsertWarnToWarnRecord(QString StrWarnInfo);

    //更新记录
    bool UpdateFailToFailureRecord(int RecordID);

    bool UpdateWarnToWarnRecord(QString WarnTaskName);

    //更新手动故障定位结果
    bool UpdateFailToFailureMannulSet(int RecordID,QString StrMannulSet);

    //查找所有历史报警信息
    QVector<DataBase::Signal> SelectHisAlarmSignalFromDataBase(QDate StartDate,QDate EndDate,QString SearchStr,QString PosStr,int MinRecordIdx,int MaxRecordIdx,int &TotalRecords);

    QStringList SelectHisDataFromTaskDataSave(QDate StartDate,QDate EndDate,QString SearchStr);

    QVector<DataBase::WarnRecord> SelectHisWarnSignalFromDataBase(QDate StartDate,QDate EndDate,QString SearchStr,int MinRecordIdx,int MaxRecordIdx,int &TotalRecords);

    //删除指定记录,//Mode=0:删除指定记录  Mode=1：删除所有记录
    void DeleteHisRecord(int Mode,int ID,QDate StartDate,QDate EndDate,QString SearchStr,QString PosStr);

    void DeleteWarnHisRecord(int Mode,int ID,QDate StartDate,QDate EndDate,QString SearchStr);

    //统计历史手动故障定位结果
    QString AnalysisHisMannulSet(QString Name);

    //更新报警灯的坐标
    bool UpdateAlarmCursor(int SignalPos,int AlarmIdx,int Posx,int Posy);

    void TaskDataSave(QString StrWarnningInfo);
};

#endif // MYQSQLDATABASE_H
