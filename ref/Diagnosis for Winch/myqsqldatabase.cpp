#include "myqsqldatabase.h"
#include <QStack>
#include <QMessageBox>
#include <QHeaderView>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

myQSqlDatabase::myQSqlDatabase(QString FilePath): m_strFilePath(FilePath)
{
    TMATEconnect();
}

void myQSqlDatabase::TMATEconnect()
{//数据库连接函数
    database=database.contains(m_strFilePath)?database.database(m_strFilePath):database.addDatabase("QSQLITE",m_strFilePath);
    QFile  File(m_strFilePath);
    //若数据库文件不存在
    if(!File.exists()){
        QMessageBox::warning(nullptr, "错误", "数据库文件不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    else
        database.setDatabaseName(m_strFilePath);

    qsQuery = QSqlQuery(database);//设置数据库选择模型
    if (!database.open()){
        QMessageBox::warning(nullptr, "错误", "打开数据库失败",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    return;
}

DataBase::Str_communication myQSqlDatabase::SelectCommunicationInforFromCommunicationConfigTable(QString CommunicationName)
{//根据连接名查询连接IP和Port,若不存在该连接名则返回DataBase::Str_communication结构中Name=""
    DataBase::Str_communication ans;
    ans.Name = "";

    SelectSqlStatement = QString("SELECT Name,IP,Port FROM CommunicationConfig WHERE Name = '%1'").arg(CommunicationName);
    qsQuery.exec(SelectSqlStatement);
    if(qsQuery.first()){
        ans.Name = qsQuery.value(0).toString();
        ans.IP = qsQuery.value(1).toString();
        ans.Port = qsQuery.value(2).toString();
    }
    //qDebug()<<ans.Name<<ans.IP<<ans.Port;
    return ans;
}

bool myQSqlDatabase::UpdateCommunicationInforToCommunicationConfigTable(DataBase::Str_communication Communication)
{//更新连接名对应的连接IP和Port,若不存在该连接名则返回false
    UpdateSqlStatement = QString("UPDATE CommunicationConfig SET IP = '%1', Port = '%2' WHERE Name = '%3'")
            .arg(Communication.IP).arg(Communication.Port).arg(Communication.Name);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

QVector<DataBase::Str_account> myQSqlDatabase::SelectAccountsInforFromAccountTable(QString user, int level)
{//根据用户名和权限级别查询账号并返回结果  level=0查询所有结果，level=1为管理员，level=2为普通用户,其中user为模糊查询

    //qDebug()<<user<<level;
    QVector<DataBase::Str_account> ans;
    if(level==0){
        SelectSqlStatement = QString("SELECT ID,user,passwords,level,loginTime FROM Account"
                                     " WHERE user LIKE '%%1%'").arg(user);
    }
    else if(level==1||level==2){
        SelectSqlStatement = QString("SELECT ID,user,passwords,level,loginTime FROM Account"
                                     " WHERE user LIKE '%%1%' AND level = %2").arg(user).arg(level);
    }
    else{
        return ans;
    }

    qsQuery.exec(SelectSqlStatement);

    if (qsQuery.last())
        ans.resize(qsQuery.at() + 1);
    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next

    while(qsQuery.next()){
        ans[qsQuery.at()].Operating_ID = qsQuery.value(0).toInt();
        ans[qsQuery.at()].Operating_user = qsQuery.value(1).toString();
        ans[qsQuery.at()].Operating_PSW = qsQuery.value(2).toString();
        ans[qsQuery.at()].Operating_limit = qsQuery.value(3).toInt();
        ans[qsQuery.at()].LoginTime = qsQuery.value(4).toDateTime();
    }

    return ans;
}

DataBase::Str_account myQSqlDatabase::SelectAccountFromAccountTable(QString user)
{
    DataBase::Str_account ans;
    SelectSqlStatement = QString("SELECT ID,user,passwords,level,loginTime FROM Account"
                                 " WHERE user = '%1'").arg(user);
    qsQuery.exec(SelectSqlStatement);
    if(qsQuery.first()){
        ans.Operating_ID = qsQuery.value(0).toInt();
        ans.Operating_user = qsQuery.value(1).toString();
        ans.Operating_PSW = qsQuery.value(2).toString();
        ans.Operating_limit = qsQuery.value(3).toInt();
        ans.LoginTime = qsQuery.value(4).toDateTime();
    }
    return ans;
}

QString myQSqlDatabase::SelectPasswordsFromAccountTable(QString user)
{
    QString ans = "";
    SelectSqlStatement=QString::asprintf("SELECT passwords FROM Account WHERE user = '%1'").arg(user);
    qsQuery.prepare(SelectSqlStatement);
    qsQuery.exec();
    while (qsQuery.next())
        ans = qsQuery.value(0).toString();//原始密码
    return ans;
}

bool myQSqlDatabase::UpdateAccountPasswords(QString UserName, QString Passwords)
{
    UpdateSqlStatement=QString::asprintf("UPDATE Account SET passwords =  '%1' WHERE user = '%2' ")
            .arg(Passwords).arg(UserName);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::DeleteAccountFromAccountTable(QString UserName)
{
    DeleteSqlStatement = QString("DELETE FROM Account WHERE user = '%1';").arg(UserName);
    return qsQuery.exec(DeleteSqlStatement);
}


bool myQSqlDatabase::IsAccountExist(QString UserName)
{
    int Num = 0;
    SelectSqlStatement = QString("SELECT COUNT(*) FROM Account WHERE user = '%1';").arg(UserName);
    qsQuery.exec(SelectSqlStatement);
    while(qsQuery.next())
        Num = qsQuery.value(0).toInt();
    return Num;
}

bool myQSqlDatabase::UpdateAccountLimit(QString UserName, int Limit)
{
    UpdateSqlStatement=QString::asprintf("UPDATE Account SET level =  %1 WHERE user = '%2';")
            .arg(Limit).arg(UserName);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::InsertAccountToAccounttable(DataBase::Str_account account)
{
    qsQuery.prepare("INSERT INTO Account (user,passwords,level)"
                    " VALUES (:user,:passwords,:level)");
    qsQuery.bindValue(":user",account.Operating_user);
    qsQuery.bindValue(":passwords",account.Operating_PSW);
    qsQuery.bindValue(":level",account.Operating_limit);
    return qsQuery.exec();
}

QVector<DataBase::Str_Signal> myQSqlDatabase::SelectSignalsInforFromSignalBaseTable(QString Name, QString SignalType)
{
    //qDebug()<<Name<<SignalType;
    QVector<DataBase::Str_Signal> ans;
    if(SignalType=="ALL"){
        SelectSqlStatement = QString("SELECT Name,SignalType,DataType,Unit,SignalPos,Note,Detail,MultiPos,DisplayPosx,DisplayPosy FROM SignalBase"
                                     " WHERE Name LIKE '%%1%'").arg(Name);
    }
    else{
        SelectSqlStatement = QString("SELECT Name,SignalType,DataType,Unit,SignalPos,Note,Detail,MultiPos,DisplayPosx,DisplayPosy FROM SignalBase"
                                     " WHERE Name LIKE '%%1%' AND SignalType = '%2'").arg(Name).arg(SignalType);
    }

    qsQuery.exec(SelectSqlStatement);

    if (qsQuery.last())
        ans.resize(qsQuery.at() + 1);
    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next

    while(qsQuery.next()){
        ans[qsQuery.at()].Name = qsQuery.value(0).toString();
        ans[qsQuery.at()].SignalType = qsQuery.value(1).toString();
        ans[qsQuery.at()].DataType = qsQuery.value(2).toString();
        ans[qsQuery.at()].Unit = qsQuery.value(3).toString();
        ans[qsQuery.at()].SignalPos = qsQuery.value(4).toString();
        ans[qsQuery.at()].Note = qsQuery.value(5).toString();
        ans[qsQuery.at()].Detail = qsQuery.value(6).toString();
        ans[qsQuery.at()].MultiPos = qsQuery.value(7).toString().split(';',QString::SkipEmptyParts);
        ans[qsQuery.at()].DisplayPosx= qsQuery.value(8).toInt();
        ans[qsQuery.at()].DisplayPosy= qsQuery.value(9).toInt();
        //qDebug()<<ans[qsQuery.at()].SignalPos;
    }

    return ans;
}

bool myQSqlDatabase::IsSignalExist(QString SignalName)
{
    int Num = 0;
    SelectSqlStatement = QString("SELECT COUNT(*) FROM SignalBase WHERE Name = '%1';").arg(SignalName);
    qsQuery.exec(SelectSqlStatement);
    while(qsQuery.next())
        Num = qsQuery.value(0).toInt();
    return Num;
}

bool myQSqlDatabase::InsertSignalToSignalBaseTable(DataBase::Str_Signal signal)
{
    QString UpdateMultiPosStr="";
    for(int i=0;i<signal.MultiPos.size();i++)
    {
        if(i!=signal.MultiPos.size()-1) UpdateMultiPosStr+=signal.MultiPos[i]+";";
        else  UpdateMultiPosStr+=signal.MultiPos[i];
    }

    qsQuery.prepare("INSERT INTO SignalBase (Name,SignalType,DataType,Unit,SignalPos,Note,Detail,MultiPos)"
                    " VALUES (:Name,:SignalType,:DataType,:Unit,:SignalPos,:Note,:Detail,:MultiPos)");
    qsQuery.bindValue(":Name",signal.Name);
    qsQuery.bindValue(":SignalType",signal.SignalType);
    qsQuery.bindValue(":DataType",signal.DataType);
    qsQuery.bindValue(":Unit",signal.Unit);
    qsQuery.bindValue(":SignalPos",signal.SignalPos);
    qsQuery.bindValue(":Note",signal.Note);
    qsQuery.bindValue(":Detail",signal.Detail);
    qsQuery.bindValue(":MultiPos",UpdateMultiPosStr);
    return qsQuery.exec();
}

bool myQSqlDatabase::DeleteSignalFromSignalBaseTable(QString SignalName)
{
    DeleteSqlStatement = QString("DELETE FROM SignalBase WHERE Name = '%1';").arg(SignalName);
    return qsQuery.exec(DeleteSqlStatement);
}

bool myQSqlDatabase::UpdateSignalToSignalBaseTable(DataBase::Str_Signal OraginSignal, DataBase::Str_Signal UpdateSignal)
{
    QString UpdateMultiPosStr="";
    for(int i=0;i<UpdateSignal.MultiPos.size();i++)
    {
        qDebug()<<UpdateSignal.MultiPos[i];
        if(i!=UpdateSignal.MultiPos.size()-1) UpdateMultiPosStr+=UpdateSignal.MultiPos[i]+";";
        else  UpdateMultiPosStr+=UpdateSignal.MultiPos[i];
    }

    qDebug()<<UpdateMultiPosStr;
    UpdateSqlStatement=QString::asprintf("UPDATE SignalBase SET Name='%1',SignalType='%2',DataType='%3',Unit='%4',SignalPos='%5',Note='%6',Detail='%7',MultiPos='%8' "
                                         " WHERE Name = '%9';")
            .arg(UpdateSignal.Name).arg(UpdateSignal.SignalType).arg(UpdateSignal.DataType).arg(UpdateSignal.Unit).arg(UpdateSignal.SignalPos).arg(UpdateSignal.Note).arg(UpdateSignal.Detail).arg(UpdateMultiPosStr).arg(OraginSignal.Name);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::CheckIfTaskParaExist(DataBase::Str_WarnRule Rule)
{
    SelectSqlStatement = "SELECT * FROM WarnBase WHERE Name = '"+Rule.Name+"' AND ID <> "+QString::number(Rule.ID);
    qsQuery.exec(SelectSqlStatement);
    if(qsQuery.next()) return true;
    QStringList ListTaskPara=Rule.TaskParaList.split(",");
    for(int i=0;i<ListTaskPara.count();i++)
    {
        if(ListTaskPara.at(i).contains("(")&&ListTaskPara.at(i).contains(")"))
        {
           ListTaskPara[i]= ListTaskPara.at(i).mid(0,ListTaskPara.at(i).lastIndexOf("("));
        }
    }
    SelectSqlStatement = "SELECT * FROM WarnBase WHERE ID <> "+QString::number(Rule.ID);
    qsQuery.exec(SelectSqlStatement);
    bool NotSame=false;
    if (!qsQuery.next()) NotSame=true;
    qsQuery.first();
    qsQuery.previous();
    while(qsQuery.next())
    {
        QStringList QueryTaskPara=qsQuery.value("TaskParaList").toString().split(",");
        for(int i=0;i<QueryTaskPara.count();i++)
        {
            if(QueryTaskPara.at(i).contains("(")&&QueryTaskPara.at(i).contains(")"))
            {
               QueryTaskPara[i]= QueryTaskPara.at(i).mid(0,QueryTaskPara.at(i).lastIndexOf("("));
            }
        }

        for(int i=0;i<ListTaskPara.count();i++)
        {
            bool Find=false;
            for(int j=0;j<QueryTaskPara.count();j++)
            {
                if(ListTaskPara.at(i)==QueryTaskPara.at(j)) {Find=true;break;}
            }
            if(!Find)
            {
                NotSame=true;
                break;
            }
        }
        if(NotSame) break;
    }
    if(NotSame) return false;
    else return true;
}

QVector<DataBase::Str_WarnRule> myQSqlDatabase::SelectWarnRulesInforFromRuleBaseTable(QString Name,int State)
{
    //qDebug()<<Name<<State;
    QVector<DataBase::Str_WarnRule> ans;
    if(State==-1){
        SelectSqlStatement = QString("SELECT Name,State,Editor,Description,TaskParaList,WarnParaList,ID FROM WarnBase"
                                     " WHERE Name LIKE '%%1%' order by ID").arg(Name);
    }
    else if(State==0){
        SelectSqlStatement = QString("SELECT Name,State,Editor,Description,TaskParaList,WarnParaList,ID FROM WarnBase"
                                     " WHERE Name LIKE '%%1%' AND State = 0 order by ID").arg(Name);
    }
    else{
        SelectSqlStatement = QString("SELECT Name,State,Editor,Description,TaskParaList,WarnParaList,ID FROM WarnBase"
                                     " WHERE Name LIKE '%%1%' AND State != 0  order by ID").arg(Name);
    }

    qsQuery.exec(SelectSqlStatement);

    if (qsQuery.last())
        ans.resize(qsQuery.at() + 1);
    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next

    while(qsQuery.next()){
        ans[qsQuery.at()].Name = qsQuery.value(0).toString();
        ans[qsQuery.at()].State = qsQuery.value(1).toBool();
        ans[qsQuery.at()].Editor = qsQuery.value(2).toString();
        ans[qsQuery.at()].Description = qsQuery.value(3).toString();
        ans[qsQuery.at()].TaskParaList = qsQuery.value(4).toString();
        ans[qsQuery.at()].WarnParaList = qsQuery.value(5).toString();
        ans[qsQuery.at()].ID=qsQuery.value(6).toInt();
    }

    return ans;
}

QVector<DataBase::Str_Rule> myQSqlDatabase::SelectRulesInforFromRuleBaseTable(QString Name, QString SignalPos,int State)
{
    //qDebug()<<Name<<State;
    QVector<DataBase::Str_Rule> ans;
    if(State==-1){
        SelectSqlStatement = QString("SELECT Name,State,Editor,Description,Condition,ResultThen,ResultElse,DurTime,RulePos FROM RuleBase"
                                     " WHERE Name LIKE '%%1%' AND RulePos LIKE '%%2%' order by RulePos").arg(Name).arg(SignalPos);
    }
    else if(State==0){
        SelectSqlStatement = QString("SELECT Name,State,Editor,Description,Condition,ResultThen,ResultElse,DurTime,RulePos FROM RuleBase"
                                     " WHERE Name LIKE '%%1%' AND RulePos LIKE '%%2%' AND State = 0 order by RulePos").arg(Name).arg(SignalPos);
    }
    else{
        SelectSqlStatement = QString("SELECT Name,State,Editor,Description,Condition,ResultThen,ResultElse,DurTime,RulePos FROM RuleBase"
                                     " WHERE Name LIKE '%%1%' AND RulePos LIKE '%%2%' AND State != 0  order by RulePos").arg(Name).arg(SignalPos);
    }

    qsQuery.exec(SelectSqlStatement);

    if (qsQuery.last())
        ans.resize(qsQuery.at() + 1);
    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next

    while(qsQuery.next()){
        ans[qsQuery.at()].Name = qsQuery.value(0).toString();
        ans[qsQuery.at()].State = qsQuery.value(1).toBool();
        ans[qsQuery.at()].Editor = qsQuery.value(2).toString();
        ans[qsQuery.at()].Description = qsQuery.value(3).toString();
        ans[qsQuery.at()].Condition = qsQuery.value(4).toString();
        ans[qsQuery.at()].ResultThen = qsQuery.value(5).toString();
        ans[qsQuery.at()].ResultElse = qsQuery.value(6).toString();
        ans[qsQuery.at()].DurTime = qsQuery.value(7).toDouble();
        ans[qsQuery.at()].RulePos = qsQuery.value(8).toString();
    }

    return ans;
}

DataBase::Str_WarnRule myQSqlDatabase::SelectWarnRuleFromWarnBaseTable(QString Name)
{
    DataBase::Str_WarnRule ans;
    SelectSqlStatement = QString("SELECT Name,State,Editor,Description,TaskParaList,WarnParaList,ID FROM WarnBase"
                                 " WHERE Name = '%1'").arg(Name);
    qsQuery.exec(SelectSqlStatement);
    if(qsQuery.first()){
        ans.Name = qsQuery.value(0).toString();
        ans.State = qsQuery.value(1).toBool();
        ans.Editor = qsQuery.value(2).toString();
        ans.Description = qsQuery.value(3).toString();
        ans.TaskParaList = qsQuery.value(4).toString();
        ans.WarnParaList = qsQuery.value(5).toString();
        ans.ID = qsQuery.value(6).toInt();
    }
    return ans;
}

DataBase::Str_Rule myQSqlDatabase::SelectRuleFromRuleBaseTable(QString Name)
{
    DataBase::Str_Rule ans;
    SelectSqlStatement = QString("SELECT Name,State,Editor,Description,Condition,ResultThen,ResultElse,DurTime,RulePos FROM RuleBase"
                                 " WHERE Name = '%1'").arg(Name);
    qsQuery.exec(SelectSqlStatement);
    if(qsQuery.first()){
        ans.Name = qsQuery.value(0).toString();
        ans.State = qsQuery.value(1).toBool();
        ans.Editor = qsQuery.value(2).toString();
        ans.Description = qsQuery.value(3).toString();
        ans.Condition = qsQuery.value(4).toString();
        ans.ResultThen = qsQuery.value(5).toString();
        ans.ResultElse = qsQuery.value(6).toString();
        ans.DurTime = qsQuery.value(7).toDouble();
        ans.RulePos = qsQuery.value(8).toString();
    }
    return ans;
}
bool myQSqlDatabase::UpdateWarnRuleToRuleBaseTable(DataBase::Str_WarnRule OraginRule, DataBase::Str_WarnRule UpdateRule)
{
    UpdateSqlStatement=QString::asprintf("UPDATE WarnBase SET Name='%1',State=%2,Editor='%3',Description='%4',"
                                         "TaskParaList='%5',WarnParaList='%6'"
                                         " WHERE Name = '%7';")
            .arg(UpdateRule.Name).arg(UpdateRule.State).arg(UpdateRule.Editor).arg(UpdateRule.Description).arg(UpdateRule.TaskParaList)
            .arg(UpdateRule.WarnParaList).arg(OraginRule.Name);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}
bool myQSqlDatabase::UpdateRuleToRuleBaseTable(DataBase::Str_Rule OraginRule, DataBase::Str_Rule UpdateRule)
{
    UpdateSqlStatement=QString::asprintf("UPDATE RuleBase SET Name='%1',State=%2,Editor='%3',Description='%4',"
                                         "Condition='%5',ResultThen='%6',ResultElse='%7',DurTime='%8',RulePos='%9'"
                                         " WHERE Name = '%10';")
            .arg(UpdateRule.Name).arg(UpdateRule.State).arg(UpdateRule.Editor).arg(UpdateRule.Description).arg(UpdateRule.Condition)
            .arg(UpdateRule.ResultThen).arg(UpdateRule.ResultElse).arg(UpdateRule.DurTime).arg(UpdateRule.RulePos).arg(OraginRule.Name);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::UpdateWarnRuleForbidden(QString RuleName, bool state)
{
    UpdateSqlStatement=QString::asprintf("UPDATE WarnBase SET State=%1 WHERE Name = '%2';")
            .arg(state).arg(RuleName);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::UpdateRuleForbidden(QString RuleName, bool state)
{
    UpdateSqlStatement=QString::asprintf("UPDATE RuleBase SET State=%1 WHERE Name = '%2';")
            .arg(state).arg(RuleName);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::DeleteWarnRuleFromRuleBaseTable(QString RuleName)
{
    DeleteSqlStatement = QString("DELETE FROM WarnBase WHERE Name = '%1';").arg(RuleName);
    return qsQuery.exec(DeleteSqlStatement);
}

bool myQSqlDatabase::DeleteRuleFromRuleBaseTable(QString RuleName)
{
    DeleteSqlStatement = QString("DELETE FROM RuleBase WHERE Name = '%1';").arg(RuleName);
    return qsQuery.exec(DeleteSqlStatement);
}
bool myQSqlDatabase::InsertWarnRuleToRuleBaseTable(DataBase::Str_WarnRule Rule)
{
    qsQuery.prepare("INSERT INTO WarnBase (Name,State,Editor,Description,TaskParaList,WarnParaList)"
                    " VALUES (:Name,:State,:Editor,:Description,:TaskParaList,:WarnParaList)");
    qsQuery.bindValue(":Name",Rule.Name);
    qsQuery.bindValue(":State",Rule.State);
    qsQuery.bindValue(":Editor",Rule.Editor);
    qsQuery.bindValue(":Description",Rule.Description);
    qsQuery.bindValue(":TaskParaList",Rule.TaskParaList);
    qsQuery.bindValue(":WarnParaList",Rule.WarnParaList);
    return qsQuery.exec();
}
bool myQSqlDatabase::InsertRuleToRuleBaseTable(DataBase::Str_Rule Rule)
{
    qsQuery.prepare("INSERT INTO RuleBase (Name,State,Editor,Description,Condition,ResultThen,ResultElse,DurTime,RulePos)"
                    " VALUES (:Name,:State,:Editor,:Description,:Condition,:ResultThen,:ResultElse,:DurTime,:RulePos)");
    qsQuery.bindValue(":Name",Rule.Name);
    qsQuery.bindValue(":State",Rule.State);
    qsQuery.bindValue(":Editor",Rule.Editor);
    qsQuery.bindValue(":Description",Rule.Description);
    qsQuery.bindValue(":Condition",Rule.Condition);
    qsQuery.bindValue(":ResultThen",Rule.ResultThen);
    qsQuery.bindValue(":ResultElse",Rule.ResultElse);
    qsQuery.bindValue(":DurTime",Rule.DurTime);
    qsQuery.bindValue(":RulePos",Rule.RulePos);
    return qsQuery.exec();
}

bool myQSqlDatabase::IsRuleExist(QString RuleName)
{
    int Num = 0;
    SelectSqlStatement = QString("SELECT COUNT(*) FROM RuleBase WHERE Name = '%1';").arg(RuleName);
    qsQuery.exec(SelectSqlStatement);
    while(qsQuery.next())
        Num = qsQuery.value(0).toInt();
    return Num;
}

void myQSqlDatabase::TaskDataSave(QString StrWarnningInfo)
{
    QString WarnTaskName=StrWarnningInfo.split(":").at(0);
    QString TaskPara=StrWarnningInfo.split(":").at(1).split(";").at(0);
    QString WarnPara=StrWarnningInfo.split(":").at(1).split(";").at(1);
    qsQuery.prepare("INSERT INTO TaskDataSave (TaskName,TaskAllPara)"
                    " VALUES (:TaskName,:TaskAllPara)");
    qsQuery.bindValue(":TaskName",WarnTaskName);
    qsQuery.bindValue(":TaskAllPara",TaskPara+","+WarnPara);
    qsQuery.exec();
}

//工况:参数1=值,参数2=值;参数1=值,参数2=值
int myQSqlDatabase::InsertWarnToWarnRecord(QString StrWarnInfo)
{
    QString WarnTaskName=StrWarnInfo.split(":").at(0);
    QString TaskPara=StrWarnInfo.split(":").at(1).split(";").at(0);
    QString WarnPara=StrWarnInfo.split(":").at(1).split(";").at(1);
    qsQuery.prepare("INSERT INTO WarnRecord (WarnTaskName,TaskPara,WarnPara)"
                    " VALUES (:WarnTaskName,:TaskPara,:WarnPara)");
    qsQuery.bindValue(":WarnTaskName",WarnTaskName);
    qsQuery.bindValue(":TaskPara",TaskPara);
    qsQuery.bindValue(":WarnPara",WarnPara);
    qsQuery.exec();
    qsQuery.prepare("SELECT max(ID) FROM WarnRecord");
    qsQuery.exec();
    qsQuery.first();
    //qDebug()<<"recordID= "<<qsQuery.value(0).toInt();

    return qsQuery.value(0).toInt();
}

int myQSqlDatabase::InsertFailToFailureRecord(QString FailSignalName,QString SignalPos)
{
    qsQuery.prepare("INSERT INTO FailureRecord (FailureSignalName,SignalPos)"
                    " VALUES (:FailureSignalName,:SignalPos)");
    qsQuery.bindValue(":FailureSignalName",FailSignalName);
    qsQuery.bindValue(":SignalPos",SignalPos);
    qsQuery.exec();
    qsQuery.prepare("SELECT max(ID) FROM FailureRecord");
    qsQuery.exec();
    qsQuery.first();
    //qDebug()<<"recordID= "<<qsQuery.value(0).toInt();

    return qsQuery.value(0).toInt();
}

bool myQSqlDatabase::UpdateWarnToWarnRecord(QString WarnTaskName)
{
    //qDebug()<<"UpdateFailToFailureRecord"<<RecordID;
    QString ID;
    UpdateSqlStatement="SELECT MAX(ID) FROM WarnRecord WHERE WarnTaskName = '"+WarnTaskName+"'";
    qsQuery.exec(UpdateSqlStatement);
    if(qsQuery.next()) ID=qsQuery.value(0).toString();
    UpdateSqlStatement=QString::asprintf("UPDATE WarnRecord SET FinishDateTime=datetime('%1') WHERE ID = %2;")
            .arg(QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss")).arg(ID);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

bool myQSqlDatabase::UpdateFailToFailureRecord(int RecordID)
{
    //qDebug()<<"UpdateFailToFailureRecord"<<RecordID;
    UpdateSqlStatement=QString::asprintf("UPDATE FailureRecord SET FinishDateTime=datetime('%1') WHERE ID = %2;")
            .arg(QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss")).arg(RecordID);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();

}

DataBase::Str_Signal myQSqlDatabase::SelectSignalFromSignalBaseTable(QString signalName)
{
    DataBase::Str_Signal ans;
    SelectSqlStatement = QString("SELECT Name,SignalType,DataType,Unit,SignalPos,Note,Detail,MultiPos FROM SignalBase"
                                 " WHERE Name = '%1'").arg(signalName);
    qsQuery.exec(SelectSqlStatement);
    if(qsQuery.first()){
        ans.Name = qsQuery.value(0).toString();
        ans.SignalType = qsQuery.value(1).toString();
        ans.DataType = qsQuery.value(2).toString();
        ans.Unit = qsQuery.value(3).toString();
        ans.SignalPos = qsQuery.value(4).toString();
        ans.Note = qsQuery.value(5).toString();
        ans.Detail = qsQuery.value(6).toString();
        ans.MultiPos = qsQuery.value(7).toString().split(';',QString::SkipEmptyParts);
    }
    return ans;
}

//Mode=0:删除指定记录  Mode=1：删除所有记录
void myQSqlDatabase::DeleteWarnHisRecord(int Mode,int ID,QDate StartDate,QDate EndDate,QString SearchStr)
{
   QSqlQuery m_Query= QSqlQuery(database);//设置数据库选择模型
   QSqlQuery QuerySearch= QSqlQuery(database);//设置数据库选择模型
   if(Mode==0)
   {
       SelectSqlStatement="DELETE FROM WarnRecord WHERE ID = "+QString::number(ID);
       m_Query.exec(SelectSqlStatement);
   }
   else if(Mode==1)
   {
       SelectSqlStatement="DELETE FROM WarnRecord WHERE (StartDateTime"
                              " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                              " AND WarnTaskName LIKE '%"+SearchStr+"%'";
       m_Query.exec(SelectSqlStatement);
   }//end of else if(Mode==1)
}

//Mode=0:删除指定记录  Mode=1：删除所有记录
void myQSqlDatabase::DeleteHisRecord(int Mode,int ID,QDate StartDate,QDate EndDate,QString SearchStr,QString PosStr)
{
   QSqlQuery m_Query= QSqlQuery(database);//设置数据库选择模型
   QSqlQuery QuerySearch= QSqlQuery(database);//设置数据库选择模型
   if(Mode==0)
   {
       SelectSqlStatement="DELETE FROM FailureRecord WHERE ID = "+QString::number(ID);
       m_Query.exec(SelectSqlStatement);
   }
   else if(Mode==1)
   {
       if(PosStr=="ALL")
       {
           SelectSqlStatement="DELETE FROM FailureRecord WHERE (StartDateTime"
                              " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                              " AND FailureSignalName LIKE '%"+SearchStr+"%'";
           m_Query.exec(SelectSqlStatement);
       }
       else
       {
           SelectSqlStatement = QString("SELECT ID,FailureSignalName FROM FailureRecord WHERE (StartDateTime"
                                        " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                                        " AND FailureSignalName LIKE '%"+SearchStr+"%' order by ID desc");
           qsQuery.exec(SelectSqlStatement);
           while(qsQuery.next())
           {
               SelectSqlStatement="SELECT SignalPos FROM SignalBase WHERE Name = '"+qsQuery.value(1).toString()+"'";
               QuerySearch.exec(SelectSqlStatement);
               if(QuerySearch.next())
               {
                   if(QuerySearch.value(0).toString()==PosStr)
                   {
                       SelectSqlStatement="DELETE FROM FailureRecord WHERE ID = "+qsQuery.value(0).toString();
                       QuerySearch.exec(SelectSqlStatement);
                   }
               }
           }
       }
   }//end of else if(Mode==1)
}

QStringList myQSqlDatabase::SelectHisDataFromTaskDataSave(QDate StartDate,QDate EndDate,QString SearchStr)
{
    QStringList ans;
    QSqlQuery m_Query= QSqlQuery(database);//设置数据库选择模型
    SelectSqlStatement = QString("SELECT ID,TaskAllPara FROM TaskDataSave WHERE (DateTime"
                                     " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                                     " AND TaskName = '"+SearchStr+"' order by ID desc");
    qsQuery.exec(SelectSqlStatement);
    while(qsQuery.next()){
        ans.append(qsQuery.value("TaskAllPara").toString());
    }
    return ans;
}

//工况:参数1=值,参数2=值;参数1=值,参数2=值:ID
QVector<DataBase::WarnRecord> myQSqlDatabase::SelectHisWarnSignalFromDataBase(QDate StartDate,QDate EndDate,QString SearchStr,int MinRecordIdx,int MaxRecordIdx,int &TotalRecords)
{
    QVector<DataBase::WarnRecord> ans;
    QSqlQuery m_Query= QSqlQuery(database);//设置数据库选择模型

    SelectSqlStatement = QString("SELECT ID,WarnTaskName,StartDateTime,FinishDateTime,TaskPara,WarnPara FROM WarnRecord WHERE (StartDateTime"
                                     " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                                     " AND WarnTaskName LIKE '%"+SearchStr+"%' order by ID desc");

    qsQuery.exec(SelectSqlStatement);
    //TotalRecords=qsQuery.record().count();
    TotalRecords=0;
    QSqlQuery QuerySearch= QSqlQuery(database);//设置数据库选择模型
    if (qsQuery.last())
    {
        TotalRecords=qsQuery.at() + 1;
        //ans.resize(qsQuery.at() + 1);
    }

    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next
    int RecordIdx=0;
    ans.clear();
    while(qsQuery.next()){
        if((MinRecordIdx<=RecordIdx)&&(MaxRecordIdx>RecordIdx))
        {
            DataBase::WarnRecord myWarnRecord;
            myWarnRecord.RecordID=qsQuery.value(0).toInt();
            myWarnRecord.WarnTaskName=qsQuery.value(1).toString();
            myWarnRecord.RecordStartDateTime=qsQuery.value(2).toDateTime();
            myWarnRecord.RecordFinishDateTime=qsQuery.value(3).toDateTime();
            myWarnRecord.TaskPara=qsQuery.value(4).toString();
            myWarnRecord.WarnPara=qsQuery.value(5).toString();
            ans.append(myWarnRecord);
            RecordIdx++;
        }
        else
        {
            RecordIdx++;
            continue;
        }
    }
    return ans;
}

//MinRecordIdx~MaxRecordIdx-1
QVector<DataBase::Signal> myQSqlDatabase::SelectHisAlarmSignalFromDataBase(QDate StartDate,QDate EndDate,QString SearchStr,QString PosStr,int MinRecordIdx,int MaxRecordIdx,int &TotalRecords)
{
    QVector<DataBase::Signal> ans;
    QSqlQuery m_Query= QSqlQuery(database);//设置数据库选择模型

    if(PosStr=="ALL")
    {
        SelectSqlStatement = QString("SELECT ID,FailureSignalName,StartDateTime,FinishDateTime,MultiPosMannulSet FROM FailureRecord WHERE (StartDateTime"
                                     " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                                     " AND FailureSignalName LIKE '%"+SearchStr+"%' order by ID desc");
    }
    else
    {
        SelectSqlStatement = QString("SELECT ID,FailureSignalName,StartDateTime,FinishDateTime,MultiPosMannulSet FROM FailureRecord WHERE (StartDateTime"
                                     " BETWEEN '"+StartDate.toString("yyyy-MM-dd")+" 00:00:00' AND '"+EndDate.toString("yyyy-MM-dd")+" 23:59:59')"
                                     " AND FailureSignalName LIKE '%"+SearchStr+"%' AND SignalPos = '"+PosStr+"' order by ID desc");

    }
    qsQuery.exec(SelectSqlStatement);
    //TotalRecords=qsQuery.record().count();
    TotalRecords=0;
    QSqlQuery QuerySearch= QSqlQuery(database);//设置数据库选择模型
    if (qsQuery.last())
    {
        TotalRecords=qsQuery.at() + 1;
        //ans.resize(qsQuery.at() + 1);
    }

    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next
    int RecordIdx=0;
    ans.clear();
    while(qsQuery.next()){
        if((MinRecordIdx<=RecordIdx)&&(MaxRecordIdx>RecordIdx))
        {        
            DataBase::Signal mySignal;
            mySignal.RecordID=qsQuery.value(0).toInt();
            mySignal.Name=qsQuery.value(1).toString();
            mySignal.RecordStartDateTime=qsQuery.value(2).toDateTime();
            mySignal.RecordFinishDateTime=qsQuery.value(3).toDateTime();
            mySignal.MultiPosMannulSet=qsQuery.value(4).toString();
            //qDebug()<<"FailureSignalName="<<qsQuery.value(1).toString();
            //查询变量信息
            SelectSqlStatement = QString("SELECT SignalType,SignalPos,Note,Detail,MultiPos FROM SignalBase WHERE Name= '%1'").arg(qsQuery.value(1).toString());
            m_Query.exec(SelectSqlStatement);
            if(!m_Query.first()) continue;
            mySignal.signalType=m_Query.value(0).toString();
            mySignal.SignalPos=m_Query.value(1).toString();
            mySignal.Note=m_Query.value(2).toString();
            mySignal.Detail=m_Query.value(3).toString();
            mySignal.MultiPos=m_Query.value(4).toString().split(';',QString::SkipEmptyParts);
            ans.append(mySignal);
            RecordIdx++;
        }
        else
        {
            RecordIdx++;
            continue;
        }
    }
    return ans;
}

//更新手动故障定位结果到数据库
bool myQSqlDatabase::UpdateFailToFailureMannulSet(int RecordID,QString StrMannulSet)
{
    UpdateSqlStatement=QString::asprintf("UPDATE FailureRecord SET MultiPosMannulSet='%1' WHERE ID = %2;")
            .arg(StrMannulSet).arg(RecordID);
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

//统计历史手动故障定位
QString myQSqlDatabase::AnalysisHisMannulSet(QString Name)
{
    QString RetStr="";
    SelectSqlStatement = QString("SELECT MultiPos,SignalType FROM SignalBase WHERE Name = '%1'").arg(Name);
    qsQuery.exec(SelectSqlStatement);
    qsQuery.first();
    if(qsQuery.value(1).toString()!="报警信号"&&qsQuery.value(1).toString()!="故障信号") return "";
    QStringList MannulList=qsQuery.value(0).toString().split(';',QString::SkipEmptyParts);
    //qDebug()<<"Name="<<Name;
    //qDebug()<<"MannulList="<<MannulList;
    QVector<int> AnalysisCount;
    AnalysisCount.resize(MannulList.size());
    for(int i=0;i<AnalysisCount.size();i++)  AnalysisCount[i]=0;

    SelectSqlStatement = QString("SELECT MultiPosMannulSet FROM FailureRecord WHERE FailureSignalName = '%1'").arg(Name);
    qsQuery.exec(SelectSqlStatement);
    qsQuery.first();//重新定位指针到结果集首位
    qsQuery.previous();//将指针移动到首位的上一位执行next
    int TotalRecordCount=0;
    int TotalMannulCount=0;
    while(qsQuery.next()){
        for(int i=0;i<MannulList.size();i++)
        {
          TotalRecordCount++;
          //qDebug()<<qsQuery.value(0).toString()<<"   "<<MannulList[i];
          if(qsQuery.value(0).toString()==MannulList[i]) AnalysisCount[i]++;
        }
    }

    for(int i=0;i<AnalysisCount.size();i++) TotalMannulCount+=AnalysisCount[i];
    if(TotalRecordCount==0) {RetStr="无历史案例";return RetStr;}


    RetStr="发生次数："+QString::number(TotalRecordCount)+"次\n";
    if(MannulList.size()>0)//具有模糊组
    {
        for(int i=0;i<AnalysisCount.size();i++)
        {
            RetStr+=MannulList[i]+":"+QString::number(AnalysisCount[i])+"次";
            if(TotalMannulCount>0) RetStr+="("+QString::number(AnalysisCount[i]*100.0/TotalMannulCount,'f',1)+"%)";
            RetStr+="\n";
        }
        RetStr+="未设定:"+QString::number(TotalRecordCount-TotalMannulCount)+"次";
    }



    return RetStr;
}
int AlarmDataBaseID[5][30]={
                              {264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293},
                              {144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173},
                              {174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203},
                              {204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233},
                              {234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263}
                            };
bool myQSqlDatabase::UpdateAlarmCursor(int SignalPos,int AlarmIdx,int Posx,int Posy)
{
    QString SignalPosStr="";
    if(SignalPos==0) SignalPosStr="传感器信号-外部";
    if(SignalPos==1) SignalPosStr="传感器信号-内部";
    if(SignalPos==2) SignalPosStr="变频器控制信号";
    if(SignalPos==3) SignalPosStr="备用泵电机启动箱";
    if(SignalPos==4) SignalPosStr="提升泵电机启动箱";
    UpdateSqlStatement=QString::asprintf("UPDATE SignalBase SET DisplayPosx= %1,DisplayPosy= %2 WHERE SignalPos = '%3' and ID = %4")
            .arg(Posx).arg(Posy).arg(SignalPosStr).arg(AlarmDataBaseID[SignalPos][AlarmIdx-1]);
    qDebug()<<UpdateSqlStatement;
    qsQuery.prepare(UpdateSqlStatement);
    return qsQuery.exec();
}

