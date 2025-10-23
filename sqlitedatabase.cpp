#include "sqlitedatabase.h"
#include <QFormLayout>
#include <QListWidget>
#include <QTextEdit>

SQliteDatabase::SQliteDatabase(QString databaseName)
{
    this->databaseName = databaseName;
    this->connectionName = QString("sqlite_conn_%1").arg(reinterpret_cast<quintptr>(this), 0, 16);
}

SQliteDatabase::~SQliteDatabase()
{
    if (database.isValid()) {
        database.close();
    }
    if (!connectionName.isEmpty()) {
        QSqlDatabase::removeDatabase(connectionName);
    }
}

bool SQliteDatabase::connect()
{
    if (QSqlDatabase::contains(connectionName)) {
        database = QSqlDatabase::database(connectionName);
    } else {
        database = QSqlDatabase::addDatabase("QSQLITE", connectionName);
        database.setDatabaseName(databaseName);
    }
    if (!database.isValid() || !database.isOpen()) {
        if (!database.open()) {
            qDebug() << "Error: Failed to connect database." << database.lastError();
            return false;
        }
    }

    QSqlQuery pragma(database);
    pragma.exec("PRAGMA foreign_keys = ON");
    return true;
}

component SQliteDatabase::selectComponentByMark(QString mark)
{
    QSqlQuery sql_query(database);
    component ans;

    QString sql = QString("select id,type,mark,variable,parameter,description,failuremode FROM components WHERE mark = '%1'")
                .arg(mark);

    if(sql_query.exec(sql)){
        while(sql_query.next()){
            ans.setId(sql_query.value(0).toInt());
            ans.setType(sql_query.value(1).toString());
            ans.setMark(sql_query.value(2).toString());
            ans.setVariable(sql_query.value(3).toString());
            ans.setParameter(sql_query.value(4).toString());
            ans.setDescription(sql_query.value(5).toString());
            ans.setFailureMode(sql_query.value(6).toString());
            ans.setFailureProbability(ans.getFailureMode());
        }
    }
    return ans;
}

model SQliteDatabase::selectModelByName(QString name)
{
    QSqlQuery sql_query(database);
    model ans;

    QString sql = QString("select id,name,systemDescription,testDiscription,connectNodes,functionDescription FROM models WHERE name = '%1'")
                .arg(name);
    qDebug()<<"name "<<name;
    if(sql_query.exec(sql)){
        qDebug()<<"sql_query.size() " <<sql_query.size();
        while(sql_query.next()){
            ans.setId(sql_query.value(0).toInt());
            ans.setName(sql_query.value(1).toString());
            ans.setSystemDescription(sql_query.value(2).toString());
            ans.setTestDiscription(sql_query.value(3).toString());
            ans.setConnectNodes(sql_query.value(4).toString());
            ans.setFunctionDiscription(sql_query.value(5).toString());
        }
    }
    return ans;
}

parameter SQliteDatabase::selectParameterByNameAndComponentId(QString name, int componentId)
{
    QSqlQuery sql_query(database);
    parameter ans;

    QString sql = QString("select id,defaultValue FROM parameters WHERE componentId = %1 AND name = '%2'")
                .arg(componentId).arg(name);

    if(sql_query.exec(sql)){
        while(sql_query.next()){
            ans.setId(sql_query.value(0).toInt());
            ans.setComponentId(componentId);
            ans.setName(name);
            ans.setDefaultValue(sql_query.value(1).toString());
        }
    }
    return ans;
}

QStringList SQliteDatabase::selectAllModelName()
{
    QSqlQuery sql_query(database);
    QStringList ans;

    QString sql = QString("select name FROM models");
    if(sql_query.exec(sql)){
        while(sql_query.next()){
            ans.append(sql_query.value(0).toString());
        }
    }
    return ans;
}

bool SQliteDatabase::componentMarkExist(QString mark)
{
    component ans = selectComponentByMark(mark);
    return ans.getMark() == mark;
}

bool SQliteDatabase::insertNewComponent(component c)
{
    bool ans = true;

    QMap<QString, QString> parameterMap;
    QStringList List = c.getParameter().split(",");
    for(QString va:List){
        QList<QString> parameter = va.split("=", QString::SkipEmptyParts);
        if(parameter.size()!=2) continue;
        //parameterMap.insert(parameter[0],parameter[1].toDouble());
		parameterMap.insert(parameter[0], parameter[1]);
    }

    QString ParameterString;
    QMap<QString, QString>::iterator iter = parameterMap.begin();
    while (iter != parameterMap.end())
    {
        ParameterString.append(iter.key());
        ParameterString.append(",");
        iter++;
    }
    ParameterString.remove(ParameterString.size()-1,1);

    QSqlQuery sql_query(database);
    QString sql = QString("INSERT INTO components (type,mark,parameter,variable,description) "
                             "VALUES (:type,:mark,:parameter,:variable,:description)");
    sql_query.prepare(sql);
    sql_query.bindValue(":type",c.getType());
    sql_query.bindValue(":mark",c.getMark());
    sql_query.bindValue(":parameter",ParameterString);
    sql_query.bindValue(":variable",c.getVariable());
    sql_query.bindValue(":description",c.getDescription());
    ans = sql_query.exec();

    if(ans){
        int componentId = selectComponentByMark(c.getMark()).getId();

        QMap<QString, QString>::iterator iter = parameterMap.begin();
        while (iter != parameterMap.end()&&ans)
        {
            QSqlQuery sql_query(database);
            QString sql = QString("INSERT INTO parameters (componentId,name,defaultValue) "
                                     "VALUES (:componentId,:name,:defaultValue)");
            sql_query.prepare(sql);
            sql_query.bindValue(":componentId",componentId);
            sql_query.bindValue(":name",iter.key());
            sql_query.bindValue(":defaultValue",iter.value());
            ans = sql_query.exec();

            iter++;
        }
    }
    return ans;
}

bool SQliteDatabase::saveModel(model model)
{
    QSqlQuery sql_query(database);
    QString sql = QString("INSERT INTO models (name,systemDescription,testDiscription,connectNodes,functionDescription) "
                             "VALUES (:name,:systemDescription,:testDiscription,:connectNodes,:functionDescription)");
    sql_query.prepare(sql);
    sql_query.bindValue(":name",model.getName());
    sql_query.bindValue(":systemDescription",model.getSystemDescription());
    sql_query.bindValue(":testDiscription",model.getTestDiscription());
    sql_query.bindValue(":connectNodes",model.getConnectNodes());
    sql_query.bindValue(":functionDescription",model.getFunctionDiscription());
    return sql_query.exec();
}

bool SQliteDatabase::updateModel(model& model)
{
    QSqlQuery sql_query(database);
    QString sql = QString("UPDATE models SET systemDescription=:systemDescription, "
                          "testDiscription=:testDiscription,connectNodes=:connectNodes,functionDescription=:functionDescription WHERE name=:name");
    sql_query.prepare(sql);
    sql_query.bindValue(":name",model.getName());
    sql_query.bindValue(":systemDescription",model.getSystemDescription());
    sql_query.bindValue(":testDiscription",model.getTestDiscription());
    sql_query.bindValue(":connectNodes",model.getConnectNodes());
    sql_query.bindValue(":functionDescription",model.getFunctionDiscription());
    //QMessageBox::information(nullptr, QString("模型名称及系统描述"), model.getName()+"\n"+model.getSystemDescription(), QString("确定"));
    return sql_query.exec();
}

bool SQliteDatabase::modelExist(QString name)
{
    model ans = selectModelByName(name);
    return ans.getName() == name;
}

void SQliteDatabase::saveConnectNodes(const QString& name, const QList<QStringList>& list)
{
    if(list.isEmpty())
        return;

    QString temp;
    int length = list.count();
    for(int i=0; i<length; i++)
    {
        int length2 = list.at(i).count();
        for(int j=0; j<length2; j++)
        {
            temp.append(list.at(i).at(j));
            temp.append("$");
        }
        temp.append("%");

    }

    QSqlQuery sql_query(database);
    QString temp_add = QString("UPDATE models SET connectNodes=:connectNodes WHERE name=:name");
    sql_query.prepare(temp_add);
    sql_query.bindValue(":connectNodes",name);
    sql_query.bindValue(":name",temp);

    sql_query.exec();
    return;
}
