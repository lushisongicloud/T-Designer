#ifndef SQLITEDATABASE_H
#define SQLITEDATABASE_H

#include <QSqlDatabase>
#include <QtGlobal>
#include <QDebug>
#include <QMessageBox>
#include <QSqlError>
#include <QSqlQuery>

#include "DO/component.h"
#include "DO/parameter.h"
#include "DO/model.h"

class SQliteDatabase
{
public:
    SQliteDatabase(QString databaseName);
    ~SQliteDatabase();

    bool connect();

    component selectComponentByMark(QString mark);

    model selectModelByName(QString name);

    parameter selectParameterByNameAndComponentId(QString name,int componentId);

    QStringList selectAllModelName();

    bool insertNewComponent(component c);

    bool componentMarkExist(QString mark);

    bool saveModel(model model);

    bool updateModel(model& model);

    bool modelExist(QString name);

    void saveConnectNodes(const QString& name, const QList<QStringList>& list);

    bool haveConnectNodes(const QString& name);     //判断一个model里是否
private:
    QSqlDatabase database;

    QString databaseName;
    QString connectionName;
};

#endif // SQLITEDATABASE_H
