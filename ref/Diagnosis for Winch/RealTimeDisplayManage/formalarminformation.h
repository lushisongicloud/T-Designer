#ifndef FORMALARMINFORMATION_H
#define FORMALARMINFORMATION_H

#include <QWidget>
#include <QTableWidget>
#include "myqsqldatabase.h"
#include <QFormLayout>
#include <QComboBox>
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:故障报警和预报警显示窗口,支持信息显示、清空显示操作
**************************************************/

namespace Ui {
class FormAlarmInformation;
}

class FormAlarmInformation : public QWidget
{
    Q_OBJECT

public:
    //Name字段为窗口名称
    explicit FormAlarmInformation(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~FormAlarmInformation();

    //清空窗口显示
    void ClearLoggingUI();

    //窗口增加显示newLogging字符串
    void updateLoggingUI(QString newLogging);

    void AddRecord(DataBase::Signal signal,int StartIdx,bool IsReal);

    bool UpdateMannulSet();

    void DeleteRecord(int Mode,myQSqlDatabase *TMATE_Database);

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

private:
    Ui::FormAlarmInformation *ui;
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);


    //窗口名称
    QString m_name;

private slots:

};

#endif // FORMALARMINFORMATION_H
