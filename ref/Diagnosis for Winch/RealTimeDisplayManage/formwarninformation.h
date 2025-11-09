#ifndef FORMWARNINFORMATION_H
#define FORMWARNINFORMATION_H

#include <QWidget>
#include <QMessageBox>
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
class FormWarnInformation;
}

class FormWarnInformation : public QWidget
{
    Q_OBJECT

public:
    //Name字段为窗口名称
    explicit FormWarnInformation(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~FormWarnInformation();

    //清空窗口显示

    //窗口增加显示newLogging字符串
    void DeleteRecord(int Mode);

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    QTimer* timerUpdateUI;

private:
    Ui::FormWarnInformation *ui;
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);
    void UpdateHisWarnRecord();
    int CurWarnPageNum=1;

    //窗口名称
    QString m_name;

private slots:
    void DoUpdateUI();
    void on_BtnWarnTable_FirstPage_clicked();
    void on_BtnWarnTable_PreviousPage_clicked();
    void on_BtnNextWarnPage_clicked();
    void on_BtnLastWarnPage_clicked();
    void on_spinBoxWarnPageNum_valueChanged(int arg1);
    void on_BtnWarnSearch_clicked();
    void on_radioButton_HisWarn_clicked();
    void on_radioButton_realtimeWarn_clicked();
    void on_BtnClearCurAllWarnRecords_clicked();
    void on_BtnClearCurSelectWarnRecords_clicked();
    void on_BtnClearCurWarnPageRecords_clicked();
    void on_CbPageWarnRecordsNumber_currentIndexChanged(int index);
};

#endif // FORMALARMINFORMATION_H
