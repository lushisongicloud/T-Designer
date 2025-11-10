#ifndef VARIABLEMANAGE_H
#define VARIABLEMANAGE_H

#include <QWidget>
#include "myqsqldatabase.h"

namespace Ui {
class VariableManage;
}

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:变量库管理界面
**************************************************/


class VariableManage : public QWidget
{
    Q_OBJECT

public:
    explicit VariableManage(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~VariableManage();

    void update();


    //设置是否可修改变量信息
    void SetChangeEnabled(bool enable);

private slots:
    void on_Btn_VariableBaseSelect_clicked();

    void on_Btn_VariableBaseNew_clicked();

    void on_Btn_VariableBaseAlter_clicked();

    void on_Btn_VariableBaseDelete_clicked();

private:
    Ui::VariableManage *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    QWidget* mpShadeWindow = nullptr;//遮罩窗口

    QVector<DataBase::Str_Signal> m_Signal;

private:
    //表格QSS设置,参数列表分别为表头字符串、表指针、拓展宽度的列号列表
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);


signals:
    void  VariableNameChange(QString OraginVariableName,QString ChangeVariableName);
    void  VariableDelete(QString VariableName);
};

#endif // VARIABLEMANAGE_H
