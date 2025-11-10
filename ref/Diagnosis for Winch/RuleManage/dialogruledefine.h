#ifndef DIALOGRULEDEFINE_H
#define DIALOGRULEDEFINE_H

#include <QDialog>
#include "myqsqldatabase.h"
#include <QTableWidget>
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:规则定义窗口，规则检查功能和规则变量选取功能待开发
**************************************************/

namespace Ui {
class DialogRuleDefine;
}

class DialogRuleDefine : public QDialog
{
    Q_OBJECT

public:
    //TMATE_Database为数据库检索指针,rule为初始的规则值,isCreatRule是为新建规则还是修改规则的标志变量
    explicit DialogRuleDefine(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr
            ,DataBase::Str_Rule rule = {},bool isCreatRule = false);

    ~DialogRuleDefine();

    //获取定义的规则
    DataBase::Str_Rule GetDefinedRule(){return m_rule;}

private slots:
    //规则名称修改
    void on_lineEdit_RuleName_textChanged(const QString &arg1);

    //取消按钮
    void on_Btn_Cancel_clicked();

    //确定按钮
    void on_Btn_OK_clicked();

    //规则检查按钮
    void on_Btn_Check_clicked();

    void on_textEdit_Condition_textChanged();

    void on_textEdit_Then_textChanged();

    void on_textEdit_Else_textChanged();

    void on_tableWidget_BasicVariable_doubleClicked(const QModelIndex &index);

    void on_tableWidget_MidVariable_doubleClicked(const QModelIndex &index);

    void on_tableWidget_FaliureVariable_doubleClicked(const QModelIndex &index);

    void on_tableWidget_WarnningVariable_doubleClicked(const QModelIndex &index);

private:
    Ui::DialogRuleDefine *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    DataBase::Str_Rule m_rule;//规则

    bool m_isCreatRule = false;//为新建规则还是修改规则

    //bool check = false;

    QVector<DataBase::Str_Signal> m_BasicSignal;//基础信号列表
    QVector<DataBase::Str_Signal> m_MidSignal;//中间信号列表
    QVector<DataBase::Str_Signal> m_FaliureSignal;//故障信号列表
    QVector<DataBase::Str_Signal> m_WarnningSignal;//报警信号列表

    QTableWidget *m_TableWidget[4];
    //初始化窗口
    void InitTabWidget_Variable();

private:
    //表格QSS设置,参数列表分别为表头字符串、表指针、拓展宽度的列号列表
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);

protected:
    virtual bool eventFilter(QObject * obj,QEvent *event) override;
};

#endif // DIALOGRULEDEFINE_H
