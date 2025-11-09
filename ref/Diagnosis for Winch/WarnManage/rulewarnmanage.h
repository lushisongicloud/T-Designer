#ifndef RULEWARNMANAGE_H
#define RULEWARNMANAGE_H

#include <QWidget>
#include "myqsqldatabase.h"
#include "Diagnosis/rulepool.h"
#include <QTextEdit>
#include "texteditdelegate.h"
#include "dialogshowtaskcurve.h"
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:规则库管理界面
**************************************************/

namespace Ui {
class WarnManage;
}

class WarnManage : public QWidget
{
    Q_OBJECT

public:
    explicit WarnManage(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~WarnManage();

    //更新规则表
    void update();

    //设置是否可修改规则
    void SetChangeEnabled(bool enable);

private slots:
    void on_Btn_KnowledgeBaseSelect_clicked();

    void on_Btn_KnowledgeBaseCreat_clicked();

    void on_Btn_KnowledgeBaseAlter_clicked();

    void on_Btn_KnowledgeBaseDelete_clicked();

    void on_tableWidget_KnowledgeBase_cellChanged(int row, int column);

    void DoUpdateUI();

    void on_BtnSetStandard_clicked();

    void on_tableWidget_KnowledgeBase_doubleClicked(const QModelIndex &index);

private:
    Ui::WarnManage *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    QWidget* mpShadeWindow = nullptr;//遮罩窗口

    QVector<DataBase::Str_WarnRule> m_Rule;//规则库

    QTimer* timerUpdateUI;
private:
    //表格QSS设置,参数列表分别为表头字符串、表指针、拓展宽度的列号列表
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);

};

#endif // RULEWARNMANAGE_H
