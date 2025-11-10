#ifndef USERMANAGE_H
#define USERMANAGE_H

#include <QWidget>

#include "myqsqldatabase.h"
#include "QTableWidget"
#include <QMessageBox>
#include <QFileDialog>
#include <QtCharts>

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-9
 * Description:账户管理窗口
**************************************************/

namespace Ui {
class UserManage;
}

class UserManage : public QWidget
{
    Q_OBJECT

public:
    explicit UserManage(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~UserManage();

    //更新显示
    void update();

    //设置是否可修改账户信息
    void SetChangeEnabled(bool enable);

private:
    Ui::UserManage *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    QWidget* mpShadeWindow = nullptr;//遮罩窗口

    QVector<DataBase::Str_account> m_account;//检索出的账户数据

private slots:

    void on_Btn_AccountSelect_clicked();

    void on_Btn_AccountNew_clicked();

    void on_Btn_AccountDelete_clicked();

    void on_Btn_AccountPasswordsAlter_clicked();

    void on_Btn_AccountLevelAlter_clicked();

private:
    //表格QSS设置,参数列表分别为表头字符串、表指针、拓展宽度的列号列表
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);

    //字符串加密
    QString encrypt(const QString& str);
};

#endif // USERMANAGE_H
