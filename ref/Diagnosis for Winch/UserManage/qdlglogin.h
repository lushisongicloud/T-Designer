#ifndef QDLGLOGIN_H
#define QDLGLOGIN_H

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-9
 * Description:账户登陆界面
**************************************************/


#include <QDialog>
#include <QtSql>
#include <QDateTime>
#include "myqsqldatabase.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

namespace Ui {
class qdlglogin;
}

class qdlglogin : public QDialog
{
    Q_OBJECT
private:

    Ui::qdlglogin *ui;

    bool    m_moving=false;//表示窗口是否在鼠标操作下移动
    QPoint  m_lastPos;//上一次的鼠标位置

    //默认账户
    DataBase::Str_account  manageAccount{0,"admin","admin",0,QDateTime::currentDateTime()};

    //登陆账户
    DataBase::Str_account  loginAccount;

    QSqlDatabase  db_account;//数据库连接
    QSqlQuery qsQuery_account;//数据库选择模型

    int m_tryCount=0; //试错次数
    QString m_password;//从数据库读取的用户密码
    QDateTime current_date_time;//当前时间

private:

    QString encrypt(const QString& str);//字符串加密
    bool account_database_connection();//数据库链接
    DataBase::Str_account selectAccount(QString UserOrID);//从数据库选择账户

public:
    explicit qdlglogin(QWidget *parent = nullptr);
    ~qdlglogin();

    DataBase::Str_account getLoginAccount(){return loginAccount;}//获取当前登录账户信息

protected:
    //用于鼠标拖动窗口的鼠标事件操作
    void mousePressEvent(QMouseEvent *event);
    void mouseMoveEvent(QMouseEvent *event);
    void mouseReleaseEvent(QMouseEvent *event);

private slots:
    void on_pushButton_cancel_clicked();
    void on_pushButton_account_login_clicked();
};

#endif // QDLGLOGIN_H
