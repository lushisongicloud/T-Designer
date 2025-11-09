//#ifndef ADD_NEW_ACCOUNT_H
//#define ADD_NEW_ACCOUNT_H

#ifndef ADD_NEW_ACCOUNT_H
#define ADD_NEW_ACCOUNT_H

#include <QDialog>
#include "myqsqldatabase.h"

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-9
 * Description:账户创建窗口,用于新建账户信息
**************************************************/


namespace Ui {
class add_new_account;
}

class add_new_account : public QDialog
{
    Q_OBJECT

public:
    explicit add_new_account(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~add_new_account();

    //获取创建的账户信息
    DataBase::Str_account GetCreatAccount(){return m_Account;}

    //密码字符串加密
    QString encrypt(const QString& str);

private slots:
    void on_btn_add_clicked();

    void on_lineEdit_account_psd_2_textChanged(const QString &arg1);

    void on_lineEdit_account_psd_1_textChanged(const QString &arg1);

    void on_lineEdit_account_name_textChanged(const QString &arg1);

private:
    Ui::add_new_account *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    DataBase::Str_account m_Account;//账户信息
};

#endif // ADD_NEW_ACCOUNT_H
