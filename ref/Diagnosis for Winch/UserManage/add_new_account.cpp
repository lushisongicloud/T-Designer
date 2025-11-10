#include "add_new_account.h"
#include "ui_add_new_account.h"
#include <QCryptographicHash>
#include <QMessageBox>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern DataBase::Str_account  m_loginAccount;

add_new_account::add_new_account(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QDialog(parent),ui(new Ui::add_new_account),m_Database(TMATE_Database)
{
    ui->setupUi(this);
    this->setWindowFlags(Qt::Dialog| Qt::FramelessWindowHint);//隐藏窗口边框
    this->setAttribute(Qt::WA_TranslucentBackground);//背景透明
    setWindowTitle(tr("Add New Account"));
    ui->btn_add->setEnabled(false);
    ui->label_warning_2->setText("用户名不得为空");
    ui->lineEdit_account_psd_1->setEchoMode(QLineEdit::Password); //密码输入编辑框设置为密码输入模式
    ui->lineEdit_account_psd_2->setEchoMode(QLineEdit::Password); //密码输入编辑框设置为密码输入模式
}

add_new_account::~add_new_account()
{
    delete ui;
}

void add_new_account::on_btn_add_clicked()//确认按钮按下
{
    //读取输入信息
    m_Account.Operating_user = ui->lineEdit_account_name->text();//用户名;
    m_Account.Operating_limit = ui->comboBox_account_limit->currentIndex();//权限等级
    m_Account.Operating_PSW = encrypt(ui->lineEdit_account_psd_2->text());//加密后的密码

    //密码和用户名不能为空
    if((m_Account.Operating_user=="")||(ui->lineEdit_account_psd_2->text()==""))
    {
        QMessageBox::warning(nullptr, "提示", "请将信息填写完整");
        return;
    }

    //admin为默认初始超级用户，不支持创建
    if(m_Account.Operating_user =="admin")
    {
        QMessageBox::warning(nullptr, "提示", "默认超级管理员用户不支持创建");
        return;
    }

    //不支持创建同用户名用户
    if(m_Database->IsAccountExist(m_Account.Operating_user))
    {
        QMessageBox::warning(nullptr, "提示", "用户已存在");
        return;
    }

    //不支持创建比当前登录用户权限高的账户
    if(m_loginAccount.Operating_limit>m_Account.Operating_limit){
        QMessageBox::warning(nullptr, "提示", "您的权限不足以创建此用户");
        return;
    }

    this->accept();
}

QString add_new_account::encrypt(const QString &str)
{ //字符串MD5算法加密
    QByteArray btArray;

    btArray.append(str);//加入原始字符串

    QCryptographicHash hash(QCryptographicHash::Md5);  //Md5加密算法

    hash.addData(btArray);  //添加数据到加密哈希值

    QByteArray resultArray =hash.result();  //返回最终的哈希值

    QString md5 =resultArray.toHex();//转换为16进制字符串

    return  md5;
}

void add_new_account::on_lineEdit_account_psd_2_textChanged(const QString &arg1)//再次输入密码不一致
{
    if(ui->lineEdit_account_psd_1->text()!=arg1)
    {
        ui->label_warning->setText("输入密码不一致");
        ui->btn_add->setEnabled(false);
    }
    if(ui->lineEdit_account_psd_1->text()==arg1)
    {
        ui->label_warning->setText("");
        ui->btn_add->setEnabled(true);
    }
}

void add_new_account::on_lineEdit_account_psd_1_textChanged(const QString &arg1)//再次输入密码不一致
{
    if(ui->lineEdit_account_psd_2->text()!=arg1)
    {
        ui->label_warning->setText("输入密码不一致");
        ui->btn_add->setEnabled(false);
    }
    if(ui->lineEdit_account_psd_2->text()==arg1)
    {
        ui->label_warning->setText("");
        ui->btn_add->setEnabled(true);
    }
}

void add_new_account::on_lineEdit_account_name_textChanged(const QString &arg1)
{
    if(arg1 == "")
    {
        ui->label_warning_2->setText("用户名不得为空");
        ui->btn_add->setEnabled(false);
    }
    else
    {
        ui->label_warning_2->setText("");
        ui->btn_add->setEnabled(true);
    }
}
