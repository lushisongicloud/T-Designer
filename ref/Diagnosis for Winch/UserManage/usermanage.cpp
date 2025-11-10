#include "usermanage.h"
#include "ui_usermanage.h"

#include "add_new_account.h"

extern DataBase::Str_account  m_loginAccount;

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

UserManage::UserManage(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),ui(new Ui::UserManage),m_Database(TMATE_Database)
{
    ui->setupUi(this);

    //设置遮罩窗口
    mpShadeWindow = new QWidget(this);
    QString str("QWidget{background-color:rgba(0,0,0,0.6);}");
    mpShadeWindow->setStyleSheet(str);
    mpShadeWindow->setGeometry(0, 0, 1, 1);
    mpShadeWindow->hide();

    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("ID") << tr("用户名称") << tr("权限等级") << tr("最后登录时间");

    StretchHorizontalIndex<<0<<1<<2<<3;
    TableWidgetQss(headerString,ui->tableWidget_Account,StretchHorizontalIndex);

    ui->lineEdit_AccountName->clear();
    ui->Cmb_AuthorityLevels->setCurrentIndex(0);
    update();
}

UserManage::~UserManage()
{
    delete ui;
}

QString UserManage::encrypt(const QString &str)
{ //字符串MD5算法加密
    QByteArray btArray;

    btArray.append(str);//加入原始字符串

    QCryptographicHash hash(QCryptographicHash::Md5);  //Md5加密算法

    hash.addData(btArray);  //添加数据到加密哈希值

    QByteArray resultArray =hash.result();  //返回最终的哈希值

    QString md5 =resultArray.toHex();//转换为16进制字符串

    return  md5;

}

void UserManage::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
{

    QString tableWidgetStyleSheet = "QTableWidget{border:0px;"
                                    "background-color: rgba(255, 255, 255, 0.2);"
                                    "alternate-background-color: rgba(243, 248, 251, 0.2);"
                                    "color: rgb(0, 0, 0);font: 14pt '微软雅黑';}"
                                    "QTableWidget::item:selected{"
                                    "color: rgb(0, 0, 0);"
                                    "background-color: rgba(191, 223, 252, 0.2);}"
                                    "QHeaderView::section{"
                                    "border:1px solid rgba(19, 67, 79, 1);"
                                    "background-color: rgba(19, 67, 79, 1);"
                                    "height: 35px;font: 75 14pt '微软雅黑';color: rgba(102, 249, 247, 1);"
                                    "padding-left: 4px;"
                                    "text-align:center;}"
                                    "QTableWidget::indicator {width: 50px;height: 50px;}"
                                    "QTableWidget::indicator:unchecked {image: url(:/new/prefix1/No.png);}"
                                    "QTableWidget::indicator:checked {image: url(:/new/prefix1/Yes.png);}"
                                    "QTableWidget::item{padding-top:15px;padding-bottom:15px;}";

    TableWidget->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    TableWidget->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选
    TableWidget->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色
    //设置表格的默认的列数
    TableWidget->setColumnCount(headerString.count());//设置列数
    TableWidget->setHorizontalHeaderLabels(headerString);//设置列标题

    for(int i=0;i<StretchHorizontalIndex.size();i++)
        TableWidget->horizontalHeader()->setSectionResizeMode(StretchHorizontalIndex[i], QHeaderView::Stretch);

    TableWidget->setAlternatingRowColors(true);//使表格颜色交错功能为真
    TableWidget->setFocusPolicy(Qt::NoFocus);
    TableWidget->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    TableWidget->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑
}


void UserManage::update()
{
    m_account.clear();
    m_account = m_Database->SelectAccountsInforFromAccountTable(ui->lineEdit_AccountName->text(),ui->Cmb_AuthorityLevels->currentIndex());

    ui->tableWidget_Account->blockSignals(true);

    //设置表格的默认的行数
    ui->tableWidget_Account->setRowCount(m_account.size());//设置默认的行数
    ui->tableWidget_Account->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_account.size();i++){

        ui->tableWidget_Account->setItem(i,0,new QTableWidgetItem(QString::number(m_account[i].Operating_ID)));
        ui->tableWidget_Account->setItem(i,1,new QTableWidgetItem(m_account[i].Operating_user));


        if(m_account[i].Operating_limit>2)
            m_account[i].Operating_limit = 2;
        QStringList LimitGrade = {"超级管理员","管理员","普通用户"};
        ui->tableWidget_Account->setItem(i,2,new QTableWidgetItem(LimitGrade[m_account[i].Operating_limit]));
        ui->tableWidget_Account->setItem(i,3,new QTableWidgetItem(m_account[i].LoginTime.toString("yyyy/MM/dd hh:mm:ss")));


        ui->tableWidget_Account->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_Account->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_Account->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_Account->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    ui->tableWidget_Account->blockSignals(false);
}

void UserManage::SetChangeEnabled(bool enable)
{
    ui->Btn_AccountNew->setEnabled(enable);
    ui->Btn_AccountDelete->setEnabled(enable);
    ui->Btn_AccountLevelAlter->setEnabled(enable);
    ui->Btn_AccountPasswordsAlter->setEnabled(enable);
}

void UserManage::on_Btn_AccountSelect_clicked()
{//检索按钮
    update();
}

void UserManage::on_Btn_AccountPasswordsAlter_clicked()
{//修改用户密码
        int curRow = ui->tableWidget_Account->currentRow();

        if(curRow==-1){
            QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择账户"),QMessageBox::Yes);
            return;}

        QString User = ui->tableWidget_Account->item(curRow,1)->text();//获取当前名称

        QString original_password;//原始密码
        QString New_password_1;//第一次更改密码
        QString New_password_2;//第二次更改密码

        QString dlgTitle="修改密码";
        QString txtLabel_1="请输入原始密码:";
        QString defaultInput="";
        QLineEdit::EchoMode echoMode=QLineEdit::Password;//密码输入
        bool ok=false;
        QString text = QInputDialog::getText(nullptr, dlgTitle,txtLabel_1, echoMode,defaultInput, &ok);
        if (ok)
        {
            //查询数据库对应信息
            original_password = m_Database->SelectPasswordsFromAccountTable(User);

            text = encrypt(text);

            if( text == original_password)
            {
                QString txtLabel_2="请输入修改密码:";
                bool ok=false;
                New_password_1 = QInputDialog::getText(nullptr, dlgTitle,txtLabel_2, echoMode,defaultInput, &ok);
                if (ok)
                {
                    QString txtLabel_3="请再次输入修改密码:";
                    bool ok=false;
                    New_password_2 = QInputDialog::getText(nullptr, dlgTitle,txtLabel_3, echoMode,defaultInput, &ok);
                    if (ok)
                    {
                        if( New_password_1 == New_password_2)
                        {
                            New_password_2 = encrypt(New_password_2);

                            m_Database->UpdateAccountPasswords(User,New_password_2);

                            QString dlgTitle="提示";
                            QString strInfo="密码修改成功";
                            QMessageBox::warning(nullptr, dlgTitle, strInfo);
                        }
                        else
                        {
                            {
                                QString dlgTitle="warning";
                                QString strInfo="输入密码不一致";
                                QMessageBox::warning(nullptr, dlgTitle, strInfo);
                            }
                        }
                    }
                }
            }
            else
            {
                QString dlgTitle="warning";
                QString strInfo="原始密码错误";
                QMessageBox::warning(nullptr, dlgTitle, strInfo);
            }
        }
        update();//账号管理表显示更新
}

void UserManage::on_Btn_AccountDelete_clicked()
{//删除账户
    if(m_loginAccount.Operating_limit>=2){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("普通用户无法删除账户"),QMessageBox::Yes);
        return;
    }
    int curRow = ui->tableWidget_Account->currentRow();
    if(curRow==-1){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择要删除的账户"),QMessageBox::Yes);
        return;}


    QString User = ui->tableWidget_Account->item(curRow,1)->text();//获取当前名称
    DataBase::Str_account  selectedAccount = m_Database->SelectAccountFromAccountTable(User);
    if(m_loginAccount.Operating_limit>=selectedAccount.Operating_limit){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("权限不足无法删除账户"),QMessageBox::Yes);
        return;
    }

    //确认是否删除
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("是否确认删除该账户?"),
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes)
    {
        if(m_Database->DeleteAccountFromAccountTable(User))
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("账户已删除"));
        else
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("删除失败"));
        update();
    }
}

void UserManage::on_Btn_AccountLevelAlter_clicked()
{//修改账户权限
        int curRow = ui->tableWidget_Account->currentRow();

        if(curRow==-1){
            QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择账户"),QMessageBox::Yes);
            return;}

        QString User = ui->tableWidget_Account->item(curRow,1)->text();//获取当前要修改的用户名称
        QString UserLimit = ui->tableWidget_Account->item(curRow,2)->text();//获取当前要修改的用户权限

        DataBase::Str_account  selectedAccount = m_Database->SelectAccountFromAccountTable(User);

        if(m_loginAccount.Operating_limit>selectedAccount.Operating_limit){
            QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("权限不足无法修改账户权限"),QMessageBox::Yes);
            return;
        }

        QDialog *dialogChangeLimit =new QDialog();
        dialogChangeLimit->setWindowTitle("修改用户权限");
        dialogChangeLimit->setMinimumSize(QSize(250,100));

        QFormLayout *formlayoutEnterUsernameAndPassword = new QFormLayout(dialogChangeLimit);

        QLabel *lineEditUserName = new QLabel(dialogChangeLimit);
        lineEditUserName->setText(User);

        QComboBox *Limit = new QComboBox();
        QStringList LimitGrade = {"超级管理员","管理员","普通用户"};
        Limit->addItems(LimitGrade);//密码输入

        QHBoxLayout *layout = new QHBoxLayout(nullptr);
        QPushButton *pushbuttonOK = new QPushButton(dialogChangeLimit);
        pushbuttonOK->setText("确认");
        QPushButton *pushbuttonCancel = new QPushButton(dialogChangeLimit);
        pushbuttonCancel->setText("取消");
        layout->addWidget(pushbuttonOK);
        layout->addWidget(pushbuttonCancel);

        formlayoutEnterUsernameAndPassword->addRow("用户名:", lineEditUserName);

        formlayoutEnterUsernameAndPassword->addRow("权  限:", Limit);
        formlayoutEnterUsernameAndPassword->addRow(layout);
        Limit->setCurrentText(UserLimit);
        QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogChangeLimit,SLOT(accept()));
        QObject::connect(pushbuttonCancel,SIGNAL(clicked()),dialogChangeLimit,SLOT(close()));

        if (dialogChangeLimit->exec()==QDialog::Accepted)
        {
            if(m_loginAccount.Operating_limit<=selectedAccount.Operating_limit&&m_loginAccount.Operating_limit<=Limit->currentIndex()){
                m_Database->UpdateAccountLimit(User,Limit->currentIndex());

                QString dlgTitle="提示";
                QString strInfo="权限修改成功";
                QMessageBox::warning(nullptr, dlgTitle, strInfo);

                update();//账号管理表显示更新
            }
            else{
                QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("权限不足无法修改账户权限"),QMessageBox::Yes);
                return;
            }
        }
        delete layout;
        delete dialogChangeLimit;
}

void UserManage::on_Btn_AccountNew_clicked()
{//新增账户
        mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
        mpShadeWindow->show();//遮罩效果

        //模态对话框，动态创建，用过后删除
        add_new_account    *add_new_account_view=new add_new_account(nullptr,m_Database); //创建对话框
        Qt::WindowFlags    flags=add_new_account_view->windowFlags();
        add_new_account_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

        int ret=add_new_account_view->exec();// 以模态方式显示对话框

        if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
        {
            DataBase::Str_account m_Account = add_new_account_view->GetCreatAccount();
            //qDebug()<<m_Account.LoginTime<<m_Account.Operating_ID<<m_Account.Operating_PSW<<m_Account.Operating_limit<<m_Account.Operating_user;
            m_Database->InsertAccountToAccounttable(add_new_account_view->GetCreatAccount());
            QString dlgTitle="注册账号";
            QString strInfo=QString::asprintf("注册成功！");
            QMessageBox::information(nullptr, dlgTitle, strInfo,
                                     QMessageBox::Ok,QMessageBox::NoButton);
        }
        delete add_new_account_view; //删除对话框
        mpShadeWindow->hide();//遮罩效果取消
        update();
}






