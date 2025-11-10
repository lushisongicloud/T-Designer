#include "qdlglogin.h"
#include "ui_qdlglogin.h"

#include    <QMouseEvent>
#include    <QMessageBox>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern QString m_strFilePath;

qdlglogin::qdlglogin(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::qdlglogin)
{
    ui->setupUi(this);

    this->setWindowIcon(QIcon(":/widget/Logo.ico"));

    //密码输入编辑框设置为密码输入模式
    ui->lineEdit_account_password->setEchoMode(QLineEdit::Password);

    //无边框，但是在任务显示对话框标题
    this->setWindowFlags(Qt::FramelessWindowHint);

    //设置数据库连接
    if(!account_database_connection())
        delete this;

    ui->lineEdit_account_name->setText("admin");
    ui->lineEdit_account_password->setText("admin");
}

qdlglogin::~qdlglogin()
{
    delete ui;
}

bool qdlglogin::account_database_connection()
{
    //链接数据库,连接成功则返回true
    db_account=QSqlDatabase::contains("qt_sql_default_connection")
            ?QSqlDatabase::database("qt_sql_default_connection")
           :QSqlDatabase::addDatabase("QSQLITE");

    QFile  File(m_strFilePath);
    //若数据库文件不存在，则返回
    if(!File.exists()){
        QMessageBox::warning(nullptr, "错误", "数据库文件不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return false;
    }

    db_account.setDatabaseName(m_strFilePath);

    if (!db_account.open()){
        QMessageBox::warning(nullptr, QObject::tr("Database Error"),
                             db_account.lastError().text());
        return false;
    }

    //设置数据库选择模型
    qsQuery_account = QSqlQuery(db_account);
    return true;
}

void qdlglogin::on_pushButton_account_login_clicked()
{
    static int m_tryCount = 0;
    QString user=ui->lineEdit_account_name->text().trimmed();//输入用户名
    QString pswd=ui->lineEdit_account_password->text().trimmed(); //输入密码
    QString encrptPSWD=encrypt(pswd); //对输入密码进行加密

    if(user==manageAccount.Operating_user)
    {
        loginAccount = manageAccount;
        loginAccount.Operating_PSW = encrypt(manageAccount.Operating_PSW);
    }
    else
        loginAccount=selectAccount(user);

    //登录校验
    if (encrptPSWD==loginAccount.Operating_PSW)
    {
        //若为普通用户登录，则更新登录时间
        if(user!=manageAccount.Operating_user)
        {
            QDateTime current_date_time =QDateTime::currentDateTime();//获取当前时间
            QString sql_prepare=QString::asprintf("UPDATE Account SET loginTime =  '%1' WHERE ID = %2 ")
                    .arg(current_date_time.toString("yyyy/MM/dd hh:mm:ss")).arg(loginAccount.Operating_ID);
            qsQuery_account.prepare(sql_prepare);
            qsQuery_account.exec();
        }
        this->accept(); //对话框 accept()，关闭对话框
    }
    else
    {
        m_tryCount++; //错误次数
        if (m_tryCount>3)
        {
            QMessageBox::critical(nullptr, "错误", "输入错误次数太多，强行退出");
            this->reject(); //退出
        }
        else
            QMessageBox::warning(nullptr, "错误提示", "用户名或密码错误");
    }
}

QString qdlglogin::encrypt(const QString &str)
{ //字符串MD5算法加密
    QByteArray btArray;

    btArray.append(str);//加入原始字符串

    QCryptographicHash hash(QCryptographicHash::Md5);  //Md5加密算法

    hash.addData(btArray);  //添加数据到加密哈希值

    QByteArray resultArray =hash.result();  //返回最终的哈希值

    QString md5 =resultArray.toHex();//转换为16进制字符串

    return  md5;
}

DataBase::Str_account qdlglogin::selectAccount(QString UserOrID)
{    
    QString sql_prepare = QString("select ID,user,passwords,level,loginTime "
                                  "from Account WHERE ID = %1 OR user = '%2'")
            .arg(UserOrID.toInt()).arg(UserOrID);

    DataBase::Str_account Account;
    qsQuery_account.exec(sql_prepare);
    if(qsQuery_account.first()){
        Account.Operating_ID = qsQuery_account.value(0).toInt();
        Account.Operating_user = qsQuery_account.value(1).toString();
        Account.Operating_PSW = qsQuery_account.value(2).toString();
        Account.Operating_limit = qsQuery_account.value(3).toInt();
        Account.LoginTime =  qsQuery_account.value(4).toDateTime();
    }
    return  Account;
}

void qdlglogin::mousePressEvent(QMouseEvent *event)
{ //鼠标按键被按下
    if (event->button() == Qt::LeftButton)
    {
        m_moving = true;
        //记录下鼠标相对于窗口的位置
        //event->globalPos()鼠标按下时，鼠标相对于整个屏幕位置
        //pos() this->pos()鼠标按下时，窗口相对于整个屏幕位置
        m_lastPos = event->globalPos() - pos();
    }
    return QDialog::mousePressEvent(event);  //
}

void qdlglogin::mouseMoveEvent(QMouseEvent *event)
{//鼠标按下左键移动
    //(event->buttons() && Qt::LeftButton)按下是左键
    //鼠标移动事件需要移动窗口，窗口移动到哪里呢？就是要获取鼠标移动中，窗口在整个屏幕的坐标，然后move到这个坐标，怎么获取坐标？
    //通过事件event->globalPos()知道鼠标坐标，鼠标坐标减去鼠标相对于窗口位置，就是窗口在整个屏幕的坐标
    if (m_moving && (event->buttons() && Qt::LeftButton)
            && (event->globalPos()-m_lastPos).manhattanLength() > QApplication::startDragDistance())
    {
        move(event->globalPos()-m_lastPos);
        m_lastPos = event->globalPos() - pos();
    }
    return QDialog::mouseMoveEvent(event);
}

void qdlglogin::mouseReleaseEvent(QMouseEvent *event)
{//鼠标按键释放,停止移动
    Q_UNUSED(event);
    m_moving=false;
}

void qdlglogin::on_pushButton_cancel_clicked()
{
    this->reject();
}

