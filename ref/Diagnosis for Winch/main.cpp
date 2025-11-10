#include "mainwindow.h"
#include <QApplication>
#include "UserManage/qdlglogin.h"
#include "mythread.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif


int main(int argc, char *argv[])
{
    QTextCodec *codec = QTextCodec::codecForName("UTF-8");
    QTextCodec::setCodecForLocale(codec); //解决汉字乱码问题
    Mythread *tid_udp,*tid_dataSave;

    QApplication a(argc, argv);
    a.setFont(QFont("Microsoft Yahei", 10));

    qdlglogin   *dlgLogin=new qdlglogin(); //创建对话框
    MainWindow w;

    if (dlgLogin->exec()==QDialog::Accepted){
        w.setLoginAccount(dlgLogin->getLoginAccount());
        delete dlgLogin;
        tid_udp=new Mythread(NULL,0);tid_udp->start();
        tid_dataSave=new Mythread(NULL,1);tid_dataSave->start();
        //w.showMaximized();
        w.show();
        return a.exec();
    }
    else  return  0;
}
