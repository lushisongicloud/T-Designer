#include "mainwindow.h"
#include <QApplication>
#include <ActiveQt/QAxWidget>
#include <ActiveQt/QAxObject>
#include <QtSql>
#include "common.h"
#define LIBFilePathName "D:\\SynologyDrive\\Project\\T_DESIGNER\\ref\\LdMainData.db"
QSqlDatabase  T_LibDatabase;
QAxWidget *GlobalBackAxWidget = nullptr;
IMxDrawApplication *pApp = nullptr;
bool database_init()
{
    if(T_LibDatabase.isOpen()) T_LibDatabase.close();
    T_LibDatabase = QSqlDatabase::addDatabase("QSQLITE","LdMainData");
    QFile  File(LIBFilePathName);
    if(!File.exists()){
            QMessageBox::warning(nullptr, "错误", "数据库文件不存在",
                                 QMessageBox::Ok,QMessageBox::NoButton);
            return false;
    }
    else
        T_LibDatabase.setDatabaseName(LIBFilePathName);
    if (!T_LibDatabase.open()){
        QMessageBox::warning(nullptr, "错误", "数据库文件打开错误", QMessageBox::Ok,QMessageBox::NoButton);
        return false;
    }
    return true;
}
int main(int argc, char *argv[])
{
     QApplication a(argc, argv);

     // 设置应用程序默认编码
     QTextCodec *codec = QTextCodec::codecForName("UTF-8");
     QTextCodec::setCodecForLocale(codec);

     OleInitialize(0);
     if(!database_init())  return 0;
     MainWindow w;
     w.showMaximized(); 
     return a.exec();
}
