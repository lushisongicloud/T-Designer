#ifndef DETECTOR2_DATATRANSTHREAD_H
#define DETECTOR2_DATATRANSTHREAD_H

#include <QThread>
#include "Diagnosis/rulevariablepool.h"
#include <QTcpSocket>
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:1.Detector2通信端口的通信线程
 * Description:2.实时更新m_RuleVariablePool中由Detector2通信的变量
 * Description:3.目前通信协议未写，暂以一个随机数代替
**************************************************/

class Detector2_DataTrans : public QObject
{
    Q_OBJECT

public:
    explicit Detector2_DataTrans(myQSqlDatabase *TMATE_Database = nullptr);

    Detector2_DataTrans();

    void ProcessBuf(unsigned char *Buf,int Len);

    QString BufToStr(unsigned char* buf,int len);

    QTcpSocket *Socket;

    QTimer *TimerTcp;

    bool ConnectSt=false;

private:
    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    //该线程中接收的信号值
    int DetectVPara[16];
    int DetectIPara[6];
    bool DetectVIsUpdated=false;
    bool DetectIIsUpdated=false;
protected:
    //void    run() Q_DECL_OVERRIDE;  //线程任务

public slots:
    void readBuf(); //读取报文（自动监听）
    //void writeBuf(unsigned char * buf,int Len);//接到循环子线程checkthread发送报文
    void conetHost(QString hostIP,quint16 port);//连接服务器
    void conetOK();  //发送连接成功信号（自动监听）
    void disconet(); //发送断开连接信号（自动监听）
    void timerRun();
};

#endif // DETECTOR2_DATATRANSTHREAD_H
