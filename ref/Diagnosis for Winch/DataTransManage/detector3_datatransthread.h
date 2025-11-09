#ifndef DETECTOR3_DATATRANSTHREAD_H
#define DETECTOR3_DATATRANSTHREAD_H

#include <QThread>
#include "Diagnosis/rulevariablepool.h"

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:1.Detector3通信端口的通信线程
 * Description:2.实时更新m_RuleVariablePool中由Detector3通信的变量
 * Description:3.目前通信协议未写，暂以一个随机数代替
**************************************************/

class Detector3_DataTransThread : public QThread
{
    Q_OBJECT
private:
    bool    m_stop=false; //停止线程

    //该线程中接收的信号值
    double Derect3 = 0;

protected:
    void    run() Q_DECL_OVERRIDE;  //线程任务

public:
    Detector3_DataTransThread();

    void stopThread(); //结束线程
};

#endif // DETECTOR3_DATATRANSTHREAD_H
