#ifndef DIAGNOSIS_H
#define DIAGNOSIS_H

#include <QThread>
#include "rulevariablepool.h"

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-9
 * Description:故障诊断线程
**************************************************/

class Diagnosis : public QThread
{
    Q_OBJECT
private:
    bool    m_stop=false; //停止线程

protected:
    void    run() Q_DECL_OVERRIDE;  //线程任务

public:
    Diagnosis();

    void stopThread(); //结束线程

signals:
    void  newFaliureError(QVector<DataBase::Signal> signal); //发射故障报警信号
    void  newWarnningError(); //发射预警报警信号
    void  newBasicSignalUpdate(); //发射基础信号值更新信号
};

#endif // DIAGNOSIS_H
