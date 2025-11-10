#ifndef FORMREALTIMEDATA_H
#define FORMREALTIMEDATA_H

#include <QWidget>
#include "myqsqldatabase.h"

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:1.数据实时状态显示窗口,因显示变量个数未知，暂未完成
 * Description:2.该窗口应支持对每个变量数值的设置或者统一设置
**************************************************/

namespace Ui {
class FormRealTimeData;
}

class FormRealTimeData : public QWidget
{
    Q_OBJECT

public:
    explicit FormRealTimeData(QWidget *parent = nullptr);
    ~FormRealTimeData();

    //更新显示
    void UpDate(QMap<QString,DataBase::Signal> signal);
private:
    Ui::FormRealTimeData *ui;



private slots:

    void on_Btn_RealTimeDataPreviousPage_clicked();

    void on_Btn_RealTimeDataNextPage_clicked();
};

#endif // FORMREALTIMEDATA_H
