#ifndef CONNECTSET_H
#define CONNECTSET_H

#include <QWidget>
#include "myqsqldatabase.h"

/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:通信配置子窗口界面及配置操作
**************************************************/

namespace Ui {
class ConnectSet;
}

class ConnectSet : public QWidget
{
    Q_OBJECT

public:
    explicit ConnectSet(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~ConnectSet();

    //设置所有配置按钮是否可用
    void SetConfigurationEnabled(bool enable);

private:
    Ui::ConnectSet *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    QWidget* mpShadeWindow = nullptr;//遮罩窗口

    //初始化系统IP设置UI
    void InitSystemConfigUI();

private slots:

    void on_pushButton_MK2CPU_IP_SET_clicked();

    void on_pushButton_MK2CPU_PORT_SET_clicked();

    void on_pushButton_MK5CPU_IP_SET_clicked();

    void on_pushButton_MK5CPU_PORT_SET_clicked();

    void on_pushButton_Detector1_IP_SET_clicked();

    void on_pushButton_Detector1_PORT_SET_clicked();

    void on_pushButton_Detector2_IP_SET_clicked();

    void on_pushButton_Detector2_PORT_SET_clicked();

    void on_pushButton_Detector3_IP_SET_clicked();

    void on_pushButton_Detector3_PORT_SET_clicked();
};

#endif // CONNECTSET_H
