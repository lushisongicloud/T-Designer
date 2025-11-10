#ifndef FORMHYDRAULICSTATE_H
#define FORMHYDRAULICSTATE_H

#include <QWidget>
#include "myqsqldatabase.h"
#include <QDebug>
#include <QCheckBox>
#include "Diagnosis/rulevariablepool.h"
#include "Diagnosis/rulepool.h"
#include <QMouseEvent>
#include <QInputDialog>
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:1.液压实时状态图像显示窗口,因显示变量个数未知，暂未完成
 * Description:2.该窗口应支持对每个变量灯颜色的设置或者统一设置
**************************************************/

namespace Ui {
class FormHydraulicState;
}

class FormHydraulicState : public QWidget
{
    Q_OBJECT

public:
    explicit FormHydraulicState(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr);
    ~FormHydraulicState();
    myQSqlDatabase *m_Database = nullptr;//数据库检索类
    //更新显示
    void UpDate(QMap<QString,DataBase::Signal> signal);

    void SetStackWidgetPage(int WinInd);

    int GetStackWidgetPageName();

    void InitDisPlayRadioButton();

    void DelDisPlayRadioButton();

    void Set3DWidgetPNG(int Ind);

    QVector<QCheckBox *> DisPlayQCheckBox[5];
private:
    Ui::FormHydraulicState *ui;
    void LoadDisPlayRadioButton(int SignalPosIdx,QVector<DataBase::Signal> Alarm_signal);
protected:
    virtual bool eventFilter(QObject * obj,QEvent *event) override;
private slots:
    void on_BtReturn_6_clicked();
    void on_BtReturn_2_clicked();
    void on_BtReturn_3_clicked();
    void on_BtReturn_4_clicked();
    void on_BtReturn_5_clicked();
signals:
    void  newFaliureError(); //发射故障报警信号
};

#endif // FORMHYDRAULICSTATE_H
