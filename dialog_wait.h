/*************************************************
 * Copyright:杭州诺云科技有限公司
 * Author:许伟
 * Date:2020-5-11
 * Description:诊断初始化时等待覆盖界面
**************************************************/
#ifndef DIALOG_WAIT_H
#define DIALOG_WAIT_H

#include <QDialog>

namespace Ui {
class Dialog_wait;
}

class Dialog_wait : public QDialog
{
    Q_OBJECT

public:
    explicit Dialog_wait(QWidget *parent = nullptr);
    ~Dialog_wait();

    void CloseWindow ();

private:
    Ui::Dialog_wait *ui;
};

#endif // DIALOG_WAIT_H
