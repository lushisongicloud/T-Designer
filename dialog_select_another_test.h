/*************************************************
 * Copyright:杭州诺云科技有限公司
 * Author:许伟
 * Date:2020-5-11
 * Description:诊断过程中选择其他测试界面及相关函数
**************************************************/
#ifndef DIALOG_SELECT_ANOTHER_TEST_H
#define DIALOG_SELECT_ANOTHER_TEST_H

#include <QDialog>
#include "common.h"
namespace Ui {
class Dialog_select_another_test;
}

class Dialog_select_another_test : public QDialog
{
    Q_OBJECT

public:
    explicit Dialog_select_another_test(QWidget *parent = nullptr,QList<TestPoint> *list_test = nullptr);
    ~Dialog_select_another_test();

    QString get_test_name();
    void SetTestPreference(int TestPreference);
    void setText();
    QString test_name;
    int m_Mode;

private:
    Ui::Dialog_select_another_test *ui;
    QList<TestPoint> m_list_test;

private slots:

    void on_btn_tool_serch_clicked();
    void on_Test_tableWidget_clicked(const QModelIndex &index);
    void on_CbTestPreference_currentIndexChanged(int index);
};

#endif // DIALOG_SELECT_ANOTHER_TEST_H
