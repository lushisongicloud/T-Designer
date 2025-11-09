#ifndef DIALOGVARIABLEDEFINE_H
#define DIALOGVARIABLEDEFINE_H

#include <QDialog>
#include "myqsqldatabase.h"
#include <QFormLayout>
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:规则定义窗口，变量定义界面
**************************************************/

namespace Ui {
class DialogVariableDefine;
}

class DialogVariableDefine : public QDialog
{
    Q_OBJECT

public:
    explicit DialogVariableDefine(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr,
                                  DataBase::Str_Signal signal = {},bool isCreatSignal = false);
    ~DialogVariableDefine();

    //获取定义的变量
    DataBase::Str_Signal GetDefinedSignal(){return m_signal;}

private slots:
    void on_btn_OK_clicked();

    void on_lineEdit_name_textChanged(const QString &arg1);

    void on_comboBox_SignalType_currentIndexChanged(const QString &arg1);

    void on_btn_AddNewMultiPos_clicked();

    void on_btn_DelMultiPos_clicked();

    void on_btn_ModMultiPos_clicked();

private:
    Ui::DialogVariableDefine *ui;

    myQSqlDatabase *m_Database = nullptr;//数据库检索类

    //定义的变量
    DataBase::Str_Signal m_signal;

    //是否是创建新变量
    bool m_isCreatSignal = false;
};

#endif // DIALOGVARIABLEDEFINE_H
