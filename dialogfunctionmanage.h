#ifndef DIALOGFUNCTIONMANAGE_H
#define DIALOGFUNCTIONMANAGE_H

#include <QDialog>
#include "common.h"
#include "qxcombobox.h"
#include <QDialog>
#include <QFormLayout>
#include <QLabel>
#include <QComboBox>
extern QSqlDatabase  T_Database;

namespace Ui {
class dialogFunctionManage;
}

class dialogFunctionManage : public QDialog
{
    Q_OBJECT

public:
    explicit dialogFunctionManage(QWidget *parent = nullptr);
    ~dialogFunctionManage();
    void LoadFunctionManage();
    void AddOrModifyCmd(int Mode,QString StrSelectedCmd,QString StrCmdState);//Mode=1:add Mode=2:modify
    void AddOrModifyExec(int Mode,QString StrSelectedExec);
    void AddOrModifyUserTest(int Mode,QString StrSelectedUserTest,QString StrUserTestState);
    void UpdateSystemDefine();
    QString CmdName,CmdVal,CopyFunctionID,CurFunctionID,StrSystemDefine;

private slots:
    void on_tableWidgetFunction_clicked(const QModelIndex &index);

    void on_BtnAddCmd_clicked();

    void on_BtnDeleteCmd_clicked();

    void on_BtnModify_clicked();

    void on_BtnAddExec_clicked();

    void on_BtnExecModify_clicked();

    void on_BtnDeleteExec_clicked();

    void on_BtnClose_clicked();

    void on_BtnApply_clicked();

    void on_BtnAddFunc_clicked();

    void on_BtnDeleteFunc_clicked();

    void on_BtnCopyFunc_clicked();

    void on_BtnPasteFunc_clicked();

    void on_BtnAddUserTest_clicked();

    void on_BtnModifyUserTest_clicked();

    void on_BtnDeleteUserTest_clicked();

    void on_BtnAddUserMannulTest_clicked();

    void on_BtnModifyUserMannulTest_clicked();

    void on_BtnDeleteMannulTest_clicked();

    void on_BtnAddSpur_clicked();

private:
    Ui::dialogFunctionManage *ui;

signals:
    //void UpdateSystemDefine(QStringList ListExec);
};

#endif // DIALOGFUNCTIONMANAGE_H
