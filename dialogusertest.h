#ifndef DIALOGUSERTEST_H
#define DIALOGUSERTEST_H

#include <QDialog>
#include "common.h"
#include "qxcombobox.h"
#include <QFormLayout>
#include <QLabel>
#include <QComboBox>

namespace Ui {
class DialogUserTest;
}

class DialogUserTest : public QDialog
{
    Q_OBJECT

public:
    explicit DialogUserTest(QWidget *parent = nullptr);
    ~DialogUserTest();
    void AddOrModifyObserve(int Mode,QString StrSelectedUnit,QString StrSelectPara);
    void AddOrModifyCondition(int Mode,QString StrSelectedUnit,QString StrSelectedSpur);
    void AddOrModifyCmd(int Mode,QString StrSelectedCmd,QString StrCmdState);
    void LoadInfo(QString Name,QStringList ListCondition,QStringList ListTest);
    bool Canceled=true;
    QString StrSystemDefine,StrCondition,StrActions,TestName;
    QStringList CurExecsList;

private slots:
    void on_BtnAddObserve_clicked();

    void on_BtnAddCondition_clicked();

    void on_BtnModifyCondition_clicked();

    void on_BtnDeleteCondition_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnAddTest_clicked();

    void on_BtnModifyTest_clicked();

    void on_BtnDeleteTest_clicked();

private:
    Ui::DialogUserTest *ui;
};

#endif // DIALOGUSERTEST_H
