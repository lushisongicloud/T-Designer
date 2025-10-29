#ifndef DIALOGNEWLIB_H
#define DIALOGNEWLIB_H

#include <QDialog>
#include "common.h"
#include "dialogfuncdefine.h"

namespace Ui {
class DialogNewLib;
}

class DialogNewLib : public QDialog
{
    Q_OBJECT

public:
    explicit DialogNewLib(QWidget *parent = nullptr);
    ~DialogNewLib();
    void LoadMode(int Mode,int Level,QString DefaultFunctionDefineClass_ID,int TermCount);
    QString FunctionDefineClass_ID,FileName,SymbolType;
    bool Canceled=true;
    int ValidLevel=4;
    int Mode=0;
    //QString DefaultFunctionDefineName;
private slots:
    void on_BtnFuncSet_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

private:
    Ui::DialogNewLib *ui;
    DialogFuncDefine dlgFuncDefine;
};

#endif // DIALOGNEWLIB_H
