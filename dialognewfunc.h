#ifndef DIALOGNEWFUNC_H
#define DIALOGNEWFUNC_H

#include <QDialog>
#include <QMessageBox>
#include "common.h"
#include <Qsci/qsciscintilla.h>
#include <Qsci/qscilexercpp.h>
#include <Qsci/qsciapis.h>
#include "qscilexercppattach.h"
namespace Ui {
class DialogNewFunc;
}

class DialogNewFunc : public QDialog
{
    Q_OBJECT

public:
    explicit DialogNewFunc(QWidget *parent = nullptr);
    ~DialogNewFunc();
    void LoadInfo(QString FunctionDefineClass_ID);
    void InitTEdit();
    void SetUIEnabled(QString Level);
    bool Canceled=true;
    QString FileName;
    QString FunctionDefineClass_ID;
    QString ParentNo;
    QString FilePath="";
    int Mode=0;//0:Add  1:modify
    QsciScintilla *QsciEdit;
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnFuncSymbolSet_clicked();

    void on_BtnDelFuncSymbol_clicked();

    void on_RbSingleTerm_clicked(bool checked);

private:
    Ui::DialogNewFunc *ui;
};

#endif // DIALOGNEWFUNC_H
