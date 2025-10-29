#ifndef DIALOGFUNCDEFINE_H
#define DIALOGFUNCDEFINE_H

#include <QDialog>
#include <QFormLayout>
#include <QLineEdit>
#include "common.h"
#include "dialognewfunc.h"
namespace Ui {
class DialogFuncDefine;
}

class DialogFuncDefine : public QDialog
{
    Q_OBJECT

public:
    explicit DialogFuncDefine(QWidget *parent = nullptr);
    ~DialogFuncDefine();
    void LoadFunctionDefineClass();
    void SetCurrentIndex(QString FunctionDefineClass_ID);
    void SetCurrentIndexByFunctionDefineName(QString DefaultFunctionDefineName);
    void SetCurStackedWidgetIndex(int Index);
    void SetVirtualPort(QString FuncType,QString FunctionDefineName);
    QStandardItemModel *Model;
    QString FunctionDefineName,FunctionDefineCode,FunctionDefineClass_ID,FunctionType;
    bool Canceled;
    int ValidLevel=4;
    int Mode=0;//Mode=0选择 Mode=1库管理
    QString FuncType;//接线端口、虚拟端口-观测布尔量、虚拟端口-观测实数量
private slots:
    void on_BtnOk_clicked();

    void on_treeView_clicked(const QModelIndex &index);

    void on_BtnCancel_clicked();

    void ShowtreeViewPopMenu(const QPoint &pos);

    void NewLevel0();

    void NewLevel();

    void Delete();

    void Rename();

    void FuncEdit();

    void on_BtnOk_Manage_clicked();

    void on_RbVirtualPort_clicked();

private:
    Ui::DialogFuncDefine *ui;
};

#endif // DIALOGFUNCDEFINE_H
