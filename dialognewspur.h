#ifndef DIALOGNEWSPUR_H
#define DIALOGNEWSPUR_H

#include <QDialog>
#include "common.h"
namespace Ui {
class DialogNewSpur;
}

class DialogNewSpur : public QDialog
{
    Q_OBJECT

public:
    explicit DialogNewSpur(QWidget *parent = nullptr,int Type=0);//Type=0:普通功能（非端子） Type=1:端子功能
    ~DialogNewSpur();
    void LoadFunctionDefineClass();
    void SetCurrentIndex(QString FunctionDefineClass_ID);
    bool CheckTermNum();
    QStandardItemModel *Model;
    QString FunctionDefineName,FunctionDefineCode,FunctionDefineClass_ID,SPSName;
    bool Canceled;
    int SpurType;
    int SpurCount,TermCount;
    QStringList ListTermNum;
private slots:
    void on_BtnOk_clicked();

    void on_treeView_clicked(const QModelIndex &index);

    void on_BtnCancel_clicked();

    void on_EdTermNum_textChanged(const QString &arg1);

private:
    Ui::DialogNewSpur *ui;
};

#endif // DIALOGFUNCDEFINE_H
