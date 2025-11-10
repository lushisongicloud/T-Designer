#ifndef DIALOGMULTILIB_H
#define DIALOGMULTILIB_H

#include <QDialog>
#include "common.h"
#include <QStandardItemModel>
#include <QFormLayout>
#include <QLineEdit>
namespace Ui {
class DialogMultiLib;
}

class DialogMultiLib : public QDialog
{
    Q_OBJECT

public:
    explicit DialogMultiLib(QWidget *parent = nullptr);
    ~DialogMultiLib();
    void UpdateList();
    QStandardItemModel *ModelFold;
    bool Canceled=true;
    int RetCode=-1;//RetCode=1:修改符号  RetCode=2:关闭  RetCode=3:载入符号
    QString OpenFilePath;
private slots:
    void on_BtnAdd_clicked();

    void on_treeViewFold_clicked(const QModelIndex &index);

    void on_listWidget_clicked(const QModelIndex &index);

    void on_BtnModify_clicked();

    void on_BtnDelete_clicked();

    void ShowtreeViewFoldByUnitPopMenu(const QPoint &pos);

    void NewFold();

    void RenameFold();

    void DeleteFold();

    void on_listWidget_doubleClicked(const QModelIndex &index);

private:
    Ui::DialogMultiLib *ui;
};

#endif // DIALOGMULTILIB_H
