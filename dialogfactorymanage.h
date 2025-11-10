#ifndef DIALOGFACTORYMANAGE_H
#define DIALOGFACTORYMANAGE_H

#include <QDialog>
#include "common.h"
#include "dialogfactoryedit.h"
namespace Ui {
class DialogFactoryManage;
}

class DialogFactoryManage : public QDialog
{
    Q_OBJECT

public:
    explicit DialogFactoryManage(QWidget *parent = nullptr);
    ~DialogFactoryManage();


private slots:
    void on_tableWidget_clicked(const QModelIndex &index);

    void on_tableWidget_doubleClicked(const QModelIndex &index);

    void LoadInfo();

    void on_BtnAdd_clicked();

    void on_BtnInsert_clicked();

    void on_BtnModify_clicked();

    void on_BtnDelete_clicked();

    void on_BtnClose_clicked();

    void on_BtnSearch_clicked();

    void on_BtnSetTop_clicked();

    void on_BtnSetUp_clicked();

    void on_BtnSetBottom_clicked();

    void on_BtnSetDown_clicked();

private:
    Ui::DialogFactoryManage *ui;
};

#endif // DIALOGFACTORYMANAGE_H
