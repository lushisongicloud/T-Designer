#ifndef DIALOGFACTORYEDIT_H
#define DIALOGFACTORYEDIT_H

#include <QDialog>
#include "common.h"
namespace Ui {
class DialogFactoryEdit;
}

class DialogFactoryEdit : public QDialog
{
    Q_OBJECT

public:
    explicit DialogFactoryEdit(QWidget *parent = nullptr);
    ~DialogFactoryEdit();
    void LoadInfo(QString Factory_ID);
    QString Factory_ID;
    bool Canceled=true;
    int Mode=0;//Mode=0:编辑  Mode=1:增加
    int _Order;
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnSetLogo_clicked();

private:
    Ui::DialogFactoryEdit *ui;

signals:
};

#endif // DIALOGFACTORYEDIT_H
