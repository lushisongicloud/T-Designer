#ifndef DIALOGCONNECTATTR_H
#define DIALOGCONNECTATTR_H

#include <QDialog>
#include "common.h"
namespace Ui {
class DialogConnectAttr;
}

class DialogConnectAttr : public QDialog
{
    Q_OBJECT

public:
    explicit DialogConnectAttr(QWidget *parent = nullptr);
    ~DialogConnectAttr();
    void LoadConnectAttr(QString ConnectName,int Dir);
    bool Canceled;
    QString ConnectName;
    int Dir=0;
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

private:
    Ui::DialogConnectAttr *ui;
};

#endif // DIALOGCONNECTATTR_H
