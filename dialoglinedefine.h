#ifndef DIALOGLINEDEFINE_H
#define DIALOGLINEDEFINE_H

#include <QDialog>
#include "common.h"
namespace Ui {
class DialogLineDefine;
}

class DialogLineDefine : public QDialog
{
    Q_OBJECT

public:
    explicit DialogLineDefine(QWidget *parent = nullptr);
    ~DialogLineDefine();
    void LoadLineInfo(int m_Wires_ID);
    bool Canceled;
    int Wires_ID;
    int SymbolMode;
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnChangeForm_clicked();

private:
    Ui::DialogLineDefine *ui;
};

#endif // DIALOGLINEDEFINE_H
