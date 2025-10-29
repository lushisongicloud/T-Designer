#ifndef DIALOGADDCONDITION_H
#define DIALOGADDCONDITION_H

#include <QDialog>
#include "common.h"
#include "qxcombobox.h"
#include <QFormLayout>
#include <QLabel>
#include <QComboBox>

namespace Ui {
class DialogAddCondition;
}

class DialogAddCondition : public QDialog
{
    Q_OBJECT

public:
    explicit DialogAddCondition(QWidget *parent = nullptr);
    ~DialogAddCondition();
    void AddOrModifyCondition(int Mode,QString StrSelectedUnit,QString StrSelectedSpur);
    void LoadCurCondition(QString CurCondition);
    QString StrSystemDefine;
    bool Canceled=true;
    QStringList ListCondition;

private slots:
    void on_BtnAddCondition_clicked();

    void on_BtnModifyCondition_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnDeleteCondition_clicked();

private:
    Ui::DialogAddCondition *ui;
};

#endif // DIALOGADDCONDITION_H
