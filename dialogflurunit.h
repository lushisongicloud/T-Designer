#ifndef DIALOGFLURUNIT_H
#define DIALOGFLURUNIT_H

#include <QDialog>
#include "common.h"
namespace Ui {
class DialogFlurUnit;
}

class DialogFlurUnit : public QDialog
{
    Q_OBJECT

public:
    explicit DialogFlurUnit(QWidget *parent = nullptr,QList<QString> *list_unit = nullptr);
    ~DialogFlurUnit();
    QString get_unit_name();
    void InitTable(int Mode);
    QString unit_name;
    int m_Mode,RetCode;
    QStringList RetDiagnoseList;

private slots:
    void on_BtnClose_clicked();
    void setText(QList<QString> list_test);

    void on_Test_tableWidget_clicked(const QModelIndex &index);

    void on_BtnDiagnoseOver_clicked();

    void on_CbAllSelect_clicked();

private:
    Ui::DialogFlurUnit *ui;
    QList<QString> m_list_unit;
};

#endif // DIALOGFLURUNIT_H
