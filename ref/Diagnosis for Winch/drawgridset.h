#ifndef DRAWGRIDSET_H
#define DRAWGRIDSET_H

#include <QDialog>
#include <QLabel>
#include <QCheckBox>
#include <QDoubleSpinBox>
namespace Ui {
class DrawGridSet;
}

class DrawGridSet : public QDialog
{
    Q_OBJECT

public:
    explicit DrawGridSet(QWidget *parent = nullptr);
    ~DrawGridSet();
    QLabel *m_LbParaName[8];
    QCheckBox *m_CbShow[8];
    QDoubleSpinBox *m_SpinSF[8];
    QDoubleSpinBox *m_SpinPY[8];
private slots:
    void on_btnDel1_1_clicked();

    void on_btnDel1_2_clicked();

    void on_btnDel1_3_clicked();

    void on_btnDel1_4_clicked();

    void on_btnDel1_5_clicked();

    void on_btnDel1_6_clicked();

    void on_btnDel1_7_clicked();

    void on_btnDel1_8_clicked();

private:
    Ui::DrawGridSet *ui;
};

#endif // DRAWGRIDSET_H
