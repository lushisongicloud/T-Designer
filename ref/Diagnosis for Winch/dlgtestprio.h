#ifndef DLGTESTPRIO_H
#define DLGTESTPRIO_H

#include <QGroupBox>

namespace Ui {
class DlgTestPrio;
}

class DlgTestPrio : public QGroupBox
{
    Q_OBJECT

public:
    explicit DlgTestPrio(QWidget *parent = nullptr);
    ~DlgTestPrio();

private slots:
    void on_BtnExit_clicked();

private:
    Ui::DlgTestPrio *ui;
};

#endif // DLGTESTPRIO_H
