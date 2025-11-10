#ifndef DIALOGDIAGUSERTEST_H
#define DIALOGDIAGUSERTEST_H

#include <QDialog>
#include <QComboBox>
#include "common.h"
namespace Ui {
class DialogDiagUserTest;
}

class DialogDiagUserTest : public QDialog
{
    Q_OBJECT

public:
    explicit DialogDiagUserTest(QWidget *parent = nullptr);
    ~DialogDiagUserTest();
    void LoadTestList(QStringList ListUserTest);
    QStringList m_ListUserTest;
    bool Canceled=true;
    QString CmdStr;

private slots:

    void on_listWidget_currentRowChanged(int currentRow);

    void on_Button_OK_clicked();

    void on_Button_cancel_clicked();

private:
    Ui::DialogDiagUserTest *ui;
};

#endif // DIALOGDIAGUSERTEST_H
