#ifndef DIALOGADDTERMINAL_H
#define DIALOGADDTERMINAL_H

#include <QDialog>
#include <QFormLayout>
#include <QLabel>
#include <QListWidget>
#include "common.h"
namespace Ui {
class DialogAddTerminal;
}

class DialogAddTerminal : public QDialog
{
    Q_OBJECT

public:
    explicit DialogAddTerminal(QWidget *parent = nullptr);
    ~DialogAddTerminal();
    bool Canceled=true;
    QString DT;
    int Designation;

private slots:
    void on_BtnTerminalStripSet_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_CbDesignation_currentTextChanged(const QString &arg1);

    void on_EdTerminalTag_textChanged(const QString &arg1);

    void on_CbTerminalStripTag_currentTextChanged(const QString &arg1);

private:
    Ui::DialogAddTerminal *ui;
};

#endif // DIALOGADDTERMINAL_H
