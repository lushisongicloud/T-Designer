#ifndef TESTEDITDIALOG_H
#define TESTEDITDIALOG_H

#include <QDialog>

#include "BO/test/testdefinition.h"

namespace Ui {
class TestEditDialog;
}

class TestEditDialog : public QDialog
{
    Q_OBJECT

public:
    explicit TestEditDialog(QWidget *parent = nullptr);
    ~TestEditDialog() override;

    void setTest(const GeneratedTest &test);
    GeneratedTest test() const;

private slots:
    void onAccepted();

private:
    void populateCategory();

    Ui::TestEditDialog *ui;
    GeneratedTest m_test;
};

#endif // TESTEDITDIALOG_H
