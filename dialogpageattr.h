#ifndef DIALOGPAGEATTR_H
#define DIALOGPAGEATTR_H

#include <QDialog>
#include <QDateTime>
#include <QComboBox>
#include "dialogpagenameset.h"
namespace Ui {
class DialogPageAttr;
}

class DialogPageAttr : public QDialog
{
    Q_OBJECT

public:
    explicit DialogPageAttr(QWidget *parent = nullptr);
    ~DialogPageAttr();
    void LoadPageInfo();
    void SetPageName();
    DialogPageNameSet dlgPageNameSet;
    bool PageNameSetUpdated;
    int Mode;//Mode=1:Add Page  Mode=2:modify page
    bool Canceled;
    int Page_ID;
    QString PageInitName;
    //QString RetStrGaoceng,RetStrPos,RetStrPage;
private slots:
    void on_BtnPageNameSet_clicked();

    void on_BtnOk_clicked();

    void on_BtnCancel_clicked();

private:
    Ui::DialogPageAttr *ui;
};

#endif // DIALOGPAGEATTR_H
