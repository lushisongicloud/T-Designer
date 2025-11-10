#ifndef DIALOGLINKEDIT_H
#define DIALOGLINKEDIT_H

#include <QDialog>
#include "common.h"
#include "dialogpagenameset.h"
namespace Ui {
class DialogLinkEdit;
}

class DialogLinkEdit : public QDialog
{
    Q_OBJECT

public:
    explicit DialogLinkEdit(QWidget *parent = nullptr);
    ~DialogLinkEdit();
    bool Canceled;
    void LoadLinkInfo(int LinkID);
    int Link_ID;
    int ProjectStructure_ID;
    bool ProSetUpdated;
    QString RetStrLinkTag,RetStrLinkTextPosition;
    DialogPageNameSet dlgPageNameSet;
    int Page_ID;
    int AttrMode;//AttrMode=1:add  AttrMode=2:modify
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnProSet_clicked();

private:
    Ui::DialogLinkEdit *ui;
};

#endif // DIALOGLINKEDIT_H
