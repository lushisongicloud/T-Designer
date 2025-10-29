#ifndef DIALOGCABLEDEFINE_H
#define DIALOGCABLEDEFINE_H

#include <QDialog>
#include "common.h"
#include "dialogpagenameset.h"
namespace Ui {
class DialogCableDefine;
}

class DialogCableDefine : public QDialog
{
    Q_OBJECT

public:
    explicit DialogCableDefine(QWidget *parent = nullptr);
    ~DialogCableDefine();
    void LoadCableInfo(int m_Cable_ID);
    DialogPageNameSet dlgPageNameSet;
    int Cable_ID;
    bool Canceled;
    int Page_ID;
    bool ProSetUpdated;
    int ProjectStructure_ID;
    int AttrMode;//AttrMode=1:add  AttrMode=2:modify
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnProSet_clicked();

private:
    Ui::DialogCableDefine *ui;
};

#endif // DIALOGCABLEDEFINE_H
