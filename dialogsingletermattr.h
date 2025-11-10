#ifndef DIALOGSINGLETERMATTR_H
#define DIALOGSINGLETERMATTR_H

#include <QDialog>
#include "common.h"
#include "dialogpagenameset.h"
#include "dialogunitmanage.h"
namespace Ui {
class DialogSingleTermAttr;
}

class DialogSingleTermAttr : public QDialog
{
    Q_OBJECT

public:
    explicit DialogSingleTermAttr(QWidget *parent = nullptr);
    ~DialogSingleTermAttr();
    void LoadInfo(int Terminal_ID,int TerminalInstanceID);
    void SetCbShowTagVisible(bool visible);
    DialogPageNameSet dlgPageNameSet;
    QString StrProTag,StrSymbolName;
    QString CurTerminal_ID,CurTerminalInstanceID;
    bool Canceled,DTChanged=false;
    int NewProjectStructure_ID;
    bool TerminalTagVisible;
private:
    Ui::DialogSingleTermAttr *ui;
signals:
    void UpdateProjectTerminal();
private slots:
    void on_BtnProSet_clicked();
    void on_BtnOK_clicked();
    void on_BtnUnitChoose_clicked();
    void on_BtnCancel_clicked();
    void on_EdTerminalTag_textChanged(const QString &arg1);
    void on_CbTerminalFunction_currentTextChanged(const QString &arg1);
    void on_CbLeftTerm_currentTextChanged(const QString &arg1);
};

#endif // DIALOGSINGLETERMATTR_H
