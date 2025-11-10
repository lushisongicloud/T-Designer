#ifndef DIALOGTERMINALATTR_H
#define DIALOGTERMINALATTR_H

#include <QDialog>
#include "common.h"
#include "dialogpagenameset.h"
#include "dialogunitmanage.h"
namespace Ui {
class DialogTerminalAttr;
}

class DialogTerminalAttr : public QDialog
{
    Q_OBJECT

public:
    explicit DialogTerminalAttr(QWidget *parent = nullptr);
    ~DialogTerminalAttr();
    void LoadInfo(int Mode,int Equipment_ID);
    QStringList GetTerminalList(QString StrTerminal);
    DialogPageNameSet dlgPageNameSet;
    QString StrProTag,StrSymbolName;
    QString CurTerminalStrip_ID;
    bool Canceled;
    bool SymbolTermCountChanged=false,TerminalStripTagChanged=false;
    int NewProjectStructure_ID;
    int AttrMode;//AttrMode=1:add  AttrMode=2:modify
private slots:
    void on_BtnProSet_clicked();

    void on_BtnOK_clicked();

    void on_EdTerminalTag_textChanged(const QString &arg1);

    void on_BtnCancel_clicked();

    void on_BtnUnitChoose_clicked();

    void on_BtnReplaceTerminalSymbol_clicked();

    void on_BtnAdd_clicked();

    void on_BtnInsert_clicked();

    void on_BtnDelete_clicked();

private:
    Ui::DialogTerminalAttr *ui;
signals:
    void UpdateProjectTerminal();
};

#endif // DIALOGTERMINALATTR_H
