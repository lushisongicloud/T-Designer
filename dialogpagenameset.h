#ifndef DIALOGPAGENAMESET_H
#define DIALOGPAGENAMESET_H

#include <QDialog>
#include <QComboBox>
#include <QTableWidget>
#include "common.h"
namespace Ui {
class DialogPageNameSet;
}

class DialogPageNameSet : public QDialog
{
    Q_OBJECT

public:
    explicit DialogPageNameSet(QWidget *parent = nullptr);
    ~DialogPageNameSet();
    void HideEdPageName();
    void LoadTable(QString PageName,int Mode);//=高层+位置&文档类型·名称.dwg
    QString ReturnPageName,StrGaoceng,StrPos,StrPage,ReturnUnitPro,ReturnTerminalPro;
    bool Canceled;
    int ProMode;
private slots:
    void on_BtnOK_clicked();

    void on_EdPageName_textChanged(const QString &arg1);

    void on_BtnCancel_clicked();

private:
    Ui::DialogPageNameSet *ui;
};

#endif // DIALOGPAGENAMESET_H
