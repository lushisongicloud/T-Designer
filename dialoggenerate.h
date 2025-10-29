#ifndef DIALOGGENERATE_H
#define DIALOGGENERATE_H

#include <QDialog>
#include <QComboBox>
#include "common.h"
namespace Ui {
class DialogGenerate;
}

class DialogGenerate : public QDialog
{
    Q_OBJECT

public:
    explicit DialogGenerate(QWidget *parent = nullptr);
    ~DialogGenerate();
    void LoadTable(int Type);
    QString InitPageName;
    bool Canceled,ReplaceOriginalDwg,AllGaoceng,AllPos;
    QString ReturnPageName,StrGaoceng,StrPos,StrPage;
    int ProjectStructure_ID;
private slots:
    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void UpdateCbPos(int index);

private:
    Ui::DialogGenerate *ui;
};

#endif // DIALOGGENERATE_H
