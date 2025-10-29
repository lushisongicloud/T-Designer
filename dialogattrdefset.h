#ifndef DIALOGATTRDEFSET_H
#define DIALOGATTRDEFSET_H

#include <QDialog>
#include "mxdrawxlib.h"
#include "common.h"
#include <QMessageBox>
using namespace MxDrawXLib;
namespace Ui {
class DialogAttrDefSet;
}

class DialogAttrDefSet : public QDialog
{
    Q_OBJECT

public:
    explicit DialogAttrDefSet(QWidget *parent = nullptr,IMxDrawAttributeDefinition *AttrDef = nullptr,IMxDrawAttribute *Attr=nullptr,IMxDrawMText *Text=nullptr);
    ~DialogAttrDefSet();
    IMxDrawAttributeDefinition *mAttrDef;
    IMxDrawAttribute *mAttr;
    IMxDrawMText *mText;
    bool Canceled=true;
private slots:
    void on_BtnOk_clicked();

    void on_BtnCancel_clicked();

private:
    Ui::DialogAttrDefSet *ui;
};

#endif // DIALOGATTRDEFSET_H
