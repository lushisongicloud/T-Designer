#ifndef DIALOGBRANCHATTR_H
#define DIALOGBRANCHATTR_H

#include <QDialog>
#include "common.h"
#include "dialogpagenameset.h"
#include "dialogtag.h"
using namespace MxDrawXLib;
namespace Ui {
class DialogBranchAttr;
}

class DialogBranchAttr : public QDialog
{
    Q_OBJECT

public:
    explicit DialogBranchAttr(QWidget *parent = nullptr);
    ~DialogBranchAttr();
    void LoadSymbolInfo(QString Symbol_ID);
    int RetCode=0;
    QString StrProTag,DBSymbol_ID,DBSymbol,DBSymbol_Category,DBFunDefine;
    QStringList ListConnNum,ListConnDesc;//连接点代号，连接点描述
    IMxDrawBlockReference* blkEnty;
    DialogPageNameSet dlgPageNameSet;
    bool DTChanged=false;
private slots:
    void on_CbSymbolPattern_currentIndexChanged(const QString &arg1);

    void on_BtnOk_clicked();

    void on_BtnCancel_clicked();

    void on_tableWidgetTermInfo_clicked(const QModelIndex &index);

    void on_BtnUnitAttr_clicked();

    void on_BtnProSet_clicked();

    void on_EdUnitTag_textChanged(const QString &arg1);

    void on_BtnReplaceFunSymbol_clicked();

    void SlotDrawTermTag(int Type,QColor mColor);

    void on_BtnCancelTermSign_2_clicked();

    void on_BtnSaveTerm_2_clicked();

    void on_BtnFromUnitImage_2_clicked();

    void on_BtnFromDisk_2_clicked();

private:
    Ui::DialogBranchAttr *ui;
    BQGraphicsScene m_scene_term;
    dialogTag *m_dialogTermTag;
    unsigned char CurUnitImageIndex=0;
    QString CurImgPath;

};

#endif // DIALOGBRANCHATTR_H
