#ifndef DIALOGSYMBOLATTRIBUTE_H
#define DIALOGSYMBOLATTRIBUTE_H

#include <QDialog>
#include "mxdrawxlib.h"
#include <QList>
#include <QDebug>
#include <QMessageBox>
#include "dialogmodifyptermial.h"
#include "DrawStyle.h"
#include "common.h"

#define mindelta 0.00001
using namespace MxDrawXLib;
namespace Ui {
class DialogSymbolAttribute;
}

class DialogSymbolAttribute : public QDialog
{
    Q_OBJECT

public:
    explicit DialogSymbolAttribute(QWidget *parent = nullptr);
    ~DialogSymbolAttribute();
    void LoadSymbolAttribute();//载入符号属性
    void SetTerminalData();
    void closeEvent(QCloseEvent *event);
    void initTable();//初始化端号表
    void LoadAttrDefTable(int Index);// 0:"全部" 1:"普通元件" 2:"PLC" 3:"端子/插针"  4:"元件连接点"
    void CheckSymbolType(QString DescStr);
    void GetDwgCenterPos(double &x,double &y);
    bool SetAttrDefValue(QAxWidget* tmp_MxDrawWidget,QString OriginalTag,QString NewTag,QString NewText);
    bool Canceled,IsGettingBasePoint;
    QString SymbolFileName;//符号文件名称 xxx.dwg
    QString DataBaseSymbolID;//符号在数据库中的Symb2Lib_ID
    QString FunctionDefineClass_ID;
    QString SymbolType;//PLC 线圈等
    QAxWidget* tmp_MxDrawWidget;
    //QList<qlonglong> lTermId;
    DialogModifyPTermial *dlgModifyPTermial;
    bool DeleteFile=false;
public slots:
    void SlotGetUrPoint(IMxDrawPoint *point);
    void SlotDrawAttrDefDone(QString Tag,qlonglong AttrDefID);
    void SlotDrawAttrDefDelete(QString Tag,qlonglong AttrDefID);
private slots:
    void on_BtnOK_clicked();

    void on_BtnAddTerminal_clicked();

    void on_BtnModify_clicked();

    void on_BtnDelTerminal_clicked();

    void on_BtnCancel_clicked();

    void on_BtnInsertTerminal_clicked();

    void on_CbSymbolType_currentIndexChanged(const QString &arg1);

    void on_BtnPutAttrDef_clicked();

    void on_BtnGetBasePoint_clicked();

private:
    Ui::DialogSymbolAttribute *ui;

signals:
    void DialogIsClosed();
    void GetUrPoint(IMxDrawPoint *point);
    void SignalUpdateLib(QString CurSelectSymb2Class_ID);
    void SignalUpdateAttrdefTable(QString Tag,qlonglong AttrDefID);
    void SignalAddAttrdefTable(QString Tag,qlonglong AttrDefID);
};

#endif // DIALOGSYMBOLATTRIBUTE_H
