#ifndef DIALOGSYMBOLS_H
#define DIALOGSYMBOLS_H

#include <QDialog>
#include <QDebug>
#include <QStringList>
#include <QDir>
#include <QMessageBox>
//#include <QLabel>
#include "qxlabel.h"
#include "dialogsymbolattribute.h"
#include "dialogsymbolsort.h"
#include "mxdrawxlib.h"
#include "common.h"
#include "dialognewlib.h"
using namespace MxDrawXLib;
namespace Ui {
class DialogSymbols;
}
#ifdef LabelWidth
#undef LabelWidth
#endif
#define LabelWidth 115
#ifdef LabelHeight
#undef LabelHeight
#endif
#define LabelHeight 74
#ifdef TotalLabelNum
#undef TotalLabelNum
#endif
#define TotalLabelNum 16
#ifdef ColumnLabelNum
#undef ColumnLabelNum
#endif
#define ColumnLabelNum 4

class DialogSymbols : public QDialog
{
    Q_OBJECT

public:
    explicit DialogSymbols(QWidget *parent = nullptr);
    ~DialogSymbols();
    void LoadModelFromDB(QString CurSelectSymb2Class_ID);
    void LoadSymbolList(const QModelIndex &index);
    bool Canceled;
    QString BlockFileName;
    QString SymbolID,SymbolType;
    int RetCode=-1;//RetCode=1:修改符号  RetCode=2:关闭  RetCode=3:载入符号
    QStandardItemModel *Model;
    QString Symb2_Name,FunctionDefineClass_ID,CurSelectSymb2Class_ID;
    int _Order;
private slots:
    void SymbolSel(int id);

    void SymbolSelect(int id);

    void on_treeView_clicked(const QModelIndex &index);

    void on_Btn_Modify_clicked();

    void on_BtnClose_clicked();

    void on_BtnPrePage_clicked();

    void on_BtnNextPage_clicked();

    void on_BtnFirstPage_clicked();

    void on_BtnLastPage_clicked();

    void on_BtnDelSelectSymbol_clicked();

    void on_BtnNewLib_clicked();

    void on_BtnUpdateJpg_clicked();

    void ShowtreeViewPopMenu(const QPoint &pos);

    void DeleteLevel();

    void AutoMakeAllDir();

    void CopySymbol();

    void MoveLevel();

    void ReName();

    void on_BtnNext_clicked();

    void on_BtnSearch_clicked();

    QString GetFunctionDefineIDFromIndex();

private:
    Ui::DialogSymbols *ui;
    QXlabel *labels[TotalLabelNum];
    QLabel *lbDwgName[TotalLabelNum];
    void UpdateSymbols(QStringList listSymbolName,QStringList listSymbolID);
    int BaseIndex=0;
    int AllSymbolCount=0;
    int LastSelectId=-1;
    //QAxWidget *mAxWidget;
signals:
    //void SignalUpdateLib();
};

#endif // DIALOGSYMBOLS_H
