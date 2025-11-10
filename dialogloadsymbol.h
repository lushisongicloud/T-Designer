#ifndef DIALOGLOADSYMBOL_H
#define DIALOGLOADSYMBOL_H

#include <QDialog>
#include <QDebug>
#include <QStringList>
#include <QDir>
#include <QComboBox>
#include "qxlabel.h"
#include "dialogsymbolattribute.h"
#include "mxdrawxlib.h"
#include "common.h"
#ifdef LabelWidth
#undef LabelWidth
#endif
#define LabelWidth 50
#ifdef LabelHeight
#undef LabelHeight
#endif
#define LabelHeight 42
#ifdef TotalLabelNum
#undef TotalLabelNum
#endif
#define TotalLabelNum 24
#ifdef ColumnLabelNum
#undef ColumnLabelNum
#endif
#define ColumnLabelNum 4
using namespace MxDrawXLib;
namespace Ui {
class DialogLoadSymbol;
}
class DialogLoadSymbol : public QDialog
{
    Q_OBJECT

public:
    explicit DialogLoadSymbol(QWidget *parent = nullptr);
    ~DialogLoadSymbol();
    void LoadModelFromDB();
    void LoadSymbolList(const QModelIndex &index);
    void closeEvent(QCloseEvent *event);
    void SetCurStackedWidgetIndex(int Index);
    bool Canceled;
    QString BlockFileName;
    QString SymbolID;
    int RetCode=-1;//RetCode=1:修改符号  RetCode=2:关闭  RetCode=3:载入符号
    QStandardItemModel *Model;

private slots:
    void SymbolSel(int id);

    void SymbolSelect(int id);

    void on_treeView_clicked(const QModelIndex &index);

    void on_BtnPrePage_clicked();

    void on_BtnNextPage_clicked();

    void on_BtnFirstPage_clicked();

    void on_BtnLastPage_clicked();

    void on_BtnOK_clicked();

    void on_BtnCancel_clicked();

    void on_BtnReLoad_clicked();

private:
    Ui::DialogLoadSymbol *ui;
    QXlabel *labels[TotalLabelNum];
    QLabel *lbDwgName[TotalLabelNum];
    void UpdateSymbols(QStringList listSymbolName,QStringList listSymbolID);
    int BaseIndex;
    int AllSymbolCount=0;
    int LastSelectId=-1;

signals:
    void DialogIsClosed();
};

#endif // DIALOGSYMBOLS_H

