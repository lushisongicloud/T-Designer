#ifndef DIALOGSYMBOLSORT_H
#define DIALOGSYMBOLSORT_H

#include <QDialog>
#include <QDebug>
#include <QFile>
#include <QMenu>
#include <QAction>
#include <QStringList>
#include <QStandardItemModel>
#include <QStandardItem>
#include <QFileInfo>
#include "mxdrawxlib.h"

#include "qxlabel.h"
#include "dialogsymbolattribute.h"

using namespace MxDrawXLib;
namespace Ui {
class DialogSymbolSort;
}

class DialogSymbolSort : public QDialog
{
    Q_OBJECT

public:
    explicit DialogSymbolSort(QWidget *parent = nullptr);
    ~DialogSymbolSort();
    void UpdateGroupMembers();
    void LoadData();
    bool Canceled;
    int RetCode=-1;//RetCode=1:修改符号  RetCode=2:关闭  RetCode=3:载入符号
    QStandardItemModel *ModelGroup ;
    QList<QStringList> SymbolGroupList;
    QStringList ListGroupName;
    QStringList *ListAllSymbols;
    int SymbolType;
    int Mode;//Mode=0:Symbol  Mode=1:Stamp

private:
    Ui::DialogSymbolSort *ui;

private slots:
    void showGroupMember(QModelIndex index);
    void GroupMemberView(QModelIndex index);
    void AllSymbolsView(QModelIndex index);
    void on_BtnCancel_clicked();
    void on_BtnAddToGroup_clicked();
    void on_BtnRemoveGroup_clicked();
    void on_BtnOK_clicked();
    void show_Menu(const QPoint&);
    void DoAddGroup();
    void DoModifyGroup();
    void DoRemoveGroup();

    void on_BtnMemberSearch_clicked();
    void on_BtnAllSymbolSearch_clicked();
};

#endif // DIALOGSYMBOLSORT_H
