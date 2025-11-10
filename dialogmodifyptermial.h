#ifndef DIALOGMODIFYPTERMIAL_H
#define DIALOGMODIFYPTERMIAL_H

#include <QDialog>
#include <QDebug>
#include <QTableWidget>
#include "mxdrawxlib.h"
#include <QMessageBox>
#include <QTableWidget>
#include "common.h"
#include <QMouseEvent>
#include <QDragEnterEvent> //拖拽事件
#include <QDropEvent> //放下事件
#include <QDrag>
namespace Ui {
class DialogModifyPTermial;
}
using namespace MxDrawXLib;
class DialogModifyPTermial : public QDialog
{
    Q_OBJECT

public:
    explicit DialogModifyPTermial(QWidget *parent = nullptr);
    ~DialogModifyPTermial();
    void closeEvent(QCloseEvent *event);
    bool eventFilter(QObject *obj, QEvent *e);
    void UpdatePara(int Val_dir,int Val_num,int Val_base);   
    void LoadTerminalInfo();//载入端子信息
    bool Canceled;
    QString TerminalName;//逻辑端号
    QString LineDirection;//连线方向
    //IMxDrawPoint* TerminalPoint;
    //IMxDrawPoint* TerminalLabelPoint;
    bool TerminalPointIsNull;//逻辑端号位置为空
    double TerminalPointX;//逻辑端号位置X
    double TerminalPointY;//逻辑端号位置X
    QString NoLine;//是否为不接线端
    QAxWidget* tmp_MxDrawWidget;
    QPoint startPos;             //拖拽起点
    bool m_validPress = false;
    int Mode=0;//add:1 modify:2 insert:3
    QList<qlonglong> ListAttrDefID;
protected:
    void dragEnterEvent(QDragEnterEvent *event);//复写”拖拽事件“函数
    void dragMoveEvent(QDragMoveEvent* event);
    void dropEvent(QDropEvent *event);//复写”放下事件“函数
public slots:
    void SlotGetUrPoint(IMxDrawPoint *point);
    void SlotUpdateAttrdefTable(QString Tag,qlonglong AttrDefID);
    void SlotAddAttrdefTable(QString Tag,qlonglong AttrDefID);
private slots:

    void on_BtnOK_clicked();

    void on_btn_GetTerminalPoint_clicked();

    void on_BtnCancel_clicked();

    void on_tableAttrDef_itemPressed(QTableWidgetItem *item);

    void on_BtnPutAttrDef_clicked();

private:
    Ui::DialogModifyPTermial *ui;
    int UrGetPointType;

signals:
    void DialogIsClosed();
};

#endif // DIALOGMODIFYPTERMIAL_H
