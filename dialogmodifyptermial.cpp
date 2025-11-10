#include "dialogmodifyptermial.h"
#include "ui_dialogmodifyptermial.h"

extern bool FlagPuttingAttrDef;
extern QString m_dragText;
DialogModifyPTermial::DialogModifyPTermial(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogModifyPTermial)
{
    ui->setupUi(this);
    //ui->tableAttrDef->viewport()->installEventFilter(this);
    Canceled=true;
}

DialogModifyPTermial::~DialogModifyPTermial()
{
    delete ui;
}

void DialogModifyPTermial::closeEvent(QCloseEvent *event)
{
    emit(DialogIsClosed());
}
//载入端子信息
void DialogModifyPTermial::LoadTerminalInfo()
{
   ui->EditTerminalName->setText(TerminalName);
   ui->comboBox_dir->setCurrentText(LineDirection);

   if(!TerminalPointIsNull){
     ui->EditTerminalPointX->setText(QString::number(TerminalPointX,'f',2));
     ui->EditTerminalPointY->setText(QString::number(TerminalPointY,'f',2));
   }
   else
   {
       ui->EditTerminalPointX->setText("");
       ui->EditTerminalPointY->setText("");
   }
   ui->checkBox_NoLine->setChecked(NoLine=="是");
   //根据tag来加载属性定义对象table
   ui->tableAttrDef->setRowCount(0);
   if(Mode!=3)
   {
       if(GetAttrDefTextString(tmp_MxDrawWidget,TerminalName)=="未找到")
       {
           qDebug()<<"未找到";
           ui->tableAttrDef->setRowCount(ui->tableAttrDef->rowCount()+1);
           ui->tableAttrDef->setItem(ui->tableAttrDef->rowCount()-1,0,new QTableWidgetItem(TerminalName));
       }
       if(GetAttrDefTextString(tmp_MxDrawWidget,"符号的连接点描述["+TerminalName+"]")=="未找到")
       {
           ui->tableAttrDef->setRowCount(ui->tableAttrDef->rowCount()+1);
           ui->tableAttrDef->setItem(ui->tableAttrDef->rowCount()-1,0,new QTableWidgetItem("符号的连接点描述["+TerminalName+"]"));
       }
   }
   else
   {
       ui->tableAttrDef->setRowCount(ui->tableAttrDef->rowCount()+1);
       ui->tableAttrDef->setItem(ui->tableAttrDef->rowCount()-1,0,new QTableWidgetItem(TerminalName));
       ui->tableAttrDef->setRowCount(ui->tableAttrDef->rowCount()+1);
       ui->tableAttrDef->setItem(ui->tableAttrDef->rowCount()-1,0,new QTableWidgetItem("符号的连接点描述["+TerminalName+"]"));
   }
}

void DialogModifyPTermial::on_BtnOK_clicked()
{
    TerminalName=ui->EditTerminalName->text();
    if(ui->comboBox_dir->currentIndex()<0)
    {
        QMessageBox::warning(nullptr, "提示", "接线方向不能为空");
        return;
    }
    LineDirection=ui->comboBox_dir->currentText();
    NoLine=ui->checkBox_NoLine->isChecked()?"是":"";
    if(ui->EditTerminalPointX->text()==""||ui->EditTerminalPointY->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", "坐标不允许为空！");
        return;
    }
    if(GetAttrDefTextString(tmp_MxDrawWidget,TerminalName)=="未找到")
    {
        QMessageBox::warning(nullptr, "提示", "请放置连接点代号！");
        return;
    }
    TerminalPointX=ui->EditTerminalPointX->text().toDouble();
    TerminalPointY=ui->EditTerminalPointY->text().toDouble();
    Canceled=false;
    close();
}

void DialogModifyPTermial::on_btn_GetTerminalPoint_clicked()
{
    tmp_MxDrawWidget->dynamicCall("DoCommand(const int&)",104);
}
void DialogModifyPTermial::SlotGetUrPoint(IMxDrawPoint *point)
{
    ui->EditTerminalPointX->setText(QString::number(point->x(),'f',2));
    ui->EditTerminalPointY->setText(QString::number(point->y(),'f',2));
}

void DialogModifyPTermial::SlotUpdateAttrdefTable(QString Tag,qlonglong AttrDefID)
{
   for(int i=0;i<ui->tableAttrDef->rowCount();i++)
   {
       if(ui->tableAttrDef->item(i,0)->text()==Tag)  ui->tableAttrDef->removeRow(i);
   }
   bool Existed=false;
   for(int i=0;i<ListAttrDefID.count();i++)
   {
       if(ListAttrDefID.at(i)==AttrDefID)
       {
           Existed=true;
           break;
       }
   }
   if(!Existed) ListAttrDefID.append(AttrDefID);
qDebug()<<"AttrDefID="<<AttrDefID;
}

void DialogModifyPTermial::SlotAddAttrdefTable(QString Tag,qlonglong AttrDefID)
{
    ui->tableAttrDef->insertRow(0);
    ui->tableAttrDef->setItem(0,0,new QTableWidgetItem(Tag));
    for(int i=0;i<ListAttrDefID.count();i++)
    {
        if(ListAttrDefID.at(i)==AttrDefID)
        {
            ListAttrDefID.removeAt(i);
        }
    }
}

void DialogModifyPTermial::on_BtnCancel_clicked()
{
    Canceled=true;
    DeleteAttrDef(tmp_MxDrawWidget,TerminalName);
    DeleteAttrDef(tmp_MxDrawWidget,"符号的连接点描述["+TerminalName+"]");
    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");
    close();
}

void DialogModifyPTermial::on_tableAttrDef_itemPressed(QTableWidgetItem *item)
{
    if (item!=nullptr)
    {
        QDrag *drag = new QDrag(this);
        QMimeData *mimeData = new QMimeData;
        mimeData->setText(item->text());
        drag->setMimeData(mimeData);
        drag->exec(Qt::MoveAction);
    }
}

bool DialogModifyPTermial::eventFilter(QObject *obj, QEvent *e)
{
    /*
    if (obj == ui->tableAttrDef->viewport())
    {
        if (e->type() == QEvent::MouseButtonPress){
            qDebug()<<"mousePressEvent";
            //类型转换
            startPos=static_cast<QMouseEvent *>(e)->pos();
            QModelIndex index=ui->tableAttrDef->indexAt(startPos);
            if(index.isValid())
            {
                m_validPress=true;
                m_dragText = ui->tableAttrDef->item(index.row(), 0)->text();
                ui->tableAttrDef->setMouseTracking(true);
            }
            else
            {
                m_validPress=false;
                ui->tableAttrDef->setMouseTracking(false);
            }
        }
        if(e->type() == QEvent::MouseMove)
        {
            qDebug()<<"mouseMoveEvent";
            if(!m_validPress) return false;
            if ((static_cast<QMouseEvent *>(e)->pos() - startPos).manhattanLength() >= QApplication::startDragDistance())
            {
                m_validPress=false;
                //调用tmp_MxDrawWidget的动态绘制命令绘制属性定义对象
                qDebug()<<"调用tmp_MxDrawWidget的动态绘制命令绘制属性定义对象,m_dragText="<<m_dragText;
                tmp_MxDrawWidget->dynamicCall("DoCommand(const int&)",105);
            }
        }
    }*/
    return QWidget::eventFilter(obj,e);

}

void DialogModifyPTermial::dragEnterEvent(QDragEnterEvent *event)//复写”拖拽事件“函数
{
    qDebug()<<"dragEnterEvent";
    if (event->mimeData()->hasText())
    {
        event->acceptProposedAction();
    }
    else
    {
        event->ignore();
    }
}

void DialogModifyPTermial::dragMoveEvent(QDragMoveEvent* event)
{
    qDebug()<<"dragMoveEvent";
    QDrag* drag = new QDrag(this);
    QMimeData* mimeData = new QMimeData;
    mimeData->setText(m_dragText);
    drag->setMimeData(mimeData);

    if (drag->exec(Qt::MoveAction) == Qt::MoveAction)
    {
    }

    delete drag;
}
void DialogModifyPTermial::dropEvent(QDropEvent *event)//复写”放下事件“函数
{
    qDebug()<<"dropEvent";
    if (event->mimeData()->hasText())
    {
        qDebug()<<event->mimeData()->text();
        event->acceptProposedAction();
        return;
     }
     event->ignore();
}

void DialogModifyPTermial::on_BtnPutAttrDef_clicked()
{
    if(ui->tableAttrDef->currentRow()<0) return;
    m_dragText = ui->tableAttrDef->item(ui->tableAttrDef->currentRow(), 0)->text();
    tmp_MxDrawWidget->dynamicCall("DoCommand(const int&)",105);
}
