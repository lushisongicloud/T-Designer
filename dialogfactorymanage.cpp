#include "dialogfactorymanage.h"
#include "ui_dialogfactorymanage.h"

DialogFactoryManage::DialogFactoryManage(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogFactoryManage)
{
    ui->setupUi(this);
    LoadInfo();
}

DialogFactoryManage::~DialogFactoryManage()
{
    delete ui;
}

void DialogFactoryManage::LoadInfo()
{
    ui->tableWidget->setRowCount(0);
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM Factory ORDER BY _Order";
    QueryVar.exec(temp);
    while(QueryVar.next())
    {
       ui->tableWidget->setRowCount(ui->tableWidget->rowCount()+1);
       ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidget->rowCount())));//序号
       ui->tableWidget->item(ui->tableWidget->rowCount()-1,0)->setData(Qt::UserRole,QueryVar.value("Factory_ID").toString());
       ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,1,new QTableWidgetItem(QueryVar.value("Factory").toString()));//厂家名
       ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,2,new QTableWidgetItem(QueryVar.value("ForShort").toString()));//简称
       ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,3,new QTableWidgetItem(QueryVar.value("Logo").toString()));//Logo文件
       ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,4,new QTableWidgetItem(QueryVar.value("WebSite").toString()));//网址
       ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,5,new QTableWidgetItem(QueryVar.value("Remark").toString()));//备注
    }
    if(ui->tableWidget->rowCount()>0)
    {
        ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(0,0));
        on_tableWidget_clicked(ui->tableWidget->currentIndex());
    }
}

void DialogFactoryManage::on_tableWidget_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    ui->LbFactory->setText(ui->tableWidget->item(index.row(),1)->text());
    ui->LbForShort->setText(ui->tableWidget->item(index.row(),2)->text());
    ui->LbLogo->setText(ui->tableWidget->item(index.row(),3)->text());
    ui->LbWebSite->setText(ui->tableWidget->item(index.row(),4)->text());
    ui->LbRemark->setText(ui->tableWidget->item(index.row(),5)->text());

    QPixmap p=QPixmap("C:/TBD/LOGO/"+ui->tableWidget->item(index.row(),3)->text());
    ui->LbPic->setStyleSheet("background-color: rgb(255, 255, 255)");
    ui->LbPic->setScaledContents(false);
    ui->LbPic->setFrameShape(QFrame::Panel);
    ui->LbPic->setFrameShadow(QFrame::Sunken);
    ui->LbPic->setLineWidth(3);
    ui->LbPic->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);
    ui->LbPic->setPixmap(p.scaled(ui->LbPic->width(),ui->LbPic->height()));
}

void DialogFactoryManage::on_tableWidget_doubleClicked(const QModelIndex &index)
{
    DialogFactoryEdit *dlg = new DialogFactoryEdit(this);
    //Mode=0:编辑  Mode=1:增加
    dlg->Mode=0;
    dlg->setModal(true);
    dlg->LoadInfo(ui->tableWidget->item(index.row(),0)->data(Qt::UserRole).toString());
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString temp = "SELECT * FROM Factory WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
        QueryVar.exec(temp);
        if(QueryVar.next())
        {
           ui->tableWidget->item(ui->tableWidget->currentRow(),1)->setText(QueryVar.value("Factory").toString());
           ui->tableWidget->item(ui->tableWidget->currentRow(),2)->setText(QueryVar.value("ForShort").toString());
           ui->tableWidget->item(ui->tableWidget->currentRow(),3)->setText(QueryVar.value("Logo").toString());
           ui->tableWidget->item(ui->tableWidget->currentRow(),4)->setText(QueryVar.value("WebSite").toString());
           ui->tableWidget->item(ui->tableWidget->currentRow(),5)->setText(QueryVar.value("Remark").toString());
        }
        on_tableWidget_clicked(ui->tableWidget->currentIndex());
    }

    delete dlg;
}

void DialogFactoryManage::on_BtnAdd_clicked()
{
    DialogFactoryEdit *dlg = new DialogFactoryEdit(this);
    //Mode=0:编辑  Mode=1:增加
    dlg->Mode=1;
    dlg->_Order=GetMaxIDOfDB(T_LibDatabase,"Factory","_Order");
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString temp = "SELECT * FROM Factory WHERE Factory_ID = '"+dlg->Factory_ID+"'";
        QueryVar.exec(temp);
        if(QueryVar.next())
        {
            ui->tableWidget->setRowCount(ui->tableWidget->rowCount()+1);
            ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidget->rowCount())));//序号
            ui->tableWidget->item(ui->tableWidget->rowCount()-1,0)->setData(Qt::UserRole,QueryVar.value("Factory_ID").toString());
            ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,1,new QTableWidgetItem(QueryVar.value("Factory").toString()));//厂家名
            ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,2,new QTableWidgetItem(QueryVar.value("ForShort").toString()));//简称
            ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,3,new QTableWidgetItem(QueryVar.value("Logo").toString()));//Logo文件
            ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,4,new QTableWidgetItem(QueryVar.value("WebSite").toString()));//网址
            ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,5,new QTableWidgetItem(QueryVar.value("Remark").toString()));//备注
            ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(ui->tableWidget->rowCount()-1,0));
            on_tableWidget_clicked(ui->tableWidget->currentIndex());
        }
    }
    delete dlg;
}

void DialogFactoryManage::on_BtnInsert_clicked()
{
    if(ui->tableWidget->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", "未选中有效行");
        return;
    }
    int CurrentRowIndex=ui->tableWidget->currentRow();
    DialogFactoryEdit *dlg = new DialogFactoryEdit(this);
    //Mode=0:编辑  Mode=1:增加
    dlg->Mode=1;
    dlg->_Order=CurrentRowIndex+1;//GetMaxIDOfDB(T_LibDatabase,"Factory","_Order")
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString temp = "SELECT * FROM Factory WHERE Factory_ID = '"+dlg->Factory_ID+"'";
        QueryVar.exec(temp);
        if(QueryVar.next())
        {
            ui->tableWidget->insertRow(CurrentRowIndex);
            ui->tableWidget->setItem(CurrentRowIndex,0,new QTableWidgetItem(QString::number(CurrentRowIndex+1)));//序号
            for(int i=CurrentRowIndex+1;i<ui->tableWidget->rowCount();i++)
            {
               ui->tableWidget->item(i,0)->setText(QString::number(i+1));
            }
            ui->tableWidget->item(CurrentRowIndex,0)->setData(Qt::UserRole,QueryVar.value("Factory_ID").toString());
            ui->tableWidget->setItem(CurrentRowIndex,1,new QTableWidgetItem(QueryVar.value("Factory").toString()));//厂家名
            ui->tableWidget->setItem(CurrentRowIndex,2,new QTableWidgetItem(QueryVar.value("ForShort").toString()));//简称
            ui->tableWidget->setItem(CurrentRowIndex,3,new QTableWidgetItem(QueryVar.value("Logo").toString()));//Logo文件
            ui->tableWidget->setItem(CurrentRowIndex,4,new QTableWidgetItem(QueryVar.value("WebSite").toString()));//网址
            ui->tableWidget->setItem(CurrentRowIndex,5,new QTableWidgetItem(QueryVar.value("Remark").toString()));//备注
            ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(CurrentRowIndex,0));
            on_tableWidget_clicked(ui->tableWidget->currentIndex());
        }
    }

    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Factory WHERE _Order >= "+QString::number(CurrentRowIndex+1)+" AND Factory_ID <> '"+dlg->Factory_ID+"'";
    QueryVar.exec(SqlStr);
    while(QueryVar.next())
    {
        QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+QueryVar.value("Factory_ID").toString()+"'";
        QueryUpdate.prepare(SqlStr);
        QueryUpdate.bindValue(":_Order",QString::number(QueryVar.value("_Order").toInt()+1));
        QueryUpdate.exec();
    }
    delete dlg;
}

void DialogFactoryManage::on_BtnModify_clicked()
{
    if(!ui->tableWidget->currentIndex().isValid()) return;
    on_tableWidget_doubleClicked(ui->tableWidget->currentIndex());
}

void DialogFactoryManage::on_BtnDelete_clicked()
{
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = "DELETE FROM Factory WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
    QueryVar.exec(temp);

    result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否删除该厂家的元件?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result==QMessageBox::Yes)
    {
        QSqlQuery QueryEquipment = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr = "SELECT Equipment_ID FROM Equipment WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
        QueryEquipment.exec(SqlStr);
        while(QueryEquipment.next())
        {
            QSqlQuery QueryEquipmentTemplate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            SqlStr = "DELETE FROM EquipmentTemplate WHERE Equipment_ID = '"+QueryEquipment.value(0).toString()+"'";
            QueryEquipmentTemplate.exec(SqlStr);
        }
        SqlStr = "DELETE FROM Equipment WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
        QueryEquipment.exec(SqlStr);
    }

    LoadInfo();
}

void DialogFactoryManage::on_BtnClose_clicked()
{
    this->close();
}

void DialogFactoryManage::on_BtnSearch_clicked()
{
    for(int i=0;i<ui->tableWidget->rowCount();i++)
    {
        if(ui->tableWidget->item(i,1)->text().contains(ui->EdSearchFact->text()))
        {
            ui->tableWidget->setCurrentItem(ui->tableWidget->item(i,0));
            break;
        }
    }
}

void DialogFactoryManage::on_BtnSetTop_clicked()
{
    if(ui->tableWidget->currentRow()<0) return;
    QString Factory_ID=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString();
    ui->tableWidget->removeRow(ui->tableWidget->currentRow());
    ui->tableWidget->insertRow(0);
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Factory WHERE Factory_ID = '"+Factory_ID+"'";
    QueryVar.exec(SqlStr);
    if(QueryVar.next())
    {
        ui->tableWidget->setItem(0,0,new QTableWidgetItem("1"));//序号
        ui->tableWidget->item(0,0)->setData(Qt::UserRole,QueryVar.value("Factory_ID").toString());
        ui->tableWidget->setItem(0,1,new QTableWidgetItem(QueryVar.value("Factory").toString()));//厂家名
        ui->tableWidget->setItem(0,2,new QTableWidgetItem(QueryVar.value("ForShort").toString()));//简称
        ui->tableWidget->setItem(0,3,new QTableWidgetItem(QueryVar.value("Logo").toString()));//Logo文件
        ui->tableWidget->setItem(0,4,new QTableWidgetItem(QueryVar.value("WebSite").toString()));//网址
        ui->tableWidget->setItem(0,5,new QTableWidgetItem(QueryVar.value("Remark").toString()));//备注
    }
    SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+Factory_ID+"'";
    QueryVar.prepare(SqlStr);
    QueryVar.bindValue(":_Order",1);
    QueryVar.exec();
    SqlStr = "SELECT Factory_ID FROM Factory WHERE Factory_ID <> '"+Factory_ID+"' ORDER BY _Order";
    QueryVar.exec(SqlStr);
    int index=2;
    while(QueryVar.next())
    {
        QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+QueryVar.value(0).toString()+"'";
        QueryUpdate.prepare(SqlStr);
        QueryUpdate.bindValue(":_Order",index);
        QueryUpdate.exec();
        index++;
    }
    for(int i=0;i<ui->tableWidget->rowCount();i++)
    {
        ui->tableWidget->item(i,0)->setText(QString::number(i+1));
    }
    ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(0,0));
}

void DialogFactoryManage::on_BtnSetUp_clicked()
{
    if(ui->tableWidget->currentRow()<=0) return;
    //上下对调
    QString TempStr;
    for(int i=1;i<5;i++)
    {
        TempStr=ui->tableWidget->item(ui->tableWidget->currentRow(),i)->text();
        ui->tableWidget->item(ui->tableWidget->currentRow(),i)->setText(ui->tableWidget->item(ui->tableWidget->currentRow()-1,i)->text());
        ui->tableWidget->item(ui->tableWidget->currentRow()-1,i)->setText(TempStr);
    }

    QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
    QueryUpdate.prepare(SqlStr);
    QueryUpdate.bindValue(":_Order",QString::number(ui->tableWidget->currentRow()));
    QueryUpdate.exec();
    SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow()-1,0)->data(Qt::UserRole).toString()+"'";
    QueryUpdate.prepare(SqlStr);
    QueryUpdate.bindValue(":_Order",QString::number(ui->tableWidget->currentRow()+1));
    QueryUpdate.exec();

    TempStr=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString();
    ui->tableWidget->item(ui->tableWidget->currentRow(),0)->setData(Qt::UserRole,ui->tableWidget->item(ui->tableWidget->currentRow()-1,0)->data(Qt::UserRole).toString());
    ui->tableWidget->item(ui->tableWidget->currentRow()-1,0)->setData(Qt::UserRole,TempStr);

    ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(ui->tableWidget->currentRow()-1,0));


}

void DialogFactoryManage::on_BtnSetBottom_clicked()
{
    if(ui->tableWidget->currentRow()<0) return;
    QString Factory_ID=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString();
    ui->tableWidget->removeRow(ui->tableWidget->currentRow());
    ui->tableWidget->setRowCount(ui->tableWidget->rowCount()+1);
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Factory WHERE Factory_ID = '"+Factory_ID+"'";
    QueryVar.exec(SqlStr);
    if(QueryVar.next())
    {
        ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidget->rowCount())));//序号
        ui->tableWidget->item(ui->tableWidget->rowCount()-1,0)->setData(Qt::UserRole,QueryVar.value("Factory_ID").toString());
        ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,1,new QTableWidgetItem(QueryVar.value("Factory").toString()));//厂家名
        ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,2,new QTableWidgetItem(QueryVar.value("ForShort").toString()));//简称
        ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,3,new QTableWidgetItem(QueryVar.value("Logo").toString()));//Logo文件
        ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,4,new QTableWidgetItem(QueryVar.value("WebSite").toString()));//网址
        ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,5,new QTableWidgetItem(QueryVar.value("Remark").toString()));//备注
    }
    SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+Factory_ID+"'";
    QueryVar.prepare(SqlStr);
    QueryVar.bindValue(":_Order",GetMaxIDOfDB(T_LibDatabase,"Factory","_Order")-1);
    QueryVar.exec();
    SqlStr = "SELECT Factory_ID FROM Factory WHERE Factory_ID <> '"+Factory_ID+"' ORDER BY _Order";
    QueryVar.exec(SqlStr);
    int index=1;
    while(QueryVar.next())
    {
        QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+QueryVar.value(0).toString()+"'";
        QueryUpdate.prepare(SqlStr);
        QueryUpdate.bindValue(":_Order",index);
        QueryUpdate.exec();
        index++;
    }
    for(int i=0;i<ui->tableWidget->rowCount();i++)
    {
        ui->tableWidget->item(i,0)->setText(QString::number(i+1));
    }
    ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(ui->tableWidget->rowCount()-1,0));
}

void DialogFactoryManage::on_BtnSetDown_clicked()
{
    if(ui->tableWidget->currentRow()<0) return;
    if(ui->tableWidget->currentRow()==(ui->tableWidget->rowCount()-1)) return;
    //上下对调
    QString TempStr;
    for(int i=1;i<5;i++)
    {
        TempStr=ui->tableWidget->item(ui->tableWidget->currentRow(),i)->text();
        ui->tableWidget->item(ui->tableWidget->currentRow(),i)->setText(ui->tableWidget->item(ui->tableWidget->currentRow()+1,i)->text());
        ui->tableWidget->item(ui->tableWidget->currentRow()+1,i)->setText(TempStr);
    }

    QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString()+"'";
    QueryUpdate.prepare(SqlStr);
    QueryUpdate.bindValue(":_Order",QString::number(ui->tableWidget->currentRow()+2));
    QueryUpdate.exec();
    SqlStr="UPDATE Factory SET _Order=:_Order WHERE Factory_ID = '"+ui->tableWidget->item(ui->tableWidget->currentRow()+1,0)->data(Qt::UserRole).toString()+"'";
    QueryUpdate.prepare(SqlStr);
    QueryUpdate.bindValue(":_Order",QString::number(ui->tableWidget->currentRow()+1));
    QueryUpdate.exec();

    TempStr=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toString();
    ui->tableWidget->item(ui->tableWidget->currentRow(),0)->setData(Qt::UserRole,ui->tableWidget->item(ui->tableWidget->currentRow()+1,0)->data(Qt::UserRole).toString());
    ui->tableWidget->item(ui->tableWidget->currentRow()+1,0)->setData(Qt::UserRole,TempStr);
    ui->tableWidget->setCurrentIndex(ui->tableWidget->model()->index(ui->tableWidget->currentRow()+1,0));
}
