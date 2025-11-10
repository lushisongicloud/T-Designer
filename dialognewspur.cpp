#include "dialognewspur.h"
#include "ui_dialognewspur.h"

DialogNewSpur::DialogNewSpur(QWidget *parent,int Type) :
    QDialog(parent),
    ui(new Ui::DialogNewSpur),SpurType(Type)
{
    ui->setupUi(this);
    Canceled=true;
    Model = new QStandardItemModel(0, 0,this);
    ui->treeView->header()->setVisible(false);
    ui->treeView->setColumnWidth(0,50);
    ui->treeView->setModel(Model);
    LoadFunctionDefineClass();
    if(Model->rowCount()>0)
    {
        ui->treeView->expand(Model->item(0,0)->index());
        if(Model->item(0,0)->rowCount()>0)
        {
            ui->treeView->setCurrentIndex(Model->item(0,0)->child(0,0)->index());
        }
    }
    ListTermNum.clear();

    if(SpurType==1)
    {
        ui->LbPara2->setText("起止序号");
        ui->LbPara2->setText("端子数量");
        ui->GroupList->setTitle("端子列表");
        QStringList ListHeader={"序号","端子序号"};
        ui->tableWidget->setHorizontalHeaderLabels(ListHeader);
        ui->spinSpurCount->setEnabled(false);
    }
}

DialogNewSpur::~DialogNewSpur()
{
    delete ui;
}

void DialogNewSpur::LoadFunctionDefineClass()
{
qDebug()<<"1";
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 0 ORDER BY _Order");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/电气符号.png"),QueryVar.value("FunctionDefineName").toString());
    //fatherItem->setData(QVariant(QueryVar.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
    //fatherItem->setData(QVariant("0"),Qt::WhatsThisRole);
    Model->appendRow(fatherItem);
    if(SpurType==0)  temp = "SELECT * FROM FunctionDefineClass WHERE Level = 1 ORDER BY _Order";
    else if(SpurType==1) temp = "SELECT * FROM FunctionDefineClass WHERE Level = 1 AND FunctionDefineName = '端子,接插件' ORDER BY _Order";
    QueryVar.exec(temp);
qDebug()<<"2";
    while(QueryVar.next())
    {
        QString Parent_ID=QueryVar.value("ParentNo").toString();
        QSqlQuery QueryVar2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        temp = QString("SELECT FunctionDefineName FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+Parent_ID+"'");
        QueryVar2.exec(temp);
        if(!QueryVar2.next()) continue;
        for(int i=0;i<Model->rowCount();i++)
        {
            if(Model->item(i,0)->text()==QueryVar2.value(0).toString())
            {
                QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号大类.png"),QueryVar.value("FunctionDefineName").toString());
                SubFatherItem->setData(QVariant(QueryVar.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                SubFatherItem->setData(QVariant("1"),Qt::WhatsThisRole);
                Model->item(i,0)->appendRow(SubFatherItem);
                if(SpurType==1) ui->treeView->expand(Model->indexFromItem(SubFatherItem));
                break;
            }
        }
    }
    temp = "SELECT * FROM FunctionDefineClass WHERE Level = 2  ORDER BY _Order";
    QueryVar.exec(temp);
    while(QueryVar.next())
    {
        bool FlagAddItem=true;
        QString Parent_ID=QueryVar.value("ParentNo").toString();
        QSqlQuery QueryVar2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        temp = QString("SELECT FunctionDefineName FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+Parent_ID+"'");
        QueryVar2.exec(temp);
        if(!QueryVar2.next()) continue;
        for(int i=0;i<Model->rowCount();i++)
        {
            for(int j=0;j<Model->item(i,0)->rowCount();j++)
            {
                if(Model->item(i,0)->child(j,0)->text()==QueryVar2.value(0).toString())
                {
                    if(SpurType==0)
                    {
                        if((Model->item(i,0)->child(j,0)->text()=="端子,接插件")&&((QueryVar.value("FunctionDefineName").toString()=="端子")||(QueryVar.value("FunctionDefineName").toString()=="端子附件")))
                            FlagAddItem=false;
                    }
                    else
                    {
                        if((QueryVar.value("FunctionDefineName").toString()=="插针")||(QueryVar.value("FunctionDefineName").toString()=="隔离端子"))
                            FlagAddItem=false;
                    }
                    if(FlagAddItem)
                    {
                        QStandardItem *SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号小类.png"),QueryVar.value("FunctionDefineName").toString());
                        SubSubFatherItem->setData(QVariant(QueryVar.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                        SubSubFatherItem->setData(QVariant("2"),Qt::WhatsThisRole);
                        Model->item(i,0)->child(j,0)->appendRow(SubSubFatherItem);
                        if(SpurType==1) ui->treeView->expand(Model->indexFromItem(SubSubFatherItem));
                    }
                    break;
                }
            }
        }
    }
qDebug()<<"4";
    temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 3 ORDER BY _Order");
    QueryVar.exec(temp);
    while(QueryVar.next())
    {
        QString Parent_ID=QueryVar.value("ParentNo").toString();
        QSqlQuery QueryVar2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        temp = QString("SELECT FunctionDefineName FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+Parent_ID+"'");
        QueryVar2.exec(temp);
        if(!QueryVar2.next()) continue;
        for(int i=0;i<Model->rowCount();i++)
        {
            for(int j=0;j<Model->item(i,0)->rowCount();j++)
            {
                for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)
                {
                    if(Model->item(i,0)->child(j,0)->child(k,0)->text()==QueryVar2.value(0).toString())
                    {
                        QStandardItem *SubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号规格.png"),QueryVar.value("FunctionDefineName").toString());
                        SubSubSubFatherItem->setData(QVariant(QueryVar.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                        SubSubSubFatherItem->setData(QVariant("3"),Qt::WhatsThisRole);
                        Model->item(i,0)->child(j,0)->child(k,0)->appendRow(SubSubSubFatherItem);
                        break;
                    }
                }
            }
        }
    }
    temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 4 ORDER BY _Order");
    QueryVar.exec(temp);
qDebug()<<"5";
    while(QueryVar.next())
    {
        QString Parent_ID=QueryVar.value("ParentNo").toString();
        QSqlQuery QueryVar2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        temp = QString("SELECT FunctionDefineName FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+Parent_ID+"'");
        QueryVar2.exec(temp);
        if(!QueryVar2.next()) continue;
        for(int i=0;i<Model->rowCount();i++)
        {
            for(int j=0;j<Model->item(i,0)->rowCount();j++)
            {
                for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)
                {
                    for(int m=0;m<Model->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                    {
                        if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->text()==QueryVar2.value(0).toString())
                        {
                            QStandardItem *SubSubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/功能定义节点图标.png"),QueryVar.value("FunctionDefineName").toString());
                            SubSubSubSubFatherItem->setData(QVariant(QueryVar.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                            SubSubSubSubFatherItem->setData(QVariant("4"),Qt::WhatsThisRole);
                            Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->appendRow(SubSubSubSubFatherItem);
                            break;
                        }
                    }
                }
            }
        }
    }
qDebug()<<"6";
}

void DialogNewSpur::SetCurrentIndex(QString FunctionDefineClass_ID)//如1302.1.1
{
    for(int i=0;i<Model->rowCount();i++)//电气工程
    {
        for(int j=0;j<Model->item(i,0)->rowCount();j++)//功能大类
            for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)//功能小类
            {
                for(int m=0;m<Model->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                   for(int n=0;n<Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->rowCount();n++)
                   {
                       if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)->data(Qt::UserRole).toString()==FunctionDefineClass_ID)
                       {
                           ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)));
                           ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                           break;
                       }
                   }
                }
            }
    }
}

void DialogNewSpur::on_BtnOk_clicked()
{
    if(!CheckTermNum())
    {
        QMessageBox::warning(nullptr, "提示", " 起止序号必须以数字开头，例如1~20或1,2,3..");
        return;
    }
    if(SpurType==0)
    {
        if(ui->LbTermCount->text()!="")
        {
            if((ListTermNum.count()>0)&&(ListTermNum.count()!=ui->LbTermCount->text().toInt()))
            {
                QMessageBox::warning(nullptr, "提示", "端号与实际端口数量不符");
                return;
            }
            TermCount=ui->LbTermCount->text().toInt();
        }
        else TermCount=0;
    }
    else
    {
       if(ui->EdTermNum->text()=="")
       {
           QMessageBox::warning(nullptr, "提示", "请输入端子起止序号！");
           return;
       }
    }

    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp;
    temp= QString("SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'");
    QueryVar.exec(temp);
    if(QueryVar.next())
    {
        Canceled=false;
        SpurCount=ui->spinSpurCount->value();
        FunctionDefineName=QueryVar.value("FunctionDefineName").toString();
        FunctionDefineCode=QueryVar.value("FunctionDefineCode").toString();
        FunctionDefineClass_ID=QueryVar.value("FunctionDefineClass_ID").toString();
        SPSName=QueryVar.value("DefaultSymbol").toString();
        close();
    }
    else
    {
        Canceled=true;
        close();
    }
}

void DialogNewSpur::on_treeView_clicked(const QModelIndex &index)
{
    if(!index.parent().parent().parent().parent().isValid()) {ui->BtnOk->setEnabled(false);return;}
    else ui->BtnOk->setEnabled(true);

    QSqlQuery QueryFunctionDefineClass = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    if(QueryFunctionDefineClass.next())
    {
        ui->LbTermCount->setText(QString::number(GetDwgTermCount("C:/TBD/SPS/"+QueryFunctionDefineClass.value("DefaultSymbol").toString()+".dwg",QueryFunctionDefineClass.value("DefaultSymbol").toString())));//QuerySPSFuncDef.value("TermCount").toString());
        UnitSymbolsView("C:/TBD/SPS/"+QueryFunctionDefineClass.value("DefaultSymbol").toString()+".dwg","C:/TBD/data/TempImage/"+QueryFunctionDefineClass.value("DefaultSymbol").toString()+".jpg",ui->LbSpurJpg,true);
    }
}

void DialogNewSpur::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

bool DialogNewSpur::CheckTermNum()
{
    if(ui->EdTermNum->text()=="") return true;
    if((ui->EdTermNum->text().at(0)<'0')||(ui->EdTermNum->text().at(0)>'9'))
    {
        //QMessageBox::warning(nullptr, "提示", " 起止序号必须以数字开头，例如1~20或1,2,3..");
        return false;
    }
    for(int i=0;i<ui->EdTermNum->text().count();i++)
    {
        if(((ui->EdTermNum->text().at(i)<'0')||(ui->EdTermNum->text().at(i)>'9'))&&(ui->EdTermNum->text().at(i)!=',')&&(ui->EdTermNum->text().at(i)!='~'))
        {
            //QMessageBox::warning(nullptr, "提示", " 起止序号格式错误1，正确格式例如1~20或1,2,3..");
            return false;
        }
    }
    if(ui->EdTermNum->text().contains("~"))
    {
        QStringList ListTermNum=ui->EdTermNum->text().split("~");
        if(ListTermNum.count()!=2)
        {
            //QMessageBox::warning(nullptr, "提示", " 起止序号格式错误2，正确格式例如1~20或1,2,3..");
            return false;
        }
        for(int i=0;i<ListTermNum.count();i++)
        {
            if((ListTermNum.at(i)<'0')||(ListTermNum.at(i)>'9'))
            {
                //QMessageBox::warning(nullptr, "提示", " 起止序号格式错误3，正确格式例如1~20或1,2,3..");
                return false;
            }
        }
    }
    if(ui->EdTermNum->text().contains(","))
    {
        QStringList ListTermNum=ui->EdTermNum->text().split(",");
        for(int i=0;i<ListTermNum.count();i++)
        {
            if((ListTermNum.at(i)<'0')||(ListTermNum.at(i)>'9'))
            {
                //QMessageBox::warning(nullptr, "提示", " 起止序号格式错误4，正确格式例如1~20或1,2,3..");
                return false;
            }
        }
    }

    QString StrTermAll=ui->EdTermNum->text();
    //判断是1~20类型还是1,2,3,...类型
    ListTermNum.clear();
    if(StrTermAll.contains("~"))
    {
        QStringList ListTemp=StrTermAll.split("~");
        if(ListTemp.at(0).toInt()>ListTemp.at(1).toInt())
        {
            for(int i=0;i<(ListTemp.at(0).toInt()-ListTemp.at(1).toInt()+1);i++)
            {
               ListTermNum.append(QString::number(ListTemp.at(1).toInt()+i));
            }
        }
        else
        {
            for(int i=0;i<(ListTemp.at(1).toInt()-ListTemp.at(0).toInt()+1);i++)
            {
               ListTermNum.append(QString::number(ListTemp.at(0).toInt()+i));
            }
        }
    }
    else if(StrTermAll.contains(","))
    {
        ListTermNum=StrTermAll.split(",");
    }
    else ListTermNum.append(StrTermAll);

    for(int i=0;i<ListTermNum.count();i++)
    {
       for(int j=0;j<i;j++)
       {
           if(ListTermNum.at(i)==ListTermNum.at(j))
           {
               QMessageBox::warning(nullptr, "提示", " 起止序号格式错误，端号重复");
               return false;
           }
       }
    }

    ui->tableWidget->setRowCount(ListTermNum.count());
    for(int i=0;i<ListTermNum.count();i++)
    {
       ui->tableWidget->setItem(i,0,new QTableWidgetItem(QString::number(i+1)));
       ui->tableWidget->setItem(i,1,new QTableWidgetItem(ListTermNum.at(i)));
    }
    if(SpurType==1) ui->spinSpurCount->setValue(ui->tableWidget->rowCount());
    return true;
}

void DialogNewSpur::on_EdTermNum_textChanged(const QString &arg1)
{
    CheckTermNum();
}
