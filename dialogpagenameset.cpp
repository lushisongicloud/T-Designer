#include "dialogpagenameset.h"
#include "ui_dialogpagenameset.h"
extern QSqlDatabase  T_ProjectDatabase;
DialogPageNameSet::DialogPageNameSet(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogPageNameSet)
{
    ui->setupUi(this);
    Canceled=true;
    ui->tableWidget->setColumnWidth(1,50);
}

DialogPageNameSet::~DialogPageNameSet()
{
    delete ui;
}
void DialogPageNameSet::HideEdPageName()
{
  ui->EdPageName->setVisible(false);
  ui->labelPageName->setVisible(false);
  ui->BtnOK->pos().setY(ui->EdPageName->pos().y());
  ui->BtnCancel->pos().setY(ui->EdPageName->pos().y());
  //this->setGeometry(this->x(),this->y(),this->width(),this->height()-ui->EdPageName->height());
}

//Mode=1:Page项目代号  Mode=2:Unit项目代号
void DialogPageNameSet::LoadTable(QString PageName,int Mode)
{
   ProMode=Mode;

   ui->tableWidget->setRowCount(3);
   ui->tableWidget->setItem(0,0,new QTableWidgetItem("高层代号"));ui->tableWidget->setItem(0,1,new QTableWidgetItem("="));
   ui->tableWidget->setItem(1,0,new QTableWidgetItem("位置代号"));ui->tableWidget->setItem(1,1,new QTableWidgetItem("+"));
   ui->tableWidget->setItem(2,0,new QTableWidgetItem("分组"));ui->tableWidget->setItem(2,1,new QTableWidgetItem("&"));
   if(Mode==2) ui->tableWidget->setRowHidden(2,true);
   else if(Mode==3)
   {
       ui->tableWidget->setRowHidden(0,true);
       ui->tableWidget->setRowHidden(2,true);
   }


   QComboBox *CbGaoCeng=new QComboBox(ui->tableWidget);
   CbGaoCeng->setEditable(true);
   //查询工程数据库
   QSqlQuery query=QSqlQuery(T_ProjectDatabase);
   QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3'");
   query.exec(sqlstr);
   while(query.next())
   {
      bool Existed=false;
      for(int i=0;i<CbGaoCeng->count();i++) if(CbGaoCeng->itemText(i)==query.value("Structure_INT").toString()) { Existed=true;break;}
      if(!Existed) CbGaoCeng->addItem(query.value("Structure_INT").toString());
   }
   if(PageName.contains("="))
   {
       int index=PageName.indexOf("·");

       if(ProMode==1)//Mode=1:Page项目代号  Mode=2:Unit项目代号  Mode=3:Terminal项目代号
       {
           if(PageName.contains("&")) index=PageName.indexOf("&");
           if(PageName.contains("+")) index=PageName.indexOf("+");
           CbGaoCeng->setCurrentText(PageName.mid(PageName.indexOf("=")+1,index-PageName.indexOf("=")-1));
       }
       else
       {
           index=PageName.indexOf("-");
           if(PageName.contains("+")) index=PageName.indexOf("+");
           CbGaoCeng->setCurrentText(PageName.mid(PageName.indexOf("=")+1,index-PageName.indexOf("=")-1));
       }
   }
   else CbGaoCeng->setCurrentText("");
   ui->tableWidget->setCellWidget(0,2,CbGaoCeng);
   sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3' AND Structure_INT = '"+CbGaoCeng->currentText()+"'");
   query.exec(sqlstr);
   QTableWidgetItem *gaocengDescItem = new QTableWidgetItem();
   if(query.next()) {
       gaocengDescItem->setText(query.value("Struct_Desc").toString());
   }
   gaocengDescItem->setFlags(gaocengDescItem->flags() | Qt::ItemIsEditable);
   ui->tableWidget->setItem(0,3,gaocengDescItem);
   
   // 连接信号，当高层代号改变时更新描述
   connect(CbGaoCeng, QOverload<const QString &>::of(&QComboBox::currentTextChanged), this, [this](const QString &text) {
       // ProMode=3时高层行被隐藏,不处理
       if (ProMode == 3) return;
       
       QSqlQuery query(T_ProjectDatabase);
       QString sqlstr = QString("SELECT Struct_Desc FROM ProjectStructure WHERE Structure_ID = '3' AND Structure_INT = :val");
       query.prepare(sqlstr);
       query.bindValue(":val", text.trimmed());
       QTableWidgetItem *item = ui->tableWidget->item(0, 3);
       if (!item) {
           item = new QTableWidgetItem();
           item->setFlags(item->flags() | Qt::ItemIsEditable);
           ui->tableWidget->setItem(0, 3, item);
       }
       if(query.exec() && query.next()) {
           item->setText(query.value("Struct_Desc").toString());
       } else {
           item->setText("");
       }
   });

   QComboBox *CbPos=new QComboBox(ui->tableWidget);
   CbPos->setEditable(true);
   sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5'");
   query.exec(sqlstr);
   while(query.next())
   {
      bool Existed=false;
      for(int i=0;i<CbPos->count();i++) if(CbPos->itemText(i)==query.value("Structure_INT").toString()) {Existed=true;break;}
      if(!Existed) CbPos->addItem(query.value("Structure_INT").toString());
   }
   if(PageName.contains("+"))
   {
       int index=PageName.indexOf("·");
       if(ProMode==1)//Mode=1:Page项目代号  Mode=2:Unit项目代号  Mode=3:Terminal项目代号
       {
           if(PageName.contains("&")) index=PageName.indexOf("&");
           CbPos->setCurrentText(PageName.mid(PageName.indexOf("+")+1,index-PageName.indexOf("+")-1));
       }
       else
       {
           if(PageName.contains("-"))
           {
               index=PageName.indexOf("-");
               CbPos->setCurrentText(PageName.mid(PageName.indexOf("+")+1,index-PageName.indexOf("+")-1));
           }
           else
           {
               CbPos->setCurrentText(PageName.mid(PageName.indexOf("+")+1,PageName.count()-PageName.indexOf("+")-1));
           }
       }
   }
   else CbPos->setCurrentText("");
   ui->tableWidget->setCellWidget(1,2,CbPos);
   sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+CbPos->currentText()+"'");
   query.exec(sqlstr);
   QTableWidgetItem *posDescItem = new QTableWidgetItem();
   if(query.next()) {
       posDescItem->setText(query.value("Struct_Desc").toString());
   }
   posDescItem->setFlags(posDescItem->flags() | Qt::ItemIsEditable);
   ui->tableWidget->setItem(1,3,posDescItem);
   
   // 连接信号，当位置代号改变时更新描述
   connect(CbPos, QOverload<const QString &>::of(&QComboBox::currentTextChanged), this, [this](const QString &text) {
       QSqlQuery query(T_ProjectDatabase);
       QString sqlstr = QString("SELECT Struct_Desc FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = :val");
       query.prepare(sqlstr);
       query.bindValue(":val", text.trimmed());
       QTableWidgetItem *item = ui->tableWidget->item(1, 3);
       if (!item) {
           item = new QTableWidgetItem();
           item->setFlags(item->flags() | Qt::ItemIsEditable);
           ui->tableWidget->setItem(1, 3, item);
       }
       if(query.exec() && query.next()) {
           item->setText(query.value("Struct_Desc").toString());
       } else {
           item->setText("");
       }
   });

   if(ProMode!=1) return;

   QComboBox *CbPageType=new QComboBox(ui->tableWidget);
   CbPageType->setEditable(true);
   sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6'");
   query.exec(sqlstr);
   while(query.next())
   {
      bool Existed=false;
      for(int i=0;i<CbPageType->count();i++) if(CbPageType->itemText(i)==query.value("Structure_INT").toString().trimmed()) {Existed=true;break;};
      if(!Existed) CbPageType->addItem(query.value("Structure_INT").toString().trimmed());
   }
   if(PageName.contains("&"))
   {
       int index=PageName.indexOf("·");
       QString groupValue = PageName.mid(PageName.indexOf("&")+1,index-PageName.indexOf("&")-1).trimmed();
       // groupValue 可能是 Structure_INT 或 Struct_Desc，优先按 Structure_INT 匹配
       bool found = false;
       QSqlQuery queryCheck(T_ProjectDatabase);
       queryCheck.prepare("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '6' AND Structure_INT = :val");
       queryCheck.bindValue(":val", groupValue);
       if(queryCheck.exec() && queryCheck.next()) {
           // 找到了，直接使用
           CbPageType->setCurrentText(groupValue);
           found = true;
       } else {
           // 没找到，尝试按 Struct_Desc 查找
           queryCheck.prepare("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '6' AND Struct_Desc = :val");
           queryCheck.bindValue(":val", groupValue);
           if(queryCheck.exec() && queryCheck.next()) {
               CbPageType->setCurrentText(queryCheck.value("Structure_INT").toString().trimmed());
               found = true;
           }
       }
       if(!found) CbPageType->setCurrentText("");
   }
   else CbPageType->setCurrentText("");
   ui->tableWidget->setCellWidget(2,2,CbPageType);
   {
       QSqlQuery queryDesc(T_ProjectDatabase);
       queryDesc.prepare("SELECT Struct_Desc FROM ProjectStructure WHERE Structure_ID = '6' AND Structure_INT = :val");
       queryDesc.bindValue(":val", CbPageType->currentText().trimmed());
       QTableWidgetItem *pageDescItem = new QTableWidgetItem();
       if(queryDesc.exec() && queryDesc.next()) {
           pageDescItem->setText(queryDesc.value("Struct_Desc").toString());
       }
       pageDescItem->setFlags(pageDescItem->flags() | Qt::ItemIsEditable);
       ui->tableWidget->setItem(2, 3, pageDescItem);
   }
   // 连接信号，当分组改变时更新描述
   connect(CbPageType, QOverload<const QString &>::of(&QComboBox::currentTextChanged), this, [this](const QString &text) {
       // 只在ProMode=1时处理分组
       if (ProMode != 1) return;
       
       QSqlQuery query(T_ProjectDatabase);
       query.prepare("SELECT Struct_Desc FROM ProjectStructure WHERE Structure_ID = '6' AND Structure_INT = :val");
       query.bindValue(":val", text.trimmed());
       QTableWidgetItem *item = ui->tableWidget->item(2, 3);
       if (!item) {
           item = new QTableWidgetItem();
           item->setFlags(item->flags() | Qt::ItemIsEditable);
           ui->tableWidget->setItem(2, 3, item);
       }
       if(query.exec() && query.next()) {
           item->setText(query.value("Struct_Desc").toString());
       } else {
           item->setText("");
       }
   });

   // 安全提取页名部分
   int dotIndex = PageName.indexOf("·");
   if (dotIndex >= 0 && dotIndex < PageName.length() - 1) {
       ui->EdPageName->setText(PageName.mid(dotIndex + 1));
   } else {
       ui->EdPageName->setText("");
   }
}

void DialogPageNameSet::on_BtnOK_clicked()
{
    ReturnPageName="";
    
    // 安全获取ComboBox指针并检查
    QComboBox *cbGaoceng = qobject_cast<QComboBox*>(ui->tableWidget->cellWidget(0, 2));
    QComboBox *cbPos = qobject_cast<QComboBox*>(ui->tableWidget->cellWidget(1, 2));
    
    if (!cbGaoceng || !cbPos) {
        // ComboBox不存在,异常情况
        Canceled = true;
        close();
        return;
    }
    
    StrGaoceng = cbGaoceng->currentText();
    StrPos = cbPos->currentText();

    // 保存描述信息到数据库
    // 保存高层描述(ProMode=3时高层行被隐藏,不保存)
    if (ProMode != 3 && !StrGaoceng.trimmed().isEmpty()) {
        QTableWidgetItem *gaocengDescItem = ui->tableWidget->item(0, 3);
        if (gaocengDescItem) {
            QString gaocengDesc = gaocengDescItem->text().trimmed();
            UpdateProjectStructureDesc("3", StrGaoceng, gaocengDesc);
        }
    }
    
    // 保存位置描述
    if (!StrPos.trimmed().isEmpty()) {
        QTableWidgetItem *posDescItem = ui->tableWidget->item(1, 3);
        if (posDescItem) {
            QString posDesc = posDescItem->text().trimmed();
            UpdateProjectStructureDesc("5", StrPos, posDesc);
        }
    }
    
    // 保存分组描述（仅当ProMode==1时）
    if (ProMode == 1) {
        QComboBox *cbPageType = qobject_cast<QComboBox*>(ui->tableWidget->cellWidget(2, 2));
        if (cbPageType) {
            StrPage = cbPageType->currentText();
            if (!StrPage.trimmed().isEmpty()) {
                QTableWidgetItem *pageDescItem = ui->tableWidget->item(2, 3);
                if (pageDescItem) {
                    QString pageDesc = pageDescItem->text().trimmed();
                    UpdateProjectStructureDesc("6", StrPage, pageDesc);
                }
            }
        }
    }

    // 构建返回的页名字符串
    if(StrGaoceng!="") ReturnPageName+="="+StrGaoceng;
    if(StrPos!="") ReturnPageName+="+"+StrPos;
    if(ProMode==1 && !StrPage.isEmpty())
    {
        if(StrPage!="") ReturnPageName+="&"+StrPage;
    }
    if(ReturnPageName!="") ReturnPageName+="·";
    ReturnPageName+=ui->EdPageName->text();
    ReturnUnitPro="="+StrGaoceng+"+"+StrPos;
    ReturnTerminalPro="="+StrGaoceng+"+"+StrPos;
    Canceled=false;
    close();
}
void DialogPageNameSet::on_EdPageName_textChanged(const QString &arg1)
{
    if(ProMode!=1) return;
    if(arg1.contains("=")||arg1.contains("+")||arg1.contains("&")||arg1.contains("·"))
    {
        QMessageBox::information(this, "提示信息","页名不能包含下列任何字符\n+=%·", QMessageBox::Yes);
        ui->EdPageName->setText(arg1.mid(0,arg1.count()-1));
        return;
    }
}

void DialogPageNameSet::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}
