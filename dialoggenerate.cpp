#include "dialoggenerate.h"
#include "ui_dialoggenerate.h"

DialogGenerate::DialogGenerate(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogGenerate)
{
    ui->setupUi(this);
    Canceled=true;
    ui->tableWidget->setRowCount(3);
    ui->tableWidget->setItem(0,0,new QTableWidgetItem("高层代号"));ui->tableWidget->setItem(0,1,new QTableWidgetItem("="));
    ui->tableWidget->setItem(1,0,new QTableWidgetItem("位置代号"));ui->tableWidget->setItem(1,1,new QTableWidgetItem("+"));
    ui->tableWidget->setItem(2,0,new QTableWidgetItem("文档类型"));ui->tableWidget->setItem(2,1,new QTableWidgetItem("&"));
    QComboBox *CbGaoCeng=new QComboBox(ui->tableWidget);
    CbGaoCeng->setEditable(false);
    connect(CbGaoCeng,SIGNAL(currentIndexChanged(int)),this,SLOT(UpdateCbPos(int)));
    ui->tableWidget->setCellWidget(0,2,CbGaoCeng);
    QComboBox *CbPos=new QComboBox(ui->tableWidget);
    CbPos->setEditable(false);
    ui->tableWidget->setCellWidget(1,2,CbPos);
    /*
    QComboBox *CbPageType=new QComboBox(ui->tableWidget);
    CbPageType->addItem("图纸目录");
    CbPageType->addItem("元件列表");
    CbPageType->addItem("部件汇总表");
    CbPageType->addItem("端子列表");
    CbPageType->addItem("连接列表");
    CbPageType->addItem("电缆列表");
    //CbPageType->setEditable(true);
    ui->tableWidget->setCellWidget(2,2,CbPageType);*/
    ui->tableWidget->setItem(2,2,new QTableWidgetItem(""));
}

DialogGenerate::~DialogGenerate()
{
    delete ui;
}

void DialogGenerate::UpdateCbPos(int index)
{
    QComboBox *CbGaoCeng=(QComboBox *)ui->tableWidget->cellWidget(0,2);
    QComboBox *CbPos=(QComboBox *)ui->tableWidget->cellWidget(1,2);
    CbPos->clear();
    CbPos->addItem("所有");
    //查询工程数据库
    QSqlQuery query=QSqlQuery(T_ProjectDatabase);
    QString sqlstr="SELECT * FROM ProjectStructure WHERE Structure_ID = '3' AND Structure_INT = '"+CbGaoCeng->currentText()+"'";
    query.exec(sqlstr);
    while(query.next())
    {
        QSqlQuery queryPos=QSqlQuery(T_ProjectDatabase);
        sqlstr="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Parent_ID = '"+query.value("ProjectStructure_ID").toString()+"'";
        queryPos.exec(sqlstr);
        while(queryPos.next())
        {
           bool Existed=false;
           for(int i=0;i<CbPos->count();i++) if(CbPos->itemText(i)==queryPos.value("Structure_INT").toString()) {Existed=true;break;}
           if(!Existed) CbPos->addItem(queryPos.value("Structure_INT").toString());
        }
    }
    CbPos->setCurrentText("所有");
}

//Type=0:图纸目录 Type=1:元件列表 Type=2:部件汇总表 Type=3:端子列表 Type=4:连接列表 Type=5:电缆列表
QStringList ListType={"图纸目录","元件列表","部件汇总表","端子列表","连接列表","电缆列表"};
void DialogGenerate::LoadTable(int Type)
{
   QComboBox *CbGaoCeng=(QComboBox *)ui->tableWidget->cellWidget(0,2);
   QComboBox *CbPos=(QComboBox *)ui->tableWidget->cellWidget(1,2);
   //QComboBox *CbPageType=(QComboBox *)ui->tableWidget->cellWidget(2,2);
   QString StrOriginalGaoCeng=CbGaoCeng->currentText();
   QString StrOriginalPos=CbPos->currentText();
   ui->tableWidget->item(2,2)->setText(ListType.at(Type));//CbPageType->currentText();
   //查询工程数据库
   QSqlQuery query=QSqlQuery(T_ProjectDatabase);
   CbGaoCeng->clear();
   CbGaoCeng->addItem("所有");
   QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3'");
   query.exec(sqlstr);
   while(query.next())
   {
      bool Existed=false;
      for(int i=0;i<CbGaoCeng->count();i++) if(CbGaoCeng->itemText(i)==query.value("Structure_INT").toString()) { Existed=true;break;}
      if(!Existed) CbGaoCeng->addItem(query.value("Structure_INT").toString());
   }
   CbGaoCeng->setCurrentText("所有");


   CbPos->clear();
   CbPos->addItem("所有");
   /*
   sqlstr="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Parent_ID = '"+query.value("ProjectStructure_ID").toString()+"'";
   query.exec(sqlstr);
   while(query.next())
   {
      bool Existed=false;
      for(int i=0;i<CbPos->count();i++) if(CbPos->itemText(i)==query.value("Structure_INT").toString()) {Existed=true;break;}
      if(!Existed) CbPos->addItem(query.value("Structure_INT").toString());
   }
   */
   CbPos->setCurrentText("所有");
}

void DialogGenerate::on_BtnOK_clicked()
{   
    if(ui->EdStartPageName->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", "请输入起始页名！");
        return;
    }
    ReplaceOriginalDwg=ui->CbReplaceOriginalDwg->isChecked();
    StrGaoceng=((QComboBox *)ui->tableWidget->cellWidget(0,2))->currentText();
    StrPos=((QComboBox *)ui->tableWidget->cellWidget(1,2))->currentText();
    StrPage=ui->tableWidget->item(2,2)->text();
    //查看页面名称是否与现有的重名
    if(!ReplaceOriginalDwg)
    {
        QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString StrSql;
        StrSql= "SELECT * FROM Page WHERE PageType = '图纸目录' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos,ui->tableWidget->item(2,2)->text())+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
           if(GetStrRemoveLastNum(QueryPage.value("PageName").toString())==GetStrRemoveLastNum(ui->EdStartPageName->text()))
           {
               QMessageBox::warning(nullptr, "提示", "起始页名与已有图纸重复！");
               return;
           }
        }
    }

    if(StrGaoceng=="所有") {StrGaoceng="";AllGaoceng=true;}
    else AllGaoceng=false;
    if(StrPos=="所有") {StrPos="";AllPos=true;}
    else AllPos=false;

    ProjectStructure_ID=InsertRecordToProjectStructure(1,StrGaoceng,StrPos,StrPage);
    InitPageName=ui->EdStartPageName->text();
    Canceled=false;
    close();
}

void DialogGenerate::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}
