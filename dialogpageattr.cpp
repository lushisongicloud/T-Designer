#include "dialogpageattr.h"
#include "ui_dialogpageattr.h"
#include "common.h"
extern QSqlDatabase  T_ProjectDatabase;
DialogPageAttr::DialogPageAttr(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogPageAttr)
{
    ui->setupUi(this);
    PageNameSetUpdated=false;
    Canceled=true;
    ui->tableWidget->setRowCount(0);
    QStringList listTableName;
    listTableName.clear();
    listTableName<<"图号"<<"页数"<<"设计"<<"设计日期"<<"审核"<<"审核日期"<<"工艺"<<"工艺日期"<<"校核"<<"校核日期"<<"标准化"<<"标准化日期"<<"批准"<<"批准日期"<<"标记"<<"处数"<<"更改文件号"<<"签名"<<"日期";
    for(int i=0;i<listTableName.count();i++)
    {
       ui->tableWidget->setRowCount(i+1);
       ui->tableWidget->setItem(i,0,new QTableWidgetItem(listTableName.at(i)));
       ui->tableWidget->setItem(i,1,new QTableWidgetItem(""));
    }
}

DialogPageAttr::~DialogPageAttr()
{
    delete ui;
}
void DialogPageAttr::SetPageName()
{
    ui->EdPageName->setText(PageInitName);
}
//根据Page_ID载入page信息,Mode=1：新建图纸 Mode=2：图纸属性  Mode=3：添加已有图纸并更新数据库
void DialogPageAttr::LoadPageInfo()
{
qDebug()<<"LoadPageInfo,Mode="<<Mode;
   if(Mode==1)
   {
       ui->EdPageName->setText(PageInitName);
       ui->EdPageType->setText("原理图");
       dlgPageNameSet.LoadTable(ui->EdPageName->text(),1);//1:Page项目代号  2:Unit项目代号
   }
   else if(Mode==2)
   {
       QString PageName=GetPageNameByPageID(Page_ID);
       ui->EdPageName->setText(PageName);
       QSqlQuery query=QSqlQuery(T_ProjectDatabase);
       QString sqlstr=QString("SELECT * FROM Page WHERE Page_ID = "+QString::number(Page_ID));
       query.exec(sqlstr);
       if(!query.next()) return;
       ui->EdPageDesc->setText(query.value("Page_Desc").toString());
       ui->EdPageFrame->setText(query.value("Title").toString());
       ui->EdPageType->setText(query.value("PageType").toString());
   }
}

void DialogPageAttr::on_BtnPageNameSet_clicked()
{
    dlgPageNameSet.Canceled=true;
    dlgPageNameSet.LoadTable(ui->EdPageName->text(),1);//Mode=1:Page项目代号  Mode=2:Unit项目代号
    dlgPageNameSet.setModal(true);
    dlgPageNameSet.show();
    dlgPageNameSet.exec();
    if(dlgPageNameSet.Canceled) PageNameSetUpdated=false;
    else
    {
        PageNameSetUpdated=true;
        ui->EdPageName->setText(dlgPageNameSet.ReturnPageName);
    }
}


void DialogPageAttr::on_BtnOk_clicked()
{
    QSqlQuery query=QSqlQuery(T_ProjectDatabase);
    int ProjectStructure_ID;
    QString displayName = ui->EdPageName->text().trimmed();
    QString prefix = ExtractPagePrefix(displayName);
    QString baseName = ExtractPageBaseName(displayName);
    if (baseName.isEmpty())
        baseName = displayName;
    QString StrGaoCeng, StrPos, StrPage;
    SplitPagePrefix(prefix, &StrGaoCeng, &StrPos, &StrPage);
    if (StrPage.isEmpty())
        StrPage = baseName;
    QString canonicalName = BuildCanonicalPageName(prefix, StrPage, baseName);
    if (canonicalName != displayName)
        ui->EdPageName->setText(canonicalName);
    QString canonicalPrefix = ExtractPagePrefix(ui->EdPageName->text());
    SplitPagePrefix(canonicalPrefix, &StrGaoCeng, &StrPos, &StrPage);

    ProjectStructure_ID=InsertRecordToProjectStructure(1,StrGaoCeng,StrPos,StrPage);

    QString PageName = ExtractPageBaseName(ui->EdPageName->text());
    if (PageName.isEmpty())
        PageName = ui->EdPageName->text();

    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp;
    if(Mode==1) temp= "SELECT * FROM Page WHERE ProjectStructure_ID = '"+QString::number(ProjectStructure_ID)+"'";
    else temp= "SELECT * FROM Page WHERE ProjectStructure_ID = '"+QString::number(ProjectStructure_ID)+"' AND Page_ID <> "+QString::number(Page_ID);
    QueryVar.exec(temp);
    while(QueryVar.next())
    {
        if(QueryVar.value("PageName").toString()==PageName)
        {
            QMessageBox::warning(nullptr, "提示", "与已有图纸名称重复！");
            return;
        }
    }
    /*
    if(PageNameSetUpdated||(Mode==1))
    {
        //Mode=0不添加page记录   Mode=1 添加page记录
qDebug()<<dlgPageNameSet.StrGaoceng<<dlgPageNameSet.StrPos<<dlgPageNameSet.StrPage;

    }
    else//未修改过页属性设置，根据当前页名确定ProjectStructure_ID
    {
        QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString tempSQL = QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6' AND Structure_INT = '"+StrPage+"'");
        QueryPage.exec(tempSQL);
        while(QueryPage.next())
        {
            QSqlQuery QueryPos= QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString tempPos = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString());
            QueryPos.exec(tempPos);
            if(!QueryPos.next()) return;
            if(StrPos!=QueryPos.value("Structure_INT").toString()) continue;
            QSqlQuery QueryGaoceng= QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString tempGaoceng = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
            QueryGaoceng.exec(tempPos);
            if(!QueryGaoceng.next()) return;
            if(StrGaoCeng!=QueryGaoceng.value("Structure_INT").toString()) continue;
            ProjectStructure_ID=QueryPage.value("ProjectStructure_ID").toInt();
            break;
        }
    }*/

    //更新页属性
    if(Mode==1)//Add page 或添加已有图纸
    {
        //新增数据库Page表中的记录
        Page_ID=GetMaxIDOfDB(T_ProjectDatabase,"Page","Page_ID");
        QString temp =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                          "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
        query.prepare(temp);
        query.bindValue(":Page_ID",Page_ID);
        query.bindValue(":ProjectStructure_ID",QString::number(ProjectStructure_ID));
        query.bindValue(":Page_Desc",ui->EdPageDesc->text());
        query.bindValue(":PageType",ui->EdPageType->text());     
        query.bindValue(":PageName",PageName);
        query.bindValue(":Scale","1:1");
        query.bindValue(":Border","A3:420x297");
        query.bindValue(":Title",ui->EdPageFrame->text());
        query.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
        query.exec();
    }
    else if(Mode==2)//modify page
    {
        QString tempSQL=QString("UPDATE Page SET ProjectStructure_ID=:ProjectStructure_ID,Page_Desc=:Page_Desc,PageType=:PageType,PageName=:PageName,Scale=:Scale,Border=:Border,Title=:Title,AlterTime=:AlterTime"
                                " WHERE Page_ID="+QString::number(Page_ID));
        query.prepare(tempSQL);
        query.bindValue(":ProjectStructure_ID",QString::number(ProjectStructure_ID));
        query.bindValue(":Page_Desc",ui->EdPageDesc->text());
        query.bindValue(":PageType",ui->EdPageType->text());
        query.bindValue(":PageName",ExtractPageBaseName(ui->EdPageName->text()));
        query.bindValue(":Scale","1:1");
        query.bindValue(":Border","A3:420x297");
        query.bindValue(":Title",ui->EdPageFrame->text());
        query.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
        query.exec();
    }

    Canceled=false;
    PageInitName=ui->EdPageName->text();
    close();
}

void DialogPageAttr::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}
