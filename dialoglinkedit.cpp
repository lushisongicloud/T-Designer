#include "dialoglinkedit.h"
#include "ui_dialoglinkedit.h"

DialogLinkEdit::DialogLinkEdit(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogLinkEdit)
{
    ui->setupUi(this);
    Canceled=true;
    ProSetUpdated=false;
}

DialogLinkEdit::~DialogLinkEdit()
{
    delete ui;
}

void DialogLinkEdit::LoadLinkInfo(int LinkID)
{
   if(AttrMode==1)//新增
   {
        ProjectStructure_ID=GetProjectStructureIDByPageID(Page_ID).toInt();
        ui->LbProTag->setText(GetProjectStructureStrByProjectStructureID(ProjectStructure_ID));
        return;
   }

   Link_ID= LinkID;
   QSqlQuery QueryLink=QSqlQuery(T_ProjectDatabase);
   QString StrSql="SELECT * FROM Link WHERE Link_ID = "+QString::number(Link_ID);
   QueryLink.exec(StrSql);
   if(!QueryLink.next()) return;
   ui->EdLinkTag->setText(QueryLink.value("Link_Label").toString());
   ui->EdDesc->setText(QueryLink.value("Link_Desc").toString());
   ProjectStructure_ID=QueryLink.value("ProjectStructure_ID").toInt();
   ui->LbProTag->setText(GetProjectStructureStrByProjectStructureID(QueryLink.value("ProjectStructure_ID").toInt())+"-"+QueryLink.value("Link_Label").toString());
   if(QueryLink.value("LinkText_Location").toString()=="0") ui->CbTextPos->setCurrentText("箭头");
   else ui->CbTextPos->setCurrentText("箭尾");
}

void DialogLinkEdit::on_BtnOK_clicked()
{
    if(ui->EdLinkTag->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", "链接点代号不能为空");
        return;
    }
    QSqlQuery QueryLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    if(AttrMode==2) SqlStr="SELECT * FROM Link WHERE Link_Label = '"+ui->EdLinkTag->text()+"' AND Link_ID <> "+QString::number(Link_ID);
    else SqlStr="SELECT * FROM Link WHERE Link_Label = '"+ui->EdLinkTag->text()+"'";
    QueryLink.exec(SqlStr);
    int LinkCount=0;
    while(QueryLink.next()) LinkCount++;
    if(LinkCount>=2)
    {
        QMessageBox::warning(nullptr, "提示", "该链接点代号已定义2处！");
        return;
    }
    Canceled=false;
    if(ProSetUpdated)
    {
        QString GaocengStr,PosStr;
        QString TmpStr=ui->LbProTag->text();
        int indexGaoceng=TmpStr.indexOf("=");
        int indexPos=TmpStr.indexOf("+");
        int indexUnit=TmpStr.indexOf("-");
        if(indexGaoceng>=0) GaocengStr=TmpStr.mid(indexGaoceng+1,indexPos-indexGaoceng-1);
        if(indexPos>=0) PosStr=TmpStr.mid(indexPos+1,indexUnit-indexPos-1);
        ProjectStructure_ID=InsertRecordToProjectStructure(0,GaocengStr,PosStr,"");
    }
    //更新器件信息,区分是新增还是修改
    if(AttrMode==1)//新增
    {
        QSqlQuery queryLink(T_ProjectDatabase);
        SqlStr = QString("INSERT INTO Link (Link_ID,ProjectStructure_ID,Page_ID,Link_Label,Link_Desc,LinkText_Location)"
                          " VALUES (:Link_ID,:ProjectStructure_ID,:Page_ID,:Link_Label,:Link_Desc,:LinkText_Location)");
        queryLink.prepare(SqlStr);
        int MaxLink_ID=GetMaxIDOfDB(T_ProjectDatabase,"Link","Link_ID");
        queryLink.bindValue(":Link_ID",MaxLink_ID);
        queryLink.bindValue(":ProjectStructure_ID",QString::number(ProjectStructure_ID));
        queryLink.bindValue(":Page_ID",QString::number(Page_ID));
        queryLink.bindValue(":Link_Label",ui->EdLinkTag->text());
        queryLink.bindValue(":Link_Desc",ui->EdDesc->text());
        queryLink.bindValue(":LinkText_Location",QString::number(ui->CbTextPos->currentIndex()));
        queryLink.exec();
        Link_ID=MaxLink_ID;
    }
    else
    {
        QSqlQuery queryLink(T_ProjectDatabase);
        QString tempSQL="UPDATE Link SET ProjectStructure_ID=:ProjectStructure_ID,Link_Label=:Link_Label,Link_Desc=:Link_Desc,LinkText_Location=:LinkText_Location"
                                " WHERE Link_ID = "+QString::number(Link_ID);
        queryLink.prepare(tempSQL);
        queryLink.bindValue(":ProjectStructure_ID",QString::number(ProjectStructure_ID));
        queryLink.bindValue(":Link_Label",ui->EdLinkTag->text());
        queryLink.bindValue(":Link_Desc",ui->EdDesc->text());
        queryLink.bindValue(":LinkText_Location",QString::number(ui->CbTextPos->currentIndex()));
        queryLink.exec();
    }
    RetStrLinkTag=ui->EdLinkTag->text();
    RetStrLinkTextPosition=ui->CbTextPos->currentText();
    close();
}

void DialogLinkEdit::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogLinkEdit::on_BtnProSet_clicked()
{
    dlgPageNameSet.LoadTable(ui->LbProTag->text(),2);//Mode=1:Page项目代号  Mode=2:Unit项目代号
    dlgPageNameSet.HideEdPageName();
    dlgPageNameSet.setModal(true);
    dlgPageNameSet.show();
    dlgPageNameSet.exec();
    if(!dlgPageNameSet.Canceled)
    {
        ProSetUpdated=true;
        ui->LbProTag->setText(dlgPageNameSet.ReturnUnitPro+"-"+ui->EdLinkTag->text());
    }
}
