#include "dialogcabledefine.h"
#include "ui_dialogcabledefine.h"

DialogCableDefine::DialogCableDefine(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogCableDefine)
{
    ui->setupUi(this);
    Canceled=true;
    ProSetUpdated=false;
    ui->CbCableMech->clear();
    ui->CbCableMech->addItem("");
    ui->CbCableMech->addItem("10×1.5");
    ui->CbCableMech->addItem("10×2.5");
    ui->CbCableMech->addItem("14×1.5");
    ui->CbCableMech->addItem("14×2.5");
    ui->CbCableMech->addItem("18×1.5");
    ui->CbCableMech->addItem("18×2.5");
    ui->CbCableMech->addItem("24×1.5");
    ui->CbCableMech->addItem("24×2.5");
    ui->CbCableMech->addItem("3×10+1×6");
    ui->CbCableMech->addItem("3×3.5+1×10");
    ui->CbCableMech->addItem("4×1.5");
    ui->CbCableMech->addItem("4×2.5");
    ui->CbCableMech->addItem("4×4");
    ui->CbCableMech->addItem("6×1.5");
    ui->CbCableMech->addItem("6×2.5");
    ui->CbCableMech->addItem("6×4");
    ui->CbCableMech->addItem("8×1.5");
    ui->CbCableMech->addItem("8×2.5");
    ui->CbCableType->clear();
    ui->CbCableType->addItem("");
    QSqlQuery QueryCable=QSqlQuery(T_ProjectDatabase);
    QString tempSQL="SELECT * FROM Cable";
    QueryCable.exec(tempSQL);
    while(QueryCable.next())
    {
        bool Find=false;
        for(int i=0;i<ui->CbCableType->count();i++)
        {
            if(ui->CbCableType->itemText(i)==QueryCable.value("Type").toString())
            {
                Find=true;
                break;
            }
        }
        if(!Find) ui->CbCableType->addItem(QueryCable.value("Type").toString());
    }
}

DialogCableDefine::~DialogCableDefine()
{
    delete ui;
}

void DialogCableDefine::LoadCableInfo(int m_Cable_ID)
{
    if(AttrMode==1)//新增
    {   
        ProjectStructure_ID=GetProjectStructureIDByPageID(Page_ID).toInt();
        ui->LbProTag->setText(GetProjectStructureStrByProjectStructureID(ProjectStructure_ID));
        return;
    }
    Cable_ID=m_Cable_ID;
    QSqlQuery QueryCable=QSqlQuery(T_ProjectDatabase);
    QString tempSQL="SELECT * FROM Cable WHERE Cable_ID = "+QString::number(Cable_ID);
    QueryCable.exec(tempSQL);
    if(!QueryCable.next()) return;
    ui->EdPartCode->setText(QueryCable.value("PartCode").toString());
    ui->EdCableLength->setText(QueryCable.value("Length").toString());
    ui->EdCableTag->setText(QueryCable.value("CableNum").toString());
    ui->CbCableMech->setCurrentText(QueryCable.value("Structure").toString());
    ui->CbCableType->setCurrentText(QueryCable.value("Type").toString());
    ProjectStructure_ID=QueryCable.value("ProjectStructure_ID").toInt();
    ui->LbProTag->setText(GetProjectStructureStrByProjectStructureID(ProjectStructure_ID)+"-"+QueryCable.value("CableNum").toString());
}

void DialogCableDefine::on_BtnOK_clicked()
{
    if(ui->EdCableTag->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", " 电缆代号不能为空");
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
        //如果电缆代号和ProjectStructure_ID重复，则合并不新增
        QSqlQuery QueryCable = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString tempSQL="SELECT * FROM Cable WHERE CableNum = '"+ui->EdCableTag->text()+"' AND ProjectStructure_ID = '"+QString::number(ProjectStructure_ID)+"'";
        QueryCable.exec(tempSQL);
        if(QueryCable.next()) return;

        int MaxCable_ID=GetMaxIDOfDB(T_ProjectDatabase,"Cable","Cable_ID");
        //更新T_ProjectDatabase数据库的Cable表

        tempSQL = "INSERT INTO Cable (Cable_ID,ProjectStructure_ID,CableNum,Type,PartCode,Structure,Length)"
                          "VALUES (:Cable_ID,:ProjectStructure_ID,:CableNum,:Type,:PartCode,:Structure,:Length)";
        QueryCable.prepare(tempSQL);
        QueryCable.bindValue(":Cable_ID",MaxCable_ID);
        QueryCable.bindValue(":ProjectStructure_ID",QString::number(ProjectStructure_ID));
        QueryCable.bindValue(":CableNum",ui->EdCableTag->text());
        QueryCable.bindValue(":Type",ui->CbCableType->currentText());
        QueryCable.bindValue(":PartCode",ui->EdPartCode->text());
        QueryCable.bindValue(":Structure",ui->CbCableMech->currentText());
        QueryCable.bindValue(":Length",ui->EdCableLength->text());
        QueryCable.exec();
        Cable_ID=MaxCable_ID;


    }
    else if(AttrMode==2)//modify
    {
        //如果
        QSqlQuery QueryCable = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="UPDATE Cable SET ProjectStructure_ID=:ProjectStructure_ID,CableNum=:CableNum,Type=:Type,PartCode=:PartCode,Structure=:Structure,Length=:Length"
                                " WHERE Cable_ID = "+QString::number(Cable_ID);
        QueryCable.prepare(SqlStr);
        QueryCable.bindValue(":ProjectStructure_ID",QString::number(ProjectStructure_ID));
        QueryCable.bindValue(":CableNum",ui->EdCableTag->text());
        QueryCable.bindValue(":Type",ui->CbCableType->currentText());
        QueryCable.bindValue(":PartCode",ui->EdPartCode->text());
        QueryCable.bindValue(":Structure",ui->CbCableMech->currentText());
        QueryCable.bindValue(":Length",ui->EdCableLength->text());
        QueryCable.exec();
    }
    close();
}

void DialogCableDefine::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogCableDefine::on_BtnProSet_clicked()
{
    dlgPageNameSet.LoadTable(ui->LbProTag->text(),2);//Mode=1:Page项目代号  Mode=2:Unit项目代号
    dlgPageNameSet.HideEdPageName();
    dlgPageNameSet.setModal(true);
    dlgPageNameSet.show();
    dlgPageNameSet.exec();
    if(!dlgPageNameSet.Canceled)
    {
        ProSetUpdated=true;
        ui->LbProTag->setText(dlgPageNameSet.ReturnUnitPro+"-"+ui->EdCableTag->text());
    }
}
