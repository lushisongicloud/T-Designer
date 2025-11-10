#include "dialoglinedefine.h"
#include "ui_dialoglinedefine.h"

DialogLineDefine::DialogLineDefine(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogLineDefine)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogLineDefine::~DialogLineDefine()
{
    delete ui;
}

//Mode=0 RotateAngle=0,SingleOrMutiLine=0
//Mode=1 RotateAngle=0,SingleOrMutiLine=1
//Mode=2 RotateAngle=1,SingleOrMutiLine=0
//Mode=3 RotateAngle=1,SingleOrMutiLine=1
void DialogLineDefine::LoadLineInfo(int m_Wires_ID)
{
    Wires_ID=m_Wires_ID;
    QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
    QString tempSQL="SELECT * FROM Wires WHERE Wires_ID = "+QString::number(m_Wires_ID);
    QueryWires.exec(tempSQL);
    if(!QueryWires.next()) return;
    ui->EdPartCode->setText(QueryWires.value("PartCode").toString());
    ui->EdType->setText(QueryWires.value("Type").toString());
    ui->EdWireTag->setText(QueryWires.value("ConnectionNumber").toString());
    ui->CbColor->setCurrentText(QueryWires.value("Color").toString());
    ui->CbDiameter->setCurrentText(QueryWires.value("Diameters").toString());
    UnitSymbolsView("C:/TBD/SPS/SPS_CDP-"+QString::number(SymbolMode+1)+".dwg","C:/TBD/data/TempImage/SPS_CDP.jpg",ui->LbWireAttrView,true);
}

void DialogLineDefine::on_BtnOK_clicked()
{
    Canceled=false;
    QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
    QString tempSQL;
    tempSQL="SELECT * FROM Wires WHERE ConnectionNumber = '"+ui->EdWireTag->text()+"' AND Wires_ID <> "+QString::number(Wires_ID);
    QueryWires.exec(tempSQL);
    if(QueryWires.next())
    {
        QMessageBox::warning(nullptr, "提示", "该线号已存在！");
        return;
    }
    tempSQL="UPDATE Wires SET ConnectionNumber=:ConnectionNumber,Color=:Color,Diameters=:Diameters,PartCode=:PartCode,Type=:Type WHERE Wires_ID= "+QString::number(Wires_ID);
    QueryWires.prepare(tempSQL);
    QueryWires.bindValue(":ConnectionNumber",ui->EdWireTag->text());
    QueryWires.bindValue(":Color",ui->CbColor->currentText());
    QueryWires.bindValue(":Diameters",ui->CbDiameter->currentText());
    QueryWires.bindValue(":PartCode",ui->EdPartCode->text());
    QueryWires.bindValue(":Type",ui->EdType->text());
    QueryWires.exec();
    close();
}

void DialogLineDefine::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogLineDefine::on_BtnChangeForm_clicked()
{
    if(SymbolMode<3) SymbolMode=SymbolMode+1;
    else SymbolMode=0;
    UnitSymbolsView("C:/TBD/SPS/SPS_CDP-"+QString::number(SymbolMode+1)+".dwg","C:/TBD/data/TempImage/SPS_CDP.jpg",ui->LbWireAttrView,true);
}
