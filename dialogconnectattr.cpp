#include "dialogconnectattr.h"
#include "ui_dialogconnectattr.h"

DialogConnectAttr::DialogConnectAttr(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogConnectAttr)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogConnectAttr::~DialogConnectAttr()
{
    delete ui;
}

void DialogConnectAttr::LoadConnectAttr(QString ConnectName,int Dir)
{
    this->ConnectName=ConnectName;
    this->Dir=Dir;
    QPixmap p;
    p=QPixmap("C:/TBD/data/"+ConnectName+"1.png");
    ui->label_Dir1->setPixmap(p);
    //ui->label_Dir1->setPixmap(p.scaled(ui->label_Dir1->width(),ui->label_Dir1->height()));
    p=QPixmap("C:/TBD/data/"+ConnectName+"2.png");
    ui->label_Dir2->setPixmap(p);
    //ui->label_Dir2->setPixmap(p.scaled(ui->label_Dir1->width(),ui->label_Dir1->height()));
    p=QPixmap("C:/TBD/data/"+ConnectName+"3.png");
    ui->label_Dir3->setPixmap(p);
    //ui->label_Dir3->setPixmap(p.scaled(ui->label_Dir1->width(),ui->label_Dir1->height()));
    p=QPixmap("C:/TBD/data/"+ConnectName+"4.png");
    ui->label_Dir4->setPixmap(p);
    //ui->label_Dir4->setPixmap(p.scaled(ui->label_Dir1->width(),ui->label_Dir1->height()));
    if(ConnectName.contains("SYMB2_M_PWF_TLRU"))
    {
        ui->RbConnect1->setText("1.目标左2.目标右");
        ui->RbConnect2->setText("1.目标右2.目标左");
        ui->RbConnect3->setText("1.目标右2.目标下");
        ui->RbConnect4->setText("1.目标左2.目标下");
    }
    else if(ConnectName.contains("SYMB2_M_PWF_TLRO"))
    {
        ui->RbConnect1->setText("1.目标左2.目标右");
        ui->RbConnect2->setText("1.目标右2.目标左");
        ui->RbConnect3->setText("1.目标左2.目标上");
        ui->RbConnect4->setText("1.目标右2.目标上");
    }
    else if(ConnectName.contains("SYMB2_M_PWF_TOUR"))
    {
        ui->RbConnect1->setText("1.目标上2.目标右");
        ui->RbConnect2->setText("1.目标下2.目标右");
        ui->RbConnect3->setText("1.目标上2.目标下");
        ui->RbConnect4->setText("1.目标下2.目标上");
    }
    else if(ConnectName.contains("SYMB2_M_PWF_TOUL"))
    {
        ui->RbConnect1->setText("1.目标上2.目标左");
        ui->RbConnect2->setText("1.目标下2.目标左");
        ui->RbConnect3->setText("1.目标上2.目标下");
        ui->RbConnect4->setText("1.目标下2.目标上");
    }

    if(Dir==1) ui->RbConnect1->setChecked(true);
    else if(Dir==2) ui->RbConnect2->setChecked(true);
    else if(Dir==3) ui->RbConnect3->setChecked(true);
    else if(Dir==4) ui->RbConnect4->setChecked(true);
}

void DialogConnectAttr::on_BtnOK_clicked()
{
    Canceled=false;
    if(ui->RbConnect1->isChecked()) Dir=1;
    else if(ui->RbConnect2->isChecked()) Dir=2;
    else if(ui->RbConnect3->isChecked()) Dir=3;
    else if(ui->RbConnect4->isChecked()) Dir=4;
    close();
}

void DialogConnectAttr::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}
