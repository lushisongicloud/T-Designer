#include "dialogsettestpreference.h"
#include "ui_dialogsettestpreference.h"

DialogSetTestPreference::DialogSetTestPreference(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogSetTestPreference)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogSetTestPreference::~DialogSetTestPreference()
{
    delete ui;
}

void DialogSetTestPreference::SetPreference(int Preference)
{
    TestPointPreference=Preference;
    if(Preference==1) ui->RbOnlyInfoMess->setChecked(true);
    else if(Preference==2) ui->RbOnlyTestCost->setChecked(true);
    else if(Preference==3) ui->RbInfoMessPrefer->setChecked(true);
    else if(Preference==4) ui->RbTestCostPrefer->setChecked(true);
}

void DialogSetTestPreference::on_BtnOK_clicked()
{
    if(ui->RbOnlyInfoMess->isChecked()) TestPointPreference=1;
    else if(ui->RbOnlyTestCost->isChecked()) TestPointPreference=2;
    else if(ui->RbInfoMessPrefer->isChecked()) TestPointPreference=3;
    else if(ui->RbTestCostPrefer->isChecked()) TestPointPreference=4;
    Canceled=false;
    this->close();
}

void DialogSetTestPreference::on_BtnCanceled_clicked()
{
    Canceled=true;
    this->close();
}
