#include "dialogmultiline.h"
#include "ui_dialogmultiline.h"

DialogMultiLine::DialogMultiLine(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogMultiLine)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogMultiLine::~DialogMultiLine()
{
    delete ui;
}

void DialogMultiLine::on_BtnDraw_clicked()
{
    Canceled=false;
    LineCount=ui->spinBox_Num->value();
    LineGap=ui->spinBox_Distance->value();
    if(ui->RbHorizontalLine->isChecked()) Mode=1;//先横
    else if(ui->RbVerticalLine->isChecked()) Mode=2;//先竖
    else Mode=3;//元件端点
    close();
}
