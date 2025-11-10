#include "dialogtag.h"
#include "ui_dialogtag.h"
QList<QColor> ListTagColor{QColor(237, 28, 36),QColor(255, 127, 39),QColor(255, 242, 0),QColor(34, 177, 76),QColor(0, 255, 255),QColor(0, 0, 255),QColor(163, 73, 164)};
dialogTag::dialogTag(QWidget *parent) :
    QWidget(parent),
    ui(new Ui::dialogTag)
{
    ui->setupUi(this);
}

dialogTag::~dialogTag()
{
    delete ui;
}

void dialogTag::ResetBtn()
{   return;
    ui->BtnRed->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/红色.png);}QToolButton:hover{image: url(:/new/prefix1/image/红色选中.png);}");
    ui->BtnOriange->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/橙色.png);}QToolButton:hover{image: url(:/new/prefix1/image/橙色选中.png);}");
    ui->BtnYellow->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/黄色.png);}QToolButton:hover{image: url(:/new/prefix1/image/黄色选中.png);}");
    ui->BtnGreen->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/绿色.png);}QToolButton:hover{image: url(:/new/prefix1/image/绿色选中.png);}");
    ui->BtnBlue->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/蓝色.png);}QToolButton:hover{image: url(:/new/prefix1/image/蓝色选中.png);}");
    ui->BtnDarkBlue->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/深蓝.png);}QToolButton:hover{image: url(:/new/prefix1/image/深蓝选中.png);}");
    ui->BtnPurple->setStyleSheet("QToolButton{image: url(:/new/prefix1/image/紫色.png);}QToolButton:hover{image: url(:/new/prefix1/image/紫色选中.png);}");
}

void dialogTag::on_BtnRed_clicked()
{
    ResetBtn();
    //ui->BtnRed->setStyleSheet("image: url(:/new/prefix1/image/红色选中.png);");
    CurTagColor=TagColor::red;
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));

}

void dialogTag::on_BtnOriange_clicked()
{
    ResetBtn();
    //ui->BtnOriange->setStyleSheet("image: url(:/new/prefix1/image/橙色选中.png);");
    CurTagColor=TagColor::orange;;//QColor(255, 127, 39);//TagColor::red;
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnYellow_clicked()
{
    ResetBtn();
    //ui->BtnYellow->setStyleSheet("image: url(:/new/prefix1/image/黄色选中.png);");
    CurTagColor=TagColor::yellow;//QColor(255, 242, 0);
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnGreen_clicked()
{
    ResetBtn();
    //ui->BtnGreen->setStyleSheet("image: url(:/new/prefix1/image/绿色选中.png);");
    CurTagColor=TagColor::green;//QColor(34, 177, 76);
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnBlue_clicked()
{
    ResetBtn();
    //ui->BtnBlue->setStyleSheet("image: url(:/new/prefix1/image/蓝色选中.png);");
    CurTagColor=TagColor::blue;//QColor(34, 177, 76);
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnDarkBlue_clicked()
{
    ResetBtn();
    //ui->BtnDarkBlue->setStyleSheet("image: url(:/new/prefix1/image/深蓝选中.png);");
    CurTagColor=TagColor::darkblue;//QColor(0, 162, 232);
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnPurple_clicked()
{
    ResetBtn();
    //ui->BtnPurple->setStyleSheet("image: url(:/new/prefix1/image/紫色选中.png);");
    CurTagColor=TagColor::purple;//QColor(163, 73, 164);
    emit(ChangeColor(ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnRec_clicked()
{
    emit(DrawTag(5,ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnCircle_clicked()
{
    emit(DrawTag(1,ListTagColor[int(CurTagColor)]));
}

void dialogTag::on_BtnPolygon_clicked()
{
    emit(DrawTag(7,ListTagColor[int(CurTagColor)]));
}
