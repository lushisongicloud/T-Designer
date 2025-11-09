#include "drawgridset.h"
#include "ui_drawgridset.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

DrawGridSet::DrawGridSet(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DrawGridSet)
{
    ui->setupUi(this);
    this->setWindowTitle("曲线参数设置");
    m_LbParaName[0]=ui->Lb_Para1;
    m_LbParaName[1]=ui->Lb_Para2;
    m_LbParaName[2]=ui->Lb_Para3;
    m_LbParaName[3]=ui->Lb_Para4;
    m_LbParaName[4]=ui->Lb_Para5;
    m_LbParaName[5]=ui->Lb_Para6;
    m_LbParaName[6]=ui->Lb_Para7;
    m_LbParaName[7]=ui->Lb_Para8;

    m_CbShow[0]=ui->CbShow1;
    m_CbShow[1]=ui->CbShow2;
    m_CbShow[2]=ui->CbShow3;
    m_CbShow[3]=ui->CbShow4;
    m_CbShow[4]=ui->CbShow5;
    m_CbShow[5]=ui->CbShow6;
    m_CbShow[6]=ui->CbShow7;
    m_CbShow[7]=ui->CbShow8;

    m_SpinSF[0]=ui->doubleSpinSF1;
    m_SpinSF[1]=ui->doubleSpinSF2;
    m_SpinSF[2]=ui->doubleSpinSF3;
    m_SpinSF[3]=ui->doubleSpinSF4;
    m_SpinSF[4]=ui->doubleSpinSF5;
    m_SpinSF[5]=ui->doubleSpinSF6;
    m_SpinSF[6]=ui->doubleSpinSF7;
    m_SpinSF[7]=ui->doubleSpinSF8;

    m_SpinPY[0]=ui->doubleSpinPY1;
    m_SpinPY[1]=ui->doubleSpinPY2;
    m_SpinPY[2]=ui->doubleSpinPY3;
    m_SpinPY[3]=ui->doubleSpinPY4;
    m_SpinPY[4]=ui->doubleSpinPY5;
    m_SpinPY[5]=ui->doubleSpinPY6;
    m_SpinPY[6]=ui->doubleSpinPY7;
    m_SpinPY[7]=ui->doubleSpinPY8;
}

DrawGridSet::~DrawGridSet()
{
    delete ui;
}

void DrawGridSet::on_btnDel1_1_clicked()
{
   m_LbParaName[0]->setText("未知");
   m_CbShow[0]->setEnabled(false);
   m_SpinSF[0]->setEnabled(false);
   m_SpinPY[0]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_2_clicked()
{
    m_LbParaName[1]->setText("未知");
    m_CbShow[1]->setEnabled(false);
    m_SpinSF[1]->setEnabled(false);
    m_SpinPY[1]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_3_clicked()
{
    m_LbParaName[2]->setText("未知");
    m_CbShow[2]->setEnabled(false);
    m_SpinSF[2]->setEnabled(false);
    m_SpinPY[2]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_4_clicked()
{
    m_LbParaName[3]->setText("未知");
    m_CbShow[3]->setEnabled(false);
    m_SpinSF[3]->setEnabled(false);
    m_SpinPY[3]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_5_clicked()
{
    m_LbParaName[4]->setText("未知");
    m_CbShow[4]->setEnabled(false);
    m_SpinSF[4]->setEnabled(false);
    m_SpinPY[4]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_6_clicked()
{
    m_LbParaName[5]->setText("未知");
    m_CbShow[5]->setEnabled(false);
    m_SpinSF[5]->setEnabled(false);
    m_SpinPY[5]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_7_clicked()
{
    m_LbParaName[6]->setText("未知");
    m_CbShow[6]->setEnabled(false);
    m_SpinSF[6]->setEnabled(false);
    m_SpinPY[6]->setEnabled(false);
}

void DrawGridSet::on_btnDel1_8_clicked()
{
    m_LbParaName[7]->setText("未知");
    m_CbShow[7]->setEnabled(false);
    m_SpinSF[7]->setEnabled(false);
    m_SpinPY[7]->setEnabled(false);
}
