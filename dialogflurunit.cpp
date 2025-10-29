#include "dialogflurunit.h"
#include "ui_dialogflurunit.h"

DialogFlurUnit::DialogFlurUnit(QWidget *parent,QList<QString> *list_unit) :
    QDialog(parent),
    ui(new Ui::DialogFlurUnit)
{
    ui->setupUi(this);
    m_list_unit = *list_unit;


    ui->Test_tableWidget->setStyleSheet("selection-background-color: rgb(85, 170, 255)");
    ui->Test_tableWidget->setFocusPolicy(Qt::NoFocus);
    setText(m_list_unit);
    RetCode=-1;
}

void DialogFlurUnit::InitTable(int Mode)
{
    m_Mode=Mode;
    QStringList ListHeader;

    ListHeader<<"故障器件名称";
    ui->Test_tableWidget->setColumnCount(ListHeader.count());//设置列数
    ui->Test_tableWidget->setHorizontalHeaderLabels(ListHeader);//设置列标题
    ui->Test_tableWidget->setColumnWidth(0,330);//故障器件名称
}

int GetRank(QString CurText)
{
    QString StrRank=CurText.mid(CurText.indexOf("Rank=")+5,CurText.indexOf(")")-CurText.indexOf("Rank=")-5);
    if(StrIsNumber(StrRank)) return StrRank.toInt();
    return -1;
}

//将rank最小的打钩
void DialogFlurUnit::setText(QList<QString> list_test)
{
    int Rank;
    ui->Test_tableWidget->setRowCount(0);
    for(int i=0;i<list_test.count();i++)
    {
        ui->Test_tableWidget->setRowCount(ui->Test_tableWidget->rowCount()+1);
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,0,new QTableWidgetItem(list_test.at(i)));
        if(i==0)
        {
            ui->Test_tableWidget->item(i,0)->setCheckState(Qt::Checked);
            Rank=GetRank(ui->Test_tableWidget->item(i,0)->text());
        }
        else
        {
            if(GetRank(ui->Test_tableWidget->item(i,0)->text())!=Rank)
              ui->Test_tableWidget->item(i,0)->setCheckState(Qt::Unchecked);
            else
              ui->Test_tableWidget->item(i,0)->setCheckState(Qt::Checked);
        }
    }
}

DialogFlurUnit::~DialogFlurUnit()
{
    delete ui;
}

void DialogFlurUnit::on_BtnClose_clicked()
{
    RetCode=0;
    this->close();
}

void DialogFlurUnit::on_Test_tableWidget_clicked(const QModelIndex &index)
{
    if(ui->Test_tableWidget->currentRow()<0) return;
    unit_name = ui->Test_tableWidget->item(ui->Test_tableWidget->currentRow(),0)->text();
}

void DialogFlurUnit::on_BtnDiagnoseOver_clicked()
{
    RetCode=1;
    for(int i=0;i<ui->Test_tableWidget->rowCount();i++)
    {
        if(ui->Test_tableWidget->item(i,0)->checkState()==Qt::Checked)
            RetDiagnoseList.append(ui->Test_tableWidget->item(i,0)->text());
    }
    this->close();
}

void DialogFlurUnit::on_CbAllSelect_clicked()
{
    if(ui->CbAllSelect->isChecked())
    {
        for(int i=0;i<ui->Test_tableWidget->rowCount();i++)
        {
            ui->Test_tableWidget->item(i,0)->setCheckState(Qt::Checked);
        }
    }
    else
    {
        for(int i=0;i<ui->Test_tableWidget->rowCount();i++)
        {
            ui->Test_tableWidget->item(i,0)->setCheckState(Qt::Unchecked);
        }
    }
}
