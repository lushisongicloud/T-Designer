#include "dialog_select_another_test.h"
#include "ui_dialog_select_another_test.h"

Dialog_select_another_test::Dialog_select_another_test(QWidget *parent,QList<TestPoint> *list_test) :
    QDialog(parent),
    ui(new Ui::Dialog_select_another_test)
{
    ui->setupUi(this);
    m_list_test = *list_test;

    ui->Test_tableWidget->setColumnWidth(0,230);//测试点名称
    ui->Test_tableWidget->setColumnWidth(1,100);//信息熵
    ui->Test_tableWidget->setColumnWidth(2,90);//测试代价
    ui->Test_tableWidget->setStyleSheet("selection-background-color: rgb(85, 170, 255)");
    ui->Test_tableWidget->setFocusPolicy(Qt::NoFocus);
    setText();
}

Dialog_select_another_test::~Dialog_select_another_test()
{
    delete ui;
}

QString Dialog_select_another_test::get_test_name()
{
    return test_name;
}

void Dialog_select_another_test::SetTestPreference(int TestPreference)
{
    ui->CbTestPreference->setCurrentIndex(TestPreference-1);
}

void Dialog_select_another_test::setText()
{
    ui->Test_tableWidget->setRowCount(0);
    for(int i=0;i<m_list_test.count();i++)
    {
        ui->Test_tableWidget->setRowCount(ui->Test_tableWidget->rowCount()+1);
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,0,new QTableWidgetItem(m_list_test.at(i).point_name));
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,1,new QTableWidgetItem(QString::number(m_list_test.at(i).calculate)));
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,2,new QTableWidgetItem(QString::number(m_list_test.at(i).test_cost)));
    }
}

void Dialog_select_another_test::on_btn_tool_serch_clicked()
{
    QString SelectTarget = ui->lineEdit_tool_serch->text();

    ui->Test_tableWidget->setRowCount(0);
    for(int i=0;i<m_list_test.count();i++)
    {
        if(!m_list_test.at(i).point_name.contains(SelectTarget)) continue;
        ui->Test_tableWidget->setRowCount(ui->Test_tableWidget->rowCount()+1);
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,0,new QTableWidgetItem(m_list_test.at(i).point_name));
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,1,new QTableWidgetItem(QString::number(m_list_test.at(i).calculate)));
        ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,2,new QTableWidgetItem(QString::number(m_list_test.at(i).test_cost)));
    }
}


void Dialog_select_another_test::on_Test_tableWidget_clicked(const QModelIndex &index)
{
    if(ui->Test_tableWidget->currentRow()<0) return;
    test_name = ui->Test_tableWidget->item(ui->Test_tableWidget->currentRow(),0)->text();
}

void Dialog_select_another_test::on_CbTestPreference_currentIndexChanged(int index)
{
    SortTestPoint(m_list_test,ui->CbTestPreference->currentIndex()+1);
    setText();
}
