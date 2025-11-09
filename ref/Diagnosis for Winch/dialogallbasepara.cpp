#include "dialogallbasepara.h"
#include "ui_dialogallbasepara.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

DialogAllBasePara::DialogAllBasePara(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QDialog(parent),ui(new Ui::DialogAllBasePara),m_Database(TMATE_Database)
{
    ui->setupUi(this);
    Canceled=true;
    InitTabWidget_Variable();
}

DialogAllBasePara::~DialogAllBasePara()
{
    delete ui;
}
void DialogAllBasePara::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
{

    QString tableWidgetStyleSheet = "QTableWidget{border:0px;"
                                    "background-color: rgba(255, 255, 255, 0.2);"
                                    "alternate-background-color: rgba(243, 248, 251, 0.2);"
                                    "color: rgb(0, 0, 0);font: 10pt '微软雅黑';}"
                                    "QTableWidget::item:selected{"
                                    "color: rgb(0, 0, 0);"
                                    "background-color: rgba(191, 223, 252, 0.2);}"
                                    "QHeaderView::section{"
                                    "border:1px solid rgba(19, 67, 79, 1);"
                                    "background-color: rgba(19, 67, 79, 1);"
                                    "height: 35px;font: 75 14pt '微软雅黑';color: rgba(102, 249, 247, 1);"
                                    "padding-left: 4px;"
                                    "text-align:center;}"
                                    "QTableWidget::indicator {width: 50px;height: 50px;}"
                                    "QTableWidget::indicator:unchecked {image: url(:/widget/No.png);}"
                                    "QTableWidget::indicator:checked {image: url(:/widget/Yes.png);}"
                                    "QTableWidget::item{padding-top:15px;padding-bottom:15px;}";

    //TableWidget->horizontalHeader()->setVisible(false);//隐藏表头
    TableWidget->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    TableWidget->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选
    TableWidget->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色
    //设置表格的默认的列数
    TableWidget->setColumnCount(headerString.count());//设置列数
    TableWidget->setHorizontalHeaderLabels(headerString);//设置列标题

    for(int i=0;i<StretchHorizontalIndex.size();i++)
        TableWidget->horizontalHeader()->setSectionResizeMode(StretchHorizontalIndex[i], QHeaderView::Stretch);

    TableWidget->setAlternatingRowColors(true);//使表格颜色交错功能为真
    TableWidget->setFocusPolicy(Qt::NoFocus);
    TableWidget->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    TableWidget->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑
}
void DialogAllBasePara::InitTabWidget_Variable()
{

    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString <<tr("")  <<tr("变量名称") << tr("变量类型") << tr("变量单位") << tr("备注信息");
    StretchHorizontalIndex<<1<<4;

    //设置QSS
    TableWidgetQss(headerString,ui->tableWidget_BasicVariable,StretchHorizontalIndex);
    ui->tableWidget_BasicVariable->setColumnWidth(0,50);
    //设置基础变量显示
    m_BasicSignal.clear();
    m_BasicSignal = m_Database->SelectSignalsInforFromSignalBaseTable("","基础信号");

    ui->tableWidget_BasicVariable->blockSignals(true);
    //设置表格的默认的行数
    ui->tableWidget_BasicVariable->setRowCount(m_BasicSignal.size());//设置默认的行数
    ui->tableWidget_BasicVariable->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_BasicSignal.size();i++){
        QCheckBox *mCheckBox = new QCheckBox(ui->tableWidget_BasicVariable);
        connect(mCheckBox,SIGNAL(clicked(bool)),this,SLOT(CheckCompareList(bool)));
        ui->tableWidget_BasicVariable->setCellWidget(i,0,mCheckBox);
        ui->tableWidget_BasicVariable->setItem(i,1,new QTableWidgetItem(m_BasicSignal[i].Name));
        ui->tableWidget_BasicVariable->setItem(i,2,new QTableWidgetItem(m_BasicSignal[i].DataType));
        ui->tableWidget_BasicVariable->setItem(i,3,new QTableWidgetItem(m_BasicSignal[i].Unit));
        ui->tableWidget_BasicVariable->setItem(i,4,new QTableWidgetItem(m_BasicSignal[i].Note));

        ui->tableWidget_BasicVariable->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_BasicVariable->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_BasicVariable->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_BasicVariable->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    LoadParaList();
    ui->tableWidget_BasicVariable->blockSignals(false);  
}

void DialogAllBasePara::CheckCompareList(bool Checked)
{
   for(int i=0;i<ui->tableWidget_BasicVariable->rowCount();i++)
   {
       if(((QCheckBox *)ui->tableWidget_BasicVariable->cellWidget(i,0))->isChecked())
       {
           for(int j=0;j<ListComparePara.count();j++)
           {
               if(ListComparePara.at(j)==ui->tableWidget_BasicVariable->item(i,1)->text())
               {
                   ((QCheckBox *)ui->tableWidget_BasicVariable->cellWidget(i,0))->setChecked(false);
                   break;
               }
           }
       }
   }
}

void DialogAllBasePara::LoadParaList()
{
    for(int i=0;i<ListPara.count();i++)
    {
        for(int j=0;j<ui->tableWidget_BasicVariable->rowCount();j++)
        {
            if(ListPara.at(i)==ui->tableWidget_BasicVariable->item(j,1)->text())
            {
                ((QCheckBox *)ui->tableWidget_BasicVariable->cellWidget(j,0))->setChecked(true);
                break;
            }
        }
    }
}

void DialogAllBasePara::on_BtnSetUnchecked_clicked()
{
    for(int i=0;i<ui->tableWidget_BasicVariable->rowCount();i++)
    {
        ((QCheckBox *)ui->tableWidget_BasicVariable->cellWidget(i,0))->setChecked(false);
    }
}

void DialogAllBasePara::on_BtnOK_clicked()
{
    Canceled=false;
    ListPara.clear();
    for(int i=0;i<ui->tableWidget_BasicVariable->rowCount();i++)
    {
        if(((QCheckBox *)ui->tableWidget_BasicVariable->cellWidget(i,0))->isChecked())
            ListPara.append(ui->tableWidget_BasicVariable->item(i,1)->text());
    }
    this->close();
}

void DialogAllBasePara::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}
