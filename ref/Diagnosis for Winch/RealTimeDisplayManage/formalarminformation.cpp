#include "formalarminformation.h"
#include "ui_formalarminformation.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

FormAlarmInformation::FormAlarmInformation(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),
    ui(new Ui::FormAlarmInformation),m_Database(TMATE_Database)
{
    ui->setupUi(this);
    ui->groupboxLogging->setTitle(m_name);
    ClearLoggingUI();
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("序号") <<tr("时间") <<tr("报警/故障") << tr("名称") << tr("报警位置") << tr("报警内容") << tr("规则库分析")<<tr("案例统计") << tr("实际排查结果")<<tr("ID");

    StretchHorizontalIndex<<1<<4<<5<<6<<7<<8;
    TableWidgetQss(headerString,ui->tableWidget_Alarm,StretchHorizontalIndex);
    ui->tableWidget_Alarm->setColumnHidden(9,true);
    ui->tableWidget_Alarm->setColumnWidth(0,80);
    ui->tableWidget_Alarm->setColumnWidth(3,330);


}

FormAlarmInformation::~FormAlarmInformation()
{
    delete ui;
}

void FormAlarmInformation::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
{

    QString tableWidgetStyleSheet = "QTableWidget{border:0px;"
                                    "background-color: rgba(255, 255, 255, 0.2);"
                                    "alternate-background-color: rgba(243, 248, 251, 0.2);"
                                    "color: rgb(0, 0, 0);font: 14pt '微软雅黑';}"
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

//Mode=0:删除选中的记录  Mode=1：删除当前页面记录
void FormAlarmInformation::DeleteRecord(int Mode,myQSqlDatabase *TMATE_Database)
{
   if(Mode==0)
   {
       for(int i=0;i<ui->tableWidget_Alarm->selectedItems().count();i++)
       {
           TMATE_Database->DeleteHisRecord(0,ui->tableWidget_Alarm->item(ui->tableWidget_Alarm->selectedItems().at(i)->row(),9)->text().toInt(),QDate::currentDate(),QDate::currentDate(),"","");
       }
   }
   else if(Mode==1)
   {
       for(int i=0;i<ui->tableWidget_Alarm->rowCount();i++)
       {
           TMATE_Database->DeleteHisRecord(0,ui->tableWidget_Alarm->item(i,9)->text().toInt(),QDate::currentDate(),QDate::currentDate(),"","");
       }
   }
}
void FormAlarmInformation::ClearLoggingUI()
{//清空记录显示UI
    //ui->textEditLogging->clear();
    ui->tableWidget_Alarm->setRowCount(0);
}

void FormAlarmInformation::updateLoggingUI(QString newLogging)
{//更新信息显示UI
    //获取当前显示区域信息并清空显示框
    //auto cur_text = ui->textEditLogging->toPlainText();
    ui->tableWidget_Alarm->setRowCount(0);
    //将之前显示信息用白色字体显示
    //ui->textEditLogging->setTextColor(Qt::white);
    //ui->textEditLogging->append(cur_text);
    //将新增显示信息用红色字体显示
    //ui->textEditLogging->setTextColor(Qt::red);
    //ui->textEditLogging->append(newLogging);
}

void FormAlarmInformation::AddRecord(DataBase::Signal signal,int StartIdx,bool IsReal)
{
    //设置表格的默认的行数
    ui->tableWidget_Alarm->setRowCount(ui->tableWidget_Alarm->rowCount()+1);//设置默认的行数

    //数据显示
    int RowIndex=ui->tableWidget_Alarm->rowCount()-1;
    ui->tableWidget_Alarm->setItem(RowIndex,0,new QTableWidgetItem(QString::number(StartIdx++)));
    if(IsReal) ui->tableWidget_Alarm->setItem(RowIndex,1,new QTableWidgetItem(QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss")));
    else ui->tableWidget_Alarm->setItem(RowIndex,1,new QTableWidgetItem(signal.RecordStartDateTime.toString("yyyy-MM-dd hh:mm:ss")));
    ui->tableWidget_Alarm->setItem(RowIndex,2,new QTableWidgetItem(signal.signalType=="故障信号"?"故障信号":"报警信号"));
    ui->tableWidget_Alarm->setItem(RowIndex,3,new QTableWidgetItem(signal.Name));//报警名称
    ui->tableWidget_Alarm->setItem(RowIndex,4,new QTableWidgetItem(signal.SignalPos));//报警位置
    ui->tableWidget_Alarm->setItem(RowIndex,5,new QTableWidgetItem(signal.Note));//报警内容
    ui->tableWidget_Alarm->setItem(RowIndex,6,new QTableWidgetItem(signal.Detail));//故障定位
    ui->tableWidget_Alarm->setItem(RowIndex,7,new QTableWidgetItem(m_Database->AnalysisHisMannulSet(signal.Name)));//历史故障定位统计信息
    ui->tableWidget_Alarm->setItem(RowIndex,9,new QTableWidgetItem(QString::number(signal.RecordID)));//ID


    QComboBox *m_ComboBox= new QComboBox;
    m_ComboBox->clear();
    m_ComboBox->addItem("");
    m_ComboBox->addItems(signal.MultiPos);
    m_ComboBox->setMinimumHeight(50);
    //m_ComboBox->setMaximumHeight(50);
    if(IsReal)  m_ComboBox->setCurrentIndex(0);
    else m_ComboBox->setCurrentText(signal.MultiPosMannulSet);
    ui->tableWidget_Alarm->setCellWidget(RowIndex,8,m_ComboBox);//手动定位选择

    // ui->tableWidget_Alarm->setItem(RowIndex,8,new QTableWidgetItem(signal.MultiPosMannulSet));//手动定位结果

    ui->tableWidget_Alarm->item(RowIndex,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,6)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->item(RowIndex,7)->setTextAlignment(Qt::AlignLeft|Qt::AlignVCenter);
    //if(!IsReal) ui->tableWidget_Alarm->item(RowIndex,8)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    ui->tableWidget_Alarm->resizeRowsToContents();
}

bool FormAlarmInformation::UpdateMannulSet()
{
   for(int i=0;i<ui->tableWidget_Alarm->rowCount();i++)
   {
       //qDebug()<<"item(i,9)="<<ui->tableWidget_Alarm->item(i,9)->text()<<" item(i,8)="<<ui->tableWidget_Alarm->item(i,8)->text();
      if(! m_Database->UpdateFailToFailureMannulSet(ui->tableWidget_Alarm->item(i,9)->text().toInt(),((QComboBox *)ui->tableWidget_Alarm->cellWidget(i,8))->currentText()))
          return false;
   }
   return true;
}
