#include "formwarninformation.h"
#include "ui_formwarninformation.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif
extern QStringList ListWarnningInfo;
extern QString ProcessingText(const QFontMetrics& font, const QString& text, int nLabelSize);
FormWarnInformation::FormWarnInformation(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),
    ui(new Ui::FormWarnInformation),m_Database(TMATE_Database)
{
    ui->setupUi(this);
    //ui->groupboxLogging->setTitle(m_name);
    //ClearLoggingUI();
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("序号") <<tr("时间") << tr("工况") << tr("工况标志参数") << tr("预警参数") <<tr("ID");

    StretchHorizontalIndex<<1<<2<<3<<4;
    TableWidgetQss(headerString,ui->tableWidgetWarn,StretchHorizontalIndex);
    ui->tableWidgetWarn->setColumnHidden(5,true);
    ui->tableWidgetWarn->setColumnWidth(0,80);

    timerUpdateUI = new QTimer(this);
    connect(timerUpdateUI,SIGNAL(timeout()),this,SLOT(DoUpdateUI()));
    timerUpdateUI->start(500);

    ui->CbPageWarnRecordsNumber->setCurrentText("12");
    ui->WarndateEditEnd->setDate(QDate::currentDate());
    ui->widgetSearch->setEnabled(false);
}

FormWarnInformation::~FormWarnInformation()
{
    delete ui;
}
void FormWarnInformation::UpdateHisWarnRecord()
{
    if(ui->radioButton_realtimeWarn->isChecked()) return;
    //历史报警列表
    QVector<DataBase::WarnRecord> His_WarnRecord;
    //if(ui->radioButton_realtimeAlarm->isChecked()) realtime_signal  = m_RuleVariablePool.FindRealtimeAlarmOrFaliure();
    int MinRecordIdx,MaxRecordIdx;
    MinRecordIdx=(CurWarnPageNum-1)*ui->CbPageWarnRecordsNumber->currentText().toInt();
    MaxRecordIdx=CurWarnPageNum*ui->CbPageWarnRecordsNumber->currentText().toInt();
    ui->tableWidgetWarn->setRowCount(0);
    int TotalRecords;
    His_WarnRecord = m_Database->SelectHisWarnSignalFromDataBase(ui->WarndateEditStart->date(),ui->WarndateEditEnd->date(),ui->EdWarnSearchRecord->text(),MinRecordIdx,MaxRecordIdx,TotalRecords);
qDebug()<<"TotalRecords="<<TotalRecords;
    ui->label_DMS_TableControl_TotalWarnNum->setText(QString::number(TotalRecords));
    if((TotalRecords%ui->CbPageWarnRecordsNumber->currentText().toInt())==0)
        ui->LbTotalWarnPageNum->setText(QString::number(TotalRecords/ui->CbPageWarnRecordsNumber->currentText().toInt()));
    else
        ui->LbTotalWarnPageNum->setText(QString::number(TotalRecords/ui->CbPageWarnRecordsNumber->currentText().toInt()+1));
    for(int i=0;i<His_WarnRecord.size();i++)
    {
        ui->tableWidgetWarn->setRowCount(ui->tableWidgetWarn->rowCount()+1);//设置默认的行数

        //数据显示
        int RowIndex=ui->tableWidgetWarn->rowCount()-1;
        ui->tableWidgetWarn->setItem(RowIndex,0,new QTableWidgetItem(QString::number(i+MinRecordIdx+1)));
        ui->tableWidgetWarn->setItem(RowIndex,1,new QTableWidgetItem(His_WarnRecord.at(i).RecordStartDateTime.toString("yyyy-MM-dd hh:mm:ss")));
        ui->tableWidgetWarn->setItem(RowIndex,2,new QTableWidgetItem(His_WarnRecord.at(i).WarnTaskName));
        QFontMetrics font(ui->tableWidgetWarn->font());
        QString TaskPara=ProcessingText(font,His_WarnRecord.at(i).TaskPara,400);//ui->tableWidget_KnowledgeBase->columnWidth(2)
        ui->tableWidgetWarn->setItem(RowIndex,3,new QTableWidgetItem(TaskPara));
        QString WarnPara=ProcessingText(font,His_WarnRecord.at(i).WarnPara,400);//ui->tableWidget_KnowledgeBase->columnWidth(2)
        ui->tableWidgetWarn->setItem(RowIndex,4,new QTableWidgetItem(WarnPara));
        ui->tableWidgetWarn->setItem(RowIndex,5,new QTableWidgetItem(QString::number(His_WarnRecord.at(i).RecordID)));//ID
        ui->tableWidgetWarn->item(RowIndex,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidgetWarn->item(RowIndex,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidgetWarn->item(RowIndex,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidgetWarn->item(RowIndex,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidgetWarn->item(RowIndex,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidgetWarn->item(RowIndex,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidgetWarn->resizeRowsToContents();
    }
}
void FormWarnInformation::DoUpdateUI()
{
    if(!ui->radioButton_realtimeWarn->isChecked()) return;
    ui->label_DMS_TableControl_TotalWarnNum->setText(QString::number(ListWarnningInfo.count()));
    ui->LbTotalWarnPageNum->setText("1");
    ui->spinBoxWarnPageNum->setValue(1);
    //工况:参数1=值,参数2=值;参数1=值,参数2=值
    for(int i=0;i<ListWarnningInfo.count();i++)
    {
        QString TaskName=ListWarnningInfo.at(i).split(":").at(0);
        QString TaskPara=ListWarnningInfo.at(i).split(":").at(1).split(";").at(0);
        QString WarnPara=ListWarnningInfo.at(i).split(":").at(1).split(";").at(1);
        bool IsInTable=false;
        for(int j=0;j<ui->tableWidgetWarn->rowCount();j++)
        {
            if(ui->tableWidgetWarn->item(j,2)->text()==TaskName)//更新表格
            {
                QFontMetrics font(ui->tableWidgetWarn->font());
                TaskPara=ProcessingText(font,TaskPara,400);
                ui->tableWidgetWarn->item(j,3)->setText(TaskPara);
                WarnPara=ProcessingText(font,WarnPara,400);
                ui->tableWidgetWarn->item(j,4)->setText(WarnPara);
                IsInTable=true;
                break;
            }
        }
        if(!IsInTable)
        {
            ui->tableWidgetWarn->setRowCount(ui->tableWidgetWarn->rowCount()+1);
            ui->tableWidgetWarn->setItem(ui->tableWidgetWarn->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidgetWarn->rowCount())));
            ui->tableWidgetWarn->setItem(ui->tableWidgetWarn->rowCount()-1,1,new QTableWidgetItem(QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss")));
            ui->tableWidgetWarn->setItem(ui->tableWidgetWarn->rowCount()-1,2,new QTableWidgetItem(TaskName));
            QFontMetrics font(ui->tableWidgetWarn->font());
            TaskPara=ProcessingText(font,TaskPara,400);
            ui->tableWidgetWarn->setItem(ui->tableWidgetWarn->rowCount()-1,3,new QTableWidgetItem(TaskPara));
            WarnPara=ProcessingText(font,WarnPara,400);
            ui->tableWidgetWarn->setItem(ui->tableWidgetWarn->rowCount()-1,4,new QTableWidgetItem(WarnPara));
        }
    }
    for(int i=0;i<ui->tableWidgetWarn->rowCount();i++)
    {
        bool IsWarn=false;
        for(int j=0;j<ListWarnningInfo.count();j++)
        {
            QString TaskName=ListWarnningInfo.at(j).split(":").at(0);
            if(ui->tableWidgetWarn->item(i,2)->text()==TaskName)
            {
                IsWarn=true;
                break;
            }
        }
        if(!IsWarn) ui->tableWidgetWarn->removeRow(i);
    }
    ui->tableWidgetWarn->resizeRowsToContents();
}

void FormWarnInformation::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
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
    TableWidget->setWordWrap(true);
}

//Mode=0:删除选中的记录  Mode=1：删除当前页面记录
void FormWarnInformation::DeleteRecord(int Mode)
{
   if(Mode==0)
   {
       for(int i=0;i<ui->tableWidgetWarn->selectedItems().count();i++)
       {
           m_Database->DeleteWarnHisRecord(0,ui->tableWidgetWarn->item(ui->tableWidgetWarn->selectedItems().at(i)->row(),5)->text().toInt(),QDate::currentDate(),QDate::currentDate(),"");
       }
   }
   else if(Mode==1)
   {
       for(int i=0;i<ui->tableWidgetWarn->rowCount();i++)
       {
           m_Database->DeleteWarnHisRecord(0,ui->tableWidgetWarn->item(i,5)->text().toInt(),QDate::currentDate(),QDate::currentDate(),"");
       }
   }
}




void FormWarnInformation::on_BtnWarnTable_FirstPage_clicked()
{
    CurWarnPageNum=1;
    ui->spinBoxWarnPageNum->setValue(CurWarnPageNum);
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_BtnWarnTable_PreviousPage_clicked()
{
    if(CurWarnPageNum==1) return;
    CurWarnPageNum--;
    ui->spinBoxWarnPageNum->setValue(CurWarnPageNum);
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_BtnNextWarnPage_clicked()
{
    if(CurWarnPageNum*ui->CbPageWarnRecordsNumber->currentText().toInt()>=ui->label_DMS_TableControl_TotalWarnNum->text().toInt()) return;
    CurWarnPageNum++;
    ui->spinBoxWarnPageNum->setValue(CurWarnPageNum);
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_BtnLastWarnPage_clicked()
{
    CurWarnPageNum=ui->label_DMS_TableControl_TotalWarnNum->text().toInt()/ui->CbPageWarnRecordsNumber->currentText().toInt();
    if(CurWarnPageNum*ui->CbPageWarnRecordsNumber->currentText().toInt()!=ui->label_DMS_TableControl_TotalWarnNum->text().toInt()) CurWarnPageNum++;
    ui->spinBoxWarnPageNum->setValue(CurWarnPageNum);
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_spinBoxWarnPageNum_valueChanged(int arg1)
{
    CurWarnPageNum=ui->spinBoxWarnPageNum->value();
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_BtnWarnSearch_clicked()
{
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_radioButton_HisWarn_clicked()
{
    ui->widgetSearch->setEnabled(true);
    UpdateHisWarnRecord();
}

void FormWarnInformation::on_radioButton_realtimeWarn_clicked()
{
    ui->widgetSearch->setEnabled(false);
    ui->tableWidgetWarn->setRowCount(0);
}

void FormWarnInformation::on_BtnClearCurAllWarnRecords_clicked()
{
    if(!ui->radioButton_HisWarn->isChecked()) return;
    QString dlgTitle="Question消息框";
    QString strInfo="是否删除所有筛选记录?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        m_Database->DeleteWarnHisRecord(1,0,ui->WarndateEditStart->date(),ui->WarndateEditEnd->date(),ui->EdWarnSearchRecord->text());
        UpdateHisWarnRecord();
    }
}

void FormWarnInformation::on_BtnClearCurSelectWarnRecords_clicked()
{
    if(!ui->radioButton_HisWarn->isChecked()) return;
    QString dlgTitle="Question消息框";
    QString strInfo="是否删除选中记录?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        DeleteRecord(0);
        UpdateHisWarnRecord();
    }
}

void FormWarnInformation::on_BtnClearCurWarnPageRecords_clicked()
{
    if(!ui->radioButton_HisWarn->isChecked()) return;
    QString dlgTitle="Question消息框";
    QString strInfo="是否删除当前页记录?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        DeleteRecord(1);
        UpdateHisWarnRecord();
    }
}

void FormWarnInformation::on_CbPageWarnRecordsNumber_currentIndexChanged(int index)
{
    if(!ui->radioButton_HisWarn->isChecked()) return;
    UpdateHisWarnRecord();
}
