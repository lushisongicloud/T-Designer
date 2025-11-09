#include "variablemanage.h"
#include "ui_variablemanage.h"
#include "dialogvariabledefine.h"
#include <QMessageBox>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

VariableManage::VariableManage(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),
    ui(new Ui::VariableManage),m_Database(TMATE_Database)
{
    ui->setupUi(this);


    //设置遮罩窗口
    mpShadeWindow = new QWidget(this);
    QString str("QWidget{background-color:rgba(0,0,0,0.6);}");
    mpShadeWindow->setStyleSheet(str);
    mpShadeWindow->setGeometry(0, 0, 1, 1);
    mpShadeWindow->hide();

    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("变量名称") << tr("信号类型") << tr("变量类型") << tr("变量单位") << tr("采集位置") << tr("备注信息") <<tr("规则库分析");

    StretchHorizontalIndex<<1<<2<<3<<4<<5<<6;
    TableWidgetQss(headerString,ui->tableWidget_VariableBase,StretchHorizontalIndex);
    ui->tableWidget_VariableBase->setColumnWidth(0,330);
    //ui->tableWidget_VariableBase->setColumnWidth(1,150);
    //ui->tableWidget_VariableBase->setColumnWidth(2,150);
    //ui->tableWidget_VariableBase->setColumnWidth(3,150);
    //ui->tableWidget_VariableBase->setColumnWidth(4,500);
    //ui->tableWidget_VariableBase->setColumnWidth(5,630);
    ui->lineEdit_VariableName->clear();
    ui->Cmb_VariableType->setCurrentIndex(0);
    update();
}

VariableManage::~VariableManage()
{
    delete ui;
}


void VariableManage::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
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


void VariableManage::update()
{
    m_Signal.clear();
    m_Signal = m_Database->SelectSignalsInforFromSignalBaseTable(ui->lineEdit_VariableName->text(),ui->Cmb_VariableType->currentText());

    ui->tableWidget_VariableBase->blockSignals(true);

    //设置表格的默认的行数
    ui->tableWidget_VariableBase->setRowCount(m_Signal.size());//设置默认的行数
    ui->tableWidget_VariableBase->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_Signal.size();i++){

        ui->tableWidget_VariableBase->setItem(i,0,new QTableWidgetItem(m_Signal[i].Name));
        ui->tableWidget_VariableBase->setItem(i,1,new QTableWidgetItem(m_Signal[i].SignalType));
        ui->tableWidget_VariableBase->setItem(i,2,new QTableWidgetItem(m_Signal[i].DataType));
        ui->tableWidget_VariableBase->setItem(i,3,new QTableWidgetItem(m_Signal[i].Unit));
        ui->tableWidget_VariableBase->setItem(i,4,new QTableWidgetItem(m_Signal[i].SignalPos));
        ui->tableWidget_VariableBase->setItem(i,5,new QTableWidgetItem(m_Signal[i].Note));
        ui->tableWidget_VariableBase->setItem(i,6,new QTableWidgetItem(m_Signal[i].Detail));

        ui->tableWidget_VariableBase->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_VariableBase->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_VariableBase->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_VariableBase->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_VariableBase->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_VariableBase->item(i,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_VariableBase->item(i,6)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    ui->tableWidget_VariableBase->blockSignals(false);
    ui->tableWidget_VariableBase->resizeRowsToContents();
}

void VariableManage::SetChangeEnabled(bool enable)
{
    ui->Btn_VariableBaseNew->setEnabled(enable);
    ui->Btn_VariableBaseAlter->setEnabled(enable);
    ui->Btn_VariableBaseDelete->setEnabled(enable);
}


void VariableManage::on_Btn_VariableBaseSelect_clicked()
{//变量检索
    update();
}

void VariableManage::on_Btn_VariableBaseNew_clicked()
{//新增变量
    DataBase::Str_Signal signal;
    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();//遮罩效果

    //模态对话框，动态创建，用过后删除
    DialogVariableDefine    *add_new_Variable_view=new DialogVariableDefine(nullptr,m_Database,signal,true); //创建对话框
    Qt::WindowFlags    flags=add_new_Variable_view->windowFlags();
    add_new_Variable_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    int ret=add_new_Variable_view->exec();// 以模态方式显示对话框

    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        m_Database->InsertSignalToSignalBaseTable(add_new_Variable_view->GetDefinedSignal());
        QString dlgTitle="新增变量";
        QString strInfo=QString::asprintf("新增变量成功！");
        QMessageBox::information(nullptr, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);
    }
    delete add_new_Variable_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    update();
}

void VariableManage::on_Btn_VariableBaseAlter_clicked()
{//修改变量
    int curRow = ui->tableWidget_VariableBase->currentRow();

    if(curRow==-1){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择账户"),QMessageBox::Yes);
        return;}

    QString Name = ui->tableWidget_VariableBase->item(curRow,0)->text();//获取变量当前名称

    DataBase::Str_Signal  selectedSignal = m_Database->SelectSignalFromSignalBaseTable(Name);
    if(selectedSignal.SignalType=="基础信号"){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("无法修改基础信号"),QMessageBox::Yes);
        return;
    }

    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();//遮罩效果

    //模态对话框，动态创建，用过后删除
    DialogVariableDefine    *add_new_Variable_view=new DialogVariableDefine(nullptr,m_Database,selectedSignal,false); //创建对话框
    Qt::WindowFlags    flags=add_new_Variable_view->windowFlags();
    add_new_Variable_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    int ret=add_new_Variable_view->exec();// 以模态方式显示对话框

    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        m_Database->UpdateSignalToSignalBaseTable(selectedSignal,add_new_Variable_view->GetDefinedSignal());
        QString dlgTitle="修改变量";
        QString strInfo=QString::asprintf("修改变量成功！");
        QMessageBox::information(nullptr, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);

        QString OraginVariableName = Name;
        QString ChangeVariableName = add_new_Variable_view->GetDefinedSignal().Name;
        if(OraginVariableName!=ChangeVariableName){
            emit VariableNameChange(OraginVariableName,ChangeVariableName);
        }
    }
    delete add_new_Variable_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    update();
}

void VariableManage::on_Btn_VariableBaseDelete_clicked()
{//删除变量
    int curRow = ui->tableWidget_VariableBase->currentRow();

    if(curRow==-1){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择要删除的变量"),QMessageBox::Yes);
        return;}

    QString Name = ui->tableWidget_VariableBase->item(curRow,0)->text();//获取变量当前名称

    DataBase::Str_Signal  selectedSignal = m_Database->SelectSignalFromSignalBaseTable(Name);
    if(selectedSignal.SignalType=="基础信号"){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("无法删除基础信号"),QMessageBox::Yes);
        return;
    }

    //确认是否删除
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("是否确认删除该信号?"),
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes)
    {
        if(m_Database->DeleteSignalFromSignalBaseTable(Name)){
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("信号已删除"));
            emit VariableDelete(Name);
        }
        else
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("删除失败"));
        update();
    }
}
