#include "dialogwarningdefine.h"
#include "ui_dialogwarningdefine.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

DialogWarningDefine::DialogWarningDefine(QWidget *parent,myQSqlDatabase *TMATE_Database,DataBase::Str_WarnRule rule,bool isCreatRule) :
    QDialog(parent),ui(new Ui::DialogWarningDefine),m_Database(TMATE_Database),m_WarnRule(rule),m_isCreatRule(isCreatRule)
{
    ui->setupUi(this);
    Canceled=true;
    //ui->modelCmb_State->setEnabled(false);
    InitTabWidget();
    LoadInfo();
}

DialogWarningDefine::~DialogWarningDefine()
{
    delete ui;
}
void DialogWarningDefine::LoadInfo()
{
    ui->tableWidget_TaskFeaturePara->setRowCount(0);
    QStringList ListTaskPara;
    if(m_WarnRule.TaskParaList!="") ListTaskPara=m_WarnRule.TaskParaList.split(",");
    ui->tableWidget_TaskFeaturePara->setRowCount(ListTaskPara.count());
    for(int i=0;i<ListTaskPara.count();i++)
    {
        QStringList ListPara=ListTaskPara.at(i).split("=");
        QString ParaName,ParaStandardValue,ParaThresholdValue;
        if(ListPara.count()==2)
        {
            ParaName=ListPara.at(0);
            ParaStandardValue=ListPara.at(1);
            if(ParaStandardValue.contains("(")&&ParaStandardValue.contains(")"))
            {
                ParaThresholdValue=ParaStandardValue.mid(ParaStandardValue.indexOf("(")+1,ParaStandardValue.indexOf(")")-ParaStandardValue.indexOf("(")-1);
                ParaStandardValue=ParaStandardValue.mid(0,ParaStandardValue.indexOf("("));
            }
        }
        else {ParaName=ListPara.at(0);ParaStandardValue="";}
        DataBase::Str_Signal Signal=m_Database->SelectSignalFromSignalBaseTable(ParaName);
        ui->tableWidget_TaskFeaturePara->setItem(i,0,new QTableWidgetItem(Signal.Name));
        ui->tableWidget_TaskFeaturePara->item(i,0)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskFeaturePara->setItem(i,1,new QTableWidgetItem(Signal.DataType));
        ui->tableWidget_TaskFeaturePara->item(i,1)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskFeaturePara->setItem(i,2,new QTableWidgetItem(Signal.Unit));
        ui->tableWidget_TaskFeaturePara->item(i,2)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskFeaturePara->setItem(i,3,new QTableWidgetItem(Signal.Note));
        ui->tableWidget_TaskFeaturePara->item(i,3)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskFeaturePara->setItem(i,4,new QTableWidgetItem(ParaStandardValue));
        ui->tableWidget_TaskFeaturePara->setItem(i,5,new QTableWidgetItem(ParaThresholdValue));

        ui->tableWidget_TaskFeaturePara->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskFeaturePara->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskFeaturePara->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskFeaturePara->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskFeaturePara->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskFeaturePara->item(i,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }

    ui->tableWidget_TaskAssoPara->setRowCount(0);
    QStringList ListWarnPara;
    if(m_WarnRule.WarnParaList!="") ListWarnPara=m_WarnRule.WarnParaList.split(",");
    ui->tableWidget_TaskAssoPara->setRowCount(ListWarnPara.count());
    for(int i=0;i<ListWarnPara.count();i++)
    {
        QStringList ListPara=ListWarnPara.at(i).split("=");
        QString ParaName,ParaStandardValue,ParaThresholdValue;
        if(ListPara.count()==2)
        {
            ParaName=ListPara.at(0);
            ParaStandardValue=ListPara.at(1);
            if(ParaStandardValue.contains("(")&&ParaStandardValue.contains(")"))
            {
                ParaThresholdValue=ParaStandardValue.mid(ParaStandardValue.indexOf("(")+1,ParaStandardValue.indexOf(")")-ParaStandardValue.indexOf("(")-1);
                ParaStandardValue=ParaStandardValue.mid(0,ParaStandardValue.indexOf("("));
            }
        }
        else {ParaName=ListPara.at(0);ParaStandardValue="";ParaThresholdValue="";}

        DataBase::Str_Signal Signal=m_Database->SelectSignalFromSignalBaseTable(ParaName);
        ui->tableWidget_TaskAssoPara->setItem(i,0,new QTableWidgetItem(Signal.Name));
        ui->tableWidget_TaskAssoPara->item(i,0)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskAssoPara->setItem(i,1,new QTableWidgetItem(Signal.DataType));
        ui->tableWidget_TaskAssoPara->item(i,1)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskAssoPara->setItem(i,2,new QTableWidgetItem(Signal.Unit));
        ui->tableWidget_TaskAssoPara->item(i,2)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskAssoPara->setItem(i,3,new QTableWidgetItem(Signal.Note));
        ui->tableWidget_TaskAssoPara->item(i,3)->setFlags(Qt::ItemIsEnabled);
        ui->tableWidget_TaskAssoPara->setItem(i,4,new QTableWidgetItem(ParaStandardValue));
        ui->tableWidget_TaskAssoPara->setItem(i,5,new QTableWidgetItem(ParaThresholdValue));

        ui->tableWidget_TaskAssoPara->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskAssoPara->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskAssoPara->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskAssoPara->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskAssoPara->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_TaskAssoPara->item(i,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }

    ui->lineEdit_RuleName->setText(m_WarnRule.Name);
    ui->lineEdit_RuleDescription->setText(m_WarnRule.Description);
    //ui->modelCmb_State->setCurrentIndex(m_WarnRule.State?1:0);
    ui->lineEdit_Editor->setText(m_WarnRule.Editor);
    ui->lineEdit_Editor->setEnabled(false);
}
void DialogWarningDefine::InitTabWidget()
{

    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString <<tr("变量名称") << tr("变量类型") << tr("变量单位") << tr("备注信息")<< tr("标准值")<< tr("阈值");
    StretchHorizontalIndex<<0<<3;

    //设置QSS
    TableWidgetQss(headerString,ui->tableWidget_TaskFeaturePara,StretchHorizontalIndex);

    //设置基础变量显示
    //设置表格的默认的行数
    ui->tableWidget_TaskFeaturePara->verticalHeader()->hide();//隐藏行序号


    headerString.clear();
    headerString <<tr("变量名称") << tr("变量类型") << tr("变量单位") << tr("备注信息")<< tr("标准值")<< tr("阈值");
    StretchHorizontalIndex.clear();
    StretchHorizontalIndex<<0<<3;

    //设置QSS
    TableWidgetQss(headerString,ui->tableWidget_TaskAssoPara,StretchHorizontalIndex);

    //设置基础变量显示
    //设置表格的默认的行数
    ui->tableWidget_TaskAssoPara->verticalHeader()->hide();//隐藏行序号

}
void DialogWarningDefine::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
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
    //TableWidget->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑
}
void DialogWarningDefine::on_Btn_TaskFeatureMod_clicked()
{
    QStringList ListTaskFeature;
    for(int i=0;i<ui->tableWidget_TaskFeaturePara->rowCount();i++)
        ListTaskFeature.append(ui->tableWidget_TaskFeaturePara->item(i,0)->text());
    QStringList ListTaskAsso;
    for(int i=0;i<ui->tableWidget_TaskAssoPara->rowCount();i++)
        ListTaskAsso.append(ui->tableWidget_TaskAssoPara->item(i,0)->text());

    DialogAllBasePara *dlg = new DialogAllBasePara(this,m_Database);
    dlg->ListPara=ListTaskFeature;
    dlg->ListComparePara=ListTaskAsso;
    dlg->LoadParaList();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        ui->tableWidget_TaskFeaturePara->setRowCount(0);
        ui->tableWidget_TaskFeaturePara->setRowCount(dlg->ListPara.count());
        for(int i=0;i<dlg->ListPara.count();i++)
        {
            DataBase::Str_Signal Signal=m_Database->SelectSignalFromSignalBaseTable(dlg->ListPara.at(i));     
            ui->tableWidget_TaskFeaturePara->setItem(i,0,new QTableWidgetItem(Signal.Name));
            ui->tableWidget_TaskFeaturePara->item(i,0)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskFeaturePara->setItem(i,1,new QTableWidgetItem(Signal.DataType));
            ui->tableWidget_TaskFeaturePara->item(i,1)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskFeaturePara->setItem(i,2,new QTableWidgetItem(Signal.Unit));
            ui->tableWidget_TaskFeaturePara->item(i,2)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskFeaturePara->setItem(i,3,new QTableWidgetItem(Signal.Note));
            ui->tableWidget_TaskFeaturePara->item(i,3)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskFeaturePara->setItem(i,4,new QTableWidgetItem(""));
            ui->tableWidget_TaskFeaturePara->setItem(i,5,new QTableWidgetItem(""));
            //与原来的m_WarnRule进行比较，载入标准值
            if(m_WarnRule.TaskParaList.contains(Signal.Name))
            {
                QStringList ListTaskPara;
                if(m_WarnRule.TaskParaList!="") ListTaskPara=m_WarnRule.TaskParaList.split(",");
                for(int j=0;j<ListTaskPara.count();j++)
                {
                    QStringList ListPara=ListTaskPara.at(j).split("=");
                    QString ParaName,ParaStandardValue,ParaThresholdValue;
                    if(ListPara.count()==2)
                    {
                        ParaName=ListPara.at(0);
                        ParaStandardValue=ListPara.at(1);
                        if(ParaStandardValue.contains("(")&&ParaStandardValue.contains(")"))
                        {
                            ParaThresholdValue=ParaStandardValue.mid(ParaStandardValue.indexOf("(")+1,ParaStandardValue.indexOf(")")-ParaStandardValue.indexOf("(")-1);
                        }
                    }
                    else {ParaName=ListPara.at(0);ParaStandardValue="";ParaThresholdValue="";}
                    if(Signal.Name==ParaName)
                    {
                        ui->tableWidget_TaskFeaturePara->item(i,4)->setText(ParaStandardValue);
                        ui->tableWidget_TaskFeaturePara->item(i,5)->setText(ParaThresholdValue);
                    }
                }
            }


            ui->tableWidget_TaskFeaturePara->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskFeaturePara->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskFeaturePara->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskFeaturePara->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskFeaturePara->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskFeaturePara->item(i,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        }

    }
    delete dlg;
}

void DialogWarningDefine::on_Btn_TaskFeatureDelete_clicked()
{
    if(ui->tableWidget_TaskFeaturePara->currentRow()<0) return;
    ui->tableWidget_TaskFeaturePara->removeRow(ui->tableWidget_TaskFeaturePara->currentRow());
}

void DialogWarningDefine::on_Btn_TaskAssoMod_clicked()
{
    QStringList ListTaskAsso;
    for(int i=0;i<ui->tableWidget_TaskAssoPara->rowCount();i++)
    {
        ListTaskAsso.append(ui->tableWidget_TaskAssoPara->item(i,0)->text());
    }
    QStringList ListTaskFeature;
    for(int i=0;i<ui->tableWidget_TaskFeaturePara->rowCount();i++)
        ListTaskFeature.append(ui->tableWidget_TaskFeaturePara->item(i,0)->text());

    DialogAllBasePara *dlg = new DialogAllBasePara(this,m_Database);
    dlg->ListPara=ListTaskAsso;
    dlg->ListComparePara=ListTaskFeature;
    dlg->LoadParaList();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        ui->tableWidget_TaskAssoPara->setRowCount(0);
        ui->tableWidget_TaskAssoPara->setRowCount(dlg->ListPara.count());
        for(int i=0;i<dlg->ListPara.count();i++)
        {
            DataBase::Str_Signal Signal=m_Database->SelectSignalFromSignalBaseTable(dlg->ListPara.at(i));
            ui->tableWidget_TaskAssoPara->setItem(i,0,new QTableWidgetItem(Signal.Name));
            ui->tableWidget_TaskAssoPara->item(i,0)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskAssoPara->setItem(i,1,new QTableWidgetItem(Signal.DataType));
            ui->tableWidget_TaskAssoPara->item(i,1)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskAssoPara->setItem(i,2,new QTableWidgetItem(Signal.Unit));
            ui->tableWidget_TaskAssoPara->item(i,2)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskAssoPara->setItem(i,3,new QTableWidgetItem(Signal.Note));
            ui->tableWidget_TaskAssoPara->item(i,3)->setFlags(Qt::ItemIsEnabled);
            ui->tableWidget_TaskAssoPara->setItem(i,4,new QTableWidgetItem(""));
            ui->tableWidget_TaskAssoPara->setItem(i,5,new QTableWidgetItem(""));
            //与原来的m_WarnRule进行比较，载入标准值
            if(m_WarnRule.WarnParaList.contains(Signal.Name))
            {
                QStringList ListWarnPara;
                if(m_WarnRule.WarnParaList!="") ListWarnPara=m_WarnRule.WarnParaList.split(",");
                for(int j=0;j<ListWarnPara.count();j++)
                {
                    QStringList ListPara=ListWarnPara.at(j).split("=");
                    QString ParaName,ParaStandardValue,ParaThresholdValue;
                    if(ListPara.count()==2)
                    {
                        ParaName=ListPara.at(0);
                        ParaStandardValue=ListPara.at(1);
                        if(ParaStandardValue.contains("(")&&ParaStandardValue.contains(")"))
                        {
                            ParaThresholdValue=ParaStandardValue.mid(ParaStandardValue.indexOf("(")+1,ParaStandardValue.indexOf(")")-ParaStandardValue.indexOf("(")-1);
                        }
                    }
                    else {ParaName=ListPara.at(0);ParaStandardValue="";ParaThresholdValue="";}
                    if(Signal.Name==ParaName)
                    {
                        ui->tableWidget_TaskAssoPara->item(i,4)->setText(ParaStandardValue);
                        ui->tableWidget_TaskAssoPara->item(i,5)->setText(ParaThresholdValue);
                    }
                }
            }

            ui->tableWidget_TaskAssoPara->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskAssoPara->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskAssoPara->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskAssoPara->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskAssoPara->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
            ui->tableWidget_TaskAssoPara->item(i,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        }
    }
    delete dlg;
}

void DialogWarningDefine::on_Btn_TaskAssoDelete_clicked()
{
    if(ui->tableWidget_TaskAssoPara->currentRow()<0) return;
    ui->tableWidget_TaskAssoPara->removeRow(ui->tableWidget_TaskAssoPara->currentRow());
}

void DialogWarningDefine::on_Btn_OK_clicked()
{
    if((ui->lineEdit_RuleName->text()=="")||(ui->tableWidget_TaskAssoPara->rowCount()==0)||(ui->tableWidget_TaskFeaturePara->rowCount()==0))
    {
        QMessageBox::warning(nullptr, "提示", "请将信息填写完整");
        return;
    }


    m_WarnRule.Description=ui->lineEdit_RuleDescription->text();
    m_WarnRule.Editor=ui->lineEdit_Editor->text();
    m_WarnRule.Name=ui->lineEdit_RuleName->text();
    //m_WarnRule.State=ui->modelCmb_State->currentIndex();
    m_WarnRule.TaskParaList="";
    for(int i=0;i<ui->tableWidget_TaskFeaturePara->rowCount();i++)
    {
        if(i>0) m_WarnRule.TaskParaList.append(",");
        m_WarnRule.TaskParaList.append(ui->tableWidget_TaskFeaturePara->item(i,0)->text());
        if(ui->tableWidget_TaskFeaturePara->item(i,4)->text()!="")
            m_WarnRule.TaskParaList.append("="+ui->tableWidget_TaskFeaturePara->item(i,4)->text());
        if(ui->tableWidget_TaskFeaturePara->item(i,5)->text()!="")
            m_WarnRule.TaskParaList.append("("+ui->tableWidget_TaskFeaturePara->item(i,5)->text()+")");
    }

    m_WarnRule.WarnParaList="";
    for(int i=0;i<ui->tableWidget_TaskAssoPara->rowCount();i++)
    {
        if(i>0) m_WarnRule.WarnParaList.append(",");
        m_WarnRule.WarnParaList.append(ui->tableWidget_TaskAssoPara->item(i,0)->text());
        if(ui->tableWidget_TaskAssoPara->item(i,4)->text()!="")
            m_WarnRule.WarnParaList.append("="+ui->tableWidget_TaskAssoPara->item(i,4)->text());
        if(ui->tableWidget_TaskAssoPara->item(i,5)->text()!="")
            m_WarnRule.WarnParaList.append("("+ui->tableWidget_TaskAssoPara->item(i,5)->text()+")");
    }

    //如果当前的TaskPara与其他的重复或名称与其他重复，则提示
    if(m_Database->CheckIfTaskParaExist(m_WarnRule))
    {
        QMessageBox::warning(nullptr, "提示", "规则名称或工况条件参数与其他规则重复！");
        return;
    }
    Canceled=false;
    this->close();
}

void DialogWarningDefine::on_Btn_Cancel_clicked()
{
    Canceled=true;
    this->close();
}
