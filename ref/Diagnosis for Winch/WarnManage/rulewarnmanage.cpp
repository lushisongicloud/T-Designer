#include "rulewarnmanage.h"
#include "ui_rulewarnmanage.h"
#include <QMessageBox>
#include "dialogwarningdefine.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern DataBase::Str_account  m_loginAccount;//当前登陆账户信息
extern RulePool m_RulePool;
extern QString ProcessingText(const QFontMetrics& font, const QString& text, int nLabelSize);
WarnManage::WarnManage(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),ui(new Ui::WarnManage),m_Database(TMATE_Database)
{
    ui->setupUi(this);

    //设置遮罩窗口
    mpShadeWindow = new QWidget(this);
    QString str("QWidget{background-color:rgba(0,0,0,0.6);}");
    mpShadeWindow->setStyleSheet(str);
    mpShadeWindow->setGeometry(0, 0, 1, 1);
    mpShadeWindow->hide();

    //设置QSS
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("工况名称")<< tr("描述") << tr("工况条件参数") << tr("关联预警参数") << tr("编辑人")<<tr("状态")<<tr("相关变量值");

    StretchHorizontalIndex<<0<<1<<2<<3<<6;
    TableWidgetQss(headerString,ui->tableWidget_KnowledgeBase,StretchHorizontalIndex);
    ui->tableWidget_KnowledgeBase->setWordWrap(true);
    //TextEditDelegate *TextEditor=new TextEditDelegate;
    //for(int i=0;i<StretchHorizontalIndex.count();i++)
    //{
    //    ui->tableWidget_KnowledgeBase->setItemDelegateForColumn(StretchHorizontalIndex.at(i),TextEditor);
    //}

    //ui->tableWidget_KnowledgeBase->setColumnHidden(3,true);
    //ui->tableWidget_KnowledgeBase->setColumnHidden(4,true);
   // connect(ui->tableWidget_KnowledgeBase->model(),SIGNAL(rowsInserted(QModelIndex,int,int)),this,SLOT(on_TableWidgetColWidth_changed(QModelIndex,int,int)));
    //清空检索框
    ui->lineEdit_RuleName->clear();
    ui->Cmb_RuleState->setCurrentIndex(0);
    update();

    timerUpdateUI = new QTimer(this);
    connect(timerUpdateUI,SIGNAL(timeout()),this,SLOT(DoUpdateUI()));
    timerUpdateUI->start(1000);
}

WarnManage::~WarnManage()
{
    delete ui;
}

void WarnManage::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
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

QString CombineParaStrAndThreshold(QString ParaStr,QString WholeStr)
{
    QStringList ListWholeStr=WholeStr.split(",");
    QStringList ListParaStr=ParaStr.split(",");
    for(int i=0;i<ListWholeStr.count();i++)
    {
       if(ListWholeStr.at(i).contains("(")&&ListWholeStr.at(i).contains(")"))
       {
           ListParaStr[i]=ListParaStr.at(i)+ListWholeStr.at(i).mid(ListWholeStr.at(i).lastIndexOf("("),ListWholeStr.at(i).lastIndexOf(")")-ListWholeStr.at(i).lastIndexOf("(")+1);
       }
    }
    QString AnsStr;
    for(int i=0;i<ListParaStr.count();i++)
    {
        AnsStr+=ListParaStr.at(i);
        if(i<ListParaStr.count()-1) AnsStr+=",";
    }
    return  AnsStr;
}

QString GetParaStrWithoutValue(QString ParaStr)
{
    QStringList ListWarnPara=ParaStr.split(",");
    for(int i=0;i<ListWarnPara.count();i++)
    {
        if(ListWarnPara.at(i).contains("="))
        {
           ListWarnPara[i]= ListWarnPara.at(i).mid(0,ListWarnPara.at(i).lastIndexOf("="));
        }
    }
    QString WarnPara;
    for(int j=0;j<ListWarnPara.count();j++)
    {
        WarnPara+=ListWarnPara.at(j);
        if(j<ListWarnPara.count()-1) WarnPara+=",";
    }
    return WarnPara;
}
void WarnManage::DoUpdateUI()
{
    for(int i=0;i<m_Rule.size();i++){
        QString TaskPara=GetParaStrWithoutValue(m_Rule[i].TaskParaList);
        QString WarnPara=GetParaStrWithoutValue(m_Rule[i].WarnParaList);
        QFontMetrics font(ui->tableWidget_KnowledgeBase->font());
        QString RealTimeParaList=ProcessingText(font,m_RulePool.GetRelatedWarnParaValStr(TaskPara+","+WarnPara),270);//ui->tableWidget_KnowledgeBase->columnWidth(2)

        ui->tableWidget_KnowledgeBase->item(i,6)->setText(RealTimeParaList);
    }
    ui->tableWidget_KnowledgeBase->resizeRowsToContents();
}
void WarnManage::update()
{//更新规则表

    m_Rule.clear();
    //获取规则信息
    m_Rule = m_Database->SelectWarnRulesInforFromRuleBaseTable(ui->lineEdit_RuleName->text(),ui->Cmb_RuleState->currentIndex()-1);
    //ui->tableWidget_KnowledgeBase->blockSignals(true);
    for(int i=0;i<m_Rule.size();i++){
        //TextEditDelegate * textEditer = new TextEditDelegate ;
        //ui->tableWidget_KnowledgeBase->setItemDelegateForRow(i,textEditer);
    }
    //设置表格的默认的行数
    ui->tableWidget_KnowledgeBase->setRowCount(m_Rule.size());//设置默认的行数
    ui->tableWidget_KnowledgeBase->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_Rule.size();i++){
       // headerString << tr("规则名称")<< tr("描述") << tr("工况条件参数") << tr("关联预警参数") << tr("编辑人")<<tr("状态")<<tr("相关变量值");
        ui->tableWidget_KnowledgeBase->setItem(i,0,new QTableWidgetItem(m_Rule[i].Name));
        ui->tableWidget_KnowledgeBase->setItem(i,1,new QTableWidgetItem(m_Rule[i].Description));
        QFontMetrics font(ui->tableWidget_KnowledgeBase->font());
        QString TaskParaList=ProcessingText(font,m_Rule[i].TaskParaList,200);//ui->tableWidget_KnowledgeBase->columnWidth(2)

        ui->tableWidget_KnowledgeBase->setItem(i,2,new QTableWidgetItem(TaskParaList));
        QFontMetrics font2(ui->tableWidget_KnowledgeBase->font());
        QString WarnParaList=ProcessingText(font,m_Rule[i].WarnParaList,200);//ui->tableWidget_KnowledgeBase->columnWidth(2)

        ui->tableWidget_KnowledgeBase->setItem(i,3,new QTableWidgetItem(WarnParaList));
        ui->tableWidget_KnowledgeBase->setItem(i,4,new QTableWidgetItem(m_Rule[i].Editor));
        ui->tableWidget_KnowledgeBase->setItem(i,6,new QTableWidgetItem(""));

        QTableWidgetItem *checkBox = new QTableWidgetItem();
        if(m_Rule[i].State)
            checkBox->setCheckState(Qt::Checked);
        else
            checkBox->setCheckState(Qt::Unchecked);

        ui->tableWidget_KnowledgeBase ->setItem(i, 5, checkBox);
        ui->tableWidget_KnowledgeBase->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,6)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    //ui->tableWidget_KnowledgeBase->blockSignals(false);
    ui->tableWidget_KnowledgeBase->resizeRowsToContents();
}

void WarnManage::SetChangeEnabled(bool enable)
{
    ui->Btn_KnowledgeBaseCreat->setEnabled(enable);
    ui->Btn_KnowledgeBaseAlter->setEnabled(enable);
    ui->Btn_KnowledgeBaseDelete->setEnabled(enable);
}

void WarnManage::on_Btn_KnowledgeBaseSelect_clicked()
{//条件筛选
    update();
}

void WarnManage::on_Btn_KnowledgeBaseCreat_clicked()
{//创建规则
    DataBase::Str_WarnRule rule;
    rule.Editor = m_loginAccount.Operating_user;

    //遮罩效果
    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();

    //模态对话框，动态创建，用过后删除
    DialogWarningDefine    *add_new_Rule_view=new DialogWarningDefine(nullptr,m_Database,rule,true); //创建对话框
    add_new_Rule_view->setWindowTitle("新建预警规则");
    Qt::WindowFlags    flags=add_new_Rule_view->windowFlags();
    add_new_Rule_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    add_new_Rule_view->exec();// 以模态方式显示对话框

    if (!add_new_Rule_view->Canceled) //OK键被按下,对话框关闭
    {
        m_Database->InsertWarnRuleToRuleBaseTable(add_new_Rule_view->m_WarnRule);
        QString dlgTitle="新增规则";
        QString strInfo=QString::asprintf("新增规则成功！");
        QMessageBox::information(nullptr, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);
    }
    delete add_new_Rule_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    update();
}

void WarnManage::on_Btn_KnowledgeBaseAlter_clicked()
{//修改规则

    //获取当前选中行
    int curRow = ui->tableWidget_KnowledgeBase->currentRow();

    //若未选中给出警告
    if(curRow==-1){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择规则"),QMessageBox::Yes);
        return;}

    //获取规则当前名称
    QString Name = ui->tableWidget_KnowledgeBase->item(curRow,0)->text();

    //获取规则信息
    DataBase::Str_WarnRule  selectedRule = m_Database->SelectWarnRuleFromWarnBaseTable(Name);

    //遮罩效果
    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();

    //模态对话框，动态创建，用过后删除
    DialogWarningDefine    *add_new_Rule_view=new DialogWarningDefine(nullptr,m_Database,selectedRule,false); //创建对话框
    add_new_Rule_view->setWindowTitle("预警规则编辑");
    Qt::WindowFlags    flags=add_new_Rule_view->windowFlags();
    add_new_Rule_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    add_new_Rule_view->exec();// 以模态方式显示对话框

    if (!add_new_Rule_view->Canceled) //OK键被按下,对话框关闭
    {
        m_Database->UpdateWarnRuleToRuleBaseTable(selectedRule,add_new_Rule_view->m_WarnRule);
        QString dlgTitle="修改规则";
        QString strInfo=QString::asprintf("修改规则成功！");
        QMessageBox::information(nullptr, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);
    }
    delete add_new_Rule_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    update();
}

void WarnManage::on_Btn_KnowledgeBaseDelete_clicked()
{//删除规则
    int curRow = ui->tableWidget_KnowledgeBase->currentRow();

    //若未选中给出警告
    if(curRow==-1){
        QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择要删除的规则"),QMessageBox::Yes);
        return;}

    QString Name = ui->tableWidget_KnowledgeBase->item(curRow,0)->text();//获取规则当前名称

    //确认是否删除
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("是否确认删除该规则?"),
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes)
    {
        if(m_Database->DeleteWarnRuleFromRuleBaseTable(Name))
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("规则已删除"));
        else
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("删除失败"));
        update();
    }
}

void WarnManage::on_tableWidget_KnowledgeBase_cellChanged(int row, int column)
{//禁用规则
    //qDebug()<<row<<","<<column<<" changed!";
    if(column==5){
        if(ui->tableWidget_KnowledgeBase->item(row, column)->checkState() == Qt::Checked)
        {
            QStringList ListTaskPara=ui->tableWidget_KnowledgeBase->item(row, 2)->text().split(",");
            for(int i=0;i<ListTaskPara.count();i++)
            {
                if(!ListTaskPara.at(i).contains("="))
                {
                    ui->tableWidget_KnowledgeBase->item(row, column)->setCheckState(Qt::Unchecked);
                    QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("工况条件参数未全部填入特征值！"));
                    return;
                }
            }
            QStringList ListWarnPara=ui->tableWidget_KnowledgeBase->item(row, 3)->text().split(",");
            for(int i=0;i<ListWarnPara.count();i++)
            {
                if(!ListWarnPara.at(i).contains("="))
                {
                    ui->tableWidget_KnowledgeBase->item(row, column)->setCheckState(Qt::Unchecked);
                    QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("关联预警参数未全部填入特征值！"));
                    return;
                }
            }
        }
        QString RuleName = ui->tableWidget_KnowledgeBase->item(row, 0)->text();
        m_Database->UpdateWarnRuleForbidden(RuleName,ui->tableWidget_KnowledgeBase->item(row, column)->checkState() == Qt::Checked);
    }
}

void WarnManage::on_BtnSetStandard_clicked()
{
    if(ui->tableWidget_KnowledgeBase->currentRow()<0) return;
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("提示"),"是否确认将当前系统状态值设定为工况"+ui->tableWidget_KnowledgeBase->item(ui->tableWidget_KnowledgeBase->currentRow(),0)->text()+"的标准样本值？",
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);
    if(result==QMessageBox::Yes)
    {
       DataBase::Str_WarnRule UpdateRule=m_Rule[ui->tableWidget_KnowledgeBase->currentRow()];

       ui->tableWidget_KnowledgeBase->item(ui->tableWidget_KnowledgeBase->currentRow(),2)->setText(CombineParaStrAndThreshold(m_RulePool.GetRelatedWarnParaValStr(GetParaStrWithoutValue(m_Rule[ui->tableWidget_KnowledgeBase->currentRow()].TaskParaList)),m_Rule[ui->tableWidget_KnowledgeBase->currentRow()].TaskParaList));
       ui->tableWidget_KnowledgeBase->item(ui->tableWidget_KnowledgeBase->currentRow(),3)->setText(CombineParaStrAndThreshold(m_RulePool.GetRelatedWarnParaValStr(GetParaStrWithoutValue(m_Rule[ui->tableWidget_KnowledgeBase->currentRow()].WarnParaList)),m_Rule[ui->tableWidget_KnowledgeBase->currentRow()].WarnParaList));
       UpdateRule.TaskParaList=ui->tableWidget_KnowledgeBase->item(ui->tableWidget_KnowledgeBase->currentRow(),2)->text();
       UpdateRule.WarnParaList=ui->tableWidget_KnowledgeBase->item(ui->tableWidget_KnowledgeBase->currentRow(),3)->text();
       m_Database->UpdateWarnRuleToRuleBaseTable(m_Rule[ui->tableWidget_KnowledgeBase->currentRow()],UpdateRule);
       QString dlgTitle="修改规则";
       QString strInfo=QString::asprintf("修改规则成功！");
       QMessageBox::information(nullptr, dlgTitle, strInfo,
                                QMessageBox::Ok,QMessageBox::NoButton);
       update();
    }
}

void WarnManage::on_tableWidget_KnowledgeBase_doubleClicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    DialogShowTaskCurve *dlg =new DialogShowTaskCurve(this,m_Database,ui->tableWidget_KnowledgeBase->item(index.row(),0)->text());
    dlg->setWindowTitle("工况"+ui->tableWidget_KnowledgeBase->item(index.row(),0)->text()+"历史数据");
    dlg->show();
    QApplication::processEvents();
}
