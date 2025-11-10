#include "rulemanage.h"
#include "ui_rulemanage.h"
#include <QMessageBox>
#include "dialogruledefine.h"

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern DataBase::Str_account  m_loginAccount;//当前登陆账户信息
extern RulePool m_RulePool;
RuleManage::RuleManage(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),ui(new Ui::RuleManage),m_Database(TMATE_Database)
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

    headerString << tr("规则名称")<< tr("描述") << tr("条件") << tr("成立")  << tr("不成立") << tr("编辑人")<<tr("保持时间")<<tr("状态")<<tr("相关变量值");

    StretchHorizontalIndex<<0<<1<<2<<8;
    TableWidgetQss(headerString,ui->tableWidget_KnowledgeBase,StretchHorizontalIndex);

    ui->tableWidget_KnowledgeBase->setColumnHidden(3,true);
    ui->tableWidget_KnowledgeBase->setColumnHidden(4,true);
    ui->tableWidget_KnowledgeBase->setWordWrap(true);
   // connect(ui->tableWidget_KnowledgeBase->model(),SIGNAL(rowsInserted(QModelIndex,int,int)),this,SLOT(on_TableWidgetColWidth_changed(QModelIndex,int,int)));
    //清空检索框
    ui->lineEdit_RuleName->clear();
    ui->Cmb_RuleState->setCurrentIndex(0);
    update();

    timerUpdateUI = new QTimer(this);
    connect(timerUpdateUI,SIGNAL(timeout()),this,SLOT(DoUpdateUI()));
    timerUpdateUI->start(1000);
}

RuleManage::~RuleManage()
{
    delete ui;
}

QString ProcessingText(const QFontMetrics& font, const QString& text, int nLabelSize)
{
    int nTextSize = font.width(text);
    if (nTextSize > nLabelSize)
    {
        int nPos = 0;
        long nOffset = 0;
        for (int i = 0; i < text.size(); i++)
        {
            nOffset += font.width(text.at(i));
            if (nOffset > nLabelSize)
            {
                nPos = i;
                break;
            }
        }

        QString qstrLeftData = text.left(nPos);
        QString qstrMidData = text.mid(nPos);
        return qstrLeftData + "\n" + ProcessingText(font, qstrMidData, nLabelSize);
    }
    return text;
}

void RuleManage::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
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

void RuleManage::DoUpdateUI()
{
    for(int i=0;i<m_Rule.size();i++){
        QFontMetrics font(ui->tableWidget_KnowledgeBase->font());
        QString Condition=ProcessingText(font,m_RulePool.GetRelatedParaValStr(m_Rule[i].Condition),330);//ui->tableWidget_KnowledgeBase->columnWidth(2)

       ui->tableWidget_KnowledgeBase->item(i,8)->setText(Condition);
    }
    ui->tableWidget_KnowledgeBase->resizeRowsToContents();
}



void RuleManage::update()
{//更新规则表

    m_Rule.clear();
    //获取规则信息
    if(ui->comboBox_SignalPos->currentText()=="ALL")
      m_Rule = m_Database->SelectRulesInforFromRuleBaseTable(ui->lineEdit_RuleName->text(),"",ui->Cmb_RuleState->currentIndex()-1);
    else
      m_Rule = m_Database->SelectRulesInforFromRuleBaseTable(ui->lineEdit_RuleName->text(),ui->comboBox_SignalPos->currentText(),ui->Cmb_RuleState->currentIndex()-1);

    //ui->tableWidget_KnowledgeBase->blockSignals(true);
    //设置表格的默认的行数
    for(int i=0;i<m_Rule.size();i++){
        //TextEditDelegate * textEditer = new TextEditDelegate ;
        //ui->tableWidget_KnowledgeBase->setItemDelegateForRow(i,textEditer);
    }
    ui->tableWidget_KnowledgeBase->setRowCount(m_Rule.size());//设置默认的行数
    ui->tableWidget_KnowledgeBase->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_Rule.size();i++){
       // headerString << tr("规则名称")<< tr("条件") << tr("成立")  << tr("不成立") << tr("编辑人") << tr("保持时间") ;
        ui->tableWidget_KnowledgeBase->setItem(i,0,new QTableWidgetItem(m_Rule[i].Name));
        ui->tableWidget_KnowledgeBase->setItem(i,1,new QTableWidgetItem(m_Rule[i].Description));
        QFontMetrics font(ui->tableWidget_KnowledgeBase->font());
        QString Condition=ProcessingText(font,m_Rule[i].Condition,200);//ui->tableWidget_KnowledgeBase->columnWidth(2)
        ui->tableWidget_KnowledgeBase->setItem(i,2,new QTableWidgetItem(Condition));
        ui->tableWidget_KnowledgeBase->setItem(i,3,new QTableWidgetItem(m_Rule[i].ResultThen));
        ui->tableWidget_KnowledgeBase->setItem(i,4,new QTableWidgetItem(m_Rule[i].ResultElse));
        ui->tableWidget_KnowledgeBase->setItem(i,5,new QTableWidgetItem(m_Rule[i].Editor));
        ui->tableWidget_KnowledgeBase->setItem(i,6,new QTableWidgetItem(QString::number(m_Rule[i].DurTime,'f',1)+"s"));
        ui->tableWidget_KnowledgeBase->setItem(i,8,new QTableWidgetItem(""));

        QTableWidgetItem *checkBox = new QTableWidgetItem();
        if(m_Rule[i].State)
            checkBox->setCheckState(Qt::Checked);
        else
            checkBox->setCheckState(Qt::Unchecked);

        ui->tableWidget_KnowledgeBase ->setItem(i, 7, checkBox);

        ui->tableWidget_KnowledgeBase->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,5)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_KnowledgeBase->item(i,6)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    //ui->tableWidget_KnowledgeBase->blockSignals(false);
    ui->tableWidget_KnowledgeBase->resizeRowsToContents();
}

void RuleManage::SetChangeEnabled(bool enable)
{
    ui->Btn_KnowledgeBaseCreat->setEnabled(enable);
    ui->Btn_KnowledgeBaseAlter->setEnabled(enable);
    ui->Btn_KnowledgeBaseDelete->setEnabled(enable);
}

void RuleManage::on_Btn_KnowledgeBaseSelect_clicked()
{//条件筛选
    update();
}

void RuleManage::on_Btn_KnowledgeBaseCreat_clicked()
{//创建规则
    DataBase::Str_Rule rule;
    rule.Editor = m_loginAccount.Operating_user;

    //遮罩效果
    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();

    //模态对话框，动态创建，用过后删除
    DialogRuleDefine    *add_new_Rule_view=new DialogRuleDefine(nullptr,m_Database,rule,true); //创建对话框
    Qt::WindowFlags    flags=add_new_Rule_view->windowFlags();
    add_new_Rule_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    int ret=add_new_Rule_view->exec();// 以模态方式显示对话框

    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        m_Database->InsertRuleToRuleBaseTable(add_new_Rule_view->GetDefinedRule());
        QString dlgTitle="新增规则";
        QString strInfo=QString::asprintf("新增规则成功！");
        QMessageBox::information(nullptr, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);
    }
    delete add_new_Rule_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    update();
}

void RuleManage::on_Btn_KnowledgeBaseAlter_clicked()
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
    DataBase::Str_Rule  selectedRule = m_Database->SelectRuleFromRuleBaseTable(Name);

    //遮罩效果
    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();

    //模态对话框，动态创建，用过后删除
    DialogRuleDefine    *add_new_Rule_view=new DialogRuleDefine(nullptr,m_Database,selectedRule,false); //创建对话框
    Qt::WindowFlags    flags=add_new_Rule_view->windowFlags();
    add_new_Rule_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    int ret=add_new_Rule_view->exec();// 以模态方式显示对话框

    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        m_Database->UpdateRuleToRuleBaseTable(selectedRule,add_new_Rule_view->GetDefinedRule());
        QString dlgTitle="修改规则";
        QString strInfo=QString::asprintf("修改规则成功！");
        QMessageBox::information(nullptr, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);
    }
    delete add_new_Rule_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    update();
}

void RuleManage::on_Btn_KnowledgeBaseDelete_clicked()
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
        if(m_Database->DeleteRuleFromRuleBaseTable(Name))
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("规则已删除"));
        else
            QMessageBox::about(nullptr,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("删除失败"));
        update();
    }
}

void RuleManage::on_tableWidget_KnowledgeBase_cellChanged(int row, int column)
{//禁用规则
    //qDebug()<<row<<","<<column<<" changed!";
    if(column==7){
        QString RuleName = ui->tableWidget_KnowledgeBase->item(row, 0)->text();
        m_Database->UpdateRuleForbidden(RuleName,ui->tableWidget_KnowledgeBase->item(row, column)->checkState() == Qt::Checked);
    }
}

