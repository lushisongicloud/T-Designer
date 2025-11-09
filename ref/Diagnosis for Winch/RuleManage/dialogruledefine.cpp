#include "dialogruledefine.h"
#include "ui_dialogruledefine.h"
#include <QMessageBox>
#include <QClipboard>
#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

DialogRuleDefine::DialogRuleDefine(QWidget *parent,myQSqlDatabase *TMATE_Database,DataBase::Str_Rule rule,bool isCreatRule) :
    QDialog(parent),ui(new Ui::DialogRuleDefine),m_Database(TMATE_Database),m_rule(rule),m_isCreatRule(isCreatRule)
{
    ui->setupUi(this);

    this->setWindowFlags(Qt::Dialog| Qt::FramelessWindowHint);//隐藏窗口边框
    setWindowTitle(tr("规则定义"));

    //若规则名称为空则确定按钮不可点击
    if(m_rule.Name==""){
        ui->Btn_OK->setEnabled(false);
    }

    //设置右侧规则信息显示
    ui->lineEdit_RuleName->setText(m_rule.Name);
    ui->lineEdit_RuleDescription->setText(m_rule.Description);
    ui->modelCmb_State->setCurrentIndex(m_rule.State?1:0);
    ui->lineEdit_Editor->setText(m_rule.Editor);
    ui->lineEdit_Editor->setEnabled(false);
    ui->textEdit_Condition->setText(m_rule.Condition);
    ui->textEdit_Then->setText(m_rule.ResultThen);
    ui->textEdit_Else->setText(m_rule.ResultElse);
    ui->SpinBoxDurTime->setValue(m_rule.DurTime);
    ui->ComboBox_RulePos->setCurrentText(m_rule.RulePos);

    m_TableWidget[0]=ui->tableWidget_BasicVariable;
    m_TableWidget[1]=ui->tableWidget_MidVariable;
    m_TableWidget[2]=ui->tableWidget_FaliureVariable;
    m_TableWidget[3]=ui->tableWidget_WarnningVariable;
    for(int i=0;i<4;i++) m_TableWidget[i]->installEventFilter(this);

    //设置左侧变量信息显示
    InitTabWidget_Variable();

    //ui->Btn_Check->hide();
}

DialogRuleDefine::~DialogRuleDefine()
{
    delete ui;
}

bool DialogRuleDefine::eventFilter(QObject * obj,QEvent *event)
{
  for(int i=0;i<4;i++)
  {
      if(obj ==m_TableWidget[i]) //你要过滤的对象
          if(event->type() == QEvent::MouseButtonDblClick)
          {

              auto cur_text = ui->textEdit_Else->toPlainText();

              ui->textEdit_Else->blockSignals(true);

              int iCurPos= ui->textEdit_Else->textCursor().position();//当前光标的位置




            return true;
          }
  }
  return false;
}

void DialogRuleDefine::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
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

void DialogRuleDefine::on_Btn_OK_clicked()
{
    QString OraginName = m_rule.Name;

    //获取当前修改后的规则信息
    m_rule.Name = ui->lineEdit_RuleName->text();
    m_rule.Description = ui->lineEdit_RuleDescription->text();
    m_rule.State = ui->modelCmb_State->currentIndex();
    m_rule.Editor = ui->lineEdit_Editor->text();
    m_rule.Condition = ui->textEdit_Condition->toPlainText();
    m_rule.ResultThen = ui->textEdit_Then->toPlainText();
    m_rule.ResultElse = ui->textEdit_Else->toPlainText();
    m_rule.DurTime = ui->SpinBoxDurTime->value();
    m_rule.RulePos = ui->ComboBox_RulePos->currentText();
    //若规则名称为空则提示
    if(m_rule.Name=="")
    {
        QMessageBox::warning(nullptr, "提示", "请将信息填写完整");
        return;
    }

    //查询数据库中是否含有修改后的规则名称

    if(m_Database->IsRuleExist(m_rule.Name)){
        //若存在该名称且此时为新建规则;或当前为修改规则但是修改后的规则名称存在则不可创建
        if(m_isCreatRule||m_rule.Name!=OraginName){
            QMessageBox::warning(nullptr, "提示", "信号名称已存在");
            return;
        }
    }

    this->accept();
    ui->textEdit_Else->setText(m_rule.ResultElse);
}

void DialogRuleDefine::on_Btn_Check_clicked()
{
    //QDebug()<<"用于测试,未用";

      //这里的nCursor其实就是我们一个文本在一行中的位置

}

void DialogRuleDefine::InitTabWidget_Variable()
{

    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("变量名称") << tr("变量类型") << tr("变量单位") << tr("备注信息");
    StretchHorizontalIndex<<0<<3;

    //设置QSS
    TableWidgetQss(headerString,ui->tableWidget_BasicVariable,StretchHorizontalIndex);
    TableWidgetQss(headerString,ui->tableWidget_MidVariable,StretchHorizontalIndex);
    TableWidgetQss(headerString,ui->tableWidget_FaliureVariable,StretchHorizontalIndex);
    TableWidgetQss(headerString,ui->tableWidget_WarnningVariable,StretchHorizontalIndex);

    ////设置基础变量显示
    m_BasicSignal.clear();
    m_BasicSignal = m_Database->SelectSignalsInforFromSignalBaseTable("","基础信号");

    ui->tableWidget_BasicVariable->blockSignals(true);
    //设置表格的默认的行数
    ui->tableWidget_BasicVariable->setRowCount(m_BasicSignal.size());//设置默认的行数
    ui->tableWidget_BasicVariable->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_BasicSignal.size();i++){
        ui->tableWidget_BasicVariable->setItem(i,0,new QTableWidgetItem(m_BasicSignal[i].Name));
        ui->tableWidget_BasicVariable->setItem(i,1,new QTableWidgetItem(m_BasicSignal[i].DataType));
        ui->tableWidget_BasicVariable->setItem(i,2,new QTableWidgetItem(m_BasicSignal[i].Unit));
        ui->tableWidget_BasicVariable->setItem(i,3,new QTableWidgetItem(m_BasicSignal[i].Note));

        ui->tableWidget_BasicVariable->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_BasicVariable->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_BasicVariable->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_BasicVariable->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    ui->tableWidget_BasicVariable->blockSignals(false);


    ////设置中间变量显示
    m_MidSignal.clear();
    m_MidSignal = m_Database->SelectSignalsInforFromSignalBaseTable("","中间信号");

    ui->tableWidget_MidVariable->blockSignals(true);
    //设置表格的默认的行数
    ui->tableWidget_MidVariable->setRowCount(m_MidSignal.size());//设置默认的行数
    ui->tableWidget_MidVariable->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_MidSignal.size();i++){

        ui->tableWidget_MidVariable->setItem(i,0,new QTableWidgetItem(m_MidSignal[i].Name));
        ui->tableWidget_MidVariable->setItem(i,1,new QTableWidgetItem(m_MidSignal[i].DataType));
        ui->tableWidget_MidVariable->setItem(i,2,new QTableWidgetItem(m_MidSignal[i].Unit));
        ui->tableWidget_MidVariable->setItem(i,3,new QTableWidgetItem(m_MidSignal[i].SignalPos));

        ui->tableWidget_MidVariable->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_MidVariable->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_MidVariable->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_MidVariable->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    ui->tableWidget_MidVariable->blockSignals(false);

    ////设置故障变量显示
    m_FaliureSignal.clear();
    m_FaliureSignal = m_Database->SelectSignalsInforFromSignalBaseTable("","故障信号");

    ui->tableWidget_FaliureVariable->blockSignals(true);
    //设置表格的默认的行数
    ui->tableWidget_FaliureVariable->setRowCount(m_FaliureSignal.size());//设置默认的行数
    ui->tableWidget_FaliureVariable->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_FaliureSignal.size();i++){

        ui->tableWidget_FaliureVariable->setItem(i,0,new QTableWidgetItem(m_FaliureSignal[i].Name));
        ui->tableWidget_FaliureVariable->setItem(i,1,new QTableWidgetItem(m_FaliureSignal[i].DataType));
        ui->tableWidget_FaliureVariable->setItem(i,2,new QTableWidgetItem(m_FaliureSignal[i].Unit));
        ui->tableWidget_FaliureVariable->setItem(i,3,new QTableWidgetItem(m_FaliureSignal[i].Note));

        ui->tableWidget_FaliureVariable->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_FaliureVariable->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_FaliureVariable->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_FaliureVariable->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    ui->tableWidget_FaliureVariable->blockSignals(false);

    ////设置报警变量显示
    m_WarnningSignal.clear();
    m_WarnningSignal = m_Database->SelectSignalsInforFromSignalBaseTable("","报警信号");

    ui->tableWidget_WarnningVariable->blockSignals(true);
    //设置表格的默认的行数
    ui->tableWidget_WarnningVariable->setRowCount(m_WarnningSignal.size());//设置默认的行数
    ui->tableWidget_WarnningVariable->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<m_WarnningSignal.size();i++){

        ui->tableWidget_WarnningVariable->setItem(i,0,new QTableWidgetItem(m_WarnningSignal[i].Name));
        ui->tableWidget_WarnningVariable->setItem(i,1,new QTableWidgetItem(m_WarnningSignal[i].DataType));
        ui->tableWidget_WarnningVariable->setItem(i,2,new QTableWidgetItem(m_WarnningSignal[i].Unit));
        ui->tableWidget_WarnningVariable->setItem(i,3,new QTableWidgetItem(m_WarnningSignal[i].Note));

        ui->tableWidget_WarnningVariable->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_WarnningVariable->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_WarnningVariable->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_WarnningVariable->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    ui->tableWidget_WarnningVariable->blockSignals(false);

    ui->tabWidget_Variable->setCurrentIndex(0);
}

void DialogRuleDefine::on_lineEdit_RuleName_textChanged(const QString &arg1)
{
    //若规则名称为空则确定按钮不可点击
    if(arg1=="")
        ui->Btn_OK->setEnabled(false);
    else
        ui->Btn_OK->setEnabled(true);
}

void DialogRuleDefine::on_Btn_Cancel_clicked()
{
    this->close();
}

void DialogRuleDefine::on_textEdit_Condition_textChanged()
{
    auto cur_text = ui->textEdit_Condition->toPlainText();

    ui->textEdit_Condition->blockSignals(true);

    int iCurPos= ui->textEdit_Condition->textCursor().position();//当前光标的位置

    ui->textEdit_Condition->clear();

    int n = cur_text.size();
    int i=0;
    while(i<n){
        if(cur_text[i]=='='||cur_text[i]=='<'||cur_text[i]=='>'||cur_text[i]=='+'||cur_text[i]=='-'||cur_text[i]=='*'||cur_text[i]=='/'||cur_text[i]=='|'){
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Condition->setTextColor(Qt::green);
            ui->textEdit_Condition->insertPlainText(cur);
            i++;
        }
        else if(cur_text[i]==';'||cur_text[i]==' '){
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Condition->setTextColor(Qt::black);
            ui->textEdit_Condition->insertPlainText(cur);
            i++;
        }
        else if(cur_text[i].isNumber()){
            QString Number = "";
            while(i<n&&(cur_text[i].isNumber()||cur_text[i]=='.')){
                Number.append(cur_text[i]);
                i++;
            }
            ui->textEdit_Condition->setTextColor(QColor(255,137,246,255));
            ui->textEdit_Condition->insertPlainText(Number);
        }

        else if(cur_text[i]=='['){
            i++;
            //获取变量名称
            QString VariableName = "";
            while(i<n&&cur_text[i]!=']'){
                if(cur_text[i]!=' ')
                    VariableName.append(cur_text[i]);
                i++;
            }

            bool ok = false;
            if(VariableName == "true"||VariableName == "false")
                ok = true;
            else if(m_Database->IsSignalExist(VariableName))
                ok = true;

            if(i<n&&cur_text[i]==']'){
                if(ok) ui->textEdit_Condition->setTextColor(Qt::blue);
                else ui->textEdit_Condition->setTextColor(Qt::red);
                ui->textEdit_Condition->insertPlainText("[");
                ui->textEdit_Condition->insertPlainText(VariableName);
                ui->textEdit_Condition->insertPlainText("]");
                i++;
            }
            else{
                ui->textEdit_Condition->setTextColor(Qt::red);
                ui->textEdit_Condition->insertPlainText("[");
                ui->textEdit_Condition->insertPlainText(VariableName);
            }
        }
        else{
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Condition->setTextColor(Qt::red);
            ui->textEdit_Condition->insertPlainText(cur);
            i++;
        }
    }

    //恢复光标位置
    QTextCursor tmpCursor = ui->textEdit_Condition->textCursor();
    tmpCursor.setPosition(iCurPos);
    ui->textEdit_Condition->setTextCursor(tmpCursor);

    ui->textEdit_Condition->blockSignals(false);
}

void DialogRuleDefine::on_textEdit_Then_textChanged()
{
    auto cur_text = ui->textEdit_Then->toPlainText();

    ui->textEdit_Then->blockSignals(true);

    int iCurPos= ui->textEdit_Then->textCursor().position();//当前光标的位置

    ui->textEdit_Then->clear();

    int n = cur_text.size();
    int i=0;
    while(i<n){
        if(cur_text[i]=='='||cur_text[i]=='<'||cur_text[i]=='>'||cur_text[i]=='+'||cur_text[i]=='-'||cur_text[i]=='*'||cur_text[i]=='/'){
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Then->setTextColor(Qt::green);
            ui->textEdit_Then->insertPlainText(cur);
            i++;
        }
        else if(cur_text[i]==';'||cur_text[i]==' '){
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Then->setTextColor(Qt::black);
            ui->textEdit_Then->insertPlainText(cur);
            i++;
        }
        else if(cur_text[i].isNumber()){
            QString Number = "";
            while(i<n&&(cur_text[i].isNumber()||cur_text[i]=='.')){
                Number.append(cur_text[i]);
                i++;
            }
            ui->textEdit_Then->setTextColor(QColor(255,137,246,255));
            ui->textEdit_Then->insertPlainText(Number);
        }



        else if(cur_text[i]=='['){
            i++;
            //获取变量名称
            QString VariableName = "";
            while(i<n&&cur_text[i]!=']'){
                if(cur_text[i]!=' ')
                    VariableName.append(cur_text[i]);
                i++;
            }

            bool ok = false;
            if(VariableName == "true"||VariableName == "false")
                ok = true;
            else if(m_Database->IsSignalExist(VariableName))
                ok = true;

            if(i<n&&cur_text[i]==']'){
                ui->textEdit_Then->setTextColor(Qt::blue);
                ui->textEdit_Then->insertPlainText("[");
                ui->textEdit_Then->insertPlainText(VariableName);
                ui->textEdit_Then->insertPlainText("]");
                i++;
            }
            else{
                ui->textEdit_Then->setTextColor(Qt::red);
                ui->textEdit_Then->insertPlainText("[");
                ui->textEdit_Then->insertPlainText(VariableName);
            }
        }
        else{
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Then->setTextColor(Qt::red);
            ui->textEdit_Then->insertPlainText(cur);
            i++;
        }
    }

    //恢复光标位置
    QTextCursor tmpCursor = ui->textEdit_Then->textCursor();
    tmpCursor.setPosition(iCurPos);
    ui->textEdit_Then->setTextCursor(tmpCursor);

    ui->textEdit_Then->blockSignals(false);
}

void DialogRuleDefine::on_textEdit_Else_textChanged()
{
    auto cur_text = ui->textEdit_Else->toPlainText();

    ui->textEdit_Else->blockSignals(true);

    int iCurPos= ui->textEdit_Else->textCursor().position();//当前光标的位置
    //qDebug()<<"iCurPos="<<iCurPos;
    ui->textEdit_Else->clear();

    int n = cur_text.size();
    int i=0;
    while(i<n){
        if(cur_text[i]=='='||cur_text[i]=='<'||cur_text[i]=='>'||cur_text[i]=='+'||cur_text[i]=='-'||cur_text[i]=='*'||cur_text[i]=='/'){
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Else->setTextColor(Qt::green);
            ui->textEdit_Else->insertPlainText(cur);
            i++;
        }
        else if(cur_text[i]==';'||cur_text[i]==' '){
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Else->setTextColor(Qt::black);
            ui->textEdit_Else->insertPlainText(cur);
            i++;
        }
        else if(cur_text[i].isNumber()){
            QString Number = "";
            while(i<n&&(cur_text[i].isNumber()||cur_text[i]=='.')){
                Number.append(cur_text[i]);
                i++;
            }
            ui->textEdit_Else->setTextColor(QColor(255,137,246,255));
            ui->textEdit_Else->insertPlainText(Number);
        }



        else if(cur_text[i]=='['){
            i++;
            //获取变量名称
            QString VariableName = "";
            while(i<n&&cur_text[i]!=']'){
                if(cur_text[i]!=' ')
                    VariableName.append(cur_text[i]);
                i++;
            }

            bool ok = false;
            if(VariableName == "true"||VariableName == "false")
                ok = true;
            else if(m_Database->IsSignalExist(VariableName))
                ok = true;

            if(i<n&&cur_text[i]==']'){
                ui->textEdit_Else->setTextColor(Qt::blue);
                ui->textEdit_Else->insertPlainText("[");
                ui->textEdit_Else->insertPlainText(VariableName);
                ui->textEdit_Else->insertPlainText("]");
                i++;
            }
            else{
                ui->textEdit_Else->setTextColor(Qt::red);
                ui->textEdit_Else->insertPlainText("[");
                ui->textEdit_Else->insertPlainText(VariableName);
            }
        }
        else{
            QString cur;
            cur.append(cur_text[i]);
            ui->textEdit_Else->setTextColor(Qt::red);
            ui->textEdit_Else->insertPlainText(cur);
            i++;
        }
    }

    //恢复光标位置
    QTextCursor tmpCursor = ui->textEdit_Else->textCursor();
    tmpCursor.setPosition(iCurPos);
    ui->textEdit_Else->setTextCursor(tmpCursor);

    ui->textEdit_Else->blockSignals(false);
}

void DialogRuleDefine::on_tableWidget_BasicVariable_doubleClicked(const QModelIndex &index)
{//双击变量列表复制变量名
    Q_UNUSED(index)
    int curRow = ui->tableWidget_BasicVariable->currentRow();

    if(curRow==-1) return;

    QString Name = "[";
    Name.append(ui->tableWidget_BasicVariable->item(curRow,0)->text());//获取当前名称
    Name.append("]");

    QClipboard *clipboard = QApplication::clipboard();//获取系统剪贴板指针
    clipboard->setText(Name);//设置剪贴板内容</span>
}

void DialogRuleDefine::on_tableWidget_MidVariable_doubleClicked(const QModelIndex &index)
{//双击变量列表复制变量名
    Q_UNUSED(index)
    int curRow = ui->tableWidget_MidVariable->currentRow();

    if(curRow==-1) return;

    QString Name = "[";
    Name.append(ui->tableWidget_MidVariable->item(curRow,0)->text());//获取当前名称
    Name.append("]");

    QClipboard *clipboard = QApplication::clipboard();//获取系统剪贴板指针
    clipboard->setText(Name);//设置剪贴板内容</span>
}

void DialogRuleDefine::on_tableWidget_FaliureVariable_doubleClicked(const QModelIndex &index)
{//双击变量列表复制变量名
    Q_UNUSED(index)
    int curRow = ui->tableWidget_FaliureVariable->currentRow();

    if(curRow==-1) return;

    QString Name = "[";
    Name.append(ui->tableWidget_FaliureVariable->item(curRow,0)->text());//获取当前名称
    Name.append("]");

    QClipboard *clipboard = QApplication::clipboard();//获取系统剪贴板指针
    clipboard->setText(Name);//设置剪贴板内容</span>
}

void DialogRuleDefine::on_tableWidget_WarnningVariable_doubleClicked(const QModelIndex &index)
{//双击变量列表复制变量名
    Q_UNUSED(index)
    int curRow = ui->tableWidget_WarnningVariable->currentRow();

    if(curRow==-1) return;

    QString Name = "[";
    Name.append(ui->tableWidget_WarnningVariable->item(curRow,0)->text());//获取当前名称
    Name.append("]");

    QClipboard *clipboard = QApplication::clipboard();//获取系统剪贴板指针
    clipboard->setText(Name);//设置剪贴板内容</span>
}

