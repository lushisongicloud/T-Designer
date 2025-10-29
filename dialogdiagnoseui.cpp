#include "dialogdiagnoseui.h"
#include "ui_dialogdiagnoseui.h"

dialogDiagnoseUI::dialogDiagnoseUI(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::dialogDiagnoseUI)
{
    ui->setupUi(this);
    this->setAttribute(Qt::WA_DeleteOnClose); //关闭时自动删除
    ui->tableWidget_function_select->setColumnWidth(0,140);//功能名称
    ui->tableWidget_function_select->setColumnWidth(1,400);//控制变量
    ui->tableWidget_function_select->setColumnWidth(2,400);//执行器名称
    ui->tableWidget_function_select->setColumnWidth(3,150);//备注
    ui->tableWidget_function_select->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_tool_select->setColumnWidth(0,400);//工具名称
    ui->tableWidget_tool_select->setFocusPolicy(Qt::NoFocus);
    LoadAllFunction();
    LoadAllTools();
}

dialogDiagnoseUI::~dialogDiagnoseUI()
{
    delete ui;
}

void dialogDiagnoseUI::LoadAllFunction()
{
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function";
    QueryFunction.exec(SqlStr);
    ui->tableWidget_function_select->setRowCount(0);
    while(QueryFunction.next())
    {
       ui->tableWidget_function_select->setRowCount(ui->tableWidget_function_select->rowCount()+1);
       ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,0,new QTableWidgetItem(QueryFunction.value("FunctionName").toString()));
       ui->tableWidget_function_select->item(ui->tableWidget_function_select->rowCount()-1,0)->setData(Qt::UserRole,QueryFunction.value("FunctionID").toString());
       ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,1,new QTableWidgetItem(QueryFunction.value("CmdValList").toString()));
       ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,2,new QTableWidgetItem(QueryFunction.value("ExecsList").toString()));
       ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,3,new QTableWidgetItem(QueryFunction.value("Remark").toString()));
    }
}

void dialogDiagnoseUI::LoadAllTools()
{
    ui->tableWidget_tool_select->setRowCount(0);
    ui->tableWidget_tool_select->setRowCount(ui->tableWidget_tool_select->rowCount()+1);
    ui->tableWidget_tool_select->setItem(ui->tableWidget_tool_select->rowCount()-1,0,new QTableWidgetItem("万用表"));
}

void dialogDiagnoseUI::SetStackIndex(int index)
{
    ui->stackedWidget_main->setCurrentIndex(index);
}

void dialogDiagnoseUI::on_toolButton_start_diagnosis_clicked()
{
    if(ui->tableWidget_function_select->currentRow()<0) return;
    //根据用户选择的功能生成xmpl
    FunctionID=ui->tableWidget_function_select->item(ui->tableWidget_function_select->currentRow(),0)->data(Qt::UserRole).toString();
    emit(signalUpdateExec(FunctionID));
    init_symptom_list();
    SetStackIndex(1);
}

void dialogDiagnoseUI::init_symptom_list()//初始化征兆信号UI列表
{
    ui->tableWidget_known_symptom_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_known_symptom_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_known_symptom_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);

    ui->tableWidget_known_symptom_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("观测对象名称") << tr("观测对象变量") << tr("观测值");
    ui->tableWidget_known_symptom_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_known_symptom_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);

    ui->tableWidget_known_symptom_select->setAlternatingRowColors(true);//使表格颜色交错功能为真

    //设置表头
    ui->tableWidget_known_symptom_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_known_symptom_select->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_known_symptom_select->setRowCount(0);
}

void dialogDiagnoseUI::AddOrModifyExec(int Mode,QString StrSelectedExec,QString StrExecState,QString StrExecStateVal)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增观测变量");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改观测变量");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("观测对象");
    m_label1->setMaximumWidth(50);
    QComboBox *m_QComboBox1 = new QComboBox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    m_label2->setText("观测变量");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QHBoxLayout *linelayout3= new QHBoxLayout(nullptr);
    QLabel *m_label3 = new QLabel(dialogNewExec);
    m_label3->setText("观测值");
    m_label3->setMaximumWidth(50);
    qxcombobox *m_QComboBox3 = new qxcombobox(dialogNewExec);
    linelayout3->addWidget(m_label3);
    linelayout3->addWidget(m_QComboBox3);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);
    layout3->addLayout(linelayout3);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecStateItems(QString)));
    QObject::connect(m_QComboBox2,SIGNAL(currentTextChanged(QString)),m_QComboBox3,SLOT(UpdateExecStateValueItems(QString)));
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+FunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
       QStringList ExecsList=QueryFunction.value("ExecsList").toString().split(",");
       for(QString StrExec:ExecsList)
       {
           m_QComboBox1->addItem(StrExec.mid(0,StrExec.indexOf(".")));
       }
    }
    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedExec);
        m_QComboBox2->setCurrentText(StrExecState);
        m_QComboBox3->setCurrentText(StrExecStateVal);
    }
    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(Mode==1)
        {
            ui->tableWidget_known_symptom_select->setRowCount(ui->tableWidget_known_symptom_select->rowCount()+1);
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,0,new QTableWidgetItem(m_QComboBox1->currentText()));
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,1,new QTableWidgetItem(m_QComboBox2->currentText()));
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,2,new QTableWidgetItem(m_QComboBox3->currentText()));
        }
        else if(Mode==2)
        {
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),0)->setText(m_QComboBox1->currentText());
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),1)->setText(m_QComboBox2->currentText());
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),2)->setText(m_QComboBox3->currentText());
        }
    }
    else return;
}

void dialogDiagnoseUI::on_toolButton_known_symptom_add_clicked()
{
    AddOrModifyExec(1,"","","");
}

void dialogDiagnoseUI::on_toolButton_not_exit_symptom_modify_clicked()
{
    if(ui->tableWidget_known_symptom_select->currentRow()<0) return;
    AddOrModifyExec(2,ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),0)->text(),ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),1)->text(),ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),2)->text());
}

void dialogDiagnoseUI::on_toolButton_known_symptom_delete_clicked()
{
    if(ui->tableWidget_known_symptom_select->currentRow()<0) return;
    ui->tableWidget_known_symptom_select->removeRow(ui->tableWidget_known_symptom_select->currentRow());
}

//启动诊断，将初始控制量和观测现象发给l2test
void dialogDiagnoseUI::on_toolButton_known_symptom_select_next_clicked()
{
    QString CmdValList;
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+FunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
        CmdValList=QueryFunction.value("CmdValList").toString();
    }
    QString SendCmdStr;
    for(QString StrCmdVal:CmdValList.split(","))
    {
        if(SendCmdStr!="") SendCmdStr+="\r\n";
        SendCmdStr+="progress test."+StrCmdVal;
    }
    for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
    {
        if(SendCmdStr!="") SendCmdStr+="\r\n";
        SendCmdStr+="assign test."+ui->tableWidget_known_symptom_select->item(i,0)->text()+"."+ui->tableWidget_known_symptom_select->item(i,1)->text()+"="+ui->tableWidget_known_symptom_select->item(i,2)->text();
    }
    if(ui->tableWidget_known_symptom_select->rowCount()>0) SendCmdStr+="\r\nfc";
qDebug()<<"SendCmdStr="<<SendCmdStr;
    emit(signalStartDiagnose(SendCmdStr));
    //SetStackIndex(2);
}

//TestPointName:DT
void dialogDiagnoseUI::LoadTestPointInfo(QString TestPointName,QString CurrentInOutName,QStringList ListTermStr)
{
    CurTestPointName=TestPointName+"."+CurrentInOutName;
    QString DT=TestPointName;
    if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        QString Name=QueryEquipment.value("Name").toString()+DT;
        ui->label_diagnosis_test_word->setText("测试："+Name);
        if(CurrentInOutName.contains("ePort_in")) ui->label_test_procedure->setText("检测输入电压");
        if(CurrentInOutName.contains("ePort_out")) ui->label_test_procedure->setText("检测输出电压");
        QString test_description;
        for(int i=0;i<ListTermStr.count();i++)
        {
            if(i>0) test_description+="\r\n";
            if(ListTermStr.at(i).split(",").at(1)=="0")//器件
            {
                QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+ListTermStr.at(i).split(",").at(0);
                QuerySymb2TermInfo.exec(SqlStr);
                if(QuerySymb2TermInfo.next())
                {
                    QString pointDT,pointName;
                    int UnitStripID=GetUnitStripIDByTermID(0,ListTermStr.at(i).split(",").at(0).toInt(),pointDT);
                    SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(UnitStripID);
                    QueryEquipment.exec(SqlStr);
                    if(QueryEquipment.next())
                    {
                        pointName=QueryEquipment.value("Name").toString();
                        QString PolarStr=(i==0)?"正极":"负极";
                        test_description+="万用表"+PolarStr+":"+pointName+pointDT+"."+QuerySymb2TermInfo.value("ConnNum").toString();
                    }
                }
            }
        }
        ui->label_test_description_1->setText(test_description);
    }
    SetStackIndex(2);
}

void dialogDiagnoseUI::on_btm_CalTestResult_clicked()
{
    if(!StrIsDouble(ui->EdInputVal1->text()))
    {
        QMessageBox::warning(nullptr, "提示", " 请输入正确的电压数值！");
        return;
    }
    QString SendCmdStr="assign test.";
    if(ui->EdInputVal1->text().toDouble()<16) SendCmdStr+=CurTestPointName+"=off";
    else SendCmdStr+=CurTestPointName+"=on";
    SendCmdStr+="\r\nfc";
    emit(signalSendCmdStr(SendCmdStr));
}
