#include "dialogusertest.h"
#include "ui_dialogusertest.h"
#include "dialogaddcondition.h"

DialogUserTest::DialogUserTest(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogUserTest)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogUserTest::~DialogUserTest()
{
    delete ui;
}

void DialogUserTest::LoadInfo(QString Name,QStringList ListCondition,QStringList ListTest)
{
    ui->EdTestName->setText(Name);
    ui->listWidget_Condition->clear();
    ui->listWidget_Action->clear();
    ui->listWidget_Condition->addItems(ListCondition);
    ui->listWidget_Action->addItems(ListTest);
}

void DialogUserTest::AddOrModifyObserve(int Mode,QString StrSelectedUnit,QString StrSelectPara)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增观测变量");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改观测变量");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QCheckBox *CbOnlyExec=new QCheckBox(nullptr);
    CbOnlyExec->setText("只选择执行器");
    CbOnlyExec->setChecked(true);
    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("观测对象");
    m_label1->setMaximumWidth(50);
    qxcombobox *m_QComboBox1 = new qxcombobox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);
qDebug()<<"StrSystemDefine="<<StrSystemDefine;
    m_QComboBox1->StrSystemDefine=StrSystemDefine;
    //m_QComboBox1->CurExecsList=CurExecsList;
    //connect(CbOnlyExec,SIGNAL(clicked(bool)),m_QComboBox1,SLOT(UpdateUserItems(bool)));

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    m_label2->setText("观测变量");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    /*
    QHBoxLayout *linelayout3= new QHBoxLayout(nullptr);
    QLabel *m_label3 = new QLabel(dialogNewExec);
    m_label3->setText("观测值");
    m_label3->setMaximumWidth(50);
    qxcombobox *m_QComboBox3 = new qxcombobox(dialogNewExec);
    linelayout3->addWidget(m_label3);
    linelayout3->addWidget(m_QComboBox3);
    */

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addWidget(CbOnlyExec);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);
    //layout3->addLayout(linelayout3);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecStateItems(QString)));
    //QObject::connect(m_QComboBox2,SIGNAL(currentTextChanged(QString)),m_QComboBox3,SLOT(UpdateExecStateValueItems(QString)));
    m_QComboBox1->Mode=Mode;
    for(int i=0;i<CurExecsList.count();i++)
    {
        m_QComboBox1->addItem(CurExecsList.at(i).mid(0,CurExecsList.at(i).indexOf(".")));
        m_QComboBox1->CurExecsList.append(CurExecsList.at(i).mid(0,CurExecsList.at(i).indexOf(".")));
    }
    //m_QComboBox1->UpdateUserItems(true);
    connect(CbOnlyExec,SIGNAL(clicked(bool)),m_QComboBox1,SLOT(UpdateUserItems(bool)));

    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedUnit);
        m_QComboBox2->setCurrentText(StrSelectPara);
        //m_QComboBox3->setCurrentText(StrParaVal);
    }
    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(Mode==1)//HL01.LedState=on
        {
            ui->listWidget_Action->addItem(m_QComboBox1->currentText()+"."+m_QComboBox2->currentText());
        }
        else if(Mode==2)
        {
            ui->listWidget_Action->item(ui->listWidget_Action->currentRow())->setText(m_QComboBox1->currentText()+"."+m_QComboBox2->currentText());
        }
    }
    else return;
}



//添加观测
void DialogUserTest::on_BtnAddObserve_clicked()
{
    AddOrModifyObserve(1,"","");
}

void DialogUserTest::AddOrModifyCondition(int Mode,QString StrSelectedUnit,QString StrSelectedSpur)
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增条件");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改条件");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");


    QCheckBox *CbOnlyExec=new QCheckBox(nullptr);
    CbOnlyExec->setText("只选择执行器");
    CbOnlyExec->setChecked(true);

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("器件名称");
    m_label1->setMaximumWidth(50);
    qxcombobox *m_QComboBox1 = new qxcombobox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    if(ui->CbConditionMode->currentIndex()==2) m_label2->setText("失效模式");
    else m_label2->setText("功能子块");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);
    m_QComboBox2->RbMode=ui->CbConditionMode->currentIndex()+1;

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    if(ui->CbConditionMode->currentIndex()!=2) layout3->addWidget(CbOnlyExec);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateUnitSpurItems(QString)));

    QString tmpStr=StrSystemDefine;
qDebug()<<"tmpStr="<<tmpStr;
    QStringList UnitList=tmpStr.remove("\r\n").split(";");
    for(int i=0;i<UnitList.count();i++)
    {
        UnitList[i]=UnitList.at(i).split(" ").last();
        if(UnitList[i]=="") UnitList.removeAt(i);
    }
    if(ui->CbConditionMode->currentIndex()!=2)
    {
        //m_QComboBox1->addItems(UnitList);
        m_QComboBox1->Mode=Mode;
        for(int i=0;i<CurExecsList.count();i++)
        {
            m_QComboBox1->addItem(CurExecsList.at(i).mid(0,CurExecsList.at(i).indexOf(".")));
            m_QComboBox1->CurExecsList.append(CurExecsList.at(i).mid(0,CurExecsList.at(i).indexOf(".")));
            connect(CbOnlyExec,SIGNAL(clicked(bool)),m_QComboBox1,SLOT(UpdateUserItems(bool)));
        }
    }
    else
    {
        for(int i=0;i<UnitList.count();i++)
        {
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+UnitList.at(i)+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                QStringList SubComponentList=GetSubComponentList(QueryEquipment.value("TModel").toString());
                if(SubComponentList.count()==0) m_QComboBox1->addItem(UnitList.at(i));
                else
                {
                    for(int j=0;j<SubComponentList.count();j++)
                    {
                        m_QComboBox1->addItem(UnitList.at(i)+"."+SubComponentList.at(j).split(",").at(1));
                    }
                }
            }
            else m_QComboBox1->addItem(UnitList.at(i));
        }
    }



    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedUnit);
        m_QComboBox2->setCurrentText(StrSelectedSpur);
    }

    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(ui->CbConditionMode->currentIndex()==0) //候选集包含该器件
        {
            if(Mode==1) ui->listWidget_Condition->addItem(m_QComboBox1->currentText()+(m_QComboBox2->currentText()==""?"":("."+m_QComboBox2->currentText())));
            else ui->listWidget_Condition->item(ui->listWidget_Condition->currentRow())->setText(m_QComboBox1->currentText()+(m_QComboBox2->currentText()==""?"":("."+m_QComboBox2->currentText())));
        }
        else if(ui->CbConditionMode->currentIndex()==1)//存在候选集属于该器件所在单链回路
        {
            QStringList ListExecSpurID;
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+m_QComboBox1->currentText()+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
                QuerySymbol.exec(SqlStr);
                while(QuerySymbol.next())
                {
                    if(m_QComboBox2->currentText()==GetUnitSpurStrBySymbol_ID(QuerySymbol))
                    {
                        ListExecSpurID.append(QuerySymbol.value("Symbol_ID").toString());
                        break;
                    }
                }
            }
            QStringList ListSelectLinkInfo= MakeListFinalLinkInfo(ListExecSpurID);
qDebug()<<"ListSelectLinkInfo="<<ListSelectLinkInfo;
            for(int i=0;i<ListSelectLinkInfo.count();i++)
            {
                if(ListSelectLinkInfo.at(i).split(",").at(1)=="0")//器件
                {
                    ui->listWidget_Condition->addItem(GetSubUnitBySymbolID(ListSelectLinkInfo.at(i).split(",").at(0),"0"));
                }
                else if(ListSelectLinkInfo.at(i).split(",").at(1)=="2")//导线
                {
                    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    SqlStr = "SELECT * FROM JXB WHERE JXB_ID = "+ListSelectLinkInfo.at(i).split(",").at(0);
                    QueryJXB.exec(SqlStr);
                    if(QueryJXB.next())
                    {
                        if(Mode==1)  ui->listWidget_Condition->addItem(QueryJXB.value("ConnectionNumber").toString());
                        else ui->listWidget_Condition->item(ui->listWidget_Condition->currentRow())->setText(QueryJXB.value("ConnectionNumber").toString());
                    }
                }
            }
        }
        else if(ui->CbConditionMode->currentIndex()==2)//故障模式选择
        {
            QString StrUnitDesc;
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+m_QComboBox1->currentText()+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                StrUnitDesc=QueryEquipment.value("TModel").toString();
            }

            QStringList ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal;
            CompileStructure(StrUnitDesc,"",ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal);
            //添加子器件的enum
            QStringList SubComponentList=GetSubComponentList(StrUnitDesc);
            for(QString StrSubComponent:SubComponentList)
            {
                QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
                QString StrSql="SELECT * FROM FunctionDefineClass WHERE TClassName = '"+StrSubComponent.split(",").at(0)+"'";
                QueryFunctionDefineClass.exec(StrSql);
                if(QueryFunctionDefineClass.next())
                {
                    QString SubModuleTModel=QueryFunctionDefineClass.value("TModel").toString();
                    CompileStructure(SubModuleTModel,StrSubComponent.split(",").at(1),ListEnumName,ListEnumTypeName,ListEnumVal,ListIniVal,ListCmdObsVal);
                }
            }
            if(ListEnumTypeName.contains("ModeType"))
            {
                if(Mode==1)  ui->listWidget_Condition->addItem(m_QComboBox1->currentText()+"="+m_QComboBox2->currentText());
                else ui->listWidget_Condition->item(ui->listWidget_Condition->currentRow())->setText(m_QComboBox1->currentText()+"="+m_QComboBox2->currentText());
            }
        }//end of else if(ui->RbModeType->isChecked())//故障模式选择
    }//end of if (dialogNewExec->exec()==QDialog::Accepted)
    else return;
}

void DialogUserTest::on_BtnAddCondition_clicked()
{
    AddOrModifyCondition(1,"","");
}

void DialogUserTest::on_BtnModifyCondition_clicked()
{
    if(ui->listWidget_Condition->currentRow()<0) return;
    QString SelectStr=ui->listWidget_Condition->item(ui->listWidget_Condition->currentRow())->text();
    if(SelectStr.contains("="))//失效模式
    {
        ui->CbConditionMode->setCurrentIndex(2);
        AddOrModifyCondition(2,SelectStr.mid(0,SelectStr.indexOf("=")),SelectStr.mid(SelectStr.indexOf("=")+1,SelectStr.count()-SelectStr.indexOf("=")-1));
    }
    else
    {
        ui->CbConditionMode->setCurrentIndex(0);
        if(SelectStr.contains("."))
          AddOrModifyCondition(2,SelectStr.mid(0,SelectStr.indexOf(".")),SelectStr.mid(SelectStr.indexOf(".")+1,SelectStr.count()-SelectStr.indexOf(".")-1));
        else
          AddOrModifyCondition(2,SelectStr,"");
    }
}

void DialogUserTest::on_BtnDeleteCondition_clicked()
{
    qDebug()<<"currentRow="<<ui->listWidget_Condition->currentRow();
    if(ui->listWidget_Condition->currentRow()<0) return;
    ui->listWidget_Condition->takeItem(ui->listWidget_Condition->currentRow());
}

void DialogUserTest::on_BtnOK_clicked()
{
    Canceled=false;
    StrCondition="";
    for(int i=0;i<ui->listWidget_Condition->count();i++)
    {
        if(StrCondition!="") StrCondition+=",";
        StrCondition+=ui->listWidget_Condition->item(i)->text();
    }
    for(int i=0;i<ui->listWidget_Action->count();i++)
    {
        if(StrActions!="") StrActions+=",";
        StrActions+=ui->listWidget_Action->item(i)->text();
    }
    TestName=ui->EdTestName->text();
    this->close();
}

void DialogUserTest::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}

//添加测试行为
void DialogUserTest::on_BtnAddTest_clicked()
{
    AddOrModifyCmd(1,"","");
}

void DialogUserTest::AddOrModifyCmd(int Mode,QString StrSelectedCmd,QString StrCmdState)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewCmd =new QDialog();
    if(Mode==1) dialogNewCmd->setWindowTitle("新增测试行为");
    else if(Mode==2) dialogNewCmd->setWindowTitle("修改测试行为");
    dialogNewCmd->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewCmd);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewCmd);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewCmd);
    m_label1->setText("控制变量");
    m_label1->setMaximumWidth(50);
    QComboBox *m_QComboBox1 = new QComboBox(dialogNewCmd);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewCmd);
    m_label2->setText("控制值");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewCmd);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewCmd,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateCmdItems(QString)));
    //从数据库读取所有Equipment
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment";
    QueryEquipment.exec(SqlStr);
    while(QueryEquipment.next())
    {
        QString StrUnitDesc=QueryEquipment.value("TModel").toString();
        QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
        for(QString StrStructure:ListStructure)
        {
            if(StrStructure.split(",").at(2)=="Commandable")
                m_QComboBox1->addItem(QueryEquipment.value("DT").toString()+"."+StrStructure.split(",").at(0));
        }
    }
    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedCmd);
        m_QComboBox2->setCurrentText(StrCmdState);
    }
    if (dialogNewCmd->exec()==QDialog::Accepted)
    {
        QString CmdName=m_QComboBox1->currentText();
        QString CmdVal=m_QComboBox2->currentText();
        if(Mode==1)
        {
            ui->listWidget_Action->addItem(CmdName+"="+CmdVal);
        }
        else if(Mode==2)
        {
            ui->listWidget_Action->item(ui->listWidget_Action->currentRow())->setText(CmdName+"="+CmdVal);
        }
    }
    else return;
}

void DialogUserTest::on_BtnModifyTest_clicked()
{
    if(ui->listWidget_Action->currentRow()<0) return;
    QString StrSelected=ui->listWidget_Action->item(ui->listWidget_Action->currentRow())->text();
    if(StrSelected.contains("="))//测试行为
       AddOrModifyCmd(2,StrSelected.mid(0,StrSelected.indexOf("=")),StrSelected.mid(StrSelected.indexOf("=")+1,StrSelected.count()-StrSelected.indexOf("=")-1));
    else
       AddOrModifyCmd(2,StrSelected.mid(0,StrSelected.indexOf(".")),StrSelected.mid(StrSelected.indexOf(".")+1,StrSelected.count()-StrSelected.indexOf(".")-1));
}

void DialogUserTest::on_BtnDeleteTest_clicked()
{
    if(ui->listWidget_Action->currentRow()<0) return;
    ui->listWidget_Action->takeItem(ui->listWidget_Action->currentRow());
}
