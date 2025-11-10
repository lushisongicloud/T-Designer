#include "dialogfunctionmanage.h"
#include "ui_dialogfunctionmanage.h"
#include "dialogusertest.h"

dialogFunctionManage::dialogFunctionManage(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::dialogFunctionManage)
{
    ui->setupUi(this);
    ui->tableWidgetFunction->setColumnWidth(0,140);//功能名称
    ui->tableWidgetFunction->setColumnWidth(1,300);//控制变量
    ui->tableWidgetFunction->setColumnWidth(2,300);//执行器名称
    ui->tableWidgetFunction->setColumnWidth(3,150);//备注
    ui->tableWidgetFunction->setFocusPolicy(Qt::NoFocus);

    ui->tableWidgetCmd->setColumnWidth(0,200);//控制变量
    ui->tableWidgetCmd->setColumnWidth(1,140);//控制值
    ui->tableWidgetCmd->setFocusPolicy(Qt::NoFocus);

    ui->tableWidgetExec->setColumnWidth(0,200);//执行器名称
    ui->tableWidgetExec->setColumnWidth(1,200);//功能子块
    ui->tableWidgetExec->setFocusPolicy(Qt::NoFocus);

    ui->tableWidgetUsrObserve->setColumnWidth(0,200);//器件名称
    ui->tableWidgetUsrObserve->setColumnWidth(1,200);//变量名称
    ui->tableWidgetUsrObserve->setFocusPolicy(Qt::NoFocus);

    ui->BtnPasteFunc->setEnabled(false);
    LoadFunctionManage();
    ui->tabWidget->setCurrentIndex(0);
    ui->tabWidget->removeTab(1);
}

dialogFunctionManage::~dialogFunctionManage()
{
    delete ui;
}

void dialogFunctionManage::LoadFunctionManage()
{
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function";
    QueryFunction.exec(SqlStr);
    ui->tableWidgetFunction->setRowCount(0);
    while(QueryFunction.next())
    {
       ui->tableWidgetFunction->setRowCount(ui->tableWidgetFunction->rowCount()+1);
       ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,0,new QTableWidgetItem(QueryFunction.value("FunctionName").toString()));
       ui->tableWidgetFunction->item(ui->tableWidgetFunction->rowCount()-1,0)->setData(Qt::UserRole,QueryFunction.value("FunctionID").toString());
       ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,1,new QTableWidgetItem(QueryFunction.value("CmdValList").toString()));
       ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,2,new QTableWidgetItem(QueryFunction.value("ExecsList").toString()));
       ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,3,new QTableWidgetItem(QueryFunction.value("Remark").toString()));
    }
}

void dialogFunctionManage::on_tableWidgetFunction_clicked(const QModelIndex &index)
{
qDebug()<<"on_tableWidgetFunction_clicked";
    if(!index.isValid()) return;
    CurFunctionID=ui->tableWidgetFunction->item(index.row(),0)->data(Qt::UserRole).toString();
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+ui->tableWidgetFunction->item(index.row(),0)->data(Qt::UserRole).toString();
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
       ui->EdFuncName->setText(QueryFunction.value("FunctionName").toString());
       ui->TextFuncRemark->clear();
       ui->TextFuncRemark->append(QueryFunction.value("Remark").toString());
       QStringList CmdValList=QueryFunction.value("CmdValList").toString().split(",");
       ui->tableWidgetCmd->setRowCount(0);
       for(QString CmdValStr:CmdValList)
       {
           //CmdValStr=SP01.currentIn=on
           if(CmdValStr.split("=").count()!=2) continue;
           ui->tableWidgetCmd->setRowCount(ui->tableWidgetCmd->rowCount()+1);
           ui->tableWidgetCmd->setItem(ui->tableWidgetCmd->rowCount()-1,0,new QTableWidgetItem(CmdValStr.split("=").at(0)));
           ui->tableWidgetCmd->setItem(ui->tableWidgetCmd->rowCount()-1,1,new QTableWidgetItem(CmdValStr.split("=").at(1)));
       }

       QStringList ExecsList;
       if(QueryFunction.value("ExecsList").toString()!="") ExecsList=QueryFunction.value("ExecsList").toString().split(",");
       ui->tableWidgetExec->setRowCount(0);
       for(QString ExecStr:ExecsList)
       {
           //ExecStr=HL01
           ui->tableWidgetExec->setRowCount(ui->tableWidgetExec->rowCount()+1);
           ui->tableWidgetExec->setItem(ui->tableWidgetExec->rowCount()-1,0,new QTableWidgetItem(ExecStr.mid(0,ExecStr.indexOf("."))));
           ui->tableWidgetExec->setItem(ui->tableWidgetExec->rowCount()-1,1,new QTableWidgetItem(ExecStr.mid(ExecStr.indexOf(".")+1,ExecStr.count()-ExecStr.indexOf(".")-1)));
       }

       /*
       QStringList UserTest;
       if(QueryFunction.value("UserTest").toString()!="") UserTest=QueryFunction.value("UserTest").toString().split(",");
       ui->tableWidgetUsrObserve->setRowCount(0);
qDebug()<<"UserTest="<<UserTest<<",count="<<UserTest.count();
       for(QString UserTestStr:UserTest)
       {
           //ExecStr=HL01
           ui->tableWidgetUsrObserve->setRowCount(ui->tableWidgetUsrObserve->rowCount()+1);
           ui->tableWidgetUsrObserve->setItem(ui->tableWidgetUsrObserve->rowCount()-1,0,new QTableWidgetItem(UserTestStr.split(".").at(0)));
           ui->tableWidgetUsrObserve->setItem(ui->tableWidgetUsrObserve->rowCount()-1,1,new QTableWidgetItem(UserTestStr.mid(UserTestStr.indexOf(".")+1,UserTestStr.count()-UserTestStr.indexOf(".")-1)));
       }
       */
       ui->tableWidgetUsrTest->setRowCount(0);
       QSqlQuery QueryUserTest = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
       SqlStr = "SELECT * FROM UserTest WHERE FunctionID = "+ui->tableWidgetFunction->item(index.row(),0)->data(Qt::UserRole).toString();
       QueryUserTest.exec(SqlStr);
       while(QueryUserTest.next())
       {
           ui->tableWidgetUsrTest->setRowCount(ui->tableWidgetUsrTest->rowCount()+1);
           ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->rowCount()-1,0,new QTableWidgetItem(QueryUserTest.value("Name").toString()));
           ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->rowCount()-1,1,new QTableWidgetItem(QueryUserTest.value("Condition").toString()));
           ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->rowCount()-1,2,new QTableWidgetItem(QueryUserTest.value("Test").toString()));
       }
    }
qDebug()<<"UpdateSystemDefine";
    UpdateSystemDefine();
}

void dialogFunctionManage::UpdateSystemDefine()
{
    QStringList ListExecSpurID;
    for(int i=0;i<ui->tableWidgetExec->rowCount();i++)
    {
        QString StrSpur="";
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+ui->tableWidgetExec->item(i,0)->text()+"'";
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(GetUnitSpurStrBySymbol_ID(QuerySymbol).split("￤").count()>1)
                {
                    if(ui->tableWidgetExec->item(i,1)->text()==GetUnitSpurStrBySymbol_ID(QuerySymbol))
                    {
                        if(StrSpur!="") StrSpur+=",";
                        StrSpur+=QuerySymbol.value("Symbol_ID").toString();
                    }
                }
                else if(GetUnitSpurStrBySymbol_ID(QuerySymbol)!="")
                {
                    if(ui->tableWidgetExec->item(i,1)->text().remove(" ").split("￤").contains(GetUnitSpurStrBySymbol_ID(QuerySymbol)))
                    {
                        if(StrSpur!="") StrSpur+=",";
                        StrSpur+=QuerySymbol.value("Symbol_ID").toString();
                    }
                }
            }
        }
        ListExecSpurID.append(StrSpur);
    }
qDebug()<<"ListExecSpurID="<<ListExecSpurID;
    QStringList ListFinalLinkInfo=MakeListFinalLinkInfo(ListExecSpurID);

qDebug()<<"重新排序a，ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateEquipmentTModelDiag(ListFinalLinkInfo);//镜像SymbolID对应的元件TModelDiag描述

    StrSystemDefine="\r\nclass Test {\r\n";
    //器件T语言
    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
       ListFinalLinkInfo[i]=ListFinalLinkInfo.at(i).split(",").at(0)+","+ListFinalLinkInfo.at(i).split(",").at(1)+","+ListFinalLinkInfo.at(i).split(",").at(2)+",false,"+ListFinalLinkInfo.at(i).split(",").at(4)+","+ListFinalLinkInfo.at(i).split(",").at(5);
    }
    QString StrLastePort_out;
    QString LastLinkId="0";
    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
        bool FlagSpurIsNew=true;
        if(!CheckIfLinkSpurIsNew(ListFinalLinkInfo,i)) FlagSpurIsNew=false;
        //连接关系
        QString DT=GetComponentDTBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt());
        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),0);
        if(!FlagSpurIsNew) continue;
        if(ListFinalLinkInfo.at(i).split(",").at(3)=="true") continue;
        //将器件实例化添加进StrSystemDefine，将连接关系添加进StrSystemConnection
        StrSystemDefine+="\r\n"+StrTModel.mid(StrTModel.indexOf("class")+5,StrTModel.indexOf("{")-StrTModel.indexOf("class")-5).remove(" ")+" "+DT+";";

        ListFinalLinkInfo[i]=ListFinalLinkInfo.at(i).split(",").at(0)+","+ListFinalLinkInfo.at(i).split(",").at(1)+","+ListFinalLinkInfo.at(i).split(",").at(2)+",true,"+ListFinalLinkInfo.at(i).split(",").at(4)+","+ListFinalLinkInfo.at(i).split(",").at(5);;
        for(int j=i;j<ListFinalLinkInfo.count();j++)
        {
            bool SkipFlag=false;
            if(ListFinalLinkInfo.at(i).split(",").at(1)=="2")
            {
                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(0)==ListFinalLinkInfo.at(i).split(",").at(0)))
                   SkipFlag=true;
            }
            else if(ListFinalLinkInfo.at(i).split(",").at(1)=="3")
            {
                if((ListFinalLinkInfo.at(j).split(",").at(1)=="3")&&(ListFinalLinkInfo.at(j).split(",").at(0)==ListFinalLinkInfo.at(i).split(",").at(0)))
                   SkipFlag=true;
            }
            else
            {
                if(ListFinalLinkInfo.at(j).split(",").at(1)!="2")
                {
                    int idj=GetUnitStripIDBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt());
                    int idi=GetUnitStripIDBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt());

                    if((idj==idi)&&(ListFinalLinkInfo.at(j).split(",").at(1)==ListFinalLinkInfo.at(i).split(",").at(1)))
                        SkipFlag=true;
                }
            }
            if(SkipFlag)
               ListFinalLinkInfo[j]=ListFinalLinkInfo.at(j).split(",").at(0)+","+ListFinalLinkInfo.at(j).split(",").at(1)+","+ListFinalLinkInfo.at(j).split(",").at(2)+",true,"+ListFinalLinkInfo.at(j).split(",").at(4)+","+ListFinalLinkInfo.at(j).split(",").at(5);;
        }
    }
    qDebug()<<"StrSystemDefine="<<StrSystemDefine;
}

void dialogFunctionManage::AddOrModifyCmd(int Mode,QString StrSelectedCmd,QString StrCmdState)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewCmd =new QDialog();
    if(Mode==1) dialogNewCmd->setWindowTitle("新增控制变量");
    else if(Mode==2) dialogNewCmd->setWindowTitle("修改控制变量");
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
        if(StrUnitDesc=="") continue;
qDebug()<<"StrUnitDesc="<<StrUnitDesc;
        QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
qDebug()<<"ListStructure="<<ListStructure;
        for(QString StrStructure:ListStructure)
        {
            if(StrStructure=="") continue;
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
        CmdName=m_QComboBox1->currentText();
        CmdVal=m_QComboBox2->currentText();
        if(Mode==1)
        {
            ui->tableWidgetCmd->setRowCount(ui->tableWidgetCmd->rowCount()+1);
            ui->tableWidgetCmd->setItem(ui->tableWidgetCmd->rowCount()-1,0,new QTableWidgetItem(CmdName));
            ui->tableWidgetCmd->setItem(ui->tableWidgetCmd->rowCount()-1,1,new QTableWidgetItem(CmdVal));
        }
        else if(Mode==2)
        {
            ui->tableWidgetCmd->item(ui->tableWidgetCmd->currentRow(),0)->setText(CmdName);
            ui->tableWidgetCmd->item(ui->tableWidgetCmd->currentRow(),1)->setText(CmdVal);
        }
    }
    else return;

/*




    QDialog *dialogNewCmd =new QDialog();
    if(Mode==1) dialogNewCmd->setWindowTitle("新增控制变量");
    else if(Mode==2) dialogNewCmd->setWindowTitle("修改控制变量");
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
        CmdName=m_QComboBox1->currentText();
        CmdVal=m_QComboBox2->currentText();
        if(Mode==1)
        {
            ui->tableWidgetCmd->setRowCount(ui->tableWidgetCmd->rowCount()+1);
            ui->tableWidgetCmd->setItem(ui->tableWidgetCmd->rowCount()-1,0,new QTableWidgetItem(CmdName));
            ui->tableWidgetCmd->setItem(ui->tableWidgetCmd->rowCount()-1,1,new QTableWidgetItem(CmdVal));
        }
        else if(Mode==2)
        {
            ui->tableWidgetCmd->item(ui->tableWidgetCmd->currentRow(),0)->setText(CmdName);
            ui->tableWidgetCmd->item(ui->tableWidgetCmd->currentRow(),1)->setText(CmdVal);
        }
    }
    else return;*/
}

void dialogFunctionManage::on_BtnAddCmd_clicked()
{
    AddOrModifyCmd(1,"","");
}

void dialogFunctionManage::on_BtnDeleteCmd_clicked()
{
    if(ui->tableWidgetCmd->currentRow()<0) return;
    ui->tableWidgetCmd->removeRow(ui->tableWidgetCmd->currentRow());
}

void dialogFunctionManage::on_BtnModify_clicked()
{
    if(ui->tableWidgetCmd->currentRow()<0) return;
    AddOrModifyCmd(1,ui->tableWidgetCmd->item(ui->tableWidgetCmd->currentRow(),0)->text(),ui->tableWidgetCmd->item(ui->tableWidgetCmd->currentRow(),1)->text());
}

//Mode=1:add Mode=2:modify
void dialogFunctionManage::AddOrModifyUserTest(int Mode,QString StrSelectedUserTest,QString StrUserTestState)
{
    QDialog *dialogUsrTest = new QDialog();
    if(Mode==1) dialogUsrTest->setWindowTitle("新增自定义观测变量");
    else if(Mode==2) dialogUsrTest->setWindowTitle("修改自定义观测变量");
    dialogUsrTest->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUsrTest);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogUsrTest);
    pushbuttonOK->setText("确认");

    QCheckBox *CbOnlyExec=new QCheckBox(nullptr);
    CbOnlyExec->setText("只选择执行器");
    CbOnlyExec->setChecked(true);


    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogUsrTest);
    m_label1->setText("观测对象");
    m_label1->setMaximumWidth(50);
    qxcombobox *m_QComboBox1 = new qxcombobox(dialogUsrTest);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);
    m_QComboBox1->StrSystemDefine=StrSystemDefine;
    for(int i=0;i<ui->tableWidgetExec->rowCount();i++)
    {
        m_QComboBox1->CurExecsList.append(ui->tableWidgetExec->item(i,0)->text()+"."+ui->tableWidgetExec->item(i,1)->text());
    }
    connect(CbOnlyExec,SIGNAL(clicked(bool)),m_QComboBox1,SLOT(UpdateUserItems(bool)));

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogUsrTest);
    m_label2->setText("观测变量");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogUsrTest);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addWidget(CbOnlyExec);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogUsrTest,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecStateItems(QString)));
    for(int i=0;i<ui->tableWidgetUsrObserve->rowCount();i++)
       m_QComboBox1->ExistedUnits.append(ui->tableWidgetUsrObserve->item(i,0)->text());
    m_QComboBox1->Mode=Mode;

    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CurFunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
       QString tmpStr=StrSystemDefine;
       QStringList FunctionUnitList=tmpStr.remove("\r\n").split(";");
       for(int i=0;i<FunctionUnitList.count();i++)
       {
           FunctionUnitList[i]=FunctionUnitList.at(i).split(" ").last();
           if(FunctionUnitList[i]=="") FunctionUnitList.removeAt(i);
       }
qDebug()<<"FunctionUnitList="<<FunctionUnitList;
       if(Mode==2)
       {
           bool SelectExecExist=false;
           for(int i=0;i<QueryFunction.value("ExecsList").toString().split(",").count();i++)
           {
               if(QueryFunction.value("ExecsList").toString().split(",").at(i).contains(StrSelectedUserTest))
               {
                   SelectExecExist=true;
                   break;
               }
           }
           if(!SelectExecExist) CbOnlyExec->setChecked(false);
       }

       QStringList ExecsList;
       if(CbOnlyExec->isChecked()) FunctionUnitList=QueryFunction.value("ExecsList").toString().split(",");

       //去除没有可观测变量的器件
       QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
       for(QString StrFunctionUnit:FunctionUnitList)
       {
           QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+StrFunctionUnit+"'";
           QueryEquipment.exec(SqlStr);
           if(QueryEquipment.next())
           {
              QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
              bool NoObservable=true;
              for(QString StrStructure:ListStructure)
              {
                  if(StrStructure.split(",").at(2)=="Observable") NoObservable=false;
              }
              if(NoObservable) FunctionUnitList.removeAt(FunctionUnitList.indexOf(StrFunctionUnit));
           }
       }
       m_QComboBox1->clear();
       for(QString StrExec:FunctionUnitList)
       {
           bool skip=false;
           if(Mode==1)
           {
               for(int i=0;i<ui->tableWidgetUsrObserve->rowCount();i++)
               {
                   if(StrExec.mid(0,StrExec.indexOf("."))==ui->tableWidgetUsrObserve->item(i,0)->text())
                   {
                       skip=true;
                       break;
                   }
               }
           }
           if(!skip) m_QComboBox1->addItem(StrExec.mid(0,StrExec.indexOf(".")));
       }
    }
    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedUserTest);
        m_QComboBox2->setCurrentText(StrUserTestState);
    }
    if (dialogUsrTest->exec()==QDialog::Accepted)
    {
        if(Mode==1)
        {
            ui->tableWidgetUsrObserve->setRowCount(ui->tableWidgetUsrObserve->rowCount()+1);
            ui->tableWidgetUsrObserve->setItem(ui->tableWidgetUsrObserve->rowCount()-1,0,new QTableWidgetItem(m_QComboBox1->currentText()));
            ui->tableWidgetUsrObserve->setItem(ui->tableWidgetUsrObserve->rowCount()-1,1,new QTableWidgetItem(m_QComboBox2->currentText()));
        }
        else if(Mode==2)
        {
            ui->tableWidgetUsrObserve->item(ui->tableWidgetUsrObserve->currentRow(),0)->setText(m_QComboBox1->currentText());
            ui->tableWidgetUsrObserve->item(ui->tableWidgetUsrObserve->currentRow(),1)->setText(m_QComboBox2->currentText());
        }
    }
    else return;
}

//Mode=1,StrSelectedExec不为空为增加功能子块
//Mode=1,StrSelectedExec为空为增加执行器
//Mode=2,StrSelectedExec不为空为修改执行器
void dialogFunctionManage::AddOrModifyExec(int Mode,QString StrSelectedExec)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增执行器");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改执行器");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QCheckBox *CbOnlyExec=new QCheckBox(nullptr);
    CbOnlyExec->setText("识别系统末端执行（输出）单元");
    CbOnlyExec->setChecked(true);

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("执行器");
    m_label1->setMaximumWidth(50);
    QComboBox *m_QComboBox1 = new QComboBox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    m_label2->setText("功能子块");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addWidget(CbOnlyExec);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecItems(QString)));
    if((Mode==1)&&(StrSelectedExec!="")) m_QComboBox1->addItem(StrSelectedExec);
    else
    {
        QSqlQuery QuerySymbol(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Symbol WHERE ExecConn= TRUE";
        QuerySymbol.exec(StrSql);
        while(QuerySymbol.next())
        {
            QSqlQuery QueryEquipment(T_ProjectDatabase);
            QString StrSql="SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
            QueryEquipment.exec(StrSql);
            if(QueryEquipment.next())
            {
                bool Existed=false;
                for(int i=0;i<m_QComboBox1->count();i++)
                {
                    if(m_QComboBox1->itemText(i)==QueryEquipment.value("DT").toString())
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed) m_QComboBox1->addItem(QueryEquipment.value("DT").toString());//元件名称
            }
        }//GetUnitSpurStrBySymbol_ID(QuerySymbol)
    }

    if(Mode==2) m_QComboBox1->setCurrentText(StrSelectedExec);
    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(Mode==1)
        {
            if(StrSelectedExec=="")
            {
                ui->tableWidgetExec->setRowCount(ui->tableWidgetExec->rowCount()+1);
                ui->tableWidgetExec->setItem(ui->tableWidgetExec->rowCount()-1,0,new QTableWidgetItem(m_QComboBox1->currentText()));
                ui->tableWidgetExec->setItem(ui->tableWidgetExec->rowCount()-1,1,new QTableWidgetItem(m_QComboBox2->currentText()));
            }
            else
            {
                ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),1)->setText(ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),1)->text()+" ￤ "+m_QComboBox2->currentText());
            }
        }
        else if(Mode==2)
        {
            ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),0)->setText(m_QComboBox1->currentText());
            ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),1)->setText(m_QComboBox2->currentText());
        }
    }
    else return;

    /*
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增执行器");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改执行器");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("执行器");
    m_label1->setMaximumWidth(50);
    QComboBox *m_QComboBox1 = new QComboBox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    m_label2->setText("功能子块");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecItems(QString)));
    QSqlQuery QuerySymbol(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symbol WHERE ExecConn= TRUE";
    QuerySymbol.exec(StrSql);
    while(QuerySymbol.next())
    {
        QSqlQuery QueryEquipment(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
        QueryEquipment.exec(StrSql);
        if(QueryEquipment.next())
        {
            m_QComboBox1->addItem(QueryEquipment.value("DT").toString());//元件名称
        }
    }//GetUnitSpurStrBySymbol_ID(QuerySymbol)
    if(Mode==2) m_QComboBox1->setCurrentText(StrSelectedExec);
    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(Mode==1)
        {
            ui->tableWidgetExec->setRowCount(ui->tableWidgetExec->rowCount()+1);
            ui->tableWidgetExec->setItem(ui->tableWidgetExec->rowCount()-1,0,new QTableWidgetItem(m_QComboBox1->currentText()));
            ui->tableWidgetExec->setItem(ui->tableWidgetExec->rowCount()-1,1,new QTableWidgetItem(m_QComboBox2->currentText()));
        }
        else if(Mode==2)
        {
            ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),0)->setText(m_QComboBox1->currentText());
            ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),1)->setText(m_QComboBox2->currentText());
        }
    }
    else return;*/
}

void dialogFunctionManage::on_BtnAddExec_clicked()
{
    AddOrModifyExec(1,"");
    UpdateSystemDefine();
}

void dialogFunctionManage::on_BtnExecModify_clicked()
{
    if(ui->tableWidgetExec->currentRow()<0) return;
    AddOrModifyExec(2,ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),0)->text());
    UpdateSystemDefine();
}

void dialogFunctionManage::on_BtnDeleteExec_clicked()
{
    if(ui->tableWidgetExec->currentRow()<0) return;
    ui->tableWidgetExec->removeRow(ui->tableWidgetExec->currentRow());
    UpdateSystemDefine();
}

void dialogFunctionManage::on_BtnClose_clicked()
{
    this->close();
}

void dialogFunctionManage::on_BtnApply_clicked()
{
    if(ui->tableWidgetFunction->currentRow()<0) return;
    QSqlQuery QueryFunction(T_ProjectDatabase);
    QString CurrentFunctionID=ui->tableWidgetFunction->item(ui->tableWidgetFunction->currentRow(),0)->data(Qt::UserRole).toString();
    if(ui->EdFuncName->text()=="")
    {
        QMessageBox::information(this, "提示信息","功能名称不能为空!", QMessageBox::Yes);
        return;
    }
    if(ui->tableWidgetFunction->currentRow()>=0)
    {

        QString StrSql="SELECT * FROM Function WHERE FunctionID <> "+CurrentFunctionID+" AND FunctionName = '"+ui->EdFuncName->text()+"'";
        QueryFunction.exec(StrSql);
        if(QueryFunction.next())
        {
            QMessageBox::information(this, "提示信息","功能名称已存在!", QMessageBox::Yes);
            return;
        }
    }
    QString tempSQL="UPDATE Function SET FunctionName=:FunctionName,ExecsList=:ExecsList,CmdValList=:CmdValList,Remark=:Remark WHERE FunctionID = "+CurrentFunctionID;
    QueryFunction.prepare(tempSQL);
    QueryFunction.bindValue(":FunctionName",ui->EdFuncName->text());
    QString ExecsList;
    for(int i=0;i<ui->tableWidgetExec->rowCount();i++)
    {
       if(i!=0) ExecsList+=",";
       ExecsList+=ui->tableWidgetExec->item(i,0)->text()+"."+ui->tableWidgetExec->item(i,1)->text();
    }
    QueryFunction.bindValue(":ExecsList",ExecsList);
    QString CmdValList;
    for(int i=0;i<ui->tableWidgetCmd->rowCount();i++)
    {
       if(i!=0) CmdValList+=",";
       CmdValList+=ui->tableWidgetCmd->item(i,0)->text()+"="+ui->tableWidgetCmd->item(i,1)->text();
    }
    QueryFunction.bindValue(":CmdValList",CmdValList);

    QueryFunction.bindValue(":Remark",ui->TextFuncRemark->toPlainText());
    QueryFunction.exec();

    QSqlQuery QueryUserTest(T_ProjectDatabase);
    tempSQL="DELETE FROM UserTest WHERE FunctionID = '"+CurrentFunctionID+"'";
    QueryUserTest.exec(tempSQL);
qDebug()<<"tableWidgetUsrTest->rowCount()="<<ui->tableWidgetUsrTest->rowCount();
    for(int i=0;i<ui->tableWidgetUsrTest->rowCount();i++)
    {
qDebug()<<"insert INTO UserTest";
        tempSQL =  "INSERT INTO UserTest (UserTestID,FunctionID,Name,Condition,Test)"
                        "VALUES (:UserTestID,:FunctionID,:Name,:Condition,:Test)";
        QueryUserTest.prepare(tempSQL);
        QueryUserTest.bindValue(":UserTestID",GetMaxIDOfDB(T_ProjectDatabase,"UserTest","UserTestID"));
        QueryUserTest.bindValue(":FunctionID",CurrentFunctionID);
        QueryUserTest.bindValue(":Name",ui->tableWidgetUsrTest->item(i,0)->text());
        QueryUserTest.bindValue(":Condition",ui->tableWidgetUsrTest->item(i,1)->text());
        QueryUserTest.bindValue(":Test",ui->tableWidgetUsrTest->item(i,2)->text());
        QueryUserTest.exec();
    }

    LoadFunctionManage();
    for(int i=0;i<ui->tableWidgetFunction->rowCount();i++)
    {
        if(ui->tableWidgetFunction->item(i,0)->data(Qt::UserRole).toString()==CurFunctionID)
        {
            on_tableWidgetFunction_clicked(ui->tableWidgetFunction->model()->index(i,0));
            break;
        }
    }
}

void dialogFunctionManage::on_BtnAddFunc_clicked()
{
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "INSERT INTO Function (FunctionID,FunctionName,ExecsList,CmdValList,Remark)"
                      "VALUES (:FunctionID,:FunctionName,:ExecsList,:CmdValList,:Remark)";
    QueryFunction.prepare(SqlStr);
    int MaxFunctionID=GetMaxIDOfDB(T_ProjectDatabase,"Function","FunctionID");
    QueryFunction.bindValue(":FunctionID",QString::number(MaxFunctionID));
    QueryFunction.bindValue(":FunctionName",ui->EdFuncName->text());
    QString ExecsList;
    for(int i=0;i<ui->tableWidgetExec->rowCount();i++)
    {
       if(i!=0) ExecsList+=",";
       ExecsList+=ui->tableWidgetExec->item(i,0)->text();
    }
    QueryFunction.bindValue(":ExecsList",ExecsList);
    QString CmdValList;
    for(int i=0;i<ui->tableWidgetCmd->rowCount();i++)
    {
       if(i!=0) CmdValList+=",";
       CmdValList+=ui->tableWidgetCmd->item(i,0)->text()+"="+ui->tableWidgetCmd->item(i,1)->text();
    }
    QueryFunction.bindValue(":CmdValList",CmdValList);

    QueryFunction.bindValue(":Remark",ui->TextFuncRemark->toPlainText());
    QueryFunction.exec();
    LoadFunctionManage();
    for(int i=0;i<ui->tableWidgetFunction->rowCount();i++)
    {
        if(ui->tableWidgetFunction->item(i,0)->data(Qt::UserRole).toString()==QString::number(MaxFunctionID))
        {
            on_tableWidgetFunction_clicked(ui->tableWidgetFunction->model()->index(i,0));
            break;
        }
    }
}

void dialogFunctionManage::on_BtnDeleteFunc_clicked()
{
    if(ui->tableWidgetFunction->currentRow()<0) return;
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "DELETE FROM Function WHERE FunctionID = "+ui->tableWidgetFunction->item(ui->tableWidgetFunction->currentRow(),0)->data(Qt::UserRole).toString();
    QueryFunction.exec(SqlStr);
    LoadFunctionManage();
    if(ui->tableWidgetFunction->rowCount()>0)  on_tableWidgetFunction_clicked(ui->tableWidgetFunction->model()->index(0,0));
}

void dialogFunctionManage::on_BtnCopyFunc_clicked()
{
    if(ui->tableWidgetFunction->currentRow()<0) return;
    ui->BtnPasteFunc->setEnabled(true);
    CopyFunctionID=ui->tableWidgetFunction->item(ui->tableWidgetFunction->currentRow(),0)->data(Qt::UserRole).toString();
}

void dialogFunctionManage::on_BtnPasteFunc_clicked()
{
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CopyFunctionID;
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next())
    {
        QMessageBox::warning(nullptr, "提示", " 复制功能不存在！");
        return;
    }

    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "INSERT INTO Function (FunctionID,FunctionName,ExecsList,CmdValList,Remark)"
                      "VALUES (:FunctionID,:FunctionName,:ExecsList,:CmdValList,:Remark)";
    QueryFunction.prepare(SqlStr);
    int MaxFunctionID=GetMaxIDOfDB(T_ProjectDatabase,"Function","FunctionID");
    QueryFunction.bindValue(":FunctionID",QString::number(MaxFunctionID));
    QueryFunction.bindValue(":FunctionName",QuerySearch.value("FunctionName").toString()+"副本");
    QueryFunction.bindValue(":ExecsList",QuerySearch.value("ExecsList").toString());
    QueryFunction.bindValue(":CmdValList",QuerySearch.value("CmdValList").toString());
    QueryFunction.bindValue(":Remark",QuerySearch.value("Remark").toString());
    QueryFunction.exec();
    ui->tableWidgetFunction->setCurrentIndex(ui->tableWidgetFunction->model()->index(ui->tableWidgetFunction->rowCount()-1,0));
    on_tableWidgetFunction_clicked(ui->tableWidgetFunction->currentIndex());
}

void dialogFunctionManage::on_BtnAddUserTest_clicked()
{
   AddOrModifyUserTest(1,"","");
}

void dialogFunctionManage::on_BtnModifyUserTest_clicked()
{
   AddOrModifyUserTest(2,ui->tableWidgetUsrObserve->item(ui->tableWidgetUsrObserve->currentRow(),0)->text(),ui->tableWidgetUsrObserve->item(ui->tableWidgetUsrObserve->currentRow(),1)->text());
}

void dialogFunctionManage::on_BtnDeleteUserTest_clicked()
{
    if(ui->tableWidgetUsrObserve->currentRow()<0) return;
    ui->tableWidgetUsrObserve->removeRow(ui->tableWidgetUsrObserve->currentRow());
}

void dialogFunctionManage::on_BtnAddUserMannulTest_clicked()
{
    DialogUserTest *dlg=new DialogUserTest();
    dlg->setWindowTitle("添加自定义测试");
    dlg->StrSystemDefine=StrSystemDefine;
    dlg->CurExecsList.clear();
    for(int i=0;i<ui->tableWidgetExec->rowCount();i++)
    {
        dlg->CurExecsList.append(ui->tableWidgetExec->item(i,0)->text()+"."+ui->tableWidgetExec->item(i,1)->text());
    }
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
       ui->tableWidgetUsrTest->setRowCount(ui->tableWidgetUsrTest->rowCount()+1);
       ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->rowCount()-1,0,new QTableWidgetItem(dlg->TestName));
       ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->rowCount()-1,1,new QTableWidgetItem(dlg->StrCondition));
       ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->rowCount()-1,2,new QTableWidgetItem(dlg->StrActions));
    }
    delete dlg;
}

void dialogFunctionManage::on_BtnModifyUserMannulTest_clicked()
{
    if(ui->tableWidgetUsrTest->currentRow()<0) return;
    DialogUserTest *dlg=new DialogUserTest();
    dlg->setWindowTitle("修改自定义测试");
    QStringList ListCondition,ListTest;
    if(ui->tableWidgetUsrTest->item(ui->tableWidgetUsrTest->currentRow(),1)->text()!="")
       ListCondition=ui->tableWidgetUsrTest->item(ui->tableWidgetUsrTest->currentRow(),1)->text().split(",");
    if(ui->tableWidgetUsrTest->item(ui->tableWidgetUsrTest->currentRow(),2)->text()!="")
       ListTest=ui->tableWidgetUsrTest->item(ui->tableWidgetUsrTest->currentRow(),2)->text().split(",");
    dlg->LoadInfo(ui->tableWidgetUsrTest->item(ui->tableWidgetUsrTest->currentRow(),0)->text(),ListCondition,ListTest);
    dlg->StrSystemDefine=StrSystemDefine;
    dlg->CurExecsList.clear();
    for(int i=0;i<ui->tableWidgetExec->rowCount();i++)
    {
        dlg->CurExecsList.append(ui->tableWidgetExec->item(i,0)->text()+"."+ui->tableWidgetExec->item(i,1)->text());
    }
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
       ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->currentRow(),0,new QTableWidgetItem(dlg->TestName));
       ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->currentRow(),1,new QTableWidgetItem(dlg->StrCondition));
       ui->tableWidgetUsrTest->setItem(ui->tableWidgetUsrTest->currentRow(),2,new QTableWidgetItem(dlg->StrActions));
    }
    delete dlg;
}


void dialogFunctionManage::on_BtnDeleteMannulTest_clicked()
{
    if(ui->tableWidgetUsrTest->currentRow()<0) return;
    ui->tableWidgetUsrTest->removeRow(ui->tableWidgetUsrTest->currentRow());
}

void dialogFunctionManage::on_BtnAddSpur_clicked()
{
    if(ui->tableWidgetExec->currentRow()<0) return;
    AddOrModifyExec(1,ui->tableWidgetExec->item(ui->tableWidgetExec->currentRow(),0)->text());
    UpdateSystemDefine();
}
