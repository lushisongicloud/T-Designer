#include "dialogaddcondition.h"
#include "ui_dialogaddcondition.h"

DialogAddCondition::DialogAddCondition(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogAddCondition)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogAddCondition::~DialogAddCondition()
{
    delete ui;
}

void DialogAddCondition::on_BtnAddCondition_clicked()
{
   AddOrModifyCondition(1,"","");
}

void DialogAddCondition::LoadCurCondition(QString CurCondition)
{
    ui->listWidget->addItem(CurCondition);
}

//Mode=1:add Mode=2:modify
void DialogAddCondition::AddOrModifyCondition(int Mode,QString StrSelectedUnit,QString StrSelectedSpur)
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增条件");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改条件");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("器件名称");
    m_label1->setMaximumWidth(50);
    QComboBox *m_QComboBox1 = new QComboBox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    if(ui->RbModeType->isChecked()) m_label2->setText("失效模式");
    else m_label2->setText("功能子块");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);
    if(ui->RbIncludeUnit->isChecked()) m_QComboBox2->RbMode=1;
    else if(ui->RbBelongLink->isChecked()) m_QComboBox2->RbMode=2;
    else if(ui->RbModeType->isChecked()) m_QComboBox2->RbMode=3;

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateUnitSpurItems(QString)));

    QString tmpStr=StrSystemDefine;
    QStringList UnitList=tmpStr.remove("\r\n").split(";");
    for(int i=0;i<UnitList.count();i++)
    {
        UnitList[i]=UnitList.at(i).split(" ").last();
        if(UnitList[i]=="") UnitList.removeAt(i);
    }
    m_QComboBox1->addItems(UnitList);
    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedUnit);
        m_QComboBox2->setCurrentText(StrSelectedSpur);
    }

    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        ui->listWidget->clear();
        if(ui->RbIncludeUnit->isChecked()) //候选集包含该器件
        {
            if(Mode==1) ui->listWidget->addItem(m_QComboBox1->currentText()+(m_QComboBox2->currentText()==""?"":("."+m_QComboBox2->currentText())));
            else ui->listWidget->item(ui->listWidget->currentRow())->setText(m_QComboBox1->currentText()+(m_QComboBox2->currentText()==""?"":("."+m_QComboBox2->currentText())));
        }
        else if(ui->RbBelongLink->isChecked())//存在候选集属于该器件所在单链回路
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
            for(int i=0;i<ListSelectLinkInfo.count();i++)
            {
                if(ListSelectLinkInfo.at(i).split(",").at(1)=="0")//器件
                {
                    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+ListSelectLinkInfo.at(i).split(",").at(0);
                    QuerySymbol.exec(SqlStr);
                    if(QuerySymbol.next())
                    {
                        if(Mode==1) ui->listWidget->addItem(GetComponentDTBySymbolID(ListSelectLinkInfo.at(i).split(",").at(0),ListSelectLinkInfo.at(i).split(",").at(1).toInt())+"."+GetUnitSpurStrBySymbol_ID(QuerySymbol));
                        else ui->listWidget->item(ui->listWidget->currentRow())->setText(GetComponentDTBySymbolID(ListSelectLinkInfo.at(i).split(",").at(0),ListSelectLinkInfo.at(i).split(",").at(1).toInt())+"."+GetUnitSpurStrBySymbol_ID(QuerySymbol));
                    }
                }
                else if(ListSelectLinkInfo.at(i).split(",").at(1)=="2")//导线
                {
                    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    SqlStr = "SELECT * FROM JXB WHERE JXB_ID = "+ListSelectLinkInfo.at(i).split(",").at(0);
                    QueryJXB.exec(SqlStr);
                    if(QueryJXB.next())
                    {
                        if(Mode==1)  ui->listWidget->addItem(QueryJXB.value("ConnectionNumber").toString());
                        else ui->listWidget->item(ui->listWidget->currentRow())->setText(QueryJXB.value("ConnectionNumber").toString());
                    }
                }
            }
        }
        else if(ui->RbModeType->isChecked())//故障模式选择
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
                if(Mode==1)  ui->listWidget->addItem(m_QComboBox1->currentText()+"."+ListEnumName.at(ListEnumTypeName.indexOf("ModeType"))+"="+m_QComboBox2->currentText());
                else ui->listWidget->item(ui->listWidget->currentRow())->setText(m_QComboBox1->currentText()+"."+ListEnumName.at(ListEnumTypeName.indexOf("ModeType"))+"="+m_QComboBox2->currentText());
            }
        }//end of else if(ui->RbModeType->isChecked())//故障模式选择
    }//end of if (dialogNewExec->exec()==QDialog::Accepted)
    else return;
}

//候选集包含该器件 KA01.11 ￤ 14
//存在候选集属于该器件所在单链回路 KA01.11 ￤ 14
//故障模式选择 KA01.mode=tripped
void DialogAddCondition::on_BtnModifyCondition_clicked()
{
    if(ui->listWidget->currentRow()<0) return;
    QString StrSelected=ui->listWidget->item(ui->listWidget->currentRow())->text();
    if(StrSelected.contains("="))
        AddOrModifyCondition(2,StrSelected.mid(0,StrSelected.indexOf(".")),StrSelected.mid(StrSelected.indexOf("=")+1,StrSelected.count()-StrSelected.indexOf("=")-1));
    else
        AddOrModifyCondition(2,StrSelected.mid(0,StrSelected.indexOf(".")),StrSelected.mid(StrSelected.indexOf(".")+1,StrSelected.count()-StrSelected.indexOf(".")-1));
}

void DialogAddCondition::on_BtnOK_clicked()
{
    Canceled=false;
    ListCondition.clear();
    for(int i=0;i<ui->listWidget->count();i++)
    {
        ListCondition.append(ui->listWidget->item(i)->text());
    }
    this->close();
}

void DialogAddCondition::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}

void DialogAddCondition::on_BtnDeleteCondition_clicked()
{
    if(ui->listWidget->currentRow()<0) return;
    ui->listWidget->takeItem(ui->listWidget->currentRow());
}
