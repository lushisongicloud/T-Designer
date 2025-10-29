#include "dialogdiagusertest.h"
#include "ui_dialogdiagusertest.h"

DialogDiagUserTest::DialogDiagUserTest(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogDiagUserTest)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogDiagUserTest::~DialogDiagUserTest()
{
    delete ui;
}

void DialogDiagUserTest::LoadTestList(QStringList ListUserTest)
{
    m_ListUserTest=ListUserTest;
    ui->listWidget->clear();
    for(int i=0;i<ListUserTest.count();i++)
      ui->listWidget->addItem(ListUserTest.at(i).mid(0,ListUserTest.at(i).indexOf(":")));
}

void DialogDiagUserTest::on_listWidget_currentRowChanged(int currentRow)
{
    ui->Test_tableWidget->setRowCount(0);
    QString CurTest=m_ListUserTest.at(currentRow);
    CurTest=CurTest.mid(CurTest.indexOf(":")+1,CurTest.count()-CurTest.indexOf(":")-1);
    QStringList ListTest=CurTest.split(",");
    for(QString StrCurTest:ListTest)
    {
        ui->Test_tableWidget->setRowCount(ui->Test_tableWidget->rowCount()+1);
        if(StrCurTest.contains("="))//行为
        {
           ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,0,new QTableWidgetItem(StrCurTest.mid(0,StrCurTest.lastIndexOf("."))));
           ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,1,new QTableWidgetItem(StrCurTest.mid(StrCurTest.lastIndexOf(".")+1,StrCurTest.lastIndexOf("=")-StrCurTest.lastIndexOf(".")-1)));
           ui->Test_tableWidget->item(ui->Test_tableWidget->rowCount()-1,1)->setData(Qt::WhatsThisRole,"行为");
           ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,2,new QTableWidgetItem(StrCurTest.mid(StrCurTest.lastIndexOf("=")+1,StrCurTest.count()-StrCurTest.lastIndexOf("=")-1)));
        }
        else//观测
        {
            QString EnumName=StrCurTest.mid(StrCurTest.indexOf(".")+1,StrCurTest.count()-StrCurTest.indexOf(".")-1);
            ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,0,new QTableWidgetItem(StrCurTest.mid(0,StrCurTest.indexOf("."))));
            ui->Test_tableWidget->setItem(ui->Test_tableWidget->rowCount()-1,1,new QTableWidgetItem(EnumName));
            ui->Test_tableWidget->item(ui->Test_tableWidget->rowCount()-1,1)->setData(Qt::WhatsThisRole,"观测");
            QString StrUnitDesc;
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+StrCurTest.mid(0,StrCurTest.indexOf("."))+"'";
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

            QComboBox *CbTestVal=new QComboBox();

            CbTestVal->addItems(ListEnumVal.at(ListEnumName.indexOf(EnumName)).split(","));
            ui->Test_tableWidget->setCellWidget(ui->Test_tableWidget->rowCount()-1,2,CbTestVal);
        }
    }
}

void DialogDiagUserTest::on_Button_OK_clicked()
{
    Canceled=false;
    for(int i=0;i<ui->Test_tableWidget->rowCount();i++)
    {
        if(CmdStr!="") CmdStr+="\r\n";
        if(ui->Test_tableWidget->item(i,1)->data(Qt::WhatsThisRole).toString()=="观测")
        {
            QString ObserveState=((QComboBox *)ui->Test_tableWidget->cellWidget(i,2))->currentText();
            CmdStr+="assign test."+ui->Test_tableWidget->item(i,0)->text()+"."+ui->Test_tableWidget->item(i,1)->text()+"="+ObserveState;
        }
        else
        {
            CmdStr+="progress test."+ui->Test_tableWidget->item(i,0)->text()+"."+ui->Test_tableWidget->item(i,1)->text()+"="+ui->Test_tableWidget->item(i,2)->text();
        }
    }
    this->close();
}

void DialogDiagUserTest::on_Button_cancel_clicked()
{
    Canceled=true;
    this->close();
}
