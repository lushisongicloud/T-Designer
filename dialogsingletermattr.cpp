#include "dialogsingletermattr.h"
#include "ui_dialogsingletermattr.h"

DialogSingleTermAttr::DialogSingleTermAttr(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogSingleTermAttr)
{
    ui->setupUi(this);
    ui->tableWidget->setRowCount(5);
    ui->tableWidget->setItem(0,0,new QTableWidgetItem("型号")); ui->tableWidget->setItem(0,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(1,0,new QTableWidgetItem("名称")); ui->tableWidget->setItem(1,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(2,0,new QTableWidgetItem("厂家")); ui->tableWidget->setItem(2,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(3,0,new QTableWidgetItem("订货号")); ui->tableWidget->setItem(3,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(4,0,new QTableWidgetItem("功能文本")); ui->tableWidget->setItem(4,1,new QTableWidgetItem(""));

    /*ui->CbTerminalType->clear();
    ui->CbTerminalType->addItem("");
    ui->CbTerminalType->addItem("电阻端子");
    ui->CbTerminalType->addItem("二极管端子");
    ui->CbTerminalType->addItem("隔离端子");
    ui->CbTerminalType->addItem("贯通式端子");
    ui->CbTerminalType->addItem("开关端子");
    ui->CbTerminalType->addItem("熔断器端子");*/
    Canceled=true;
}

DialogSingleTermAttr::~DialogSingleTermAttr()
{
    delete ui;
}

void DialogSingleTermAttr::SetCbShowTagVisible(bool visible)
{
    ui->CbShowTag->setVisible(visible);
}

void DialogSingleTermAttr::LoadInfo(int Terminal_ID,int TerminalInstanceID)
{
   if(TerminalInstanceID>0) ui->groupBox->setVisible(true);
   else ui->groupBox->setVisible(false);
qDebug()<<"LoadInfo,Terminal_ID="<<Terminal_ID<<",TerminalInstanceID="<<TerminalInstanceID;
   CurTerminal_ID=QString::number(Terminal_ID);
   CurTerminalInstanceID=QString::number(TerminalInstanceID);
   QSqlQuery QueryTerminal= QSqlQuery(T_ProjectDatabase);
   QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+CurTerminal_ID;
   QueryTerminal.exec(SqlStr);
   if(!QueryTerminal.next()) return;

   //查找TerminalStrip
   QSqlQuery QueryTerminalStrip= QSqlQuery(T_ProjectDatabase);
   SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QueryTerminal.value("TerminalStrip_ID").toString();
   QueryTerminalStrip.exec(SqlStr);
   if(!QueryTerminalStrip.next()) return;
   QString TerminalTag=QueryTerminalStrip.value("DT").toString();
   StrProTag=GetProjectStructureStrByProjectStructureID(QueryTerminalStrip.value("ProjectStructure_ID").toInt());//"+"+StrPos;
   ui->LbProTag->setText(StrProTag+"-"+TerminalTag);
   ui->EdTerminalTag->setText(TerminalTag);
   ui->EdDesignation->setText(QueryTerminal.value("Designation").toString());
   ui->LbPartCode->setText(QueryTerminal.value("PartCode").toString());
   //ui->CbTerminalType->setCurrentText(QueryTerminal.value("Terminalfunction").toString());
   ui->LbTerminalFunction->setText(QueryTerminal.value("FunDefine").toString());
   ui->tableWidget->item(0,1)->setText(QueryTerminal.value("TerminalType").toString());
   ui->tableWidget->item(1,1)->setText(QueryTerminal.value("TerminalName").toString());
   ui->tableWidget->item(2,1)->setText(QueryTerminal.value("Factory").toString());
   ui->tableWidget->item(3,1)->setText(QueryTerminal.value("OrderNum").toString());
   ui->tableWidget->item(4,1)->setText(QueryTerminal.value("FunctionText").toString());
   StrSymbolName=QueryTerminal.value("Symbol").toString();
qDebug()<<"ui->groupBox->isVisible()="<<ui->groupBox->isVisible();
   if(TerminalInstanceID>0)
   {
       if(ui->LbTerminalFunction->text()=="3个连接点")
       {
           ui->widget_UpDownTerm->setVisible(true);
           ui->CbLeftTerm->addItems({"","1","2","3"});
           ui->CbRightTerm->addItems({"","1","2","3"});
           ui->CbUpTerm->addItems({"","1","2","3"});
           ui->CbDownTerm->addItems({"","1","2","3"});
       }
       else if(ui->LbTerminalFunction->text()=="4个连接点")
       {
           ui->widget_UpDownTerm->setVisible(true);
           ui->CbLeftTerm->addItems({"","1","2","3","4"});
           ui->CbRightTerm->addItems({"","1","2","3","4"});
           ui->CbUpTerm->addItems({"","1","2","3","4"});
           ui->CbDownTerm->addItems({"","1","2","3","4"});
       }
       else if(ui->LbTerminalFunction->text()=="2个连接点")
       {
           ui->widget_UpDownTerm->setVisible(false);
           ui->CbLeftTerm->addItems({"","1","2"});
           ui->CbRightTerm->addItems({"","1","2"});
           ui->CbUpTerm->addItems({"","1","2"});
           ui->CbDownTerm->addItems({"","1","2"});
       }
       QSqlQuery QueryTerminalInstance= QSqlQuery(T_ProjectDatabase);
       QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+QString::number(TerminalInstanceID);
       QueryTerminalInstance.exec(SqlStr);
       if(QueryTerminalInstance.next())
       {
           ui->CbLeftTerm->setCurrentText(QueryTerminalInstance.value("LeftTerm").toString());
           ui->CbRightTerm->setCurrentText(QueryTerminalInstance.value("RightTerm").toString());
           if(ui->LbTerminalFunction->text()=="2个连接点")
           {
               ui->CbUpTerm->setCurrentText("");
               ui->CbDownTerm->setCurrentText("");
           }
           else
           {
               ui->CbUpTerm->setCurrentText(QueryTerminalInstance.value("UpTerm").toString());
               ui->CbDownTerm->setCurrentText(QueryTerminalInstance.value("DownTerm").toString());
           }
           ui->CbShowTag->setChecked(TerminalTagVisible);
       }
   }
   /*
   QString PathDwg;
   if(StrSymbolName.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+StrSymbolName+".dwg";
   else if(StrSymbolName.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+StrSymbolName+".dwg";
   UnitSymbolsView(PathDwg,"C:/TBD/data/TempImage/"+StrSymbolName+".jpg",ui->LbTerminalJpg,true);
   LoadCbSymbolPattern(StrSymbolName,ui->CbTerminalSymbolPattern);*/

   /*
   //端号
   QSqlQuery QueryTerminalTerm= QSqlQuery(T_ProjectDatabase);
   SqlStr="SELECT * FROM TerminalTerm WHERE Terminal_ID= '"+QString::number(Terminal_ID)+"' ORDER BY TerminalTerm_ID";
   QueryTerminalTerm.exec(SqlStr);
   while(QueryTerminalTerm.next())
   {
      ui->tableWidget_Term->setRowCount(ui->tableWidget_Term->rowCount()+1);
      ui->tableWidget_Term->setItem(ui->tableWidget_Term->rowCount()-1,0,new QTableWidgetItem(QueryTerminalTerm.value("ConnNum_Logic").toString()));
      ui->tableWidget_Term->setItem(ui->tableWidget_Term->rowCount()-1,1,new QTableWidgetItem(QueryTerminalTerm.value("ConnNum").toString()));
      ui->tableWidget_Term->item(ui->tableWidget_Term->rowCount()-1,0)->setFlags(ui->tableWidget_Term->item(ui->tableWidget_Term->rowCount()-1,0)->flags()&(~Qt::ItemIsEditable));
   }*/
}

void DialogSingleTermAttr::on_BtnProSet_clicked()
{
    dlgPageNameSet.LoadTable(ui->LbProTag->text(),2);//Mode=1:Page项目代号  Mode=2:Unit项目代号  Mode=3:Terminal项目代号
    dlgPageNameSet.HideEdPageName();
    dlgPageNameSet.setModal(true);
    dlgPageNameSet.show();
    dlgPageNameSet.exec();
    if(!dlgPageNameSet.Canceled)
    {
        StrProTag=dlgPageNameSet.ReturnTerminalPro;
        ui->LbProTag->setText(StrProTag+"-"+ui->EdTerminalTag->text());
    }
}

void DialogSingleTermAttr::on_BtnOK_clicked()
{
    /*
    if(ui->EdTerminalTag->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", "端子排代号不能为空");
        return;
    }*/
    if(ui->EdDesignation->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", " 端子序号不能为空");
        return;
    }

    Canceled=false;
/*
    QString GaocengStr,PosStr;
    QString TmpStr=ui->LbProTag->text();
    int indexGaoceng=TmpStr.indexOf("=");
    int indexPos=TmpStr.indexOf("+");
    int indexUnit=TmpStr.indexOf("-");
    if(indexGaoceng>=0) GaocengStr=TmpStr.mid(indexGaoceng+1,indexPos-indexGaoceng-1);
    if(indexPos>=0) PosStr=TmpStr.mid(indexPos+1,indexUnit-indexPos-1);
    NewProjectStructure_ID=InsertRecordToProjectStructure(0,GaocengStr,PosStr,"");


    QSqlQuery QueryTerminal= QSqlQuery(T_ProjectDatabase);
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    int TerminalStrip_ID=0;
    QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+CurTerminal_ID;
    QueryTerminal.exec(SqlStr);
    if(QueryTerminal.next())
    {
        TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toInt();
        //查找TerminalStrip
        QSqlQuery QueryTerminalStrip= QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QueryTerminal.value("TerminalStrip_ID").toString();
        QueryTerminalStrip.exec(SqlStr);
        if(QueryTerminalStrip.next())
        {
            //如果DT与数据库中的记录不同或NewProjectStructure_ID与数据库中的记录不同,则更新TeminalStrip
            bool UpdateTerminalStrip=false;
            if(ui->EdTerminalTag->text()!=QueryTerminalStrip.value("DT").toString())
            {
                DTChanged=true;
                UpdateTerminalStrip=true;
            }
            if(NewProjectStructure_ID!=QueryTerminalStrip.value("ProjectStructure_ID").toInt()) UpdateTerminalStrip=true;
            if(UpdateTerminalStrip)
            {
                //这里区分是否为唯一功能子块，如果是唯一功能子块，则修改元件代号，反之则新建或者合并代号
                QSqlQuery QuerySearch= QSqlQuery(T_ProjectDatabase);
                SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QString::number(TerminalStrip_ID)+"'";
                QuerySearch.exec(SqlStr);
                QuerySearch.last();
                if(QuerySearch.at()>0)//不是唯一功能子块，查看新代号和位置是否与其他元件重复，如果重复则合并器件，反之则新建元件
                {
                    SqlStr="SELECT * FROM Terminal WHERE DT = '"+ui->EdTerminalTag->text()+"' AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"' AND TerminalStrip_ID <> "+QString::number(TerminalStrip_ID);
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        SqlStr="UPDATE Terminal SET TerminalStrip_ID=:TerminalStrip_ID WHERE Terminal_ID = "+CurTerminal_ID;
                        QueryVar.prepare(SqlStr);
                        TerminalStrip_ID=QuerySearch.value("TerminalStrip_ID").toInt();
                        QueryVar.bindValue(":TerminalStrip_ID",QuerySearch.value("TerminalStrip_ID").toString());
                        QueryVar.exec();
                    }
                    else//新建器件
                    {
                        SqlStr = QString("INSERT INTO TerminalStrip (TerminalStrip_ID,DT,ProjectStructure_ID) VALUES (:TerminalStrip_ID,:DT,:ProjectStructure_ID)");
                        QueryVar.prepare(SqlStr);
                        TerminalStrip_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalStrip","TerminalStrip_ID");
                        QueryVar.bindValue(":TerminalStrip_ID",TerminalStrip_ID);
                        QueryVar.bindValue(":DT",ui->EdTerminalTag->text());
                        QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
                        QueryVar.exec();

                        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr="SELECT * FROM TerminalStripDiagnosePara WHERE TerminalStrip_ID = '"+QueryTerminalStrip.value("TerminalStrip_ID").toString()+"'";
                        QuerySearch.exec(SqlStr);
                        while(QuerySearch.next())
                        {
                            int DiagnoseParaID=GetMaxIDOfDB(T_ProjectDatabase,"EquipmentDiagnosePara","DiagnoseParaID");
                            SqlStr = "INSERT INTO EquipmentDiagnosePara (DiagnoseParaID,TerminalStrip_ID,Name,Unit,CurValue,DefaultValue,Remark)"
                                     " VALUES (:DiagnoseParaID,:TerminalStrip_ID,:Name,:Unit,:CurValue,:DefaultValue,:Remark)";
                            QueryVar.prepare(SqlStr);
                            QueryVar.bindValue(":DiagnoseParaID",DiagnoseParaID);
                            QueryVar.bindValue(":TerminalStrip_ID",QString::number(TerminalStrip_ID));
                            QueryVar.bindValue(":Name",QuerySearch.value("Name").toString());
                            QueryVar.bindValue(":Unit",QuerySearch.value("Unit").toString());
                            QueryVar.bindValue(":CurValue",QuerySearch.value("CurValue").toString());
                            QueryVar.bindValue(":DefaultValue",QuerySearch.value("DefaultValue").toString());
                            QueryVar.bindValue(":Remark",QuerySearch.value("Remark").toString());
                            QueryVar.exec();
                        }
                    }
                }
                else//是唯一功能子块，更新元件
                {
                    SqlStr="UPDATE TerminalStrip SET DT=:DT,ProjectStructure_ID=:ProjectStructure_ID"
                                            " WHERE TerminalStrip_ID = "+QString::number(TerminalStrip_ID);
                    QueryVar.prepare(SqlStr);
                    QueryVar.bindValue(":DT",ui->EdTerminalTag->text());
                    QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
                    QueryVar.exec();
                }
            }
        }
    }

    //更新Terminal表
    SqlStr ="UPDATE Terminal SET TerminalStrip_ID=:TerminalStrip_ID,Designation=:Designation,Symbol=:Symbol,"
            "TerminalType=:TerminalType,TerminalName=:TerminalName,PartCode=:PartCode,FunctionText=:FunctionText,"
            "FunDefine=:FunDefine,Factory=:Factory,OrderNum=:OrderNum,LeftTerm=:LeftTerm,RightTerm=:RightTerm,UpTerm=:UpTerm,DownTerm=:DownTerm"
            " WHERE Terminal_ID = "+CurTerminal_ID;
    QueryVar.prepare(SqlStr);
    QueryVar.bindValue(":TerminalStrip_ID",QString::number(TerminalStrip_ID));
    QueryVar.bindValue(":Designation",ui->EdDesignation->text());
    QueryVar.bindValue(":Symbol",StrSymbolName);
    //QueryVar.bindValue(":Terminalfunction",ui->CbTerminalType->currentText());
    QueryVar.bindValue(":TerminalType",ui->tableWidget->item(0,1)->text());
    QueryVar.bindValue(":TerminalName",ui->tableWidget->item(1,1)->text());
    QueryVar.bindValue(":PartCode",ui->LbPartCode->text());
    QueryVar.bindValue(":FunctionText",ui->tableWidget->item(4,1)->text());
    QueryVar.bindValue(":FunDefine",ui->LbTerminalFunction->text());
    QueryVar.bindValue(":Factory",ui->tableWidget->item(2,1)->text());
    QueryVar.bindValue(":OrderNum",ui->tableWidget->item(3,1)->text());
    QueryVar.bindValue(":LeftTerm",ui->CbLeftTerm->currentText());
    QueryVar.bindValue(":RightTerm",ui->CbRightTerm->currentText());
    QueryVar.bindValue(":UpTerm",ui->CbUpTerm->currentText());
    QueryVar.bindValue(":DownTerm",ui->CbDownTerm->currentText());
    QueryVar.exec();*/
    Canceled=false;
    //更新TerminalInstance表
    QString Terminal_ID;
    QSqlQuery QueryTerminalInstance= QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+CurTerminalInstanceID;
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        QString TerminalStrip_ID=QueryTerminalInstance.value("TerminalStrip_ID").toString();
        QSqlQuery QueryTerminal= QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+TerminalStrip_ID+"' AND Designation = '"+ui->EdDesignation->text()+"'";
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next()) Terminal_ID=QueryTerminal.value("Terminal_ID").toString();
    }

    SqlStr ="UPDATE TerminalInstance SET Terminal_ID=:Terminal_ID,Designation=:Designation,LeftTerm=:LeftTerm,RightTerm=:RightTerm,UpTerm=:UpTerm,DownTerm=:DownTerm"
            " WHERE TerminalInstanceID = "+CurTerminalInstanceID;
    QueryTerminalInstance.prepare(SqlStr);
    QueryTerminalInstance.bindValue(":Terminal_ID",Terminal_ID);
    QueryTerminalInstance.bindValue(":Designation",ui->EdDesignation->text());
    QueryTerminalInstance.bindValue(":LeftTerm",ui->CbLeftTerm->currentText());
    QueryTerminalInstance.bindValue(":RightTerm",ui->CbRightTerm->currentText());
    QueryTerminalInstance.bindValue(":UpTerm",ui->CbUpTerm->currentText());
    QueryTerminalInstance.bindValue(":DownTerm",ui->CbDownTerm->currentText());
    QueryTerminalInstance.exec();
    /*
    //更新TerminalTerm表
    //更新TerminalTerm表的连接点数量，如果增加则insert新记录，如果减少则删除多的记录
    int TermCount=ui->tableWidget_Term->rowCount();//GetDwgTermCount(DwgPath,StrSymbolName);
    int MaxConnNum_LogicVal=0;
    QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr="SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+CurTerminal_ID+"'";
    QueryTerminalTerm.exec(SqlStr);
    while(QueryTerminalTerm.next())
    {
        int ConnNum_LogicVal=QueryTerminalTerm.value("ConnNum_Logic").toString().toInt();
        if(MaxConnNum_LogicVal<ConnNum_LogicVal) MaxConnNum_LogicVal=ConnNum_LogicVal;
        if(TermCount<ConnNum_LogicVal)
        {
            //删除多余的连接点
            QSqlQuery queryDelete=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM TerminalTerm WHERE TerminalTerm_ID = "+QueryTerminalTerm.value("TerminalTerm_ID").toString());
            queryDelete.exec(temp);
        }
    }
    if(MaxConnNum_LogicVal<TermCount)
    {
        for(int i=0;i<TermCount-MaxConnNum_LogicVal;i++)
        {
            int MaxTerminalTerm_ID=1;
            SqlStr = QString("SELECT TerminalTerm_ID FROM TerminalTerm ORDER BY TerminalTerm_ID DESC");
            QueryVar.exec(SqlStr);
            if(QueryVar.next())  MaxTerminalTerm_ID=QueryVar.value(0).toInt()+1;
            qDebug()<<"MaxTerminalTerm_ID="<<MaxTerminalTerm_ID;
            QSqlQuery queryInsert=QSqlQuery(T_ProjectDatabase);
            SqlStr = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum) "
                             "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum)");
            queryInsert.prepare(SqlStr);
            queryInsert.bindValue(":TerminalTerm_ID",MaxTerminalTerm_ID);
            queryInsert.bindValue(":Terminal_ID",QueryTerminalTerm.value("TerminalTerm_ID").toString());
            queryInsert.bindValue(":ConnNum_Logic",QString::number(MaxConnNum_LogicVal+i+1));
            queryInsert.bindValue(":ConnNum",ui->tableWidget_Term->item(MaxConnNum_LogicVal+i,0)->text());
            queryInsert.exec();
        }
    }
    for(int i=0;i<TermCount;i++)
    {
        QSqlQuery QueryTerminalTerm= QSqlQuery(T_ProjectDatabase);
        SqlStr ="UPDATE TerminalTerm SET ConnNum=:ConnNum WHERE Terminal_ID = '"+CurTerminal_ID+"' AND ConnNum_Logic = '"+QString::number(i+1)+"'";
        QueryTerminalTerm.prepare(SqlStr);
        QueryTerminalTerm.bindValue(":ConnNum",ui->tableWidget_Term->item(i,1)->text());
        QueryTerminalTerm.exec();
    }*/
    TerminalTagVisible=ui->CbShowTag->isChecked();
    close();
}

void DialogSingleTermAttr::on_BtnUnitChoose_clicked()
{
    DialogUnitManage *dlg=new DialogUnitManage(this);
    dlg->setModal(true);
    dlg->SetStackWidget(0);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    QString Choose_ID=dlg->CurEquipment_ID;
    QSqlQuery QueryEquipment= QSqlQuery(T_LibDatabase);
    QString SqlStr=QString("SELECT * FROM Equipment WHERE Equipment_ID='"+Choose_ID+"'");
    QueryEquipment.exec(SqlStr);
    if(!QueryEquipment.next()) return;

    ui->LbPartCode->setText(QueryEquipment.value("PartCode").toString());
    ui->tableWidget->item(0,1)->setText(QueryEquipment.value("Type").toString());
    ui->tableWidget->item(1,1)->setText(QueryEquipment.value("Name").toString());
    ui->tableWidget->item(2,1)->setText(QueryEquipment.value("Supplier").toString());
    ui->tableWidget->item(3,1)->setText(QueryEquipment.value("OrderNum").toString());
    ui->tableWidget->item(4,1)->setText("");
}

void DialogSingleTermAttr::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogSingleTermAttr::on_EdTerminalTag_textChanged(const QString &arg1)
{
    if(ui->EdTerminalTag->text()!="") ui->LbProTag->setText(StrProTag+"-"+ui->EdTerminalTag->text());
}

void DialogSingleTermAttr::on_CbTerminalFunction_currentTextChanged(const QString &arg1)
{
    if(arg1=="2个连接点")
       ui->widget_UpDownTerm->setVisible(false);
    else
       ui->widget_UpDownTerm->setVisible(true);
}

void DialogSingleTermAttr::on_CbLeftTerm_currentTextChanged(const QString &arg1)
{
    QString JpgPath="C:/TBD/data/Term";
    if(ui->CbLeftTerm->currentText()!="") JpgPath+="_"+ui->CbLeftTerm->currentText();
    else JpgPath+="_0";
    if(ui->CbRightTerm->currentText()!="") JpgPath+="_"+ui->CbRightTerm->currentText();
    else JpgPath+="_0";
    if(ui->LbTerminalFunction->text()!="2个连接点")
    {
        if(ui->CbUpTerm->currentText()!="") JpgPath+="_"+ui->CbUpTerm->currentText();
        else JpgPath+="_0";
        if(ui->CbDownTerm->currentText()!="") JpgPath+="_"+ui->CbDownTerm->currentText();
        else JpgPath+="_0";
    }
    JpgPath+=".png";
    ui->LbTerminalJpg->setPixmap(JpgPath);
}
