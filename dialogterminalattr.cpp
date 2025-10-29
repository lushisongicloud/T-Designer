#include "dialogterminalattr.h"
#include "ui_dialogterminalattr.h"
extern int SelectTerminalStrip_ID;
extern int SelectTerminal_ID;
DialogTerminalAttr::DialogTerminalAttr(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogTerminalAttr)
{
    ui->setupUi(this);
    ui->tableWidget->setRowCount(5);
    ui->tableWidget->setItem(0,0,new QTableWidgetItem("型号")); ui->tableWidget->setItem(0,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(1,0,new QTableWidgetItem("名称")); ui->tableWidget->setItem(1,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(2,0,new QTableWidgetItem("厂家")); ui->tableWidget->setItem(2,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(3,0,new QTableWidgetItem("订货号")); ui->tableWidget->setItem(3,1,new QTableWidgetItem(""));
    ui->tableWidget->setItem(4,0,new QTableWidgetItem("功能文本")); ui->tableWidget->setItem(4,1,new QTableWidgetItem(""));
    ui->tableWidget->setColumnWidth(1,200);
/*
    ui->CbTerminalType->clear();
    ui->CbTerminalType->addItem("");
    ui->CbTerminalType->addItem("电阻端子");
    ui->CbTerminalType->addItem("二极管端子");
    ui->CbTerminalType->addItem("隔离端子");
    ui->CbTerminalType->addItem("贯通式端子");
    ui->CbTerminalType->addItem("开关端子");
    ui->CbTerminalType->addItem("熔断器端子");*/
    Canceled=true;
}

DialogTerminalAttr::~DialogTerminalAttr()
{
    delete ui;
}

//Mode=1:add  Mode=2:modify
void DialogTerminalAttr::LoadInfo(int Mode,int TerminalStrip_ID)
{
   AttrMode=Mode;
   if(Mode==1)
   {
       ui->LbProTag->setText(StrProTag);
       /*
       //设置默认端子样式SPS_M_X2_NB-1 ,功能定义:端子，常规，2个连接点,FunctionDefineClass_ID:101000500
       QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
       QString SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '101000500'";
       QueryFunctionDefineClass.exec(SqlStr);
       if(!QueryFunctionDefineClass.next()) return;
       ui->LbFuncDefine->setText(QueryFunctionDefineClass.value("FunctionDefineName").toString());
       */
       ui->CbTerminalFunction->setCurrentIndex(0);
       //StrSymbolName=QueryFunctionDefineClass.value("DefaultSymbol").toString();
       StrSymbolName="ES2_S_TERM_2P";
       QString PathDwg;
       //if(StrSymbolName.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+StrSymbolName+".dwg";
       //else if(StrSymbolName.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+StrSymbolName+".dwg";
       PathDwg="C:/TBD/SymbConnLib/"+StrSymbolName+".dwg";
       UnitSymbolsView(PathDwg,"C:/TBD/data/TempImage/"+StrSymbolName+".jpg",ui->LbTerminalJpg,true);
       //LoadCbSymbolPattern(QueryFunctionDefineClass.value("DefaultSymbol").toString(),ui->CbTerminalSymbolPattern);
       return;
   }
   ui->EdDesignationAll->setEnabled(false);
   CurTerminalStrip_ID=QString::number(TerminalStrip_ID);
   QSqlQuery QueryTerminalStrip= QSqlQuery(T_ProjectDatabase);
   QString SqlStr=QString("SELECT * FROM TerminalStrip WHERE TerminalStrip_ID="+CurTerminalStrip_ID);
   QueryTerminalStrip.exec(SqlStr);
   if(!QueryTerminalStrip.next()) return;
   StrProTag=GetProjectStructureStrByProjectStructureID(QueryTerminalStrip.value("ProjectStructure_ID").toInt());//"+"+StrPos;
   QString TerminalTag=QueryTerminalStrip.value("DT").toString();
   //StrProTag="+"+StrPos;
   ui->LbProTag->setText(StrProTag+"-"+TerminalTag);
   ui->EdTerminalTag->setText(TerminalTag);

   QSqlQuery QueryTerminal(T_ProjectDatabase);
   QStringList ListDesignation;
   SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+CurTerminalStrip_ID+"'";
   QueryTerminal.exec(SqlStr);
   bool FirstRecord=true;
   while(QueryTerminal.next())
   {
      ListDesignation.append(QueryTerminal.value("Designation").toString());
      if(FirstRecord)
      {
          FirstRecord=false;
          ui->LbPartCode->setText(QueryTerminal.value("PartCode").toString());
          ui->CbTerminalFunction->setCurrentText(QueryTerminal.value("FunDefine").toString());
          ui->tableWidget->item(0,1)->setText(QueryTerminal.value("TerminalType").toString());
          ui->tableWidget->item(1,1)->setText(QueryTerminal.value("TerminalName").toString());
          ui->tableWidget->item(2,1)->setText(QueryTerminal.value("Factory").toString());
          ui->tableWidget->item(3,1)->setText(QueryTerminal.value("OrderNum").toString());
          ui->tableWidget->item(4,1)->setText(QueryTerminal.value("FunctionText").toString());
          StrSymbolName=QueryTerminal.value("Symbol").toString();
          QString PathDwg;
          //if(StrSymbolName.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+StrSymbolName+".dwg";
          //else if(StrSymbolName.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+StrSymbolName+".dwg";
          PathDwg="C:/TBD/SymbConnLib/"+StrSymbolName+".dwg";
          UnitSymbolsView(PathDwg,"C:/TBD/data/TempImage/"+StrSymbolName+".jpg",ui->LbTerminalJpg,true);
          LoadCbSymbolPattern(StrSymbolName,ui->CbTerminalSymbolPattern);
      }
      else
      {
          if(QueryTerminal.value("PartCode").toString()!=ui->LbPartCode->text()) ui->LbPartCode->setText("多种规格");
          if(QueryTerminal.value("FunDefine").toString()!=ui->CbTerminalFunction->currentText()) ui->CbTerminalFunction->setCurrentText("多种规格");
          if(QueryTerminal.value("TerminalType").toString()!=ui->tableWidget->item(0,1)->text()) ui->tableWidget->item(0,1)->setText("");
          if(QueryTerminal.value("TerminalName").toString()!=ui->tableWidget->item(0,1)->text()) ui->tableWidget->item(1,1)->setText("");
          if(QueryTerminal.value("Factory").toString()!=ui->tableWidget->item(0,1)->text()) ui->tableWidget->item(2,1)->setText("");
          if(QueryTerminal.value("OrderNum").toString()!=ui->tableWidget->item(0,1)->text()) ui->tableWidget->item(3,1)->setText("");
          if(QueryTerminal.value("FunctionText").toString()!=ui->tableWidget->item(0,1)->text()) ui->tableWidget->item(4,1)->setText("");
          if((QueryTerminal.value("Symbol").toString())!=StrSymbolName)
          {
              ui->LbTerminalJpg->setPixmap(QPixmap("").scaled(ui->LbTerminalJpg->width()-8,ui->LbTerminalJpg->width()/2-8));
              ui->CbTerminalSymbolPattern->clear();
          }
      }
   }

   QString JumpStr="*";
   while(1)
   {
       SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+CurTerminalStrip_ID+"' AND ShortJumper = '"+JumpStr+"' ORDER BY Terminal_ID";
       QueryTerminal.exec(SqlStr);
       QString StrShortJump="";
       while(QueryTerminal.next())
       {
           int LastIndexOfDouHao=StrShortJump.lastIndexOf(",");
           int LastIndexOfBoLangHao=StrShortJump.lastIndexOf("~");
           if(LastIndexOfBoLangHao>LastIndexOfDouHao)//最后一个是~
           {
               int LastDesignation=StrShortJump.mid(LastIndexOfBoLangHao+1,StrShortJump.count()-LastIndexOfBoLangHao-1).toInt();
               if(QueryTerminal.value("Designation").toInt()==(LastDesignation+1))
               {
                  StrShortJump= StrShortJump.mid(0,LastIndexOfBoLangHao+1)+QueryTerminal.value("Designation").toString();
               }
               else
               {
                  StrShortJump= StrShortJump + ","+ QueryTerminal.value("Designation").toString();
               }
           }
           else if(LastIndexOfBoLangHao<LastIndexOfDouHao)//最后一个是,
           {
               int LastDesignation=StrShortJump.mid(LastIndexOfDouHao+1,StrShortJump.count()-LastIndexOfDouHao-1).toInt();
               if(QueryTerminal.value("Designation").toInt()==(LastDesignation+1))
               {
                  StrShortJump= StrShortJump+"~"+QueryTerminal.value("Designation").toString();
               }
               else
               {
                  StrShortJump= StrShortJump + ","+ QueryTerminal.value("Designation").toString();
               }
           }
           else//只有一个数字
           {
               if(StrShortJump=="") StrShortJump=QueryTerminal.value("Designation").toString();
               else
               {
                   if(QueryTerminal.value("Designation").toInt()==(StrShortJump.toInt()+1))
                   {
                       StrShortJump= StrShortJump+"~"+QueryTerminal.value("Designation").toString();
                   }
                   else
                   {
                       StrShortJump= StrShortJump + ","+ QueryTerminal.value("Designation").toString();
                   }
               }
           }
       }
       if(StrShortJump=="") break;
       ui->tableWidget_shortConnect->setRowCount(ui->tableWidget_shortConnect->rowCount()+1);
       ui->tableWidget_shortConnect->setItem(ui->tableWidget_shortConnect->rowCount()-1,0,new QTableWidgetItem(StrShortJump));
       JumpStr+="*";
   }
}

void DialogTerminalAttr::on_BtnProSet_clicked()
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

//处理1~6,8,10这种情况
QStringList DialogTerminalAttr::GetTerminalList(QString StrTerminal)
{
qDebug()<<"StrTerminal="<<StrTerminal;
    QStringList ListDesignation;
    ListDesignation.append(StrTerminal);
    if(StrTerminal.contains(","))
    {
        ListDesignation.clear();
        ListDesignation=StrTerminal.split(",");
    }
qDebug()<<"ListDesignation="<<ListDesignation;
    for(int m=0;m<ListDesignation.count();m++)
    {
        if(ListDesignation.at(m).contains("~"))
        {
            QStringList ListTemp=ListDesignation.at(m).split("~");
            if(ListTemp.at(0).toInt()>ListTemp.at(1).toInt())
            {
                for(int i=0;i<(ListTemp.at(0).toInt()-ListTemp.at(1).toInt()+1);i++)
                {
                    ListDesignation.insert(m,QString::number(ListTemp.at(1).toInt()+i));
                    //ListDesignation.append(QString::number(ListTemp.at(1).toInt()+i));
                }
                ListDesignation.removeAt(m+ListTemp.at(0).toInt()-ListTemp.at(1).toInt()+1);
            }
            else
            {
                for(int i=0;i<(ListTemp.at(1).toInt()-ListTemp.at(0).toInt()+1);i++)
                {
                    ListDesignation.insert(m,QString::number(ListTemp.at(1).toInt()-i));
                    //ListDesignation.append(QString::number(ListTemp.at(0).toInt()+i));
                }
                ListDesignation.removeAt(m+ListTemp.at(1).toInt()-ListTemp.at(0).toInt()+1);
            }
        }
    }
    return  ListDesignation;
}
void DialogTerminalAttr::on_BtnOK_clicked()
{
    if(ui->EdTerminalTag->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", " 端子排代号不能为空");
        return;
    }

    QString GaocengStr,PosStr;
    QString TmpStr=ui->LbProTag->text();
    int indexGaoceng=TmpStr.indexOf("=");
    int indexPos=TmpStr.indexOf("+");
    int indexUnit=TmpStr.indexOf("-");
    if(indexGaoceng>=0) GaocengStr=TmpStr.mid(indexGaoceng+1,indexPos-indexGaoceng-1);
    if(indexPos>=0) PosStr=TmpStr.mid(indexPos+1,indexUnit-indexPos-1);
    NewProjectStructure_ID=InsertRecordToProjectStructure(0,GaocengStr,PosStr,"");


    if(AttrMode==1)//新增
    {
        if(ui->EdDesignationAll->text()=="")
        {
            QMessageBox::warning(nullptr, "提示", " 起止序号不能为空");
            return;
        }
        if((ui->EdDesignationAll->text().at(0)<'0')||(ui->EdDesignationAll->text().at(0)>'9'))
        {
            QMessageBox::warning(nullptr, "提示", " 起止序号必须以数字开头，例如1~20或1,2,3..");
            return;
        }
        for(int i=0;i<ui->EdDesignationAll->text().count();i++)
        {
            if(((ui->EdDesignationAll->text().at(i)<'0')||(ui->EdDesignationAll->text().at(i)>'9'))&&(ui->EdDesignationAll->text().at(i)!=',')&&(ui->EdDesignationAll->text().at(i)!='~'))
            {
                QMessageBox::warning(nullptr, "提示", " 起止序号格式错误1，正确格式例如1~20或1,2,3..");
                return;
            }
        }
        if(ui->EdDesignationAll->text().contains("~"))
        {
            QStringList ListDesignation=ui->EdDesignationAll->text().split("~");
            for(int i=0;i<ListDesignation.count();i++)
            {
                if(((ListDesignation.at(i)<'0')||(ListDesignation.at(i)>'9'))&&(ListDesignation.at(i)!=','))
                {
                    QMessageBox::warning(nullptr, "提示", " 起止序号格式错误2，正确格式例如1~20或1,2,3..");
                    return;
                }
            }
        }
        if(ui->EdDesignationAll->text().contains(","))
        {
            QStringList ListDesignation=ui->EdDesignationAll->text().split(",");
            for(int i=0;i<ListDesignation.count();i++)
            {
                if(((ListDesignation.at(i)<'0')||(ListDesignation.at(i)>'9'))&&(ListDesignation.at(i)!='~'))
                {
                    QMessageBox::warning(nullptr, "提示", " 起止序号格式错误2，正确格式例如1~20或1,2,3..");
                    return;
                }
            }
        }

        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM TerminalStrip WHERE DT = '"+ui->EdTerminalTag->text()+"' AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"'";
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            QMessageBox::warning(nullptr, "提示", " 该端子排已存在，请修改项目代号或端子排代号！");
            return;
        }
    }

    for(int index=0;index<ui->tableWidget_shortConnect->rowCount();index++)
    {
        if(ui->tableWidget_shortConnect->item(index,0)->text()=="") continue;
        QString StrShortConnect=ui->tableWidget_shortConnect->item(index,0)->text();
        if((StrShortConnect.at(0)<'0')||(StrShortConnect.at(0)>'9'))
        {
            QMessageBox::warning(nullptr, "提示", " 短接端子起止序号必须以数字开头，例如1~20或1,2,3..");
            return;
        }
        for(int i=0;i<StrShortConnect.count();i++)
        {
            if(((StrShortConnect.at(i)<'0')||(StrShortConnect.at(i)>'9'))&&(StrShortConnect.at(i)!=',')&&(StrShortConnect.at(i)!='~'))
            {
                QMessageBox::warning(nullptr, "提示", " 短接端子起止序号格式错误1，正确格式例如1~20或1,2,3..");
                return;
            }
        }
        if(StrShortConnect.contains("~"))
        {
            QStringList ListDesignation=StrShortConnect.split("~");
            for(int i=0;i<ListDesignation.count();i++)
            {
                if(((ListDesignation.at(i)<'0')||(ListDesignation.at(i)>'9'))&&(ListDesignation.at(i)!=','))
                {
                    QMessageBox::warning(nullptr, "提示", " 短接端子起止序号格式错误2，正确格式例如1~20或1,2,3..");
                    return;
                }
            }
        }
        if(StrShortConnect.contains(","))
        {
            QStringList ListDesignation=StrShortConnect.split(",");
            for(int i=0;i<ListDesignation.count();i++)
            {
                if(((ListDesignation.at(i)<'0')||(ListDesignation.at(i)>'9'))&&(ListDesignation.at(i)!='~'))
                {
                    QMessageBox::warning(nullptr, "提示", " 短接端子起止序号格式错误2，正确格式例如1~20或1,2,3..");
                    return;
                }
            }
        }
    }
    Canceled=false;
    QList<QStringList> ListShortConnect;
    ListShortConnect.clear();
    //检查短接端子是否有重复
    for(int i=0;i<ui->tableWidget_shortConnect->rowCount();i++)
    {
        QStringList ListDesignation=GetTerminalList(ui->tableWidget_shortConnect->item(i,0)->text());
        for(int j=0;j<ListDesignation.count();j++)
        {
            for(int k=0;k<ListShortConnect.count();k++)
            {
                for(int m=0;m<ListShortConnect.at(k).count();m++)
                {
                    if(ListShortConnect.at(k).at(m)==ListDesignation.at(j))
                    {
                        QMessageBox::warning(nullptr, "提示", "短接端子有重复，请重新填写！");
                        return;
                    }
                }
            }
        }
        ListShortConnect.append(GetTerminalList(ui->tableWidget_shortConnect->item(i,0)->text()));
    }


    //更新器件信息,区分是新增还是修改
    if(AttrMode==1)//新增
    {
        //找到当前最大的Equipment_ID
        int MaxTerminalStrip_ID=1;
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString tempSQL = QString("SELECT TerminalStrip_ID FROM TerminalStrip ORDER BY TerminalStrip_ID DESC");
        QueryVar.exec(tempSQL);
        if(QueryVar.next())  MaxTerminalStrip_ID=QueryVar.value(0).toInt()+1;
        CurTerminalStrip_ID=QString::number(MaxTerminalStrip_ID);
        qDebug()<<"MaxTerminalStrip_ID="<<MaxTerminalStrip_ID;
        //更新T_ProjectDatabase数据库的Equipment表
        tempSQL = QString("INSERT INTO TerminalStrip (TerminalStrip_ID,DT,ProjectStructure_ID) VALUES (:TerminalStrip_ID,:DT,:ProjectStructure_ID)");
        QueryVar.prepare(tempSQL);
        QueryVar.bindValue(":TerminalStrip_ID",MaxTerminalStrip_ID);
        QueryVar.bindValue(":DT",ui->EdTerminalTag->text());
        QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
        QueryVar.exec();

        //根据起止序号更新T_ProjectDatabase数据库的Terminal表和TerminalTerm表
        QStringList ListDesignation=GetTerminalList(ui->EdDesignationAll->text());


qDebug()<<"ListDesignation="<<ListDesignation;
        for(int i=0;i<ListDesignation.count();i++)
        {
            int MaxTerminal_ID=1;
            tempSQL = QString("SELECT Terminal_ID FROM Terminal ORDER BY Terminal_ID DESC");
            QueryVar.exec(tempSQL);
            if(QueryVar.next())  MaxTerminal_ID=QueryVar.value(0).toInt()+1;
 qDebug()<<"MaxTerminal_ID="<<MaxTerminal_ID;
            tempSQL = QString("INSERT INTO Terminal (Terminal_ID,TerminalStrip_ID,Designation,Symbol,ShortJumper,TerminalType,TerminalName,PartCode,FunctionText,FunDefine,Factory,OrderNum) "
                              "VALUES (:Terminal_ID,:TerminalStrip_ID,:Designation,:Symbol,:ShortJumper,:TerminalType,:TerminalName,:PartCode,:FunctionText,:FunDefine,:Factory,:OrderNum)");
            QueryVar.prepare(tempSQL);
            QueryVar.bindValue(":Terminal_ID",MaxTerminal_ID);
            QueryVar.bindValue(":TerminalStrip_ID",QString::number(MaxTerminalStrip_ID));
            QueryVar.bindValue(":Designation",ListDesignation.at(i));
            if(ui->CbTerminalFunction->currentIndex()==1) QueryVar.bindValue(":Symbol","ES2_S_TERM_3P");
            else if(ui->CbTerminalFunction->currentIndex()==2) QueryVar.bindValue(":Symbol","ES2_S_TERM_4P");
            else QueryVar.bindValue(":Symbol","ES2_S_TERM_2P");
            QString StrShortJumper="";
            for(int j=0;j<ListShortConnect.count();j++)
            {
                for(int k=0;k<ListShortConnect.at(j).count();k++)
                {
                    if(ListShortConnect.at(j).at(k)==ListDesignation.at(i))
                    {
                       for(int shortnum=0;shortnum<(j+1);shortnum++) StrShortJumper+="*";
                       break;
                    }
                }
            }
            QueryVar.bindValue(":ShortJumper",StrShortJumper);
            QueryVar.bindValue(":TerminalType",ui->tableWidget->item(0,1)->text());//型号
            QueryVar.bindValue(":TerminalName",ui->tableWidget->item(1,1)->text());
            QueryVar.bindValue(":PartCode",ui->LbPartCode->text());
            QueryVar.bindValue(":FunctionText",ui->tableWidget->item(4,1)->text());
            QueryVar.bindValue(":FunDefine",ui->CbTerminalFunction->currentText());
            QueryVar.bindValue(":Factory",ui->tableWidget->item(2,1)->text());
            QueryVar.bindValue(":OrderNum",ui->tableWidget->item(3,1)->text());
            QueryVar.exec();
            /*
            //根据端子有几个连接点insert记录到TerminalTerm表
            QString DwgPath;
            if(StrSymbolName.contains("SPS_")) DwgPath="C:/TBD/SPS/"+StrSymbolName+".dwg";
            else if(StrSymbolName.contains("ES2_")) DwgPath="C:/TBD/SYMB2LIB/"+StrSymbolName+".dwg";
            int TermCount=GetDwgTermCount(DwgPath,StrSymbolName);
qDebug()<<"DwgPath="<<DwgPath<<" TermCount="<<TermCount;
            for(int j=0;j<TermCount;j++)
            {
                int MaxTerminalTerm_ID=1;
                tempSQL = QString("SELECT TerminalTerm_ID FROM TerminalTerm ORDER BY TerminalTerm_ID DESC");
                QueryVar.exec(tempSQL);
                if(QueryVar.next())  MaxTerminalTerm_ID=QueryVar.value(0).toInt()+1;
                qDebug()<<"MaxTerminalTerm_ID="<<MaxTerminalTerm_ID;
                tempSQL = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum) "
                                  "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum)");
                QueryVar.prepare(tempSQL);
                QueryVar.bindValue(":TerminalTerm_ID",MaxTerminalTerm_ID);
                QueryVar.bindValue(":Terminal_ID",QString::number(MaxTerminal_ID));
                QueryVar.bindValue(":ConnNum_Logic",QString::number(j+1));
                QueryVar.bindValue(":ConnNum",QString::number(j+1));
                QueryVar.exec();
            }*/
        }
        SelectTerminalStrip_ID=MaxTerminalStrip_ID;
        SelectTerminal_ID=0;
        emit(UpdateProjectTerminal());
    }
    else if(AttrMode==2)//modify
    {
        QList<QStringList> ListShortConnect;
        ListShortConnect.clear();
        for(int i=0;i<ui->tableWidget_shortConnect->rowCount();i++)
        {
            ListShortConnect.append(GetTerminalList(ui->tableWidget_shortConnect->item(i,0)->text()));
        }
qDebug()<<"ListShortConnect="<<ListShortConnect;
        //如果是修改端子排：如果端子排标号被修改，则查看TerminalStrip表中是否存在相同标号的端子排，如果存在则合并端子排
        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM TerminalStrip WHERE DT = '"+ui->EdTerminalTag->text()+"'AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"' AND TerminalStrip_ID <> "+CurTerminalStrip_ID;
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
           //元件标号被修改，存在相同标号的元件,询问是否合并元件
            QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"该端子排代号已存在，是否修改代号且合并端子?",
                                        QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

            if(result==QMessageBox::Yes)
            {
                //删除原TerminalStrip表中的记录，将原元件关联的Symbol关联到新的Equipment表记录
                QString CombineTerminalStrip_ID=QuerySearch.value("TerminalStrip_ID").toString();
                SqlStr="DELETE FROM TerminalStrip WHERE TerminalStrip_ID = "+CurTerminalStrip_ID;
                QuerySearch.exec(SqlStr);
                QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="UPDATE Terminal SET TerminalStrip_ID=:TerminalStrip_ID WHERE TerminalStrip_ID = '"+CurTerminalStrip_ID+"'";
                QueryTerminal.prepare(SqlStr);
                QueryTerminal.bindValue(":TerminalStrip_ID",CombineTerminalStrip_ID);
                QueryTerminal.exec();
                CurTerminalStrip_ID=CombineTerminalStrip_ID;
                TerminalStripTagChanged=true;
            }
            else return;
        }

        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+CurTerminalStrip_ID;
        QueryVar.exec(SqlStr);
        if(QueryVar.next())
        {
            if(QueryVar.value("DT").toString()!=ui->EdTerminalTag->text()) TerminalStripTagChanged=true;
        }
        //更新TerminalStrip表
        SqlStr="UPDATE TerminalStrip SET DT=:DT,ProjectStructure_ID=:ProjectStructure_ID WHERE TerminalStrip_ID ="+CurTerminalStrip_ID;
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":DT",ui->EdTerminalTag->text());
        QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
        QueryVar.exec();

        //更新Terminal表
        SqlStr = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+CurTerminalStrip_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            int Terminal_ID=QuerySearch.value("Terminal_ID").toInt();
            SqlStr ="UPDATE Terminal SET Symbol=:Symbol,ShortJumper=:ShortJumper,"
                            "TerminalType=:TerminalType,TerminalName=:TerminalName,PartCode=:PartCode,FunctionText=:FunctionText,FunDefine=:FunDefine,Factory=:Factory,OrderNum=:OrderNum"
                            " WHERE Terminal_ID = "+QString::number(Terminal_ID);
            QueryVar.prepare(SqlStr);

            if((ui->CbTerminalFunction->currentIndex()==1)||(ui->CbTerminalFunction->currentIndex()==2))
                QueryVar.bindValue(":Symbol","ES2_S_TERM_4P");
            else
                QueryVar.bindValue(":Symbol","ES2_S_TERM_2P");

            QString StrShortJumper="";
            for(int j=0;j<ListShortConnect.count();j++)
            {
                for(int k=0;k<ListShortConnect.at(j).count();k++)
                {
                    if(ListShortConnect.at(j).at(k)==QuerySearch.value("Designation").toString())
                    {
                       for(int shortnum=0;shortnum<(j+1);shortnum++) StrShortJumper+="*";
                       break;
                    }
                }
            }
            QueryVar.bindValue(":ShortJumper",StrShortJumper);
            QueryVar.bindValue(":TerminalType",ui->tableWidget->item(0,1)->text());
            QueryVar.bindValue(":TerminalName",ui->tableWidget->item(1,1)->text());
            QueryVar.bindValue(":PartCode",ui->LbPartCode->text());
            QueryVar.bindValue(":FunctionText",ui->tableWidget->item(4,1)->text());
            QueryVar.bindValue(":FunDefine",ui->CbTerminalFunction->currentText());
            QueryVar.bindValue(":Factory",ui->tableWidget->item(2,1)->text());
            QueryVar.bindValue(":OrderNum",ui->tableWidget->item(3,1)->text());
            QueryVar.exec();

            //更新TerminalTerm表
            if(SymbolTermCountChanged)
            {
                //更新TerminalTerm表的连接点数量，如果增加则insert新记录，如果减少则删除多的记录
                QString DwgPath;
                if(StrSymbolName.contains("SPS_")) DwgPath="C:/TBD/SPS/"+StrSymbolName+".dwg";
                else if(StrSymbolName.contains("ES2_")) DwgPath="C:/TBD/SYMB2LIB/"+StrSymbolName+".dwg";
                int TermCount=GetDwgTermCount(DwgPath,StrSymbolName);
                QSqlQuery QueryTerminal= QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+CurTerminalStrip_ID+"'";
                QueryTerminal.exec(SqlStr);
                int MaxConnNum_LogicVal=0;
                while(QueryTerminal.next())
                {
                    QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    SqlStr="SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+QueryTerminal.value("Terminal_ID").toString()+"'";
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
                            queryInsert.bindValue(":ConnNum",QString::number(MaxConnNum_LogicVal+i+1));
                            queryInsert.exec();
                        }
                    }
                }//while(QueryTerminal.next())
            }//if(SymbolTermCountChanged)
        }//while(QuerySearch.next())
    }//else if(AttrMode==2)//modify
    close();
}

void DialogTerminalAttr::on_EdTerminalTag_textChanged(const QString &arg1)
{
    if(ui->EdTerminalTag->text()!="") ui->LbProTag->setText(StrProTag+"-"+ui->EdTerminalTag->text());
}

void DialogTerminalAttr::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogTerminalAttr::on_BtnUnitChoose_clicked()
{
    DialogUnitManage *dlg=new DialogUnitManage(this);
    dlg->setModal(true);
    dlg->SetStackWidget(0);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    CurTerminalStrip_ID=dlg->CurEquipment_ID;
    QSqlQuery QueryEquipment= QSqlQuery(T_LibDatabase);
    QString SqlStr=QString("SELECT * FROM Equipment WHERE Equipment_ID='"+CurTerminalStrip_ID+"'");
    QueryEquipment.exec(SqlStr);
    if(!QueryEquipment.next()) return;

    ui->LbPartCode->setText(QueryEquipment.value("PartCode").toString());
    ui->tableWidget->item(0,1)->setText(QueryEquipment.value("Type").toString());
    ui->tableWidget->item(1,1)->setText(QueryEquipment.value("Name").toString());
    ui->tableWidget->item(2,1)->setText(QueryEquipment.value("Supplier").toString());
    ui->tableWidget->item(3,1)->setText(QueryEquipment.value("OrderNum").toString());
    ui->tableWidget->item(4,1)->setText("");
}

void DialogTerminalAttr::on_BtnReplaceTerminalSymbol_clicked()
{
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"确认批修改端子?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }

    SymbolTermCountChanged=true;
}

void DialogTerminalAttr::on_BtnAdd_clicked()
{
    ui->tableWidget_shortConnect->setRowCount(ui->tableWidget_shortConnect->rowCount()+1);
    ui->tableWidget_shortConnect->setItem(ui->tableWidget_shortConnect->rowCount()-1,0,new QTableWidgetItem(""));
}

void DialogTerminalAttr::on_BtnInsert_clicked()
{
    if(ui->tableWidget_shortConnect->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", " 请选择插入行！");
        return;
    }
    int currentRowIndex=ui->tableWidget_shortConnect->currentRow();
    ui->tableWidget_shortConnect->insertRow(currentRowIndex);
    ui->tableWidget_shortConnect->setItem(currentRowIndex,0,new QTableWidgetItem(""));
}

void DialogTerminalAttr::on_BtnDelete_clicked()
{
    if(ui->tableWidget_shortConnect->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", " 请选择插入行！");
        return;
    }
    ui->tableWidget_shortConnect->removeRow(ui->tableWidget_shortConnect->currentRow());
}
