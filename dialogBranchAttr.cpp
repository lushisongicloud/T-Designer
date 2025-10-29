#include "dialogBranchAttr.h"
#include "ui_dialogBranchAttr.h"
extern QStringList RemovedUnitsInfo;
DialogBranchAttr::DialogBranchAttr(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogBranchAttr)
{
    ui->setupUi(this);
    ui->tableWidgetTermInfo->setRowCount(0);
    ui->tableWidgetTermInfo->setColumnWidth(0,50);
    ui->tableWidgetTermInfo->setColumnWidth(1,150);
    ui->tableWidgetTermInfo->setColumnWidth(2,80);
    ui->tableWidgetTermInfo->setColumnWidth(3,300);
    ui->tableWidgetTermInfo->setColumnWidth(4,70);
    RetCode=0;

    m_scene_term.setBackgroundBrush(Qt::gray);
    ui->graphicsView_Term->setScene(&m_scene_term);
    QPixmap pix("");
    m_scene_term.SetBackGroundImage(pix);

    m_dialogTermTag=new dialogTag(ui->frameTag_Term_2);
    connect(m_dialogTermTag,SIGNAL(DrawTag(int,QColor)),this,SLOT(SlotDrawTermTag(int,QColor)));
}

DialogBranchAttr::~DialogBranchAttr()
{
    delete ui;
}

void DialogBranchAttr::SlotDrawTermTag(int Type,QColor mColor)
{
    if(m_scene_term.items().count()>1)
    {
        QMessageBox::warning(nullptr, "提示", "已标注过！请删除当前标注后重试");
        return;
    }
    if(Type==5)
    {
        BRectangle *m_rectangle = new BRectangle(0, 0, 80, 60, BGraphicsItem::ItemType::Rectangle);
        m_rectangle->m_pen_noSelected=mColor;
        //m_rectangle->m_pen_isSelected=mColor;
        m_rectangle->setPen(mColor);
        m_rectangle->update();
        m_scene_term.addItem(m_rectangle);
    }
    else if(Type==1)
    {
        BEllipse *m_ellipse = new BEllipse(0, 0, 120, 80, BGraphicsItem::ItemType::Ellipse);
        m_ellipse->m_pen_noSelected=mColor;
        //m_ellipse->m_pen_isSelected=mColor;
        m_ellipse->setPen(mColor);
        m_ellipse->update();
        m_scene_term.addItem(m_ellipse);
    }
}

void DialogBranchAttr::LoadSymbolInfo(QString Symbol_ID)
{
    DBSymbol_ID=Symbol_ID;
   //在数据库中根据Symbol_Handle查找符号属性
    QSqlQuery querySymbol=QSqlQuery(T_ProjectDatabase);
    QString sqlstr=QString("SELECT * FROM Symbol WHERE Symbol_ID = "+DBSymbol_ID);
    querySymbol.exec(sqlstr);
    if(!querySymbol.next()) return;
    DBSymbol=querySymbol.value("Symbol").toString();
    DBSymbol_Category=querySymbol.value("Symbol_Category").toString();
    DBFunDefine=querySymbol.value("FunDefine").toString();
    ui->EdDesignation->setText(querySymbol.value("Designation").toString());
    QSqlQuery queryEquipment=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM Equipment WHERE Equipment_ID = "+querySymbol.value("Equipment_ID").toString());
    queryEquipment.exec(sqlstr);
    if(!queryEquipment.next()) return;
    StrProTag=GetProjectStructureStrByProjectStructureID(queryEquipment.value("ProjectStructure_ID").toInt());
    ui->EdUnitProTag->setText(StrProTag+"-"+queryEquipment.value("DT").toString());
    ui->EdUnitTag->setText(queryEquipment.value("DT").toString());
    ui->EdSpurDT->setText(querySymbol.value("Show_DT").toString());
    //连接点信息
    QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
    sqlstr=QString("SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+querySymbol.value("Symbol_ID").toString()+"' ORDER BY ConnNum_Logic");
    querySymb2TermInfo.exec(sqlstr);
    while(querySymb2TermInfo.next())
    {
       ui->tableWidgetTermInfo->setRowCount(ui->tableWidgetTermInfo->rowCount()+1);       
       ui->tableWidgetTermInfo->setItem(ui->tableWidgetTermInfo->rowCount()-1,0,new QTableWidgetItem(querySymb2TermInfo.value("ConnNum").toString()));
       ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->rowCount()-1,0)->setData(Qt::UserRole,querySymb2TermInfo.value("Symb2TermInfo_ID").toString());
       ui->tableWidgetTermInfo->setItem(ui->tableWidgetTermInfo->rowCount()-1,1,new QTableWidgetItem(querySymb2TermInfo.value("ConnDesc").toString()));
       ui->tableWidgetTermInfo->setItem(ui->tableWidgetTermInfo->rowCount()-1,2,new QTableWidgetItem(querySymb2TermInfo.value("TestCost").toString()));

       //端子配置
       ui->tableWidgetTermInfo->setItem(ui->tableWidgetTermInfo->rowCount()-1,3,new QTableWidgetItem(querySymb2TermInfo.value("TermPicPath").toString()));
       if(querySymb2TermInfo.value("TagType").toString()!="")
       {
           ui->tableWidgetTermInfo->setItem(ui->tableWidgetTermInfo->rowCount()-1,4,new QTableWidgetItem("是"));
           ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->rowCount()-1,4)->setData(Qt::UserRole,querySymb2TermInfo.value("TagType").toString()+"|"+querySymb2TermInfo.value("TagColor").toString()+"|"+querySymb2TermInfo.value("TagPos").toString()+"|"+querySymb2TermInfo.value("TagEdge").toString());
       }
       else
           ui->tableWidgetTermInfo->setItem(ui->tableWidgetTermInfo->rowCount()-1,4,new QTableWidgetItem("否"));
    }
    ui->LbFunDefine->setText(querySymbol.value("FunDefine").toString());

    QString StrSymbolName=querySymbol.value("Symbol").toString()+".dwg";
    QString PathDwg;
    if(StrSymbolName.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+StrSymbolName;
    else if(StrSymbolName.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+StrSymbolName;
    UnitSymbolsView(PathDwg,"C:/TBD/data/TempImage/"+querySymbol.value("Symbol").toString()+".jpg",ui->LbFunSymbolView,true);
    /*
    QFileInfo fileDwg(PathDwg);
    if(!fileDwg.exists())
    {
        QPixmap p=QPixmap("");
        ui->LbFunSymbolView->setPixmap(p.scaled(ui->LbFunSymbolView->width(),ui->LbFunSymbolView->height()));
    }
    else
    {
        MxDrawApplication *App=new MxDrawApplication();
        IMxDrawApplication *pApp=(IMxDrawApplication*)App;
        pApp->dynamicCall("DwgToJpg(QString,QString,int,int)",PathDwg,"C:/TBD/data/TempImage/"+querySymbol.value("Symbol").toString()+".jpg",ui->LbFunSymbolView->width(),ui->LbFunSymbolView->height());
        QPixmap p=QPixmap("C:/TBD/data/TempImage/"+querySymbol.value("Symbol").toString()+".jpg");
        ui->LbFunSymbolView->setPixmap(p.scaled(ui->LbFunSymbolView->width(),ui->LbFunSymbolView->height()));
        delete App;
    }*/

    //检索当前符号有几种样式，目前是哪种样式
    //去掉-1，。。进行检索
    ui->CbSymbolPattern->clear();
    QString SearchSymbol=querySymbol.value("Symbol").toString();
    int Index=SearchSymbol.lastIndexOf("-");
    if(Index>=0) SearchSymbol=SearchSymbol.mid(0,Index+1);
    QString SearchFilePath;
    if(StrSymbolName.contains("SPS_")) SearchFilePath="C:/TBD/SPS/";
    else SearchFilePath="C:/TBD/SYMB2LIB/";

    //检索"C:/TBD/SPS/文件夹有几种样式
    //获取所选文件类型过滤器
    QStringList filters;
    //文件过滤
    filters<<QString(SearchSymbol+"*.dwg");

    //定义迭代器并设置过滤器
    QDirIterator dir_iterator(SearchFilePath,
                              filters,
                              QDir::Files | QDir::NoSymLinks);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();
        int index1=file_info.fileName().lastIndexOf("-");
        int index2=file_info.fileName().lastIndexOf(".dwg");
        if(index1>=0)
            ui->CbSymbolPattern->addItem("样式"+file_info.fileName().mid(index1+1,index2-index1-1));
        else
            ui->CbSymbolPattern->addItem("样式1");
    }
    if(Index>=0) ui->CbSymbolPattern->setCurrentText("样式"+querySymbol.value("Symbol").toString().mid(Index+1,querySymbol.value("Symbol").toString().count()-Index-1));
    else ui->CbSymbolPattern->setCurrentText("样式1");
}

//切换样式
void DialogBranchAttr::on_CbSymbolPattern_currentIndexChanged(const QString &arg1)
{
    QSqlQuery querySymbol=QSqlQuery(T_ProjectDatabase);
    QString sqlstr=QString("SELECT * FROM Symbol WHERE Symbol_ID = "+DBSymbol_ID);
    querySymbol.exec(sqlstr);
    if(!querySymbol.next()) return;
    QString StrSymbolName=querySymbol.value("Symbol").toString()+".dwg";
    QString PathDwg;
    if(StrSymbolName.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+StrSymbolName;
    else if(StrSymbolName.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+StrSymbolName;

    int Index=PathDwg.lastIndexOf("-");
    if(Index>=0) PathDwg=PathDwg.mid(0,Index+1);
    PathDwg+=ui->CbSymbolPattern->currentText().mid(2,ui->CbSymbolPattern->currentText().count()-2)+".dwg";
    QFileInfo fileDwg(PathDwg);
    if(!fileDwg.exists()) return;
    //MxDrawApplication *App=new MxDrawApplication();
    //IMxDrawApplication *pApp=(IMxDrawApplication*)App;
    pApp->dynamicCall("DwgToJpg(QString,QString,int,int)",PathDwg,"C:/TBD/data/TempImage/"+querySymbol.value("Symbol").toString()+".jpg",ui->LbFunSymbolView->width(),ui->LbFunSymbolView->height());
    //delete App;
    QPixmap p=QPixmap("C:/TBD/data/TempImage/"+querySymbol.value("Symbol").toString()+".jpg");
    ui->LbFunSymbolView->setPixmap(p.scaled(ui->LbFunSymbolView->width(),ui->LbFunSymbolView->height()));
    DBSymbol=fileDwg.fileName().mid(0,fileDwg.fileName().count()-4);
}

void DialogBranchAttr::on_BtnOk_clicked()
{
    QString GaocengStr,PosStr;
    QString TmpStr=ui->EdUnitProTag->text();
    int indexGaoceng=TmpStr.indexOf("=");
    int indexPos=TmpStr.indexOf("+");
    int indexUnit=TmpStr.indexOf("-");
    if(indexGaoceng>=0) GaocengStr=TmpStr.mid(indexGaoceng+1,indexPos-indexGaoceng-1);
    if(indexPos>=0) PosStr=TmpStr.mid(indexPos+1,indexUnit-indexPos-1);
    int NewProjectStructure_ID=InsertRecordToProjectStructure(0,GaocengStr,PosStr,"");

    QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    int Equipment_ID=0;
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+DBSymbol_ID;
    QuerySymbol.exec(SqlStr);
    if(QuerySymbol.next())
    {
        Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        //查找TerminalStrip
        QSqlQuery QueryEquipment= QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QuerySymbol.value("Equipment_ID").toString();
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            //如果DT与数据库中的记录不同或NewProjectStructure_ID与数据库中的记录不同,则更新Equipment
            bool UpdateEquipment=false;
            if(ui->EdUnitTag->text()!=QueryEquipment.value("DT").toString())
            {
                UpdateEquipment=true;
                DTChanged=true;
            }
            if(NewProjectStructure_ID!=QueryEquipment.value("ProjectStructure_ID").toInt()) UpdateEquipment=true;
            if(UpdateEquipment)
            {
                //这里区分是否为唯一功能子块，如果是唯一功能子块，则修改元件代号，反之则新建或者合并代号
                QSqlQuery QuerySearch= QSqlQuery(T_ProjectDatabase);
                SqlStr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"'";
                QuerySearch.exec(SqlStr);
                QuerySearch.last();
                if(QuerySearch.at()>0)//不是唯一功能子块，查看新代号和位置是否与其他元件重复，如果重复则合并器件，反之则新建元件
                {
     qDebug()<<"不是唯一功能子块";
                    SqlStr="SELECT * FROM Equipment WHERE DT = '"+ui->EdUnitTag->text()+"' AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"' AND Equipment_ID <> "+QString::number(Equipment_ID);
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        SqlStr="UPDATE Symbol SET Equipment_ID=:Equipment_ID WHERE Symbol_ID = "+DBSymbol_ID;
                        QueryVar.prepare(SqlStr);
                        Equipment_ID=QuerySearch.value("Equipment_ID").toInt();
                        QueryVar.bindValue(":Equipment_ID",QuerySearch.value("Equipment_ID").toString());
                        QueryVar.exec();
                    }
                    else//新建器件
                    {
                        SqlStr = "INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Eqpt_Category,Name,Desc,PartCode,SymbRemark,OrderNum,Factory,TVariable,TModel)"
                                          "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Eqpt_Category,:Name,:Desc,:PartCode,:SymbRemark,:OrderNum,:Factory,:TVariable,:TModel)";
                        QueryVar.prepare(SqlStr);
                        Equipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
                        QueryVar.bindValue(":Equipment_ID",Equipment_ID);
                        QueryVar.bindValue(":DT",ui->EdUnitTag->text());
                        QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
                        QueryVar.bindValue(":Type",QueryEquipment.value("Type").toString());
                        QueryVar.bindValue(":Eqpt_Category",QueryEquipment.value("Eqpt_Category").toString());//普通元件还是PLC元件
                        QueryVar.bindValue(":Name",QueryEquipment.value("Name").toString());
                        QueryVar.bindValue(":Desc",QueryEquipment.value("Desc").toString());
                        QueryVar.bindValue(":PartCode",QueryEquipment.value("PartCode").toString());
                        QueryVar.bindValue(":SymbRemark",QueryEquipment.value("SymbRemark").toString());
                        QueryVar.bindValue(":OrderNum",QueryEquipment.value("OrderNum").toString());
                        QueryVar.bindValue(":Factory",QueryEquipment.value("Factory").toString());
                        QueryVar.bindValue(":TVariable",QueryEquipment.value("TVariable").toString());
                        QueryVar.bindValue(":TModel",QueryEquipment.value("TModel").toString());
                        QueryVar.exec();

                        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr="SELECT * FROM EquipmentDiagnosePara WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
                        QuerySearch.exec(SqlStr);
                        while(QuerySearch.next())
                        {
                            int DiagnoseParaID=GetMaxIDOfDB(T_ProjectDatabase,"EquipmentDiagnosePara","DiagnoseParaID");
                            SqlStr = "INSERT INTO EquipmentDiagnosePara (DiagnoseParaID,Equipment_ID,Name,Unit,CurValue,DefaultValue,Remark)"
                                     " VALUES (:DiagnoseParaID,:Equipment_ID,:Name,:Unit,:CurValue,:DefaultValue,:Remark)";
                            QueryVar.prepare(SqlStr);
                            QueryVar.bindValue(":DiagnoseParaID",DiagnoseParaID);
                            QueryVar.bindValue(":Equipment_ID",QString::number(Equipment_ID));
                            QueryVar.bindValue(":Name",QuerySearch.value("Name").toString());
                            QueryVar.bindValue(":Unit",QuerySearch.value("Unit").toString());
                            QueryVar.bindValue(":CurValue",QuerySearch.value("CurValue").toString());
                            QueryVar.bindValue(":DefaultValue",QuerySearch.value("DefaultValue").toString());
                            QueryVar.bindValue(":Remark",QuerySearch.value("Remark").toString());
                            QueryVar.exec();
                        }
                    }
                }
                else//是唯一功能子块，查看新代号和位置是否与其他元件重复，如果重复则删除当前器件并更新子块的Equipment_ID
                {
                    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    QString SqlStr="SELECT * FROM Equipment WHERE DT = '"+ui->EdUnitTag->text()+"' AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"' AND Equipment_ID <> "+QString::number(Equipment_ID);
            qDebug()<<"SqlStr="<<SqlStr;
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                       //元件标号被修改，存在相同标号的元件,询问是否合并元件
                        QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"该元件已存在，是否合并功能子块?",
                                                    QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

                        if(result==QMessageBox::Yes)
                        {
                            //删除原Equipment表中的记录，将原元件关联的Symbol关联到新的Equipment表记录
                            QString CombineEquipment_ID=QuerySearch.value("Equipment_ID").toString();

                            QString StrUnitsInfo;
                            QSqlQuery query=QSqlQuery(T_ProjectDatabase);
                            QString temp="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID);
                            query.exec(temp);
                            if(query.next())
                            {
                                //DT,ProjectStructure_ID,Type,Spec,Eqpt_Category,Name,Desc,PartCode,OrderNum,Factory,Remark,TVariable,TModel
                                StrUnitsInfo+=query.value("DT").toString();
                                StrUnitsInfo+=","+query.value("ProjectStructure_ID").toString();
                                StrUnitsInfo+=","+query.value("Type").toString();
                                StrUnitsInfo+=","+query.value("Spec").toString();
                                StrUnitsInfo+=","+query.value("Eqpt_Category").toString();
                                StrUnitsInfo+=","+query.value("Name").toString();
                                StrUnitsInfo+=","+query.value("Desc").toString();
                                StrUnitsInfo+=","+query.value("PartCode").toString();
                                StrUnitsInfo+=","+query.value("OrderNum").toString();
                                StrUnitsInfo+=","+query.value("Factory").toString();
                                StrUnitsInfo+=","+query.value("Remark").toString();
                                StrUnitsInfo+=","+query.value("TVariable").toString();
                                StrUnitsInfo+=","+query.value("TModel").toString();
                                RemovedUnitsInfo.append(StrUnitsInfo);
                            }

                            SqlStr="DELETE FROM Equipment WHERE Equipment_ID = "+QString::number(Equipment_ID);
                            QuerySearch.exec(SqlStr);
                            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                            SqlStr="UPDATE Symbol SET Equipment_ID=:Equipment_ID WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"'";
                            QuerySymbol.prepare(SqlStr);
                            QuerySymbol.bindValue(":Equipment_ID",CombineEquipment_ID);
                            QuerySymbol.exec();
                            Equipment_ID=CombineEquipment_ID.toInt();
                        }
                        else return;
                    }

    qDebug()<<"是唯一功能子块，更新元件";
                    SqlStr="UPDATE Equipment SET DT=:DT,ProjectStructure_ID=:ProjectStructure_ID"
                                            " WHERE Equipment_ID = "+QString::number(Equipment_ID);
                    QueryVar.prepare(SqlStr);
                    QueryVar.bindValue(":DT",ui->EdUnitTag->text());
                    QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
                    QueryVar.exec();
                }
            }
        }
    }

    QSqlQuery querySymbol(T_ProjectDatabase);
    QString tempSQL=QString("UPDATE Symbol SET Symbol=:Symbol,Equipment_ID=:Equipment_ID,Symbol_Category=:Symbol_Category,Designation=:Designation,Characteristics=:Characteristics,FunctionText=:FunctionText,EngravingText=:EngravingText,MountingSite=:MountingSite,FunDefine=:FunDefine"
                            " WHERE Symbol_ID = "+DBSymbol_ID);
    querySymbol.prepare(tempSQL);
    querySymbol.bindValue(":Symbol",DBSymbol);
    querySymbol.bindValue(":Equipment_ID",Equipment_ID);
    querySymbol.bindValue(":Symbol_Category",DBSymbol_Category);
    querySymbol.bindValue(":Designation",ui->EdDesignation->text());

    querySymbol.bindValue(":FunDefine",DBFunDefine);
    querySymbol.exec();

    //连接点信息
    QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
    for(int i=0;i<ui->tableWidgetTermInfo->rowCount();i++)
    {
        tempSQL=QString("UPDATE Symb2TermInfo SET ConnNum=:ConnNum,ConnDesc=:ConnDesc,ConnDirection=:ConnDirection,Internal=:Internal,TestCost=:TestCost WHERE Symbol_ID = "+DBSymbol_ID+" AND ConnNum_Logic = '"+QString::number(i+1)+"'");
qDebug()<<tempSQL;
        querySymb2TermInfo.prepare(tempSQL);
        querySymb2TermInfo.bindValue(":ConnNum",ui->tableWidgetTermInfo->item(i,0)->text());
        querySymb2TermInfo.bindValue(":ConnDesc",ui->tableWidgetTermInfo->item(i,1)->text());
        QString PathDwg;
        if(DBSymbol.contains("ES2_")) PathDwg+="C:/TBD/SYMB2LIB/"+DBSymbol+".dwg";
        else if(DBSymbol.contains("SPS_")) PathDwg+="C:/TBD/SPS/"+DBSymbol+".dwg";
        QStringList ListTermInfo=GetDwgTermData(PathDwg,DBSymbol,i+1);
        if(ListTermInfo.count()==2)
        {
            querySymb2TermInfo.bindValue(":ConnDirection",ListTermInfo.at(0));
            querySymb2TermInfo.bindValue(":Internal",ListTermInfo.at(1));
        }
        else
        {
            querySymb2TermInfo.bindValue(":ConnDirection","");
            querySymb2TermInfo.bindValue(":Internal","");
        }
        querySymb2TermInfo.bindValue(":TestCost",ui->tableWidgetTermInfo->item(i,2)->text());
        querySymb2TermInfo.exec();
    }
    RetCode=1;
    close();
}

void DialogBranchAttr::on_BtnCancel_clicked()
{
    RetCode=0;
    close();
}

void DialogBranchAttr::on_tableWidgetTermInfo_clicked(const QModelIndex &index)
{
    m_scene_term.clear();
    QPixmap pix(ui->tableWidgetTermInfo->item(index.row(),3)->text());
    m_scene_term.SetBackGroundImage(pix);
    ui->graphicsView_Term->ScaleToWidget();
    CurImgPath=ui->tableWidgetTermInfo->item(index.row(),3)->text();
    CurUnitImageIndex=0;

    LoadPicTag(ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),4)->data(Qt::UserRole).toString(),ui->graphicsView_Term);
}

void DialogBranchAttr::on_BtnUnitAttr_clicked()
{
    RetCode=2;
    this->close();
}



void DialogBranchAttr::on_BtnProSet_clicked()
{
    dlgPageNameSet.LoadTable(ui->EdUnitProTag->text(),2);//Mode=1:Page项目代号  Mode=2:Unit项目代号  Mode=3:Terminal项目代号
    dlgPageNameSet.HideEdPageName();
    dlgPageNameSet.setModal(true);
    dlgPageNameSet.show();
    dlgPageNameSet.exec();
    if(!dlgPageNameSet.Canceled)
    {
        StrProTag=dlgPageNameSet.ReturnTerminalPro;
        ui->EdUnitProTag->setText(dlgPageNameSet.ReturnTerminalPro+"-"+ui->EdUnitTag->text());
    }
}

void DialogBranchAttr::on_EdUnitTag_textChanged(const QString &arg1)
{
    ui->EdUnitProTag->setText(StrProTag+"-"+ui->EdUnitTag->text());
}

void DialogBranchAttr::on_BtnReplaceFunSymbol_clicked()
{

}

void DialogBranchAttr::on_BtnCancelTermSign_2_clicked()
{
    QList<QGraphicsItem *> list = m_scene_term.items();
    for(int i=0;i<list.count();i++)
    {
        if(list[i]->type()!=7)
        {
            m_scene_term.removeItem(list[i]);
        }
    }
}

void DialogBranchAttr::on_BtnSaveTerm_2_clicked()
{
    if(ui->tableWidgetTermInfo->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", "请选择有效端口后重试！");
        return;
    }
    QList<QGraphicsItem *> list = m_scene_term.items();
    qDebug()<<"list.count()="<<list.count();
    if(list.count()==4)
    {
        QSqlQuery querySymb2TermInfo(T_ProjectDatabase);
        QString SqlStr=  "UPDATE Symb2TermInfo SET TestCost=:TestCost,TermPicPath=:TermPicPath,TagType=:TagType,TagPos=:TagPos,TagEdge=:TagEdge,TagColor=:TagColor WHERE Symb2TermInfo_ID = "+ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),0)->data(Qt::UserRole).toString();
        querySymb2TermInfo.prepare(SqlStr);
        querySymb2TermInfo.bindValue(":TestCost",ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),2)->text());
        querySymb2TermInfo.bindValue(":TermPicPath",CurImgPath);

        for(int i=0;i<4;i++) qDebug()<<"type="<<list[i]->type()<<"over";
        QString StrTagInfo;
        BGraphicsItem *item;
        for(int i=0;i<4;i++)
        {
            qDebug()<<"CurType="<<list[i]->type();
            if(list[i]->type()!=7)
            {
                item = static_cast<BGraphicsItem *>(list[i]);
                BGraphicsItem::ItemType type = item->getType();
                qDebug()<<"getType="<<type;
                if(((int)type==1)||((int)type==5))
                {
                    querySymb2TermInfo.bindValue(":TagType",(int)type);
                    StrTagInfo+=QString::number(type)+"|"+QString::number(m_dialogTermTag->CurTagColor);

                    QString StrTagPos=QString::number(item->x(),'f',2)+","+QString::number(item->y(),'f',2);
                    querySymb2TermInfo.bindValue(":TagPos",StrTagPos);
                    StrTagInfo+="|"+StrTagPos;

                    QString StrTagEdge;
                    switch (type)
                    {
                    case BGraphicsItem::ItemType::Ellipse: {
                        BEllipse *ellipse = static_cast<BEllipse *>(item);
                        StrTagEdge=QString::number(ellipse->getEdge().x(),'f',2)+","+QString::number(ellipse->getEdge().y(),'f',2);
                    } break;
                    case BGraphicsItem::ItemType::Rectangle: {
                        BRectangle *rectangle = static_cast<BRectangle *>(item);
                        StrTagEdge=QString::number(rectangle->getEdge().x(),'f',2)+","+QString::number(rectangle->getEdge().y(),'f',2);
                    } break;
                    default: break;
                    }
                    querySymb2TermInfo.bindValue(":TagEdge",StrTagEdge);
                    querySymb2TermInfo.bindValue(":TagColor",(int)m_dialogTermTag->CurTagColor);
                    StrTagInfo+="|"+StrTagEdge;
                }
            }
        }
        querySymb2TermInfo.exec();
        //更新表格
        ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),3)->setText(CurImgPath);
        ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),4)->setText("是");
        ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),4)->setData(Qt::UserRole,StrTagInfo);
    }
    else if(list.count()==1)
    {
        QSqlQuery querySymb2TermInfo(T_ProjectDatabase);
        QString SqlStr=  "UPDATE Symb2TermInfo SET TestCost=:TestCost,TermPicPath=:TermPicPath WHERE Symb2TermInfo_ID = "+ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),0)->data(Qt::UserRole).toString();
        querySymb2TermInfo.prepare(SqlStr);
        querySymb2TermInfo.bindValue(":TestCost",ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),2)->text());
        querySymb2TermInfo.bindValue(":TermPicPath",CurImgPath);
        querySymb2TermInfo.exec();
        //更新表格
        ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),3)->setText(CurImgPath);
        ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),4)->setText("否");
        ui->tableWidgetTermInfo->item(ui->tableWidgetTermInfo->currentRow(),4)->setData(Qt::UserRole,"");
    }
}

void DialogBranchAttr::on_BtnFromUnitImage_2_clicked()
{
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+DBSymbol_ID;
    QuerySearch.exec(SqlStr);
    if(QuerySearch.next())
    {
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr="SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySearch.value("Equipment_ID").toString();
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
qDebug()<<"Picture="<<QueryEquipment.value("Picture").toString();
            QStringList ListPictureInfo=QueryEquipment.value("Picture").toString().split("￤");
            if(CurUnitImageIndex<ListPictureInfo.count())
            {
                QString OnePictureInfo=ListPictureInfo.at(CurUnitImageIndex);
                QString PicPath;
                if(OnePictureInfo.contains("*")) PicPath=OnePictureInfo.mid(0,OnePictureInfo.indexOf("*"));
                else PicPath=OnePictureInfo;
                QPixmap pix(PicPath);
                m_scene_term.SetBackGroundImage(pix);
                ui->graphicsView_Term->ScaleToWidget();
                CurImgPath=PicPath;
            }
            CurUnitImageIndex++;
            if(CurUnitImageIndex>=ListPictureInfo.count()) CurUnitImageIndex=0;
        }
    }
}

void DialogBranchAttr::on_BtnFromDisk_2_clicked()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("选择文件"));
    fileDialog.setDirectory(PIC_BASE_PATH);
    fileDialog.setNameFilter(tr("Images (*.png *.xpm *.jpg *.jpeg *.gif *.webp)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    if(fileNames.count()!=1)
    {
        QMessageBox::warning(nullptr, "提示", "请选择一张图片！");
        return;
    }
    QPixmap pix(fileNames.at(0));
    m_scene_term.SetBackGroundImage(pix);
    ui->graphicsView_Term->ScaleToWidget();
    CurImgPath=fileNames.at(0);
}
