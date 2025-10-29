#include "dialogsymbolattribute.h"
#include "ui_dialogsymbolattribute.h"

DialogSymbolAttribute::DialogSymbolAttribute(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogSymbolAttribute)
{
    ui->setupUi(this);
    Canceled=true;
    IsGettingBasePoint=false;
    initTable();
    dlgModifyPTermial=new DialogModifyPTermial(this);
    connect(this,SIGNAL(GetUrPoint(IMxDrawPoint*)),dlgModifyPTermial,SLOT(SlotGetUrPoint(IMxDrawPoint*)));
    connect(this,SIGNAL(SignalUpdateAttrdefTable(QString,qlonglong)),dlgModifyPTermial,SLOT(SlotUpdateAttrdefTable(QString,qlonglong)));
    connect(this,SIGNAL(SignalAddAttrdefTable(QString,qlonglong)),dlgModifyPTermial,SLOT(SlotAddAttrdefTable(QString,qlonglong)));

}

DialogSymbolAttribute::~DialogSymbolAttribute()
{
    delete ui;
}
void DialogSymbolAttribute::closeEvent(QCloseEvent *event)
{
    emit(DialogIsClosed());
}
//初始化端号表
void DialogSymbolAttribute::initTable()
{
   ui->tableWidget->setColumnWidth(0,40);
   ui->tableWidget->setColumnWidth(1,40);
   ui->tableWidget->setColumnWidth(2,50);
   ui->tableWidget->setColumnWidth(3,95);
   ui->tableWidget_AttrDef->setColumnWidth(0,200);
}

void DialogSymbolAttribute::GetDwgCenterPos(double &x,double &y)
{
    double xmin,ymin,xmax,ymax;
    bool FirstEnty=true;
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    // 得到当前图纸空间
    IMxDrawBlockTableRecord* blkRec = (IMxDrawBlockTableRecord*)database->querySubObject("CurrentSpace()");
    // 创建一个用于遍历当前图纸空间的遍历器
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    if (iter == nullptr) return;// 循环得到所有实体
    bool NotNone=false;
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        qDebug()<<"iter";
        IMxDrawEntity* Enty = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(tmp_MxDrawWidget,Enty)) continue;//去除erase的实体
        if (Enty == nullptr)  continue;
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference") continue;
        if(Enty->dynamicCall("ObjectName()").toString()=="McDbText") continue;
        NotNone=true;
        IMxDrawPoints* pts=(IMxDrawPoints*)Enty->querySubObject("GetBoundingBox2()");
        for(int j=0;j<pts->Count();j++)
        {
            IMxDrawPoint* pt = (IMxDrawPoint*)pts->querySubObject("Item(int)",j);
            if(pt==nullptr) continue;
            qDebug()<<pt->dynamicCall("x()").toDouble()<<" "<<pt->dynamicCall("y()").toDouble();
            if(FirstEnty)
            {
                FirstEnty=false;
                xmin= pt->x();xmax= pt->x();
                ymin= pt->y();ymax= pt->y();
            }
            else
            {
                xmin=xmin<pt->x()?xmin:pt->x();
                xmax=xmax>pt->x()?xmax:pt->x();
                ymin=ymin<pt->y()?ymin:pt->y();
                ymax=ymax>pt->y()?ymax:pt->y();
            }
        }
    }
    if(NotNone)
    {
        x=(xmin+xmax)/2;
        y=(ymin+ymax)/2;
    }
}
//根据文件名称SymbolFileName载入符号属性
void DialogSymbolAttribute::LoadSymbolAttribute()
{
    qDebug()<<"LoadSymbolAttribute";
    //如果有块的话就将块打碎
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)tmp_MxDrawWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT",5020);
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    for(int i=0;i<Cnt;i++)
    {
       IMxDrawBlockReference *BlkEnty = (IMxDrawBlockReference*)ss1->querySubObject("Item(int)",i);
       if(EntyIsErased(tmp_MxDrawWidget,(IMxDrawEntity *)BlkEnty)) continue;//去除erase的实体
       QList<IMxDrawPolyline*> listBlkTerms=GetTermEnty(tmp_MxDrawWidget,BlkEnty->dynamicCall("GetBlockName()").toString());
       for(int j=0;j<listBlkTerms.count();j++) listBlkTerms.at(j)->setProperty("Visible",true);
       BlkEnty->querySubObject("Explode()");
       BlkEnty->dynamicCall("Erase()");
    }
qDebug()<<"如果有块的话就将块打碎";
    //如果是新建的符号，将基点设置为dwg的中心
    double InsbasePtx=0,InsbasePty=0;

    if(DataBaseSymbolID=="")
    {
        GetDwgCenterPos(InsbasePtx,InsbasePty);
        IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
        MxDrawPoint *ptm=new MxDrawPoint();
        IMxDrawPoint *pt=(IMxDrawPoint *)ptm;
        pt->setX(InsbasePtx);
        pt->setY(InsbasePty);
        database->dynamicCall("SetInsbase(QAxObject*)",pt->asVariant());      
    }
qDebug()<<"如果是新建的符号，将基点设置为dwg的中心";
    QString tmpStr;
    ui->EditSymbolName->setText("");
    ui->EditSymbolTag->setText("");
    if((DataBaseSymbolID!="")&&(readGlobalVar(tmp_MxDrawWidget,"LD_SYMB1LIB_DICITIONARY","LD_SYMB1LIB_XRECORD")!=nullptr))
    {
       IMxDrawResbuf *resp =readGlobalVar(tmp_MxDrawWidget,"LD_SYMB1LIB_DICITIONARY","LD_SYMB1LIB_XRECORD");
       if(resp!=nullptr)
       {
           for(int i=0;i<resp->Count();i++)
           {
               if(resp->AtString(i)=="推荐名称") ui->EditSymbolName->setText(resp->AtString(i+1));
               if(resp->AtString(i)=="推荐标号") ui->EditSymbolTag->setText(resp->AtString(i+1));              
           }
       }
    }
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    IMxDrawPoint *InsbasePt =(IMxDrawPoint*)database->querySubObject("Insbase()");
    if(InsbasePt!=nullptr)
    {
        ui->EdBasePointX->setText(QString::number(InsbasePt->x(),'f',2));
        ui->EdBasePointY->setText(QString::number(InsbasePt->y(),'f',2));
    }
    //根据符号大类确定符号类型
    if(SymbolType.contains("PLC")) LoadAttrDefTable(2);
    else if(SymbolType=="端子"||SymbolType=="插针") LoadAttrDefTable(3);
    else if(SymbolType=="元件连接点") LoadAttrDefTable(4);
    else LoadAttrDefTable(1);

    ui->tableWidget->setRowCount(0);
    QList<IMxDrawPolyline*> listTerms=GetCurrentSpaceTerms(tmp_MxDrawWidget);
    //lTermId.clear();

    /*
    //在数据库中查看有几个端口
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Symb2Lib WHERE Symb2Lib_ID = '"+DataBaseSymbolID+"'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    int TermCount=0;
    if(QueryVar.value("TermCount").toString()!="") TermCount=QueryVar.value("TermCount").toString().toInt();
    if(TermCount<=0) return;*/
    ui->tableWidget->setRowCount(listTerms.count());
    // 循环得到所有实体
    for (int i=0;i<listTerms.count();i++)
    {
        if(listTerms.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString()=="1")
        {
            IMxDrawDictionary *myDict=(IMxDrawDictionary *)listTerms.at(i)->querySubObject("GetExtensionDictionary()");
            if(myDict!=nullptr)  qDebug()<<"ExtensionDictionary!=nullptr";
        }
        //读取端口属性
        listTerms.at(i)->setProperty("Visible",true);

        //lTermId.append(listTerms.at(i)->ObjectID());
        int TERMPOINT=0;
        if(listTerms.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString()!="")
          TERMPOINT=listTerms.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString().toInt();
        //if((TERMPOINT<1)||(TERMPOINT>TermCount)) continue;
        ui->tableWidget->setItem(TERMPOINT-1,0,new QTableWidgetItem(QString::number(TERMPOINT)));//关联引脚序号
        ui->tableWidget->item(TERMPOINT-1,0)->setData(Qt::UserRole,QVariant(listTerms.at(i)->ObjectID()));
        ui->tableWidget->setItem(TERMPOINT-1,1,new QTableWidgetItem(listTerms.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString()));//连线方向
        listTerms.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB_CZTERM",0).toString();
        if(tmp_MxDrawWidget->dynamicCall("IsOk()").toString()=="true")//若存在LD_SYMB_CZTERM关键字则为不接线端
            ui->tableWidget->setItem(TERMPOINT-1,2,new QTableWidgetItem("是"));//不接线端
        else
            ui->tableWidget->setItem(TERMPOINT-1,2,new QTableWidgetItem(""));

        int VCnt=listTerms.at(i)->property("NumVerts").toInt();
        if(VCnt!=2) continue;
        double ptx=0;
        double pty=0;
        for(int k=0;k<VCnt;k++)
        {
            IMxDrawPoint* pt= (IMxDrawPoint*) listTerms.at(i)->querySubObject("GetPointAt(int)",k);
            ptx+=pt->x()/2;
            pty+=pt->y()/2;
        }
        tmpStr="("+QString::number(ptx,'f',2)+","+QString::number(pty,'f',2)+")";
        ui->tableWidget->setItem(TERMPOINT-1,3,new QTableWidgetItem(tmpStr));
    }
    SetCurLayerVisible(tmp_MxDrawWidget,"LY_Attdef",true);
    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");
    /*
    //根据符号类别确定
    QString Symb2Class_ID=QueryVar.value("Symb2Class_ID").toString();
    temp = QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+Symb2Class_ID+"'");//level=4
    QueryVar.exec(temp);
    if(QueryVar.next())
    {
        temp = QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QueryVar.value("Parent_ID").toString()+"'");//level=3
        QueryVar.exec(temp);
        if(QueryVar.next())
        {
            temp = QString("SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QueryVar.value("Parent_ID").toString()+"'");//level=2
            QueryVar.exec(temp);
            if(QueryVar.next())
            {
               CheckSymbolType(QueryVar.value("Desc").toString());
            }
        }
    }*/
}
void DialogSymbolAttribute::CheckSymbolType(QString DescStr)
{
    if((DescStr=="端子")||(DescStr=="插针"))
    {
        ui->CbSymbolType->setCurrentIndex(3);
        LoadAttrDefTable(3);
    }
    else if(DescStr=="PLC连接点")
    {
        ui->CbSymbolType->setCurrentIndex(2);
        LoadAttrDefTable(2);
    }
    else if(DescStr=="元件连接点")
    {
        ui->CbSymbolType->setCurrentIndex(4);
        LoadAttrDefTable(4);
    }
}

void DialogSymbolAttribute::SetTerminalData()
{
    //将端子信息写入到端子属性中
    IMxDrawResbuf *resp =(IMxDrawResbuf *) tmp_MxDrawWidget->querySubObject("NewResbuf()");
    //此处为符号的属性，包括符号方向(水平或者垂直)、逻辑端号自动标注为实际端号、实际端号显示、实际端号隐藏
    resp->RemoveAll();
    resp->AddString("推荐名称");
    resp->AddString(ui->EditSymbolName->text());
    resp->AddString("推荐型号");
    resp->AddString("");
    resp->AddString("推荐编码");
    resp->AddString("");
    resp->AddString("推荐标号");
    resp->AddString(ui->EditSymbolTag->text());
    resp->AddString("标号X坐标");
    resp->AddString("");
    resp->AddString("标号Y坐标");
    resp->AddString("");
    resp->AddString("方向");
    resp->AddString("");
    resp->AddString("端号自动标注");
    resp->AddString("");
    resp->AddString("端号隐藏");
    resp->AddString("");
    //resp->AddString("符号类型");
    //resp->AddString(ui->CbSymbolType->currentText());
    wirteGlobalVer(tmp_MxDrawWidget,"LD_SYMB1LIB_DICITIONARY","LD_SYMB1LIB_XRECORD", resp);//符号标号
    delete resp;

    //此处为端子属性，包括逻辑端号、端子连线方向(向左/向右/向上/向下)、是否为不接线端、端子位置、端子文字位置(可缺省)
    for(int i=0;i<ui->tableWidget->rowCount();i++)
    {
        qlonglong lID=ui->tableWidget->item(i,0)->data(Qt::UserRole).toLongLong();
        IMxDrawEntity * enty=  (IMxDrawEntity *)tmp_MxDrawWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
        if(enty==nullptr) continue;
        enty->dynamicCall("SetxDataString(QString,int,QString)","LD_SYMB1LIB_TERMPOINT",0,ui->tableWidget->item(i,0)->text());//逻辑端号
        enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,ui->tableWidget->item(i,1)->text());//端子连线方向 向左/向右/向上/向下
        if(ui->tableWidget->item(i,2)->text()=="是") enty->dynamicCall("SetxDataString(QString,int,QString)","LD_SYMB_CZTERM",0,"");
        else enty->dynamicCall("DeleteXData(QString)","LD_SYMB_CZTERM");
    }
}
void DialogSymbolAttribute::on_BtnOK_clicked()
{
    /*
    if(ui->tableWidget->rowCount()<=0)
    {
        QMessageBox::warning(nullptr, "提示", "还未添加逻辑端号！");
        return;
    }*/
    if(SymbolFileName.contains("ES2_M_")&&(ui->tableWidget->rowCount()<=1))
    {
        QMessageBox::warning(nullptr, "提示", "多端符号必须有多于一个的端点");
        return;
    }
    /*
    if((GetAttrDefTextString(tmp_MxDrawWidget,"设备标识符(显示)")=="未找到")&&(GetAttrDefTextString(tmp_MxDrawWidget,"连接点代号（带显示设备标识符）")=="未找到"))
    {
        QMessageBox::warning(nullptr, "提示", "还未添加设备标识符");
        return;
    }*/
    if((!StrIsDouble(ui->EdBasePointX->text()))||(!StrIsDouble(ui->EdBasePointY->text())))
    {
        QMessageBox::warning(nullptr, "提示", "基点坐标设置错误！");
        return;
    }

    //设置基点
    IMxDrawDatabase* database = (IMxDrawDatabase*)tmp_MxDrawWidget->querySubObject("GetDatabase()");
    MxDrawPoint *ptm=new MxDrawPoint();
    IMxDrawPoint *pt=(IMxDrawPoint *)ptm;
    pt->setX(ui->EdBasePointX->text().toDouble());
    pt->setY(ui->EdBasePointY->text().toDouble());
    database->dynamicCall("SetInsbase(QAxObject*)",pt->asVariant());

    //更新数据库，如果是新建的符号，需要创建Symb2Class和Symb2Lib记录
    //如果是编辑符号，需要更新Symb2Lib的TermCount
    QSqlQuery querySymb2Lib(T_LibDatabase);
    QString SqlStr;
    if(DataBaseSymbolID!="")
    {
        SqlStr="UPDATE Symb2Lib SET TermCount=:TermCount WHERE Symb2Lib_ID = '"+DataBaseSymbolID+"'";
        querySymb2Lib.prepare(SqlStr);
        querySymb2Lib.bindValue(":TermCount",ui->tableWidget->rowCount());
        querySymb2Lib.exec();
    }
    else
    {
        QString CurSelectSymb2Class_ID=InsertOrUpdateSymb2Lib(0,"",FunctionDefineClass_ID,SymbolFileName,ui->tableWidget->rowCount());
        emit(SignalUpdateLib(CurSelectSymb2Class_ID));
    }

    SetTerminalData();
    QList<IMxDrawPolyline*> listTerms=GetCurrentSpaceTerms(tmp_MxDrawWidget);
    for(int i=0;i<listTerms.count();i++)
    {
       listTerms.at(i)->setProperty("Visible",false);
    }
    SetCurLayerVisible(tmp_MxDrawWidget,"LY_Attdef",false);
    Canceled=false;
    this->hide();
    this->close();
}

void DialogSymbolAttribute::on_BtnAddTerminal_clicked()
{
    //如果是单端符号，最多一个端口
    if(SymbolFileName.contains("ES2_S"))
    {
        if(ui->tableWidget->rowCount()>0)
        {
            QMessageBox::warning(nullptr, "提示", "单端符号只能有一个端点！");
            return;
        }
    }
    dlgModifyPTermial->setWindowTitle("添加");
    dlgModifyPTermial->TerminalPointIsNull=true;
    dlgModifyPTermial->TerminalName=QString::number(ui->tableWidget->rowCount()+1);
    dlgModifyPTermial->LineDirection="";
    dlgModifyPTermial->NoLine="";
    dlgModifyPTermial->tmp_MxDrawWidget=tmp_MxDrawWidget;
    dlgModifyPTermial->LoadTerminalInfo();
    dlgModifyPTermial->show();
    dlgModifyPTermial->raise();
    dlgModifyPTermial->exec();

    if(dlgModifyPTermial->Canceled) return;
    ui->tableWidget->setRowCount(ui->tableWidget->rowCount()+1);
    ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,0,new QTableWidgetItem(dlgModifyPTermial->TerminalName));
    ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,1,new QTableWidgetItem(dlgModifyPTermial->LineDirection));
    ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,2,new QTableWidgetItem(dlgModifyPTermial->NoLine));
    QString tmpStr="("+QString::number(dlgModifyPTermial->TerminalPointX,'f',2)+","+QString::number(dlgModifyPTermial->TerminalPointY,'f',2)+")";
    ui->tableWidget->setItem(ui->tableWidget->rowCount()-1,3,new QTableWidgetItem(tmpStr));

    //更新图
    SetCurLayer(tmp_MxDrawWidget,"0");
    tmp_MxDrawWidget->setProperty("LineWidth",0.1);
    tmp_MxDrawWidget->setProperty("DrawCADColor", QColorToInt(QColor(255,0,0)));
    tmp_MxDrawWidget->dynamicCall("PathMoveTo(double,double)",dlgModifyPTermial->TerminalPointX-0.5,dlgModifyPTermial->TerminalPointY);
    tmp_MxDrawWidget->dynamicCall("PathLineTo(double,double)",dlgModifyPTermial->TerminalPointX+0.5,dlgModifyPTermial->TerminalPointY);

    qlonglong lID=tmp_MxDrawWidget->dynamicCall("DrawPathToPolyline()").toLongLong();
    ui->tableWidget->item(ui->tableWidget->rowCount()-1,0)->setData(Qt::UserRole,QVariant(lID));
    //lTermId.append(lID);
    IMxDrawPolyline* Newent= (IMxDrawPolyline*) tmp_MxDrawWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    Newent->setProperty("IsClosedStatus",true);
    Newent->dynamicCall("SetBulgeAt(int,double)",0,1) ;
    Newent->dynamicCall("SetBulgeAt(int,double)",1,1) ;
    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");

}

void DialogSymbolAttribute::SlotGetUrPoint(IMxDrawPoint *point)
{
    if(IsGettingBasePoint)
    {
        IsGettingBasePoint=false;
        ui->EdBasePointX->setText(QString::number(point->x(),'f',2));
        ui->EdBasePointY->setText(QString::number(point->y(),'f',2));
    }
    else emit(GetUrPoint(point));
}

void DialogSymbolAttribute::SlotDrawAttrDefDone(QString Tag,qlonglong AttrDefID)
{
    if(StrIsNumber(Tag)||Tag.contains("符号的连接点描述")) emit(SignalUpdateAttrdefTable(Tag,AttrDefID));
    else
    {
        for(int i=0;i<ui->tableWidget_AttrDef->rowCount();i++)
        {
            if(ui->tableWidget_AttrDef->item(i,0)->text()==Tag)  ui->tableWidget_AttrDef->removeRow(i);
        }
    }
}

void DialogSymbolAttribute::SlotDrawAttrDefDelete(QString Tag,qlonglong AttrDefID)
{
    if(StrIsNumber(Tag)||Tag.contains("符号的连接点描述")) emit(SignalAddAttrdefTable(Tag,AttrDefID));
    else
    {
        ui->tableWidget_AttrDef->insertRow(0);
        ui->tableWidget_AttrDef->setItem(0,0,new QTableWidgetItem(Tag));
    }
}

void DialogSymbolAttribute::on_BtnModify_clicked()
{
    if(ui->tableWidget->currentRow()<0)
    {
        QMessageBox::information(this, "机电液系统集成设计环境", "没有选择要修改的符号端点");
        return;
    }
    dlgModifyPTermial->setWindowTitle("修改");
    dlgModifyPTermial->tmp_MxDrawWidget=tmp_MxDrawWidget;
    //dlg->setModal(true);
    dlgModifyPTermial->TerminalName=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->text();
    dlgModifyPTermial->LineDirection=ui->tableWidget->item(ui->tableWidget->currentRow(),1)->text();
    dlgModifyPTermial->NoLine=ui->tableWidget->item(ui->tableWidget->currentRow(),2)->text();
    dlgModifyPTermial->TerminalPointIsNull=ui->tableWidget->item(ui->tableWidget->currentRow(),3)->text()=="";
    QString TmpStr1,TmpStr2;
    TmpStr1=ui->tableWidget->item(ui->tableWidget->currentRow(),3)->text().split(",").at(0);//(100
    TmpStr2=ui->tableWidget->item(ui->tableWidget->currentRow(),3)->text().split(",").at(1);//200)
    double TerminalPointx=TmpStr1.mid(1,TmpStr1.length()).toDouble(); //(100,200)
    double TerminalPointy=TmpStr2.mid(0,TmpStr1.length()-1).toDouble(); //(100,200)

    dlgModifyPTermial->TerminalPointX=TerminalPointx;
    dlgModifyPTermial->TerminalPointY=TerminalPointy;
    dlgModifyPTermial->LoadTerminalInfo();
    dlgModifyPTermial->show();
    dlgModifyPTermial->raise();
    dlgModifyPTermial->exec();
    if(dlgModifyPTermial->Canceled) return;
    ui->tableWidget->item(ui->tableWidget->currentRow(),0)->setText(dlgModifyPTermial->TerminalName);
    ui->tableWidget->item(ui->tableWidget->currentRow(),1)->setText(dlgModifyPTermial->LineDirection);
    ui->tableWidget->item(ui->tableWidget->currentRow(),2)->setText(dlgModifyPTermial->NoLine);
    QString tmpStr="("+QString::number(dlgModifyPTermial->TerminalPointX,'f',2)+","+QString::number(dlgModifyPTermial->TerminalPointY,'f',2)+")";
    ui->tableWidget->item(ui->tableWidget->currentRow(),3)->setText(tmpStr);

    //更新dwg中的端口位置
    qlonglong lID=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toLongLong();
    IMxDrawEntity * enty=  (IMxDrawEntity *)tmp_MxDrawWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    IMxDrawPolyline * TermDraw=(IMxDrawPolyline *)enty;
    if(TermDraw==nullptr) return;
    MxDrawPoint* mPt1=new MxDrawPoint();
    mPt1->setX(dlgModifyPTermial->TerminalPointX-0.5);
    mPt1->setY(dlgModifyPTermial->TerminalPointY);
    MxDrawPoint* mPt2=new MxDrawPoint();
    mPt2->setX(dlgModifyPTermial->TerminalPointX+0.5);
    mPt2->setY(dlgModifyPTermial->TerminalPointY);
    TermDraw->dynamicCall("SetPointAt(int,QVriant)",0,mPt1->asVariant());
    TermDraw->dynamicCall("SetPointAt(int,QVriant)",1,mPt2->asVariant());

    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");
}

void DialogSymbolAttribute::on_BtnDelTerminal_clicked()
{
    if(ui->tableWidget->currentRow()<0)
    {
        QMessageBox::information(this, "机电液系统集成设计环境", "没有选择要删除的符号端点");
        return;
    }
    //删除dwg中的端口
    //IMxDrawEntity * enty=  (IMxDrawEntity *)tmp_MxDrawWidget->querySubObject("ObjectIdToObject(const qlonglong)",lTermId.at(ui->tableWidget->currentRow()));
    qlonglong lID=ui->tableWidget->item(ui->tableWidget->currentRow(),0)->data(Qt::UserRole).toLongLong();
    tmp_MxDrawWidget->dynamicCall("Erase(qlonglong)",lID);
    //lTermId.removeAt(ui->tableWidget->currentRow());
    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");

    ui->tableWidget->removeRow(ui->tableWidget->currentRow());
}

void DialogSymbolAttribute::on_BtnCancel_clicked()
{
    QList<IMxDrawPolyline*> listTerms=GetCurrentSpaceTerms(tmp_MxDrawWidget);
    for(int i=0;i<listTerms.count();i++)
    {
       listTerms.at(i)->setProperty("Visible",false);
    }
    SetCurLayerVisible(tmp_MxDrawWidget,"LY_Attdef",false);
    Canceled=true;
    if(DataBaseSymbolID=="")  DeleteFile=true;
    else DeleteFile=false;
    this->hide();
    //如果是新建符号，则删除dwg文件
    this->close();
}

bool DialogSymbolAttribute::SetAttrDefValue(QAxWidget* tmp_MxDrawWidget,QString OriginalTag,QString NewTag,QString NewText)
{
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)tmp_MxDrawWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)tmp_MxDrawWidget->querySubObject("NewResbuf()");
    //filter->AddStringEx("LY_AttTerm",8);  // 筛选图层
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    qDebug()<<"Cnt="<<Cnt;
    for(int i=0;i<Cnt;i++)
    {
       IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",i);
       if(EntyIsErased(tmp_MxDrawWidget,Enty)) continue;//去除erase的实体
       if(Enty->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
       {
           IMxDrawAttributeDefinition *AttrDef=(IMxDrawAttributeDefinition *)Enty;
           if(AttrDef->dynamicCall("Tag()").toString()==OriginalTag)
           {
               bool IsinsertAttrDef=false;
               for(int j=0;j<dlgModifyPTermial->ListAttrDefID.count();j++)
               {
                   if(dlgModifyPTermial->ListAttrDefID.at(j)==AttrDef->ObjectID())
                   {
                       IsinsertAttrDef=true;
                       break;
                   }
               }
               if(IsinsertAttrDef) continue;
               AttrDef->dynamicCall("SetTag(QString)",NewTag);
               AttrDef->dynamicCall("SetTextString(QString)",NewText);
               return true;
           }
       }
    }
    return false;
}

void DialogSymbolAttribute::on_BtnInsertTerminal_clicked()
{
    //如果是单端符号，最多一个连接点
    if(SymbolFileName.contains("ES2_S"))
    {
        if(ui->tableWidget->rowCount()>0)
        {
            QMessageBox::warning(nullptr, "提示", "单端符号只能有一个端点！");
            return;
        }
    }
    if(ui->tableWidget->currentRow()<0)
    {
        QMessageBox::information(this, "机电液系统集成设计环境", "没有选择插入端点的位置！");
        return;
    }
    dlgModifyPTermial->tmp_MxDrawWidget=tmp_MxDrawWidget;
    dlgModifyPTermial->Mode=3;
    dlgModifyPTermial->TerminalPointIsNull=true;
    dlgModifyPTermial->TerminalName=QString::number(ui->tableWidget->currentRow()+1);
    dlgModifyPTermial->LineDirection="";
    dlgModifyPTermial->LoadTerminalInfo();
    dlgModifyPTermial->setWindowTitle("添加");
    dlgModifyPTermial->NoLine="";
    dlgModifyPTermial->tmp_MxDrawWidget=tmp_MxDrawWidget;
    dlgModifyPTermial->show();
    dlgModifyPTermial->raise();
    dlgModifyPTermial->exec();
    if(dlgModifyPTermial->Canceled) return;
    int SelectRowIndex=ui->tableWidget->currentRow();
    ui->tableWidget->insertRow(SelectRowIndex);//setRowCount(ui->tableWidget->rowCount()+1);
    ui->tableWidget->setItem(SelectRowIndex,0,new QTableWidgetItem(dlgModifyPTermial->TerminalName));
    ui->tableWidget->setItem(SelectRowIndex,1,new QTableWidgetItem(dlgModifyPTermial->LineDirection));
    ui->tableWidget->setItem(SelectRowIndex,2,new QTableWidgetItem(dlgModifyPTermial->NoLine));
    QString tmpStr="("+QString::number(dlgModifyPTermial->TerminalPointX,'f',2)+","+QString::number(dlgModifyPTermial->TerminalPointY,'f',2)+")";
    ui->tableWidget->setItem(SelectRowIndex,3,new QTableWidgetItem(tmpStr));

    //更新图
    SetCurLayer(tmp_MxDrawWidget,"0");
    tmp_MxDrawWidget->setProperty("LineWidth",0.1);
    tmp_MxDrawWidget->setProperty("DrawCADColor", QColorToInt(QColor(255,0,0)));
    tmp_MxDrawWidget->dynamicCall("PathMoveTo(double,double)",dlgModifyPTermial->TerminalPointX-0.5,dlgModifyPTermial->TerminalPointY);
    tmp_MxDrawWidget->dynamicCall("PathLineTo(double,double)",dlgModifyPTermial->TerminalPointX+0.5,dlgModifyPTermial->TerminalPointY);

    qlonglong lID=tmp_MxDrawWidget->dynamicCall("DrawPathToPolyline()").toLongLong();
    ui->tableWidget->item(SelectRowIndex,0)->setData(Qt::UserRole,QVariant(lID));
    //lTermId.append(lID);
    IMxDrawPolyline* Newent= (IMxDrawPolyline*) tmp_MxDrawWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    Newent->setProperty("IsClosedStatus",true);
    Newent->dynamicCall("SetBulgeAt(int,double)",0,1) ;
    Newent->dynamicCall("SetBulgeAt(int,double)",1,1) ;

    //更新被插入连接点的端号信息
    for(int i=SelectRowIndex+1;i<ui->tableWidget->rowCount();i++)
    {
        ui->tableWidget->item(i,0)->setText(QString::number(i+1));
        //更新被插入连接点的属性定义对象
        SetAttrDefValue(tmp_MxDrawWidget,QString::number(i),QString::number(i+1),"");
        SetAttrDefValue(tmp_MxDrawWidget,"符号的连接点描述["+QString::number(i)+"]","符号的连接点描述["+QString::number(i+1)+"]","");
    }
    tmp_MxDrawWidget->dynamicCall("UpdateDisplay()");
}
void DialogSymbolAttribute::LoadAttrDefTable(int Index)
{
    switch(Index)
    {
      case 0://"全部"
        ui->tableWidget_AttrDef->setRowCount(0);
        if(GetAttrDefTextString(tmp_MxDrawWidget,"设备标识符(显示)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("设备标识符(显示)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"关联参考(主功能或辅助功能)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("关联参考(主功能或辅助功能)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"技术参数")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("技术参数"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"增补说明[1]")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("增补说明[1]"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"功能文本")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("功能文本"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"铭牌文本")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("铭牌文本"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"装配地点(描述性)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("装配地点(描述性)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"块属性[1]")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("块属性[1]"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"插头名称")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("插头名称"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"总览关联参考")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("总览关联参考"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"PLC地址")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("PLC地址"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"符号地址(自动)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("符号地址(自动)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"功能文本(自动)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("功能文本(自动)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"端子/插针代号")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("端子/插针代号"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"端子描述/插针描述")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("端子描述/插针描述"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"连接点代号（带显示设备标识符）")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("连接点代号（带显示设备标识符）"));
        }
        break;
      case 1://"普通元件"
        ui->tableWidget_AttrDef->setRowCount(0);
        if(GetAttrDefTextString(tmp_MxDrawWidget,"设备标识符(显示)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("设备标识符(显示)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"关联参考(主功能或辅助功能)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("关联参考(主功能或辅助功能)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"技术参数")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("技术参数"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"增补说明[1]")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("增补说明[1]"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"功能文本")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("功能文本"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"铭牌文本")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("铭牌文本"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"装配地点(描述性)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("装配地点(描述性)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"块属性[1]")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("块属性[1]"));
        }
        break;
      case 2://"PLC"
        ui->tableWidget_AttrDef->setRowCount(0);
        if(GetAttrDefTextString(tmp_MxDrawWidget,"设备标识符(显示)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("设备标识符(显示)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"插头名称")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("插头名称"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"总览关联参考")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("总览关联参考"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"PLC地址")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("PLC地址"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"符号地址(自动)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("符号地址(自动)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"功能文本(自动)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("功能文本(自动)"));
        }
        break;
      case 3://"端子/插针"
        ui->tableWidget_AttrDef->setRowCount(0);
        if(GetAttrDefTextString(tmp_MxDrawWidget,"设备标识符(显示)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("设备标识符(显示)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"关联参考(主功能或辅助功能)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("关联参考(主功能或辅助功能)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"技术参数")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("技术参数"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"增补说明[1]")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("增补说明[1]"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"功能文本")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("功能文本"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"铭牌文本")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("铭牌文本"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"装配地点(描述性)")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("装配地点(描述性)"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"块属性[1]")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("块属性[1]"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"端子/插针代号")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("端子/插针代号"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"端子描述/插针描述")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("端子描述/插针描述"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"左连接点")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("左连接点"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"右连接点")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("右连接点"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"上连接点")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("上连接点"));
        }
        if(GetAttrDefTextString(tmp_MxDrawWidget,"下连接点")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("下连接点"));
        }
        break;
      case 4://"元件连接点"
        ui->tableWidget_AttrDef->setRowCount(0);
        if(GetAttrDefTextString(tmp_MxDrawWidget,"连接点代号（带显示设备标识符）")=="未找到")
        {
            ui->tableWidget_AttrDef->setRowCount(ui->tableWidget_AttrDef->rowCount()+1);
            ui->tableWidget_AttrDef->setItem(ui->tableWidget_AttrDef->rowCount()-1,0,new QTableWidgetItem("连接点代号（带显示设备标识符）"));
        }
        break;
    }
}
void DialogSymbolAttribute::on_CbSymbolType_currentIndexChanged(const QString &arg1)
{
    LoadAttrDefTable(ui->CbSymbolType->currentIndex());
}

void DialogSymbolAttribute::on_BtnPutAttrDef_clicked()
{
    if(ui->tableWidget_AttrDef->currentRow()<0) return;
    m_dragText = ui->tableWidget_AttrDef->item(ui->tableWidget_AttrDef->currentRow(), 0)->text();
    tmp_MxDrawWidget->dynamicCall("DoCommand(const int&)",105);
}

void DialogSymbolAttribute::on_BtnGetBasePoint_clicked()
{
    IsGettingBasePoint=true;
    tmp_MxDrawWidget->dynamicCall("DoCommand(const int&)",104);
}

