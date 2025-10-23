#include "formaxwidget.h"
#include "ui_formaxwidget.h"
#include <QSet>
bool IsLoadingSymbol=false;//正在载入符号
extern int SelectEquipment_ID;
extern int SelectSymbol_ID;
extern int SelectTerminalStrip_ID;
extern int SelectTerminal_ID;
extern QStringList RemovedUnitsInfo;
formaxwidget::formaxwidget(QWidget *parent,QString FileName,int Page_ID) :
    QWidget(parent),dwgFileName(FileName),Page_IDInDB(Page_ID),
    ui(new Ui::formaxwidget)
{  
    ui->setupUi(this);
    this->setAttribute(Qt::WA_DeleteOnClose); //关闭时自动删除

    BlkResp=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    ListSelectEntys.clear();

    dlgSymbolAttribute=new DialogSymbolAttribute(this);
    connect(dlgSymbolAttribute,SIGNAL(SignalUpdateLib(QString)),this,SLOT(SlotUpdateLib(QString)));
    connect(dlgSymbolAttribute,SIGNAL(DialogIsClosed()),this,SLOT(SlotEditSymbolWndClosed()));
    connect(this,SIGNAL(GetUrPoint(IMxDrawPoint*)),dlgSymbolAttribute,SLOT(SlotGetUrPoint(IMxDrawPoint*)));
    connect(this,SIGNAL(SignalDrawAttrDefDone(QString,qlonglong)),dlgSymbolAttribute,SLOT(SlotDrawAttrDefDone(QString,qlonglong)));
    connect(this,SIGNAL(SignalDrawAttrDefDelete(QString,qlonglong)),dlgSymbolAttribute,SLOT(SlotDrawAttrDefDelete(QString,qlonglong)));
    timerAutoSaveDelay = new QTimer();
    connect(timerAutoSaveDelay,SIGNAL(timeout()),this,SLOT(AutoSave()));
    ui->axWidget->setContextMenuPolicy(Qt::CustomContextMenu);
    //timerAutoSaveDelay->start(60*1000);//1分钟自动保存一次
qDebug()<<"构造函数完成";
}

formaxwidget::~formaxwidget()
{
    delete ui;
    delete dlgSymbolAttribute;
}

void formaxwidget::closeEvent(QCloseEvent *event)
{
    qDebug()<<"formaxwidget closed";
    if((!IsSavedBeforeClose)&&(!IsDoingSymbolEdit))
    {
        WaitingForSaveDwg=true;
        event->ignore();
        ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
        qDebug()<<"ignore";
    }
    else
    {
        qDebug()<<"accept";
        event->accept();
    }
}

void formaxwidget::AutoSave()
{
    //timerAutoSaveDelay->stop();
    ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
}

void formaxwidget::SlotUpdateLib(QString CurSelectSymb2Class_ID)
{
   emit(SignalUpdateSymbolLib(CurSelectSymb2Class_ID));
}

void formaxwidget::DeleteEnty(QString Symbol_Handle)
{
qDebug()<<"DeleteEnty,Symbol_Handle="<<Symbol_Handle;
    IMxDrawEntity *EntyDelete=(IMxDrawEntity *)ui->axWidget->querySubObject("HandleToObject(const QString)",Symbol_Handle);
    if(EntyDelete!=nullptr)
    {
        //如果是黑盒，删除对应的MText
        QString LD_GROUPCPXRECT_TEXT=EntyDelete->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString();
        if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
        {
              IMxDrawMText *EntyMText=(IMxDrawMText *)ui->axWidget->querySubObject("HandleToObject(const QString)",LD_GROUPCPXRECT_TEXT);
              if(EntyMText!=nullptr) EntyMText->dynamicCall("Erase()");
        }
        QString EntyDeleteInfo="";
        if(EntyDelete->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
        {
            IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)EntyDelete;
            EntyDeleteInfo.append(EntyDelete->dynamicCall("handle()").toString());
            EntyDeleteInfo.append("￤"+EntyDelete->dynamicCall("GetxDataString2(QString,0)","DbId",0).toString());
            EntyDeleteInfo.append("￤"+EntyDelete->dynamicCall("GetxDataString2(QString,0)","FunDefine",0).toString());
            EntyDeleteInfo.append("￤"+EntyDelete->dynamicCall("GetxDataString2(QString,0)","Symbol_Category",0).toString());
            EntyDeleteInfo.append("￤"+EntyDelete->dynamicCall("GetxDataString2(QString,0)","Symbol_Remark",0).toString());
            EntyDeleteInfo.append("￤设备标识符(显示)");
            EntyDeleteInfo.append("￤"+GetBlockAttrTextString(BlkEnty,"设备标识符(显示)"));
            QList<IMxDrawPolyline*> ListTermEnty=GetTermEnty(ui->axWidget,BlkEnty->dynamicCall("GetBlockName()").toString());
            for(int i=0;i<ListTermEnty.count();i++)
            {
                QString LD_SYMB1LIB_TERMPOINT=ListTermEnty.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
                EntyDeleteInfo.append("￤"+LD_SYMB1LIB_TERMPOINT);
                EntyDeleteInfo.append("￤"+GetBlockAttrTextString(BlkEnty,LD_SYMB1LIB_TERMPOINT));
            }
            ListDeletedEntyInfo.append(EntyDeleteInfo);
        }
        EntyDelete->dynamicCall("Erase()");
        ui->axWidget->dynamicCall("UpdateDisplay()");
    }
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
}

void formaxwidget::SlotEditSymbolWndClosed()
{
   if(!dlgSymbolAttribute->Canceled)
       ui->axWidget->dynamicCall("SaveDwgFile(QString)","C:/TBD/SYMB2LIB/"+dlgSymbolAttribute->SymbolFileName);
   if(dlgSymbolAttribute->Canceled&&(dlgSymbolAttribute->DataBaseSymbolID=="")&&dlgSymbolAttribute->DeleteFile) emit SignalCloseMdiWnd(1);
   else emit SignalCloseMdiWnd(0);
   dlgSymbolAttribute->hide();
}
void formaxwidget::SetGridStyle()
{
qDebug()<<"SetGridStyle";
    IMxDrawResbuf *param =(IMxDrawResbuf *) ui->axWidget->querySubObject("NewResbuf()");
    param->AddLong(1);
    ui->axWidget->querySubObject("CallEx(const QString&,QVariant)","Mx_SetGridMode",param->asVariant());
    IMxDrawResbuf *param2 =(IMxDrawResbuf *) ui->axWidget->querySubObject("NewResbuf()");
    MxDrawPoint *temppt=new MxDrawPoint();
    IMxDrawPoint *pt=(IMxDrawPoint *)temppt;
    pt->setX(2);pt->setY(2);
    param2->AddString("SNAPUNIT");
    param2->dynamicCall("AddPointEx(QAxObject*,int)",pt->asVariant(),5002);
    ui->axWidget->querySubObject("CallEx(const QString&,QVariant)","Mx_SetSysVar",param2->asVariant());
    ui->axWidget->dynamicCall("UpdateDisplay()");
}
void formaxwidget::CreateTextStyle()
{
    IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
    // 得到文本式表.
    IMxDrawTextStyleTable* textStyleTable = (IMxDrawTextStyleTable*)database->querySubObject("GetTextStyleTable()");
    IMxDrawTextStyleTableRecord* textStyle;
    // 得到文本式
    for(int i=0;i<styles.count();i++)
    {
        textStyle = (IMxDrawTextStyleTableRecord*)textStyleTable->querySubObject("GetAt(QString,bool)",styles[i].Name, true);
        if (textStyle == nullptr)
        {
            // 如果没有就新建一个。
            ui->axWidget->dynamicCall("AddTextStyle2(QString,QString,double)",styles[i].Name,styles[i].Font,styles[i].Width);
            textStyle = (IMxDrawTextStyleTableRecord*)textStyleTable->querySubObject("GetAt(QString,bool)",styles[i].Name, true);
        }
        textStyle->dynamicCall("SetFont(QString,bool,bool,int,int)",styles[i].Font, false, false, 0, 0);
        textStyle->setProperty("textSize",styles[i].Hieight);
    }
    //ui->axWidget->setProperty("TextStyle",styles[0].Name);
}

void  formaxwidget::CreateLayer()
{
    IMxDrawDatabase* database =(IMxDrawDatabase*) ui->axWidget->querySubObject("GetDatabase()");
    IMxDrawLayerTable *layerTable =(IMxDrawLayerTable *) database->querySubObject("GetLayerTable()");
    IMxDrawLinetypeTable*linetypetable=(IMxDrawLinetypeTable*) database->querySubObject("GetLineTypeTable()");
    for(int i=0;i<layertypes.count();i++)
    {
        QString sNewLayerName =layertypes[i].Name;
        IMxDrawLayerTableRecord * layerTableRec;
        layerTableRec=(IMxDrawLayerTableRecord *)layerTable->querySubObject("GetAt(QString)",sNewLayerName);
        if(layerTableRec==nullptr)
        {
            layerTableRec=(IMxDrawLayerTableRecord *)layerTable->querySubObject("Add(QString)",sNewLayerName);
            MxDrawMcCmColor color;
            color.SetRGB(layertypes[i].color.red(),layertypes[i].color.green(), layertypes[i].color.blue());
            layerTableRec->setProperty("Color", color.asVariant());
            layerTableRec->setProperty("LineWeight", layertypes[i].Wight);
            IMxDrawLinetypeTableRecord *ltype=(IMxDrawLinetypeTableRecord *)linetypetable->querySubObject("GetAt(QString)",layertypes[i].LineType);
            qlonglong lineid=ltype->ObjectID();
            layerTableRec->setProperty("LinetypeObjectId",lineid);
        }
        //if(sNewLayerName=="PORT") layerTableRec->setProperty("IsOff",true);
    }
    // 把新建的层设置成当前层
    database->setProperty("CurrentlyLayerName", "0");
}

void formaxwidget::on_axWidget_ImplementCommandEvent(int iCommandId)
{
qDebug()<<"on_axWidget_ImplementCommandEvent,iCommandId="<<iCommandId;
    if (iCommandId == 100)   DoOpenDwgFileCommand();
    if (iCommandId == 101)   DoLoadSymbolCommand("LY_Symb2");
    if (iCommandId == 102)   DoEditSymbolCommand();
    if (iCommandId == 103)   DoSymbolAttribute();
    if (iCommandId == 104)   GetUrPoint();
    if (iCommandId == 105)   PuttingAttrDef();
    if (iCommandId == 106)   DoLoadSymbolSpur();
    if (iCommandId == 107)   DoSetSymbolSpurHighLight();
    if (iCommandId == 108)   DoLoadTerminal();
    if (iCommandId == 109)   DoLineConnect();
    if (iCommandId == 110)   DoMultiLine();
    if (iCommandId == 111)   DoLineDefine();
    if (iCommandId == 112)   DoCableDefine();
    if (iCommandId == 113)   DoNodeLoad();
    if (iCommandId == 114)   InsertNodes();
    if (iCommandId == 115)   DoLoadWholeUnit();
    if (iCommandId == 116)   DoDrawBlackBox();
    if (iCommandId == 117)   DoSetTerminalHighLight();
    if (iCommandId == 118)   DoLoadEqualDistance();
    if (iCommandId == 119)   DoDrawStructBox();
    if (iCommandId == 120)   DoSelectEntitys(); 
    if (iCommandId == 121)   DoTermBatchMark();
    if (iCommandId == 122)   this->mdisubwindow->close();//关闭当前窗口
    if (iCommandId == 123)   DoAddTerminalCommand("Terminal",SymbolIdInDB,false,0,0);
    if (iCommandId == 124)   DoEditMultiLib();
    if (iCommandId == 125)   DoDrawMultiLibLine();
    if (iCommandId == 126)   DoMultiLibSymbolLoad();
    if (iCommandId == 127)   DoLoadUnitStamp();
    if (iCommandId == 128)   DoLoadText();
}

void formaxwidget::DoCableDefine()
{
    MxDrawUiPrPoint getPt;      
    PickPointCount=0;
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("CableDefining");


    // 等用户在图上点取一个点
    PickPointCount=0;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    getPt.setMessage("请指定起点");
    if (getPt.go() != McUiPrStatus::mcOk) return;
    Pt1 = GetGridPtVal(getPt.value());
    if (Pt1 == nullptr) return;   // 返回点的点对象值。
    PickPointCount++;
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    getPt.setMessage("请指定终点");
    if (getPt.go() != McUiPrStatus::mcOk) return;
    Pt2 = GetGridPtVal(getPt.value());
    if (Pt2 == nullptr) return;   // 返回点的点对象值。
    Pt2->setX(GetGridPosVal(Pt2->x()));
    Pt2->setY(GetGridPosVal(Pt2->y()));
    PickPointCount++;
    if(PickPointCount!=2) return;

    //创建选择集对象
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter =new MxDrawResbuf();
    filter->AddStringEx("LINE",5020);
    ListSelectEntys.clear();
    ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
    qDebug()<<"ss.Count()="<<ss->Count();
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(ui->axWidget,ent)) continue;
        QString sName = ent->dynamicCall("ObjectName()").toString();
        qDebug()<<sName;
        if(sName=="McDbLine")
        {
            ent->dynamicCall("Highlight(bool)",true);
            ListSelectEntys.append(ent);
        }
    }//当前框选的符号处理

    if(ListSelectEntys.count()<1) return;
    //绘制电缆（白线）
    SetCurLayer(ui->axWidget,"LY_CDP");
    qlonglong lID=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
    IMxDrawEntity *EntyCableLine= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    EntyCableLine->dynamicCall("setColorIndex(int)",McColor::mcWhite);
    MxDrawUiPrEntity getEntity;
    getEntity.setMessage("请在高亮显示的连线中选择不需要标注的电缆，回车结束");
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    while(true)
    {
        int RetCode=getEntity.go();
        if(RetCode==McUiPrStatus::mcOk)
        {
            qDebug()<<"McUiPrStatus::mcOk";
            IMxDrawEntity* ent = getEntity.Entity();
            if(ent!=nullptr)
            {
                if(ent->dynamicCall("ObjectName()").toString()=="McDbLine")
                {
                    for(int i=0;i<ListSelectEntys.count();i++)
                    {
                       if(ListSelectEntys.at(i)->dynamicCall("handle()").toString()==ent->dynamicCall("handle()").toString())
                       {
                          ent->dynamicCall("Highlight(bool)",false);
                          ListSelectEntys.removeAt(i);
                          i=i-1;
                       }
                    }
                }
            }
        }
        else if(RetCode==McUiPrStatus::mcNone)//回车
        {
            qDebug()<<"McUiPrStatus::mcNone";
            break;
        }
        else if(RetCode==McUiPrStatus::mcCancel)//取消
        {
            qDebug()<<"McUiPrStatus::mcCancel";
            return;
        }
    }
    if(ListSelectEntys.count()<1)
    {
        if(EntyCableLine!=nullptr) EntyCableLine->dynamicCall("Erase()");
        return;
    }
    //电缆定义窗口
    ShowCableAttr(EntyCableLine,1,0);
    for(int i=0;i<ListSelectEntys.count();i++)
    {
        ListSelectEntys.at(i)->dynamicCall("Highlight(bool)",false);
    }
    ListSelectEntys.clear();
    ui->axWidget->dynamicCall("UpdateDisplay()");
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
}

void formaxwidget::CableDefine()
{
   ui->axWidget->dynamicCall("DoCommand(const int&)",112);
}

void formaxwidget::DoLineDefine()
{
    MxDrawUiPrPoint getPt;
    getPt.setMessage("请指定连线");
    PickPointCount=0;

    // 等用户在图上点取一个点
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    IMxDrawPoint* frstPt = GetGridPtVal(getPt.value());
    if (frstPt == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;
    SetCurLayer(ui->axWidget,"LY_CDP");
    ui->axWidget->setProperty("TextStyle","Standard");
    //设置属性块文字
    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",frstPt->x(),frstPt->y(),SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    //写入拓展数据
    IMxDrawResbuf *BlkResp=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    BlkResp->RemoveAll();
    BlkResp->AddStringEx("RotateAngle",1001);
    BlkResp->AddStringEx("0",1000);
    BlkResp->AddStringEx("SingleOrMutiLine",1001);
    BlkResp->AddStringEx("0",1000);//单行
    blkEnty->dynamicCall("SetXData(QVariant)",BlkResp->asVariant()) ;

    //插入记录到Wires表
    QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
    int Wires_ID=GetMaxIDOfDB(T_ProjectDatabase,"Wires","Wires_ID");
    QString StrSql =  "INSERT INTO Wires (Wires_ID,Cable_ID,Symbol,Handle,Page_ID,Position)"
                                      "VALUES (:Wires_ID,:Cable_ID,:Symbol,:Handle,:Page_ID,:Position)";
    QueryWires.prepare(StrSql);
    QueryWires.bindValue(":Wires_ID",Wires_ID);
    QueryWires.bindValue(":Cable_ID","");
    QueryWires.bindValue(":Symbol","SPS_CDP");
    QueryWires.bindValue(":Handle",blkEnty->dynamicCall("handle()").toString());
    QueryWires.bindValue(":Page_ID",Page_IDInDB);
    QString StrPosition=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    StrPosition+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000,0.000000";
    QueryWires.bindValue(":Position",StrPosition);
    QueryWires.exec();
    //将DbId写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(Wires_ID));
    ShowWireAttr(blkEnty,Wires_ID);
    SetCurLayer(ui->axWidget,"0");
}

void formaxwidget::DoDrawStructBox()
{
    MxDrawUiPrPoint getPt;
    getPt.setMessage("请指定第一个点");
    PickPointCount=0;

    // 等用户在图上点取一个点
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawCustBox");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    Pt1 = GetGridPtVal(getPt.value());
    if (Pt1 == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;
    getPt.setMessage("请指定第二个点");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    Pt2 = GetGridPtVal(getPt.value());
    if (Pt2 == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;
    //查看结构盒内部是否包含功能子块
    //创建选择集对象
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter =new MxDrawResbuf();

    filter->AddStringEx("LWPOLYLINE",5020);
    filter->AddStringEx("0",8);
    ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(ui->axWidget,ent)) continue;
        ent->dynamicCall("GetxDataString2(QString,QString)","LD_GROUPSBXRECT_TEXT",0).toString();
        if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
        {
            QMessageBox::warning(nullptr, "提示", "不允许嵌套绘制");
            return;
        }
    }
    //弹出高层位置编辑框
    DialogPageNameSet *dlg = new DialogPageNameSet(this);
    dlg->LoadTable("",2);//Mode=1:Page项目代号  Mode=2:Unit项目代号  Mode=3:Terminal项目代号
    dlg->HideEdPageName();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    int NewProjectStructure_ID=InsertRecordToProjectStructure(0,dlg->StrGaoceng,dlg->StrPos,"");
    QString PageGaocengName,PagePosName,DT;
    GetPageGaocengAndPos(Page_IDInDB,PageGaocengName,PagePosName);
    if((dlg->StrGaoceng==PageGaocengName)&&(dlg->StrPos==PagePosName)) DT="";
    else DT="="+dlg->StrGaoceng+"+"+dlg->StrPos;
    ui->axWidget->dynamicCall("PathMoveTo(double,double)",Pt1->x(),Pt1->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt2->x(),Pt1->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt2->x(),Pt2->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt1->x(),Pt2->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt1->x(),Pt1->y());
    qlonglong lID=ui->axWidget->dynamicCall("DrawPathToPolyline()").toLongLong();
    IMxDrawPolyline *EntyBox= (IMxDrawPolyline*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    QString Box_Handle=EntyBox->dynamicCall("handle()").toString();
    EntyBox->dynamicCall("setColorIndex(int)",McColor::mcCyan);
    EntyBox->dynamicCall("SetLineType(QString)","MyDotLineType");
    QString BoxText_Handle;
    lID=ui->axWidget->dynamicCall("DrawMText(double,double,const QString&,double,double,double,short)",(Pt1->x()<Pt2->x()?Pt1->x():Pt2->x())-3,(Pt1->y()+Pt2->y())/2,"-"+DT,2.5,0,PI/2,5).toLongLong();
    IMxDrawMText* DTMText= (IMxDrawMText*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    BoxText_Handle=DTMText->dynamicCall("handle()").toString();
    DTMText->dynamicCall("setColorIndex(int)",McColor::mcCyan);
    DTMText->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPSBXRECT_XRECT",0,Box_Handle);
    EntyBox->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPSBXRECT_TEXT",0,BoxText_Handle);

    //更新T_ProjectDatabase数据库的StructBox表
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString tempSQL = "INSERT INTO StructBox (StructBox_ID,ProjectStructure_ID,Page_ID,Box_Handle,BoxText_Handle)"
                      "VALUES (:StructBox_ID,:ProjectStructure_ID,:Page_ID,:Box_Handle,:BoxText_Handle)";
    QueryVar.prepare(tempSQL);
    int StructBox_ID=GetMaxIDOfDB(T_ProjectDatabase,"StructBox","StructBox_ID");
    QueryVar.bindValue(":StructBox_ID",StructBox_ID);
    QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
    QueryVar.bindValue(":Page_ID",QString::number(Page_IDInDB));
    QueryVar.bindValue(":Box_Handle",Box_Handle);
    QueryVar.bindValue(":BoxText_Handle",BoxText_Handle);
    QueryVar.exec();

    filter->RemoveAll();
    filter->AddStringEx("INSERT",5020);
    filter->AddStringEx("LY_Symb2",8);
    ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
    qDebug()<<"ss.Count()="<<ss->Count();
    QStringList ListSpurEntyHandle;
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(ui->axWidget,ent)) continue;
        ent->dynamicCall("GetxDataString2(QString,int)","DbID",0).toString();
        if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
        {
            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString sqlstr = "SELECT * FROM Symbol WHERE Symbol_ID = "+ent->dynamicCall("GetxDataString2(QString,int)","DbID",0).toString();
            QuerySymbol.exec(sqlstr);
            if(QuerySymbol.next())
            {
                sqlstr="UPDATE Symbol SET StructBox_ID=:StructBox_ID WHERE Symbol_ID = "+ent->dynamicCall("GetxDataString2(QString,int)","DbID",0).toString();
                QueryVar.bindValue(":StructBox_ID",QString::number(StructBox_ID));
                QueryVar.exec();
               //更新当前子块元件的高层位置信息
                QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                sqlstr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
                QueryEquipment.exec(sqlstr);
                if(QueryEquipment.value("ProjectStructure_ID").toInt()!=NewProjectStructure_ID)
                {
                    //更新元件信息
                    sqlstr="UPDATE Equipment SET ProjectStructure_ID=:ProjectStructure_ID WHERE Equipment_ID="+QuerySymbol.value("Equipment_ID").toString();
                    QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
                    QueryVar.exec();
                    emit(SignalUpdateSpur(QuerySymbol.value("Symbol_ID").toInt()));
                }
            }
        }
    }//当前框选的符号处理

    SetCurLayer(ui->axWidget,"0");
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    emit(UpdateProjectUnits());
}

void formaxwidget::DoDrawBlackBox()//黑盒
{
    MxDrawUiPrPoint getPt;
    getPt.setMessage("请指定第一个点");
    PickPointCount=0;

    // 等用户在图上点取一个点
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawCustBox");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    Pt1 = GetGridPtVal(getPt.value());
    if (Pt1 == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;
    getPt.setMessage("请指定第二个点");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    Pt2 = GetGridPtVal(getPt.value());
    if (Pt2 == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;


    //查看黑盒内部是否包含功能子块，如果不包含则新建一个原件U，如果包含同一个元件的功能子块则将黑盒添加进该元件，不允许嵌套黑盒，不允许包含不同元件的功能子块
    //创建选择集对象
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter =new MxDrawResbuf();
    if(!IsDrawingMultiLib)
    {
        filter->AddStringEx("LWPOLYLINE",5020);
        filter->AddStringEx("0",8);
        ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
        for (int i = 0; i < ss->Count(); i++)
        {
            IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
            if(ent==nullptr) continue;
            if(EntyIsErased(ui->axWidget,ent)) continue;
            ent->dynamicCall("GetxDataString2(QString,QString)","LD_GROUPCPXRECT_TEXT",0).toString();
            if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
            {
                QMessageBox::warning(nullptr, "提示", "不允许嵌套绘制");
                return;
            }
        }
    }
    int EquipmentIDInBox=0;
    QStringList ListSpurEntyHandle;
    if(!IsDrawingMultiLib)
    {
        filter->RemoveAll();
        filter->AddStringEx("INSERT",5020);
        filter->AddStringEx("LY_Symb2",8);
        ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
        qDebug()<<"ss.Count()="<<ss->Count();

        for (int i = 0; i < ss->Count(); i++)
        {
            IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
            if(ent==nullptr) continue;
            if(EntyIsErased(ui->axWidget,ent)) continue;
            ent->dynamicCall("GetxDataString2(QString,int)","DbID",0).toString();
            if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
            {
                QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                QString sqlstr = "SELECT * FROM Symbol WHERE Symbol_ID = "+ent->dynamicCall("GetxDataString2(QString,int)","DbID",0).toString();
                QuerySymbol.exec(sqlstr);
                if(QuerySymbol.next())
                {
                    if(EquipmentIDInBox==0)  EquipmentIDInBox=QuerySymbol.value("Equipment_ID").toInt();
                    else
                    {
                        if(EquipmentIDInBox!=QuerySymbol.value("Equipment_ID").toInt())
                        {
                            QMessageBox::warning(nullptr, "提示", "存在属于不同元件的功能子块！");
                            return;
                        }
                    }
                }
                ListSpurEntyHandle.append(ent->dynamicCall("handle()").toString());
            }
        }//当前框选的符号处理
    }

    //设置属性块文字
    ui->axWidget->dynamicCall("PathMoveTo(double,double)",Pt1->x(),Pt1->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt2->x(),Pt1->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt2->x(),Pt2->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt1->x(),Pt2->y());
    ui->axWidget->dynamicCall("PathLineTo(double,double)",Pt1->x(),Pt1->y());
    qlonglong lID=ui->axWidget->dynamicCall("DrawPathToPolyline()").toLongLong();
    IMxDrawPolyline *EntyBox= (IMxDrawPolyline*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    QString Box_Handle=EntyBox->dynamicCall("handle()").toString();
    EntyBox->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
    EntyBox->dynamicCall("SetLineType(QString)","MyDotLineType");
    if(IsDrawingMultiLib) return;

    QString DT_Handle;
    if((EquipmentIDInBox==0)&&(SymbolIdInDB==0)) //选择框没有包含任何功能子块，如果SymbolIdInDB=0新建一个元件，如果SymbolIdInDB>0则在对应的Unit下添加Symbol
    {
        int DTIndex=1;
        //在数据库中检索DT的后缀数字
        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        while(1)
        {
            QString SqlStr="SELECT * FROM Equipment WHERE DT = 'U"+QString::number(DTIndex)+"'";
            QuerySearch.exec(SqlStr);
            if(!QuerySearch.next()) break;
            DTIndex++;
        }
        QString DT="U"+QString::number(DTIndex);
        lID=ui->axWidget->dynamicCall("DrawMText(double,double,const QString&,double,double,double,short)",(Pt1->x()<Pt2->x()?Pt1->x():Pt2->x())-3,(Pt1->y()+Pt2->y())/2,"-"+DT,2.5,0,PI/2,5).toLongLong();
        IMxDrawMText* DTMText= (IMxDrawMText*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
        DT_Handle=DTMText->dynamicCall("handle()").toString();
        DTMText->dynamicCall("setColorIndex(int)",McColor::mcCyan);
        DTMText->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPCPXRECT_XRECT",0,Box_Handle);
        EntyBox->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPCPXRECT_TEXT",0,DT_Handle);

        EquipmentIDInBox=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
        //更新T_ProjectDatabase数据库的Equipment表
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString tempSQL = "INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Eqpt_Category)"
                                  "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Eqpt_Category)";
        QueryVar.prepare(tempSQL);
        QueryVar.bindValue(":Equipment_ID",EquipmentIDInBox);
        QueryVar.bindValue(":DT",DT);
        QueryVar.bindValue(":ProjectStructure_ID",GetProjectStructureIDByPageID(Page_IDInDB));
        QueryVar.bindValue(":Eqpt_Category","组合元件");//普通元件还是PLC元件
        QueryVar.exec();
    }//if((EquipmentIDInBox==0)&&(SymbolIdInDB==0))  //选择框没有包含任何功能子块，新建一个元件
    else//选择框包含功能子块，将黑盒添加进该元件,并更改功能子块的块属性
    {
        if(EquipmentIDInBox==0)
        {
            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString temp = QString("SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB));
            QuerySymbol.exec(temp);
            if(!QuerySymbol.next()) return;
            EquipmentIDInBox=QuerySymbol.value("Equipment_ID").toInt();
        }
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString sqlstr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(EquipmentIDInBox);
        QueryEquipment.exec(sqlstr);
        if(QueryEquipment.next())
        {
            lID=ui->axWidget->dynamicCall("DrawMText(double,double,const QString&,double,double,double,short)",(Pt1->x()<Pt2->x()?Pt1->x():Pt2->x())-3,(Pt1->y()+Pt2->y())/2,"-"+QueryEquipment.value("DT").toString(),2.5,0,PI/2,5).toLongLong();
            IMxDrawMText* DTMText= (IMxDrawMText*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
            DT_Handle=DTMText->dynamicCall("handle()").toString();
            DTMText->dynamicCall("setColorIndex(int)",McColor::mcCyan);
            DTMText->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPCPXRECT_XRECT",0,Box_Handle);
            EntyBox->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPCPXRECT_TEXT",0,DT_Handle);

            //更改功能子块的块属性
            for (int i = 0; i < ListSpurEntyHandle.count(); i++)
            {
                IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)ui->axWidget->querySubObject("HandleToObject(const QString)",ListSpurEntyHandle.at(i));
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)","");
            }
        }
    }
    //如果该元件有黑盒但是未绘制，则更新该Symbol；如果该元件有黑盒已绘制或者没有黑盒，则插入黑盒
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString sqlstr;
    sqlstr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(EquipmentIDInBox)+"' AND (Symbol_Category = 'PLC盒子' OR Symbol_Category = '组合元件盒子') AND Symbol_Handle = ''";
    QuerySymbol.exec(sqlstr);
    if(QuerySymbol.next())
    {
       SymbolIdInDB=QuerySymbol.value("Symbol_ID").toInt();
       sqlstr = "UPDATE Symbol SET Page_ID=:Page_ID,DT_Handle=:DT_Handle,Symbol_Handle=:Symbol_Handle WHERE Symbol_ID = "+QuerySymbol.value("Symbol_ID").toString();
       QuerySymbol.prepare(sqlstr);
       QuerySymbol.bindValue(":Page_ID",QString::number(Page_IDInDB));
       QuerySymbol.bindValue(":DT_Handle",DT_Handle);
       QuerySymbol.bindValue(":Symbol_Handle",Box_Handle);
       QuerySymbol.exec();
    }
    else
    {
        SymbolIdInDB=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");
        sqlstr =  "INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol_Category,DT_Handle,Symbol_Handle,Symbol_Remark,FunDefine)"
                                "VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol_Category,:DT_Handle,:Symbol_Handle,:Symbol_Remark,:FunDefine)";
        QuerySymbol.prepare(sqlstr);
        QuerySymbol.bindValue(":Symbol_ID",QString::number(SymbolIdInDB));
        QuerySymbol.bindValue(":Page_ID",QString::number(Page_IDInDB));
        QuerySymbol.bindValue(":Equipment_ID",QString::number(EquipmentIDInBox));
        QuerySymbol.bindValue(":Symbol_Category","组合元件盒子");
        QuerySymbol.bindValue(":DT_Handle",DT_Handle);
        QuerySymbol.bindValue(":Symbol_Handle",Box_Handle);
        QuerySymbol.bindValue(":Symbol_Remark","组合元件盒子");
        QuerySymbol.bindValue(":FunDefine","黑盒");
        QuerySymbol.exec();
    }
    EntyBox->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(SymbolIdInDB));
    //将FunDefine写入到blkEnty的拓展数据中
    EntyBox->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,"黑盒");
    EntyBox->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,"黑盒");
    SetCurLayer(ui->axWidget,"0");
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    emit(UpdateProjectUnits());
}

void formaxwidget::DrawStructBox()
{
   ui->axWidget->dynamicCall("DoCommand(const int&)",119);
}

void formaxwidget::DrawBlackBox()
{
    SymbolIdInDB=0;
    ui->axWidget->dynamicCall("DoCommand(const int&)",116);
}

void formaxwidget::ShowWireAttr(IMxDrawBlockReference *EntyWire,int Wires_ID)
{
    DialogLineDefine *dlg=new DialogLineDefine(this);
    dlg->SymbolMode=0;
    dlg->LoadLineInfo(Wires_ID);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    //更新块属性,代号，颜色，截面积
    QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Wires WHERE Wires_ID = "+QString::number(Wires_ID);
    QueryWires.exec(StrSql);
    if(!QueryWires.next()) return;
    AddAttrToWireBlock(EntyWire,dlg->SymbolMode,QueryWires.value("ConnectionNumber").toString(),QueryWires.value("Color").toString(),QueryWires.value("Diameters").toString());
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
}

void formaxwidget::LineDefine()
{
    SymbolName="SPS_CDP.dwg";
    //添加块到块表
    QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg
    BlkPath="C:/TBD/SPS/"+SymbolName;
    MyInsertBlock(ui->axWidget,BlkPath,BlkName);
    ui->axWidget->dynamicCall("DoCommand(const int&)",111);
}

void formaxwidget::SetBlkRed()
{

}

void formaxwidget::SetTermVisible(bool IsVisible)//显示或隐藏所有接线端点
{  
    IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
    IMxDrawBlockTable* blkTable = (IMxDrawBlockTable*)database->querySubObject("GetBlockTable()");
    IMxDrawBlockTableIterator* iterTable =(IMxDrawBlockTableIterator *)blkTable->querySubObject("NewIterator()");
    for (; !iterTable->Done(); iterTable->Step(true, false))
    {
        IMxDrawBlockTableRecord* blkRec=(IMxDrawBlockTableRecord *)iterTable->querySubObject("GetRecord()");    
        IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
        // 循环得到所有实体
        for (; !iter->Done(); iter->Step(true, true))
        {
            // 得到遍历器当前的实体
            IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
            //if(EntyIsErased(ui->axWidget,ent)) continue;//去除erase的实体
            if((ent->dynamicCall("ObjectName()").toString()=="McDbPolyline")&&(ent->dynamicCall("colorIndex()").toInt()==McColor::mcRed))//是否为端口
            {
                //ent->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
                //if(ui->axWidget->dynamicCall("IsOk()").toString()!="true") continue;
                ent->setProperty("Visible",IsVisible);
            }
        }
    }
    ui->axWidget->dynamicCall("Regen()");
}
void formaxwidget::DrawTypicalLine(QList<stPoint> DrawPoints,int Dir,int Type,IMxDrawWorldDraw *pDrawWorldDraw)//根据输入的起点和终点坐标画线
{qDebug()<<"Dir="<<Dir;
    //for(int j=0;j<DrawPoints.count();j++) qDebug()<<"DrawTypicalLine, x="<<DrawPoints.at(j).x<<" ,y= "<<DrawPoints.at(j).y;
    bool ValidDraw;
    QList<stPoint> DrawPoints_Real;
    stPoint tempPt,MidPt;
    int LineCountNeed=0;
    //if(DrawMode!=3) LineCountNeed=DrawLineCount;
    //else LineCountNeed=1;
    LineCountNeed=1;
    SetCurLayer(ui->axWidget,"CONNECT");
    if(DrawPoints.count()<=1) return;

    DrawPoints_Real.clear();
    tempPt.x=DrawPoints.at(0).x; tempPt.y=DrawPoints.at(0).y;
    DrawPoints_Real.append(tempPt);
    for(int i=0;i<DrawPoints.count()-1;i++)
    {
        if((DrawPoints.at(i).x==DrawPoints.at(i+1).x)||(DrawPoints.at(i).y==DrawPoints.at(i+1).y))
        {
            tempPt.x=DrawPoints.at(i+1).x; tempPt.y=DrawPoints.at(i+1).y;  DrawPoints_Real.append(tempPt);
        }
        else
        {
            if(Dir==2)//先竖
            {
                tempPt.x=DrawPoints.at(i).x; tempPt.y=DrawPoints.at(i+1).y; DrawPoints_Real.append(tempPt);
                tempPt.x=DrawPoints.at(i+1).x; tempPt.y=DrawPoints.at(i+1).y; DrawPoints_Real.append(tempPt);
            }
            else if(Dir==1)//先横
            {
                tempPt.x=DrawPoints.at(i+1).x; tempPt.y=DrawPoints.at(i).y; DrawPoints_Real.append(tempPt);
                tempPt.x=DrawPoints.at(i+1).x; tempPt.y=DrawPoints.at(i+1).y; DrawPoints_Real.append(tempPt);
            }
        }
    }
    for(int j=0;j<DrawPoints_Real.count()-1;j++)
    {
       if(Type==0) ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(j).x, DrawPoints_Real.at(j).y, DrawPoints_Real.at(j+1).x,DrawPoints_Real.at(j+1).y);
       else pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(j).x, DrawPoints_Real.at(j).y, DrawPoints_Real.at(j+1).x,DrawPoints_Real.at(j+1).y);
    }

    if(DrawPoints_Real.count()==2) //2点情况
    {

        if(Dir==2)
        {
            if(DrawPoints_Real.at(0).y!=DrawPoints_Real.at(1).y)
            {
                for(int k=1;k<LineCountNeed;k++)
                {
                 if(Type==0)   ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x-k*DrawLineGap, DrawPoints_Real.at(0).y, DrawPoints_Real.at(1).x-k*DrawLineGap,DrawPoints_Real.at(1).y);
                 else pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x-k*DrawLineGap, DrawPoints_Real.at(0).y, DrawPoints_Real.at(1).x-k*DrawLineGap,DrawPoints_Real.at(1).y);
                }
            }
        }
        else if(Dir==1)//先横
        {
            if(DrawPoints_Real.at(0).x!=DrawPoints_Real.at(1).x)
            {
                for(int k=1;k<LineCountNeed;k++)
                {
                  if(Type==0)  ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x, DrawPoints_Real.at(0).y-k*DrawLineGap, DrawPoints_Real.at(1).x,DrawPoints_Real.at(1).y-k*DrawLineGap);
                  else pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x, DrawPoints_Real.at(0).y-k*DrawLineGap, DrawPoints_Real.at(1).x,DrawPoints_Real.at(1).y-k*DrawLineGap);
                }
            }
        }

    }
    else//3点情况
    {
        if(Dir==2)//先竖
        {
            for(int k=1;k<LineCountNeed;k++)
            {
                ValidDraw=false;
                MidPt.x=DrawPoints_Real.at(0).x-k*DrawLineGap;
                if((DrawPoints_Real.at(0).x-DrawPoints_Real.at(2).x)*(DrawPoints_Real.at(0).y-DrawPoints_Real.at(2).y)>0)
                {
                    MidPt.y=DrawPoints_Real.at(1).y+k*DrawLineGap;
                    if((DrawPoints_Real.at(2).x-DrawPoints_Real.at(0).x)<0)
                    {
                        if((MidPt.y<DrawPoints_Real.at(0).y)&&(MidPt.x>DrawPoints_Real.at(2).x))
                            ValidDraw=true;
                    }
                    else
                        ValidDraw=true;

                }
                else
                {
                    MidPt.y=DrawPoints_Real.at(1).y-k*DrawLineGap;
                    if((DrawPoints_Real.at(2).x-DrawPoints_Real.at(0).x)<0)
                    {
                        if((MidPt.y>DrawPoints_Real.at(0).y)&&(MidPt.x>DrawPoints_Real.at(2).x))
                            ValidDraw=true;
                    }
                    else
                        ValidDraw=true;
                }
                if(ValidDraw)
                {
                  if(Type==0)
                  {
                      ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",MidPt.x,  DrawPoints_Real.at(0).y, MidPt.x, MidPt.y);
                      ui->axWidget->dynamicCall("DrawLine(double,double,double,double)", MidPt.x, MidPt.y,DrawPoints_Real.at(2).x,MidPt.y);
                  }
                  else
                  {
                      pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)",MidPt.x,  DrawPoints_Real.at(0).y, MidPt.x, MidPt.y);
                      pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)", MidPt.x, MidPt.y,DrawPoints_Real.at(2).x,MidPt.y);
                  }
                }
            }
        }
        else if(Dir==1)//先横
        {
            for(int k=1;k<LineCountNeed;k++)
            {
                ValidDraw=false;
                MidPt.y=DrawPoints_Real.at(0).y-k*DrawLineGap;
                if((DrawPoints_Real.at(0).x-DrawPoints_Real.at(2).x)*(DrawPoints_Real.at(0).y-DrawPoints_Real.at(2).y)>0)
                {
                    MidPt.x=DrawPoints_Real.at(1).x+k*DrawLineGap;
                    if((DrawPoints_Real.at(2).x-DrawPoints_Real.at(0).x)<0)
                    {
                        if((MidPt.y>DrawPoints_Real.at(2).y)&&(MidPt.x<DrawPoints_Real.at(0).x))
                            ValidDraw=true;
                    }
                    else
                        ValidDraw=true;

                }
                else
                {
                    MidPt.x=DrawPoints_Real.at(1).x-k*DrawLineGap;
                    if((DrawPoints_Real.at(2).x-DrawPoints_Real.at(0).x)>0)
                    {
                        if((MidPt.y>DrawPoints_Real.at(2).y)&&(MidPt.x>DrawPoints_Real.at(0).x))
                            ValidDraw=true;
                    }
                    else
                        ValidDraw=true;
                }
                if(ValidDraw)
                {
                   if(Type==0)
                   {
                       int CONumber=0;
                       if((DrawPoints_Real.at(0).x>DrawPoints_Real.at(2).x)&&(DrawPoints_Real.at(0).y>DrawPoints_Real.at(2).y)) CONumber=1;
                       else if((DrawPoints_Real.at(0).x<DrawPoints_Real.at(2).x)&&(DrawPoints_Real.at(0).y>DrawPoints_Real.at(2).y)) CONumber=2;
                       else if((DrawPoints_Real.at(0).x>DrawPoints_Real.at(2).x)&&(DrawPoints_Real.at(0).y<DrawPoints_Real.at(2).y)) CONumber=3;
                       else if((DrawPoints_Real.at(0).x<DrawPoints_Real.at(2).x)&&(DrawPoints_Real.at(0).y<DrawPoints_Real.at(2).y)) CONumber=4;
                       if(CONumber==1)
                       {
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x,DrawPoints_Real.at(0).y, DrawPoints_Real.at(2).x+2,DrawPoints_Real.at(0).y).toLongLong();
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y-2, DrawPoints_Real.at(2).x,DrawPoints_Real.at(2).y).toLongLong();
                           lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y,"SYMB2_M_PWF_CO1",1.0,0).toLongLong();
                       }
                       else if(CONumber==2)
                       {
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x,DrawPoints_Real.at(0).y, DrawPoints_Real.at(2).x-2,DrawPoints_Real.at(0).y).toLongLong();
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y-2, DrawPoints_Real.at(2).x,DrawPoints_Real.at(2).y).toLongLong();
                           lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y,"SYMB2_M_PWF_CO2",1.0,0).toLongLong();
                       }
                       else if(CONumber==3)
                       {
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x,DrawPoints_Real.at(0).y, DrawPoints_Real.at(2).x+2,DrawPoints_Real.at(0).y).toLongLong();
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y+2, DrawPoints_Real.at(2).x,DrawPoints_Real.at(2).y).toLongLong();
                           lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y,"SYMB2_M_PWF_CO3",1.0,0).toLongLong();
                       }
                       else if(CONumber==4)
                       {
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x,DrawPoints_Real.at(0).y, DrawPoints_Real.at(2).x-2,DrawPoints_Real.at(0).y).toLongLong();
                           ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y+2, DrawPoints_Real.at(2).x,DrawPoints_Real.at(2).y).toLongLong();
                           lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",DrawPoints_Real.at(2).x,DrawPoints_Real.at(0).y,"SYMB2_M_PWF_CO4",1.0,0).toLongLong();
                       }

                      //ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x,  MidPt.y, MidPt.x, MidPt.y);
                      //ui->axWidget->dynamicCall("DrawLine(double,double,double,double)", MidPt.x, MidPt.y,MidPt.x,DrawPoints_Real.at(2).y);
                   }
                   else
                   {
                       pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)",DrawPoints_Real.at(0).x,  MidPt.y, MidPt.x, MidPt.y);
                       pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)", MidPt.x, MidPt.y,MidPt.x,DrawPoints_Real.at(2).y);
                   }
                }
            }
        }
    }
    ui->axWidget->dynamicCall("UpdateDisplay(void)");
    SetCurLayer(ui->axWidget,"0");
}
void formaxwidget::DoMultiLine()
{
    // 定义取点变量。
    stPoint PickPoint;
    IMxDrawPoint* Pt;
    IMxDrawCustomEntity* spDrawData;
    MxDrawUiPrPoint getPt;
    listSelectPort.clear();
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    if(DrawMode==3)//如果Mode为3（元件端点），则先框选元件并直接根据元件的方向确定画线的方向
    {
        getPt.setMessage("框选元件起始端点，右键结束");
        spDrawData = getPt.InitUserDraw("DrawCustBox");
        QList<IMxDrawEntity *> ListSelectBlk;
        while(true)
        {
            PickPointCount=0;
            // 等用户在图上点取一个第一个点
            if (getPt.go() != McUiPrStatus::mcOk)
            {
                break;
            }
            Pt1 = GetGridPtVal(getPt.value());
            if (Pt1 == nullptr) return;   // 返回点的点对象值。

            PickPointCount++;

            // 等用户在图上点取第二个点
            if (getPt.go() != McUiPrStatus::mcOk)
            {
                break;
            }
            Pt2 = GetGridPtVal(getPt.value());
            if (Pt1 == nullptr) return;   // 返回点的点对象值。
            PickPointCount++;
            if(PickPointCount!=2) return;

            //创建选择集对象
            IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
            //创建过滤对象
            MxDrawResbuf* filter =new MxDrawResbuf();

            ListSelectBlk.clear();
            ss->dynamicCall("Select(int,QAxObject*,QAxObject*,,QAxObject*)",McSelect::mcSelectionSetWindow, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
            for (int i = 0; i < ss->Count(); i++)
            {
                IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
                QString sName = ent->dynamicCall("ObjectName()").toString();
                if(sName=="McDbBlockReference")
                {
                   //listSelectSymbolID.append(ent->ObjectID());
                   ent->dynamicCall("Highlight(bool)",true);
                   ListSelectBlk.append(ent);
                   IMxDrawBlockReference* blk_ent = (IMxDrawBlockReference*)ent;
                   QString Symbol_Handle=blk_ent->dynamicCall("handle()").toString();
                   //在数据库Symbol表和Symb2TermInfo表中检索连接点的坐标
                   QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                   QString SqlStr="SELECT * FROM Symbol WHERE Symbol_Handle= '"+Symbol_Handle+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
qDebug()<<SqlStr;
                   QuerySymbol.exec(SqlStr);
                   if(QuerySymbol.next())
                   {
                       QString Symbol_ID=QuerySymbol.value("Symbol_ID").toString();
                       QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                       SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+Symbol_ID+"'";
                       QuerySymb2TermInfo.exec(SqlStr);
                       while(QuerySymb2TermInfo.next())
                       {
                           //将端口坐标加入list
                           QString Conn_Coordinate=QuerySymb2TermInfo.value("Conn_Coordinate").toString();
qDebug()<<"Find QuerySymb2TermInfo,Conn_Coordinate="<<Conn_Coordinate;
                           QStringList ListConn_Coordinate=Conn_Coordinate.split(",");
                           if(ListConn_Coordinate.count()==3)
                           {
                               PickPoint.x=ListConn_Coordinate.at(0).toDouble();
                               PickPoint.y=ListConn_Coordinate.at(1).toDouble();
                               listSelectPort.append(PickPoint);
                           }
                       }
                   }
                   //在数据库Terminal表和TerminalTerm表中检索连接点的坐标
                   QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
                   SqlStr="SELECT * FROM TerminalInstance WHERE Handle= '"+Symbol_Handle+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
                   QueryTerminalInstance.exec(SqlStr);
                   if(QueryTerminalInstance.next())
                   {
                       //将端口坐标加入list
                       QString Conn_Coordinate=QueryTerminalInstance.value("Coordinate").toString();
                       qDebug()<<"Find QuerySymb2TermInfo,Conn_Coordinate="<<Conn_Coordinate;
                       QStringList ListConn_Coordinate=Conn_Coordinate.split(",");
                       if(ListConn_Coordinate.count()==3)
                       {
                           PickPoint.x=ListConn_Coordinate.at(0).toDouble();
                           PickPoint.y=ListConn_Coordinate.at(1).toDouble();
                           listSelectPort.append(PickPoint);
                       }
                   }
                }
            }//当前框选的符号处理
        }//选择元件端点完成，下一步为画线
        for (int i = 0; i < ListSelectBlk.count(); i++)
        {
            ListSelectBlk.at(i)->dynamicCall("Highlight(bool)",false);
        }
        if(listSelectPort.count()<=0) return;
        IsDrawingMultiLine=true;
        getPt.setMessage("选择连线终点");
        spDrawData = getPt.InitUserDraw("DrawMultiLine");
        // 等用户在图上点取一个点
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            return;
        }
        Pt = GetGridPtVal(getPt.value());
        if (Pt == nullptr) return;   // 返回点的点对象值
        IsDrawingMultiLine=false;
        //为了多线绘制，必须先找到所有端点中最小的x坐标和最小的y坐标
        double minPortx=0;
        double minPorty=0;
        bool firstin=true;
        for(int i=0;i<listSelectPort.count();i++)
        {
            //根据鼠标位置确定线的方向
            if(firstin){ firstin=false;minPortx=listSelectPort.at(i).x;minPorty=listSelectPort.at(i).y;}
            if(listSelectPort.at(i).x<minPortx) minPortx=listSelectPort.at(i).x;
            if(listSelectPort.at(i).y<minPorty) minPorty=listSelectPort.at(i).y;
            //qDebug()<<"最小ptx="<<minPortx<<" 最小pty="<<minPorty;
        }

        for(int i=0;i<listSelectPort.count();i++)
        {
           //根据鼠标位置确定线的方向
           DrawPoints.clear();
           PickPoint.x=listSelectPort.at(i).x;
           PickPoint.y=listSelectPort.at(i).y;
           DrawPoints.append(PickPoint);
           //需要确定连线终点位置，因为是多线绘制，终点位置并非用户选择的终点位置。
           //如果是先水平后垂直，则终点位置x坐标为用户选择的终点x坐标+当前端点的y坐标-最低（y坐标最小）的端点y坐标;;;y坐标为用户选择的y坐标
           //如果是先垂直后水平，则终点位置y坐标为用户选择的终点y坐标+当前端点的x坐标-最低（x坐标最小）的端点x坐标;;;x坐标为用户选择的x坐标
           if(MultiLineDir==1)//0:未确定 1:先水平后垂直 2：先垂直后水平
           {
               PickPoint.x=Pt->x()+listSelectPort.at(i).y-minPorty;
               PickPoint.y=Pt->y();
           }
           else if(MultiLineDir==2)//0:未确定 1:先水平后垂直 2：先垂直后水平
           {
               PickPoint.y=Pt->y()+listSelectPort.at(i).x-minPortx;
               PickPoint.x=Pt->x();
           }
           DrawPoints.append(PickPoint);
           //qDebug()<<"DrawTypicalLine(DrawPoints,DrawMode,0,nullptr)";
           //for(int j=0;j<DrawPoints.count();j++) qDebug()<<"DrawTypicalLine, x="<<DrawPoints.at(j).x<<" ,y= "<<DrawPoints.at(j).y;

           DrawTypicalLine(DrawPoints,MultiLineDir,0,nullptr);
        }
    }//=======================以上为元件端点模式===================
    else //如果Mode不为3（元件端点）
    {
        DrawPoints.clear();
        getPt.setMessage("点取第一点");
        PickPointCount=0;
        spDrawData = getPt.InitUserDraw("DrawMultiLine");
        // 等用户在图上点取一个点
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            return;
        }

        Pt = GetGridPtVal(getPt.value());
        if (Pt == nullptr) return;   // 返回点的点对象值。
        listSelectPort.clear();
        for(int i=0;i<DrawLineCount;i++)
        {
            if(DrawMode==1)//先水平
            {
                PickPoint.x=Pt->x();
                PickPoint.y=Pt->y()-DrawLineGap*i;
            }
            else if(DrawMode==2)//先垂直
            {
                PickPoint.x=Pt->x()+DrawLineGap*i;
                PickPoint.y=Pt->y();
            }
            listSelectPort.append(PickPoint);
        }
        PickPointCount++;
        IsDrawingMultiLine=true;

        getPt.setMessage("点取第下一个点");
        // 等用户在图上点取一个点
        IMxDrawPoint* Pt2;
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            return;
        }
        Pt2 = GetGridPtVal(getPt.value());
        if (Pt2 == nullptr) return;   // 返回点的点对象值。
        PickPointCount++;
        IsDrawingMultiLine=false;

        //将用户选择端点和根据数量和间距生成的端点添加
        double minPortx=0;
        double minPorty=0;
        bool firstin=true;
        for(int i=0;i<listSelectPort.count();i++)
        {
            //根据鼠标位置确定线的方向
            if(firstin){ firstin=false;minPortx=listSelectPort.at(i).x;minPorty=listSelectPort.at(i).y;}
            if(listSelectPort.at(i).x<minPortx) minPortx=listSelectPort.at(i).x;
            if(listSelectPort.at(i).y<minPorty) minPorty=listSelectPort.at(i).y;
            //qDebug()<<"最小ptx="<<minPortx<<" 最小pty="<<minPorty;
        }

        for(int i=0;i<DrawLineCount;i++)
        {
           DrawPoints.clear();
           DrawPoints.append(listSelectPort.at(i));

           if(DrawMode==1)//0:未确定 1:先水平后垂直 2：先垂直后水平
           {
               PickPoint.x=Pt2->x()+listSelectPort.at(i).y-minPorty;
               PickPoint.y=Pt2->y();
           }
           else if(DrawMode==2)//0:未确定 1:先水平后垂直 2：先垂直后水平
           {
               PickPoint.y=Pt2->y()+listSelectPort.at(i).x-minPortx;
               PickPoint.x=Pt2->x();
           }
           DrawPoints.append(PickPoint);
           DrawTypicalLine(DrawPoints,DrawMode,0,nullptr);
        }
    }
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
}
void formaxwidget::MultiLine()
{
    DialogMultiLine *dlg=new DialogMultiLine(this);
    dlg->exec();
    if(dlg->Canceled) return;

    DrawMode=dlg->Mode;
    DrawLineCount=dlg->LineCount;
    DrawLineGap=dlg->LineGap;
    ui->axWidget->dynamicCall("DoCommand(const int&)",110);
    delete dlg;
}

//Mode=1,检查Pt1，Mode=2，检查Pt2及Pt1Pt2连线
bool formaxwidget::CheckConnectLinePt(int Mode)
{
qDebug()<<"CheckConnectLinePt,Mode="<<Mode;
    //查看Pt处的节点，如果是CO节点，则只有中心节点是有效的，不是中心节点的话必须是无接线节点
    //如果是三连接节点，则只有中心节点是有效的，并且当Mode=2的时候Pt1Pt2连线方向必须为未连接方向，不是"C"节点的话必须是无接线节点
    IMxDrawPoint *Pt=(Mode==1)?Pt1:Pt2;
    if(Pt==nullptr) return false;
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT",5020);
    filter->AddStringEx("CONNECT", 8);
    ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",Pt->asVariant(),filter->asVariant());
qDebug()<<"ss SelectAtPoint,Count="<<ss->dynamicCall("Count()").toInt();
    for(int i=0;i<ss->dynamicCall("Count()").toInt();i++)
    {
        IMxDrawBlockReference *NodeEnty=  (IMxDrawBlockReference *)ss->querySubObject("Item(int)",i);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)NodeEnty)) continue;//去除erase的实体      
        IMxDrawPoint *PtC=(IMxDrawPoint *)NodeEnty->querySubObject("Position()");
        if(PtC==nullptr) return false;
        //查看Pt处是否有连线,如果有连线则返回false
        IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filter2=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        filter2->AddStringEx("LINE",5020);
        filter2->AddStringEx("CONNECT", 8);
        ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",Pt->asVariant(),filter2->asVariant());
qDebug()<<"ss2 SelectAtPoint,Count="<<ss2->dynamicCall("Count()").toInt();
        for(int j=0;j<ss2->dynamicCall("Count()").toInt();j++)
        {
            IMxDrawLine * CrossLine=  (IMxDrawLine *)ss2->querySubObject("Item(int)",j);
            if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
            //Pt是连线的起点或终点则返回false
            double CrossLineStartx=((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x();
            double CrossLineStarty=((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y();
            double CrossLineEndx=((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x();
            double CrossLineEndy=((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y();
            if(((fabs(CrossLineStartx-Pt->x())<0.1)&&(fabs(CrossLineStarty-Pt->y())<0.1))||((fabs(CrossLineEndx-Pt->x())<0.1)&&(fabs(CrossLineEndy-Pt->y())<0.1)))
            {qDebug()<<"CrossLineStartx="<<CrossLineStartx<<"CrossLineStarty="<<CrossLineStarty<<"CrossLineEndx="<<CrossLineEndx<<"CrossLineEndy="<<CrossLineEndy<<"Pt->x()="<<Pt->x()<<"Pt->y()="<<Pt->y()<<"Pt是连线的起点或终点则返回false";return false;}
        }
        if(!NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_")) return true;
qDebug()<<"PtC->x()="<<PtC->x()<<",Pt->x()="<<Pt->x()<<",PtC->y()="<<PtC->y()<<",Pt->y()="<<Pt->y();
        if((fabs(PtC->x()-Pt->x())>minDelta)||(fabs(PtC->y()-Pt->y())>minDelta))
        {
           //不是Node的中心节点，方向有要求
            if(Mode==1) return true;
            if(Pt->x()<PtC->x())//左
            {
                if(Pt1->x()>Pt2->x()) {qDebug()<<"不是Node的中心节点，方向有左要求";return false;}
            }
            if(Pt->x()>PtC->x())//右
            {
                if(Pt1->x()<Pt2->x()) {qDebug()<<"不是Node的中心节点，方向有右要求";return false;}
            }
            if(Pt->y()>PtC->y())//上
            {
                if(Pt1->y()<Pt2->y()) {qDebug()<<"不是Node的中心节点，方向有上要求";return false;}
            }
            if(Pt->y()<PtC->y())//下
            {
                if(Pt1->y()>Pt2->y()) {qDebug()<<"不是Node的中心节点，方向有下要求";return false;}
            }
            return true;
        }
        else//是Node的中心节点，必须为无接线节点,如果是CO节点则返回true，如果是三连接节点则当Mode=2的时候Pt1Pt2连线方向必须为未连接方向
        {
           if(NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_CO")||NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点")||Mode==1) return true;
           bool IsValid=false;
           if(NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TLRU"))//Mode=2,Pt1Pt2连线方向必须为垂直方向且在中心节点的上方
           {
               if(fabs(Pt1->x()-Pt2->x())<minDelta)//,Pt1Pt2连线方向垂直
               {
                   if((Pt1->y()>=PtC->y())&&(Pt2->y()>=PtC->y())) IsValid=true;
               }
           }
           else if(NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TLRO"))//Mode=2,Pt1Pt2连线方向必须为垂直方向且在中心节点的下方
           {
               if(fabs(Pt1->x()-Pt2->x())<minDelta)//,Pt1Pt2连线方向垂直
               {
                   if((Pt1->y()<=PtC->y())&&(Pt2->y()<=PtC->y())) IsValid=true;
               }
           }
           else if(NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TOUR"))//Mode=2,Pt1Pt2连线方向必须为水平方向且在中心节点的左方
           {
               if(fabs(Pt1->y()-Pt2->y())<minDelta)//,Pt1Pt2连线方向水平
               {
                   if((Pt1->x()<=PtC->x())&&(Pt2->x()<=PtC->x())) IsValid=true;
               }
           }
           else if(NodeEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TOUL"))//Mode=2,Pt1Pt2连线方向必须为水平方向且在中心节点的右方
           {
               if(fabs(Pt1->y()-Pt2->y())<minDelta)//,Pt1Pt2连线方向水平
               {
                   if((Pt1->x()>=PtC->x())&&(Pt2->x()>=PtC->x())) IsValid=true;
               }
           }
           return IsValid;
        }
    }
    return true;
}
//查看连线两端是否有同向的连线，若有则合并,注意蓝色的连线不能合并
void formaxwidget::CombineLine(IMxDrawLine *mLine)
{
qDebug()<<"CombineLine";

    //查看mLine两端是否有同向的连线，若有则合并
    //查看mLine两端是否有垂直的连线，若有则画节点，可能为CO节点或3连接节点
    //查看mLine是否存在垂直的连线，且交点不是mLine的端点，若存在则画3连接节点
    //查看mLine两端是否有Node的中心,若有则更新Node，CO节点更新为3连接节点，3连接节点更新为4连接节点
    bool mLineShouldErase=false;
    QList<qlonglong> ListNewLine,ListNewConnect;
    IMxDrawLine *NewmLine;
    SetCurLayer(ui->axWidget,"CONNECT");
    //查看mLine两端是否有同向的连线，若有则合并
    //查看mLine两端是否有垂直的连线，若有则画节点，可能为CO节点或3连接节点
    for(int i=0;i<2;i++)
    {
        if(mLine==nullptr) return;
        IMxDrawPoint *PtCross;
        if(i==0)  PtCross = (IMxDrawPoint *)mLine->querySubObject("StartPoint()");
        else PtCross = (IMxDrawPoint *)mLine->querySubObject("EndPoint()");
        if(CheckExistTerminal(PtCross,Page_IDInDB)) continue;
        IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        filter->RemoveAll();
        filter->AddStringEx("INSERT",5020);
        filter->AddStringEx("Terminal", 8);
        ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtCross->asVariant(),filter->asVariant());
        if(ss->dynamicCall("Count()").toInt()>1) continue;

        filter->RemoveAll();
        filter->AddStringEx("LINE",5020);
        filter->AddStringEx("CONNECT", 8);
        ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtCross->asVariant(),filter->asVariant());
        if(ss->dynamicCall("Count()").toInt()>1)
        {
qDebug()<<"Count=2,i="<<i;
            IMxDrawLine *CrossLine;
            bool FindCrossLine=false;
            for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
            {
qDebug()<<"j="<<j;
                CrossLine=  (IMxDrawLine *)ss->querySubObject("Item(int)",j);
                if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
                //if(CrossLine->dynamicCall("colorIndex()").toInt()==McColor::mcBlue) continue;
                //排除PtCross和节点相交的情况
                IMxDrawSelectionSet *ssExclude= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
                IMxDrawResbuf *filterExclude=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
                filterExclude->RemoveAll();
                filterExclude->AddStringEx("INSERT",5020);
                filterExclude->AddStringEx("CONNECT", 8);
                ssExclude->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtCross->asVariant(),filterExclude->asVariant());
                if(ssExclude->dynamicCall("Count()").toInt()>0) break;
                else qDebug()<<"无PtCross和节点相交的情况";

                bool IsNewLine=false;
                for(int k=0;k<ListNewLine.count();k++)
                {
                    if(ListNewLine.at(k)==CrossLine->dynamicCall("ObjectID()").toLongLong()) //去除新绘的连线
                    {
                        IsNewLine=true;
                        break;
                    }
                }
                if(IsNewLine) continue;
                if(CrossLine->dynamicCall("ObjectID()").toLongLong()!=mLine->dynamicCall("ObjectID()").toLongLong())
                {
                    qDebug()<<"FindCrossLine=true";
                    FindCrossLine=true;
                    break;
                }
            }
            if(!FindCrossLine) continue;
            if(CrossLine==nullptr) continue;

            if(GetLineDir(CrossLine)==GetLineDir(mLine))//如果同方向则合并
            {
qDebug()<<"同方向则合并";
                IMxDrawPoint *NewLinePt1,*NewLinePt2;
                if(i==0) NewLinePt1=(IMxDrawPoint *)mLine->querySubObject("EndPoint()");
                else NewLinePt1=(IMxDrawPoint *)mLine->querySubObject("StartPoint()");
                if(GetLineDir(mLine)=="水平")
                {
                    if(NewLinePt1->x()>PtCross->x())
                    {
                        if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x()<=((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
                        else
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
                    }
                    else
                    {
                        if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x()<=((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
                        else
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
                    }
                }
                else if(GetLineDir(mLine)=="垂直")
                {
                    if(NewLinePt1->y()>PtCross->y())
                    {
                        if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y()<=((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
                        else
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
                    }
                    else
                    {
                        if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y()<=((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
                        else
                            NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
                    }
                }
                else return;
                //if((fabs(PtCross->x()-((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x())<minDelta)&&(fabs(PtCross->y()-((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y())<minDelta)) NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
                //else NewLinePt2=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
                mLine->dynamicCall("Erase()");
                CrossLine->dynamicCall("Erase()");
                SetCurLayer(ui->axWidget,"CONNECT");
                if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",NewLinePt2->x(),NewLinePt2->y(), NewLinePt1->x(),NewLinePt1->y()).toLongLong());
                else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",NewLinePt1->x(),NewLinePt1->y(),NewLinePt2->x(),NewLinePt2->y()).toLongLong());
                mLine=(IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                //timerAutoSaveDelay->start(1000);
                //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
                if(i==0) continue;
                else return;
            }
            else//查看mLine两端有垂直的连线，画节点,将对方直线分割成两段，靠近mLine的部分删除，远离mLine的部分如果长度为0则删除
            {
qDebug()<<"垂直";
                SetCurLayer(ui->axWidget,"CONNECT");
                //如果相交部分为对方直线的端点，则根据mLine方向和CrossLine方向画CO节点,如果相交部分为对方直线的中间点，则根据mLine方向和CrossLine方向画三连接节点
                int CrossInterminal=0;
                if((fabs(PtCross->x()-((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x())<minDelta)&&(fabs(PtCross->y()-((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y())<minDelta))
                   CrossInterminal=1;
                else if((fabs(PtCross->x()-((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())<minDelta)&&(fabs(PtCross->y()-((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())<minDelta))
                   CrossInterminal=2;
qDebug()<<"CrossInterminal="<<CrossInterminal;
                if(CrossInterminal>0)//垂直相交部分为对方直线的端点，则根据mLine方向和CrossLine方向画CO节点
                {
                   int CONumber=0;
                   double COBasex,COBasey;
                   IMxDrawPoint *COPt1,*COPt2;
                   if(i==0)//相交点为mLine的StartPoint
                       COPt1=(IMxDrawPoint *)mLine->querySubObject("EndPoint()");
                   else
                       COPt1=(IMxDrawPoint *)mLine->querySubObject("StartPoint()");
                   if(CrossInterminal==1)//相交点为CrossLine的StartPoint
                       COPt2=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
                   else
                       COPt2=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
qDebug()<<"q1";
                   if(GetLineDir(mLine)=="水平")
                   {
qDebug()<<"GetLineDir(mLine)==水平";
                       COBasex=COPt2->x();
                       COBasey=COPt1->y();
                       if(COPt1->x()>COPt2->x())
                       {
                           if(COPt1->y()>COPt2->y())
                           {
                               CONumber=1;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex+2,COBasey,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex+2,COBasey).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey-2, COPt2->x(),COPt2->y()).toLongLong());

                           }
                           else
                           {
                               CONumber=3;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex+2,COBasey,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex+2,COBasey).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey+2, COPt2->x(),COPt2->y()).toLongLong());
                           }
                       }
                       else
                       {
                           if(COPt1->y()>COPt2->y())
                           {
                               CONumber=2;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex-2,COBasey,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex-2,COBasey).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey-2, COPt2->x(),COPt2->y()).toLongLong());
                           }
                           else
                           {
                               CONumber=4;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex-2,COBasey,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex-2,COBasey).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey+2, COPt2->x(),COPt2->y()).toLongLong());
                           }
                       }
                   }
                   else if(GetLineDir(mLine)=="垂直")
                   {
qDebug()<<"GetLineDir(mLine)==垂直";
                       COBasex=COPt1->x();
                       COBasey=COPt2->y();
                       if(COPt1->y()>COPt2->y())
                       {
                           if(COPt1->x()>COPt2->x())
                           {
                               CONumber=4;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey+2,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex,COBasey+2).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex-2,COBasey, COPt2->x(),COPt2->y()).toLongLong());
                           }
                           else
                           {
                               CONumber=3;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey+2,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex,COBasey+2).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex+2,COBasey, COPt2->x(),COPt2->y()).toLongLong());
                           }
                       }
                       else
                       {
                           if(COPt1->x()>COPt2->x())
                           {
                               CONumber=2;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey-2,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex,COBasey-2).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex-2,COBasey, COPt2->x(),COPt2->y()).toLongLong());
                           }
                           else
                           {
                               CONumber=1;
                               if(i==0) ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex,COBasey-2,COPt1->x(),COPt1->y()).toLongLong());
                               else ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COPt1->x(),COPt1->y(),COBasex,COBasey-2).toLongLong());
                               NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",COBasex+2,COBasey, COPt2->x(),COPt2->y()).toLongLong());
                           }
                       }
                   }
qDebug()<<"CONumber="<<CONumber;
                   if(CONumber>0)
                   {
                       lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",COBasex,COBasey,"SYMB2_M_PWF_CO"+QString::number(CONumber),1.0,0).toLongLong();
qDebug()<<"DrawBlockReference";
                       IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                       ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                       //更新数据库
qDebug()<<"InsertNodeRecordToDB";
                       if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                       else qDebug()<<"blkNode=null";
                   }
                   mLineShouldErase=true;
qDebug()<<"CrossLine->dynamicCall(Erase());";
                   CrossLine->dynamicCall("Erase()");
                }
                else//CrossInterminal==0 垂直相交部分为对方直线的中间点，则根据mLine方向和CrossLine方向画三连接节点
                {
                    if(GetLineDir(CrossLine)=="水平")
                    {
                       //如果mLine在上，节点为SYMB2_M_PWF_TLRO1，如果mLine在下，节点为SYMB2_M_PWF_TLRU1
                        if(i==0)//相交点为mLine的StartPoint
                        {
                           if(((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y()>PtCross->y())//mLine在上
                           {
                               if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x()<((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())//CrossLine的左边为StartPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               }
                               else//CrossLine的左边为EndPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               }
                               lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TLRO1",1.0,0).toLongLong();
                               IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                               ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                               //更新数据库
                               if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                           }
                           else//mLine在下
                           {
                               if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x()<((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())//CrossLine的左边为StartPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               }
                               else//CrossLine的左边为EndPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y()).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                               }
                               lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TLRU1",1.0,0).toLongLong();
                               IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                               ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                               //更新数据库
                               if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                           }
                        }
                        else if(i==1)//相交点为mLine的EndPoint
                        {
                            if(((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y()>PtCross->y())//mLine在上
                            {
                                if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x()<((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())//CrossLine的左边为StartPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                }
                                else//CrossLine的左边为EndPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                }
                                lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TLRO1",1.0,0).toLongLong();
                                IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                                ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                                //更新数据库
                                if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                            }
                            else//mLine在下
                            {
                                if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x()<((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x())//CrossLine的左边为StartPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                }
                                else//CrossLine的左边为EndPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->x(),PtCross->y()).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                }
                                lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TLRU1",1.0,0).toLongLong();
                                IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                                ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                                //更新数据库
                                if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                            }
                        }
                    }
                    else if(GetLineDir(CrossLine)=="垂直")
                    {
qDebug()<<"如果mLine在左，节点为SYMB2_M_PWF_TOUL1，如果mLine在右，节点为SYMB2_M_PWF_TOUR1";
                       //如果mLine在左，节点为SYMB2_M_PWF_TOUL1，如果mLine在右，节点为SYMB2_M_PWF_TOUR1
                        if(i==0)//相交点为mLine的StartPoint
                        {
qDebug()<<"相交点为mLine的StartPoint";
                           if(((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x()<PtCross->x())//mLine在左
                           {
                               if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y()>((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())//CrossLine的上边为StartPoint
                               {
qDebug()<<"CrossLine的上边为StartPoint";
qDebug()<<"((IMxDrawPoint *)mLine->querySubObject(EndPoint()))->x()="<<((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x()<<"PtCross->y()="<<PtCross->y()<<"PtCross->x()="<<PtCross->x();
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
qDebug()<<"DrawLine,"<<((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x()<<","<<PtCross->y()<<","<<PtCross->x()-2<<","<<PtCross->y();
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                               }
                               else//CrossLine的上边为EndPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                               }
                               lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TOUL1",1.0,0).toLongLong();
                               IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                               ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                               //更新数据库
                               if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                           }
                           else//mLine在右
                           {
                               if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y()>((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())//CrossLine的上边为StartPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                               }
                               else//CrossLine的上边为EndPoint
                               {
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x(),PtCross->y()).toLongLong());
                                   NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                   ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                               }
                               lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TOUR1",1.0,0).toLongLong();
                               IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                               ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                               //更新数据库
                               if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                           }
                        }
                        else if(i==1)//相交点为mLine的EndPoint
                        {
                            if(((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x()<PtCross->x())//mLine在左
                            {
                                if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y()>((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())//CrossLine的上边为StartPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                                }
                                else//CrossLine的上边为EndPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                                }
                                lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TOUL1",1.0,0).toLongLong();
                                IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                                ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                                //更新数据库
                                if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                            }
                            else//mLine在右
                            {
                                if(((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y()>((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y())//CrossLine的上边为StartPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                                }
                                else//CrossLine的上边为EndPoint
                                {
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                                    NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                                    ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                                }
                                lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),"SYMB2_M_PWF_TOUR1",1.0,0).toLongLong();
                                IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                                ListNewConnect.append(blkNode->dynamicCall("ObjectID()").toLongLong());
                                //更新数据库
                                if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
                            }
                        }
                    }//end of if(GetLineDir(CrossLine)=="垂直")
                    mLineShouldErase=true;
 qDebug()<<"CrossLine->dynamicCall(Erase());";
                    CrossLine->dynamicCall("Erase()");
                }//end of CrossInterminal==0 垂直相交部分为对方直线的中间点，则根据mLine方向和CrossLine方向画三连接节点
            }//end of if(GetLineDir(CrossLine)!=GetLineDir(mLine))
        }//end of if(ss->dynamicCall("Count()").toInt()>1)

        //查看PtCross是否与Node的"中心点"相交，如果与CO节点相交，则根据方向变为三连接节点，如果与三连接节点相交，则变为四连接节点
        IMxDrawPoint *mLineStartPoint=(IMxDrawPoint *)mLine->querySubObject("StartPoint()");
        IMxDrawPoint *mLineEndPoint=(IMxDrawPoint *)mLine->querySubObject("EndPoint()");
        filter->RemoveAll();
        filter->AddStringEx("INSERT",5020);
        filter->AddStringEx("CONNECT", 8);
qDebug()<<"Select INSERT AtPoint PtCross";
        ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtCross->asVariant(),filter->asVariant());
qDebug()<<"Count="<<ss->dynamicCall("Count()").toInt();
        for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
        {
            QString NodeSymbolName="";
            IMxDrawBlockReference *CrossNode = (IMxDrawBlockReference *)ss->querySubObject("Item(int)",j);
            if(CrossNode==nullptr) continue;
            if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossNode)) continue;//去除erase的实体
            bool IsNewConnect=false;
            for(int k=0;k<ListNewConnect.count();k++)
            {
                if(ListNewConnect.at(k)==CrossNode->dynamicCall("ObjectID()").toLongLong()) //去除新绘的Connect
                {
                    IsNewConnect=true;
                    break;
                }
            }
            if(IsNewConnect) continue;
qDebug()<<"Find CrossNode";
            IMxDrawPoint *PtC=(IMxDrawPoint *)CrossNode->querySubObject("Position()");
            if(PtC==nullptr) continue;
qDebug()<<"Find PtC,PtC->x()="<<PtC->x()<<"PtC->y()="<<PtC->y()<<"PtCross->x()="<<PtCross->x()<<"PtCross->y()="<<PtCross->y();
            if((fabs(PtC->x()-PtCross->x())>minDelta)||(fabs(PtC->y()-PtCross->y())>minDelta)) continue;//不是Node的中心点
qDebug()<<"是Node的中心点";
            if(CrossNode->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_CO"))//与CO节点相交，则根据方向变为三连接节点
            {
 qDebug()<<"contains SYMB2_M_PWF_CO";
                if(CrossNode->dynamicCall("GetBlockName()").toString()=="SYMB2_M_PWF_CO1")//如果mLine水平则变为SYMB2_M_PWF_TLRU1，如果mLine垂直则变为SYMB2_M_PWF_TOUR1
                {
qDebug()<<"== SYMB2_M_PWF_CO1";
                    if(GetLineDir(mLine)=="水平")
                    {
qDebug()<<"GetLineDir=水平";
                        if((mLineEndPoint->x()<=PtCross->x())&&(mLineStartPoint->x()<=PtCross->x()))
                        {
qDebug()<<"(mLineEndPoint->x()<=PtCross->x())&&(mLineStartPoint->x()<=PtCross->x())";
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TLRU1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
qDebug()<<"非 (mLineEndPoint->x()<=PtCross->x())&&(mLineStartPoint->x()<=PtCross->x())";
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    else
                    {
qDebug()<<"GetLineDir=垂直";
                        if((mLineEndPoint->y()>=PtCross->y())&&(mLineStartPoint->y()>=PtCross->y()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TOUR1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    mLineShouldErase=true;
                }
                else if(CrossNode->dynamicCall("GetBlockName()").toString()=="SYMB2_M_PWF_CO2")//如果mLine水平则变为SYMB2_M_PWF_TLRU1，如果mLine垂直则变为SYMB2_M_PWF_TOUL1
                {
                    if(GetLineDir(mLine)=="水平")
                    {
                        if((mLineEndPoint->x()>=PtCross->x())&&(mLineStartPoint->x()>=PtCross->x()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TLRU1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    else
                    {
                        if((mLineEndPoint->y()>=PtCross->y())&&(mLineStartPoint->y()>=PtCross->y()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TOUL1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->y(),PtCross->x(),PtCross->y()-2,PtCross->x()).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    mLineShouldErase=true;
                }
                else if(CrossNode->dynamicCall("GetBlockName()").toString()=="SYMB2_M_PWF_CO3")//如果mLine水平则变为SYMB2_M_PWF_TLRO1，如果mLine垂直则变为SYMB2_M_PWF_TOUR1
                {
                    if(GetLineDir(mLine)=="水平")
                    {
                        if((mLineEndPoint->x()<=PtCross->x())&&(mLineStartPoint->x()<=PtCross->x()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TLRO1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    else
                    {
                        if((mLineEndPoint->y()<=PtCross->y())&&(mLineStartPoint->y()<=PtCross->y()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TOUR1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    mLineShouldErase=true;
                }
                else if(CrossNode->dynamicCall("GetBlockName()").toString()=="SYMB2_M_PWF_CO4")//如果mLine水平则变为SYMB2_M_PWF_TLRO1，如果mLine垂直则变为SYMB2_M_PWF_TOUL1
                {
                    if(GetLineDir(mLine)=="水平")
                    {
                        if((mLineEndPoint->x()>=PtCross->x())&&(mLineStartPoint->x()>=PtCross->x()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TLRO1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    else
                    {
                        if((mLineEndPoint->y()<=PtCross->y())&&(mLineStartPoint->y()<=PtCross->y()))
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                            NodeSymbolName="SYMB2_M_PWF_TOUL1";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                        else
                        {
                            if(i==0)//PtCross为mLine的StartPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                            else//PtCross为mLine的EndPoint
                              ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                            NodeSymbolName="";
                            NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
                        }
                    }
                    mLineShouldErase=true;
                }
            }
            else if(CrossNode->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TLRU"))//与三连接节点相交，则变为四连接节点
            {
                if(i==0)//PtCross为mLine的StartPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                else//PtCross为mLine的EndPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()+2).toLongLong());
                NodeSymbolName="SYMB2_M_PWF_BR1";
                mLineShouldErase=true;
                NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
            }
            else if(CrossNode->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TLRO"))//与三连接节点相交，则变为四连接节点
            {
                if(i==0)//PtCross为mLine的StartPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
                else//PtCross为mLine的EndPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),mLineStartPoint->y(),PtCross->x(),PtCross->y()-2).toLongLong());
                NodeSymbolName="SYMB2_M_PWF_BR1";
                mLineShouldErase=true;
                NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
            }
            else if(CrossNode->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TOUR"))//与三连接节点相交，则变为四连接节点
            {
                if(i==0)//PtCross为mLine的StartPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()-2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                else//PtCross为mLine的EndPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
                NodeSymbolName="SYMB2_M_PWF_BR1";
                mLineShouldErase=true;
                NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
            }
            else if(CrossNode->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_TOUL"))//与三连接节点相交，则变为四连接节点
            {
                if(i==0)//PtCross为mLine的StartPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
                else//PtCross为mLine的EndPoint
                  ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
                NodeSymbolName="SYMB2_M_PWF_BR1";
                mLineShouldErase=true;
                NewmLine= (IMxDrawLine *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListNewLine.at(ListNewLine.count()-1));
            }
qDebug()<<"NodeSymbolName="<<NodeSymbolName;
            if(NodeSymbolName!="")
            {
qDebug()<<"DrawBlockReference,NodeSymbolName="<<NodeSymbolName;
                lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),NodeSymbolName,1.0,0).toLongLong();
                //删除数据库中的Connect记录
                QSqlQuery query=QSqlQuery(T_ProjectDatabase);
                QString SqlStr =  "DELETE FROM Connector WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Connector_Handle = '"+CrossNode->dynamicCall("handle()").toString()+"'";
                query.exec(SqlStr);
qDebug()<<"Erase CrossNode";
                CrossNode->dynamicCall("Erase()");
qDebug()<<"Erase CrossNode ok";
                IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                //更新数据库
qDebug()<<"InsertNodeRecordToDB";
                if(blkNode!=nullptr) {InsertNodeRecordToDB(blkNode);continue;}
qDebug()<<"InsertNodeRecordToDB ok";
            }
            if(mLineShouldErase) break;
        }//end of for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
        if(mLineShouldErase)
        {
    qDebug()<<"Erase mLine";
            mLine->dynamicCall("Erase()");
    qDebug()<<"Erase mLine ok";
            mLine=NewmLine;
            mLineShouldErase=false;
        }
    }//end of for(int i=0;i<2;i++) ,mLine的两个端点   

qDebug()<<"查看mLine是否存在T型垂直的连线，且交点不是mLine的端点，若存在则画3连接节点";
    //查看mLine是否存在T型垂直的连线，且交点不是mLine的端点，若存在则画3连接节点
    //检索所有直线，找到与mLine垂直的直线
    if(mLine==nullptr) return;
    if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)mLine)) return;
    SetCurLayer(ui->axWidget,"CONNECT");
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter->RemoveAll();
    filter->AddStringEx("LINE",5020);
    filter->AddStringEx("CONNECT",8);
qDebug()<<"LINE CONNECT AllSelect";
    ss->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    qDebug()<<"Line ss.Count()="<<ss->Count();

    for (int i = 0; i < ss->Count(); i++)
    {
        int FindLine=0;
        QString NodeSymbolName="";
        IMxDrawLine* CrossLine = (IMxDrawLine*)ss->querySubObject("Item(int)",i);
        if(CrossLine==nullptr) continue;
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体

        //排除CrossLine的端点和节点相交的情况
        IMxDrawSelectionSet *ssExclude= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filterExclude=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        filterExclude->RemoveAll();
        filterExclude->AddStringEx("INSERT",5020);
        filterExclude->AddStringEx("CONNECT", 8);
        IMxDrawPoint *mStartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
        ssExclude->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",mStartPoint->asVariant(),filterExclude->asVariant());
        if(ssExclude->dynamicCall("Count()").toInt()>0) continue;
        IMxDrawPoint *mEndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
        ssExclude->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",mEndPoint->asVariant(),filterExclude->asVariant());
        if(ssExclude->dynamicCall("Count()").toInt()>0) continue;

        IMxDrawPoints* pts=(IMxDrawPoints*)mLine->querySubObject("IntersectWith(IDispatch*,int)",CrossLine->asVariant(),McExtendOption::mcExtendNone);
        if(pts->Count()!=1) continue;
        IMxDrawPoint *PtCross = (IMxDrawPoint *)pts->querySubObject("Item(int)",0);
        if(GetLineDir(CrossLine)==GetLineDir(mLine)) continue;

        IMxDrawPoint *mLineStartPoint=(IMxDrawPoint *)mLine->querySubObject("StartPoint()");
        IMxDrawPoint *mLineEndPoint=(IMxDrawPoint *)mLine->querySubObject("EndPoint()");
        IMxDrawPoint *CrossLineStartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
        IMxDrawPoint *CrossLineEndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
        if(GetLineDir(mLine)=="水平")
        {
            if((PtCross->y()<=CrossLineStartPoint->y())&&(PtCross->y()<=CrossLineEndPoint->y()))//对方连线为垂直且在mLine上方
            {
                if(CrossLineStartPoint->y()>PtCross->y())//对方连线上侧为StartPoint
                {
                    if((PtCross->x()>mLineStartPoint->x())&&(PtCross->x()<mLineEndPoint->x())) FindLine=1;//mLine左侧为StartPoint
                    if((PtCross->x()<mLineStartPoint->x())&&(PtCross->x()>mLineEndPoint->x())) FindLine=2;//mLine左侧为EndPoint
                }
                else//对方连线上侧为EndPoint
                {
                    if((PtCross->x()>mLineStartPoint->x())&&(PtCross->x()<mLineEndPoint->x())) FindLine=3;//mLine左侧为StartPoint
                    if((PtCross->x()<mLineStartPoint->x())&&(PtCross->x()>mLineEndPoint->x())) FindLine=4;//mLine左侧为EndPoint
                }
            }
            else if((PtCross->y()>=CrossLineStartPoint->y())&&(PtCross->y()>=CrossLineEndPoint->y()))//对方连线为垂直且在mLine下方
            {
                if(CrossLineEndPoint->y()<PtCross->y())//对方连线上侧为StartPoint
                {
                    if((PtCross->x()>mLineStartPoint->x())&&(PtCross->x()<mLineEndPoint->x())) FindLine=5;//mLine左侧为StartPoint
                    if((PtCross->x()<mLineStartPoint->x())&&(PtCross->x()>mLineEndPoint->x())) FindLine=6;//mLine左侧为EndPoint
                }
                else//对方连线上侧为EndPoint
                {
                    if((PtCross->x()>mLineStartPoint->x())&&(PtCross->x()<mLineEndPoint->x())) FindLine=7;//mLine左侧为StartPoint
                    if((PtCross->x()<mLineStartPoint->x())&&(PtCross->x()>mLineEndPoint->x())) FindLine=8;//mLine左侧为EndPoint
                }
            }
        }
        else//对方连线为水平
        {
            if((PtCross->x()>=CrossLineStartPoint->x())&&(PtCross->x()>=CrossLineEndPoint->x()))//对方连线为水平且在mLine左方
            {
                if(CrossLineStartPoint->x()<PtCross->x())//对方连线左侧为StartPoint
                {
                    if((PtCross->y()<mLineStartPoint->y())&&(PtCross->y()>mLineEndPoint->y())) FindLine=9;//mLine上侧为StartPoint
                    if((PtCross->y()>mLineStartPoint->y())&&(PtCross->y()<mLineEndPoint->y())) FindLine=10;//mLine上侧为EndPoint
                }
                else//对方连线上侧为EndPoint
                {
                    if((PtCross->y()<mLineStartPoint->y())&&(PtCross->y()>mLineEndPoint->y())) FindLine=11;//mLine上侧为StartPoint
                    if((PtCross->y()>mLineStartPoint->y())&&(PtCross->y()<mLineEndPoint->y())) FindLine=12;//mLine上侧为EndPoint
                }
            }
            else if((PtCross->x()<=CrossLineStartPoint->x())&&(PtCross->x()<=CrossLineEndPoint->x()))//对方连线为水平且在mLine右方
            {
                if(CrossLineEndPoint->x()>PtCross->x())//对方连线左侧为StartPoint
                {
                    if((PtCross->y()<mLineStartPoint->y())&&(PtCross->y()>mLineEndPoint->y())) FindLine=13;//mLine上侧为StartPoint
                    if((PtCross->y()>mLineStartPoint->y())&&(PtCross->y()<mLineEndPoint->y())) FindLine=14;//mLine上侧为EndPoint
                }
                else//对方连线右侧为StartPoint
                {
                    if((PtCross->y()<mLineStartPoint->y())&&(PtCross->y()>mLineEndPoint->y())) FindLine=15;//mLine上侧为StartPoint
                    if((PtCross->y()>mLineStartPoint->y())&&(PtCross->y()<mLineEndPoint->y())) FindLine=16;//mLine上侧为EndPoint
                }
            }
        }
qDebug()<<"FindLine="<<FindLine;
        if(FindLine<=0) continue;
        if(FindLine==1)//mLine水平，mLine左侧为StartPoint,对方连线为垂直且在mLine上方,对方连线上侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),CrossLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRO1";
        }
        else if(FindLine==2)//mLine水平，mLine左侧为EndPoint,对方连线为垂直且在mLine上方,对方连线上侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineEndPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineStartPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),CrossLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRO1";
        }
        else if(FindLine==3)//mLine水平，mLine左侧为StartPoint,对方连线为垂直且在mLine上方,对方连线上侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),CrossLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRO1";
        }
        else if(FindLine==4)//mLine水平，mLine左侧为EndPoint,对方连线为垂直且在mLine上方,对方连线上侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineEndPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineStartPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),CrossLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRO1";
        }
        else if(FindLine==5)//mLine水平，mLine左侧为StartPoint,对方连线为垂直且在mLine下方,对方连线上侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),CrossLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRU1";
        }
        else if(FindLine==6)//mLine水平，mLine左侧为EndPoint,对方连线为垂直且在mLine下方,对方连线上侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineEndPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineStartPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),CrossLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRU1";
        }
        else if(FindLine==7)//mLine水平，mLine左侧为StartPoint,对方连线为垂直且在mLine下方,对方连线上侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineEndPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),CrossLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRU1";
        }
        else if(FindLine==8)//mLine水平，mLine左侧为EndPoint,对方连线为垂直且在mLine下方,对方连线上侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",mLineEndPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x()+2,PtCross->y(),mLineStartPoint->x(),PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),CrossLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TLRU1";
        }
        else if(FindLine==9)//mLine垂直，mLine上侧为StartPoint,对方连线为水平且在mLine左方,对方连线左侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUL1";
        }
        else if(FindLine==10)//mLine垂直，mLine上侧为EndPoint,对方连线为水平且在mLine左方,对方连线左侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineStartPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUL1";
        }
        else if(FindLine==11)//mLine垂直，mLine上侧为StartPoint,对方连线为水平且在mLine左方,对方连线左侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineEndPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUL1";
        }
        else if(FindLine==12)//mLine垂直，mLine上侧为EndPoint,对方连线为水平且在mLine左方,对方连线左侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineEndPoint->x(),PtCross->y(),PtCross->x()-2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUL1";
        }
        else if(FindLine==13)//mLine垂直，mLine上侧为StartPoint,对方连线为水平且在mLine右方,对方连线左侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineEndPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUR1";
        }
        else if(FindLine==14)//mLine垂直，mLine上侧为EndPoint,对方连线为水平且在mLine右方,对方连线左侧为StartPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineEndPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUR1";
        }
        else if(FindLine==15)//mLine垂直，mLine上侧为StartPoint,对方连线为水平且在mLine右方,对方连线左侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUR1";
        }
        else if(FindLine==16)//mLine垂直，mLine上侧为EndPoint,对方连线为水平且在mLine右方,对方连线左侧为EndPoint
        {
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",CrossLineStartPoint->x(),PtCross->y(),PtCross->x()+2,PtCross->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()+2,PtCross->x(),mLineEndPoint->y()).toLongLong());
            ListNewLine.append(ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtCross->x(),PtCross->y()-2,PtCross->x(),mLineStartPoint->y()).toLongLong());
            NodeSymbolName="SYMB2_M_PWF_TOUR1";
        }
        if(NodeSymbolName!="")
        {
            lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",PtCross->x(),PtCross->y(),NodeSymbolName,1.0,0).toLongLong();
            IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
            //更新数据库
            if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
            CrossLine->dynamicCall("Erase()");
            mLine->dynamicCall("Erase()");
            break;
        }
    }

    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
}

void formaxwidget::DoDrawMultiLibLine()
{
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","OSMODE",0);
    PickPointCount=0;
    MxDrawUiPrPoint getPt;
    SetCurLayer(ui->axWidget,"0");
    while(true)
    {
        getPt.setMessage("起点，esc或鼠标右键退出");
        ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
        IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawConnectLine");
        // 等用户在图上点取一个点
        if (getPt.go() != McUiPrStatus::mcOk)  break;
        Pt1 = getPt.value();
        if (Pt1 == nullptr) break;  // 返回点的点对象值。
        PickPointCount++;

        getPt.setMessage("终点");
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            SetTermVisible(false);
            break;
        }
        Pt2  = getPt.value();//GetGridPtVal(getPt.value());
        if (Pt2 == nullptr) break;   // 返回点的点对象值。
        PickPointCount=0;
        //画线，考虑是先水平后垂直还是先垂直后水平
        qlonglong lID1,lID2;
        bool DrawHoriLine=true,DrawVerLine=true;
        if(ConnectLineDir==1) //先水平后垂直
        {
            if((fabs(Pt1->x()-Pt2->x())<0.1)||(fabs(Pt1->y()-Pt2->y())<0.1)) //只需要画一条线
            {
                if(fabs(Pt1->x()-Pt2->x())<1.9)
                {
                    lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawHoriLine=false;
                }
                else
                {
                    lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawVerLine=false;
                }
            }
            else//先水平后垂直，转角处画SYMB2_M_PWF_CO1~SYMB2_M_PWF_CO4
            {
                lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt1->y()).toLongLong();
                lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt2->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
            }
        }
        else //先垂直后水平
        {
            if((fabs(Pt1->x()-Pt2->x())<0.1)||(fabs(Pt1->y()-Pt2->y())<0.1)) //只需要画一条线
            {
                if(fabs(Pt1->x()-Pt2->x())<1.9)
                {
                    lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawHoriLine=false;
                }
                else
                {
                    lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawVerLine=false;
                }
            }
            else
            {
                lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt1->x(),Pt2->y()).toLongLong();
                lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt2->y(), Pt2->x(),Pt2->y()).toLongLong();
            }
        }
        IMxDrawLine *termline;
        if(DrawHoriLine)
        {
            termline= (IMxDrawLine*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID1);
            termline->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
            termline->dynamicCall("SetLineType(QString)","MyDotLineType");
        }
        if(DrawVerLine)
        {
            termline= (IMxDrawLine*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID2);
            termline->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
            termline->dynamicCall("SetLineType(QString)","MyDotLineType");
        }
        Pt1=Pt2;
    }
    PickPointCount=0;
}

void formaxwidget::DoLineConnect()
{
ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","OSMODE",0);
    PickPointCount=0;
    MxDrawUiPrPoint getPt;

    while(true)
    {
        getPt.setMessage("起点，esc或鼠标右键退出");
        ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
        IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawConnectLine");
        SetTermVisible(true);
        ConnectLineDir=0;
        // 等用户在图上点取一个点
        if (getPt.go() != McUiPrStatus::mcOk)  break;
        Pt1 = GetBesideTermPtVal(getPt.value());//GetGridPtVal(getPt.value());
        if (Pt1 == nullptr) break;  // 返回点的点对象值。
qDebug()<<"Pt1x="<<Pt1->x()<<",Pt1->y()="<<Pt1->y();
        if(!CheckConnectLinePt(1)) {qDebug()<<"CheckConnectLinePt(1) false";continue;}
        PickPointCount++;

        getPt.setMessage("终点");
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            SetTermVisible(false);
            break;
        }
        Pt2  = GetBesideTermPtVal(getPt.value());//GetGridPtVal(getPt.value());
        if (Pt2 == nullptr) break;   // 返回点的点对象值。
qDebug()<<"Pt2x="<<Pt2->x()<<",Pt2->y()="<<Pt2->y()<<",ConnectLineDir="<<ConnectLineDir;
        if(!CheckConnectLinePt(2)) {qDebug()<<"CheckConnectLinePt(2) false";break;}
        PickPointCount=0;
        //画线，考虑是先水平后垂直还是先垂直后水平
        SetCurLayer(ui->axWidget,"CONNECT");
        int CONumber=0;
        qlonglong lID1,lID2;
        bool DrawHoriLine=true,DrawVerLine=true;
        if(ConnectLineDir==1) //先水平后垂直
        {          
            if((fabs(Pt1->x()-Pt2->x())<1.9)||(fabs(Pt1->y()-Pt2->y())<1.9)) //只需要画一条线
            {
                if(fabs(Pt1->x()-Pt2->x())<1.9)
                {
                    lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawHoriLine=false;
                }
                else
                {
                    lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawVerLine=false;
                }
            }
            else//先水平后垂直，转角处画SYMB2_M_PWF_CO1~SYMB2_M_PWF_CO4
            {
                if((Pt1->x()>Pt2->x())&&(Pt1->y()>Pt2->y())) CONumber=1;
                else if((Pt1->x()<Pt2->x())&&(Pt1->y()>Pt2->y())) CONumber=2;
                else if((Pt1->x()>Pt2->x())&&(Pt1->y()<Pt2->y())) CONumber=3;
                else if((Pt1->x()<Pt2->x())&&(Pt1->y()<Pt2->y())) CONumber=4;

                if(fabs(Pt2->x()-Pt1->x())<=2) DrawHoriLine=false;
                if(fabs(Pt2->y()-Pt1->y())<=2) DrawVerLine=false;
                if(CONumber==1)
                {
                    if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x()+2,Pt1->y()).toLongLong();
                    if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt2->x(),Pt1->y()-2, Pt2->x(),Pt2->y()).toLongLong();
                    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt2->x(),Pt1->y(),"SYMB2_M_PWF_CO1",1.0,0).toLongLong();
                }
                else if(CONumber==2)
                {
                    if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x()-2,Pt1->y()).toLongLong();
                    if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt2->x(),Pt1->y()-2, Pt2->x(),Pt2->y()).toLongLong();
                    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt2->x(),Pt1->y(),"SYMB2_M_PWF_CO2",1.0,0).toLongLong();
                }
                else if(CONumber==3)
                {
                    if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x()+2,Pt1->y()).toLongLong();
                    if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt2->x(),Pt1->y()+2, Pt2->x(),Pt2->y()).toLongLong();
                    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt2->x(),Pt1->y(),"SYMB2_M_PWF_CO3",1.0,0).toLongLong();
                }
                else if(CONumber==4)
                {
                    if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x()-2,Pt1->y()).toLongLong();
                    if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt2->x(),Pt1->y()+2, Pt2->x(),Pt2->y()).toLongLong();
                    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt2->x(),Pt1->y(),"SYMB2_M_PWF_CO4",1.0,0).toLongLong();
                }
            }
        }
        else //先垂直后水平
        {
            if((fabs(Pt1->x()-Pt2->x())<1.9)||(fabs(Pt1->y()-Pt2->y())<1.9)) //只需要画一条线
            {
qDebug()<<"只需要画一条线";
                if(fabs(Pt1->x()-Pt2->x())<1.9)
                {
                    lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawHoriLine=false;
                }
                else
                {
                    lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt2->x(),Pt2->y()).toLongLong();
                    DrawVerLine=false;
                }
            }
            else
            {
qDebug()<<"需要画2条线";
              if((Pt1->x()<Pt2->x())&&(Pt1->y()<Pt2->y())) CONumber=1;
              else if((Pt1->x()>Pt2->x())&&(Pt1->y()<Pt2->y())) CONumber=2;
              else if((Pt1->x()<Pt2->x())&&(Pt1->y()>Pt2->y())) CONumber=3;
              else if((Pt1->x()>Pt2->x())&&(Pt1->y()>Pt2->y())) CONumber=4;

              if(fabs(Pt2->x()-Pt1->x())<=2) DrawHoriLine=false;
              if(fabs(Pt2->y()-Pt1->y())<=2) DrawVerLine=false;
              if(CONumber==1)
              {
                  if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt1->x(),Pt2->y()-2).toLongLong();
                  if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x()+2,Pt2->y(), Pt2->x(),Pt2->y()).toLongLong();
                  lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt1->x(),Pt2->y(),"SYMB2_M_PWF_CO1",1.0,0).toLongLong();
              }
              else if(CONumber==2)
              {
                  if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt1->x(),Pt2->y()-2).toLongLong();
                  if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x()-2,Pt2->y(), Pt2->x(),Pt2->y()).toLongLong();
                  lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt1->x(),Pt2->y(),"SYMB2_M_PWF_CO2",1.0,0).toLongLong();
              }
              else if(CONumber==3)
              {
                  if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt1->x(),Pt2->y()+2).toLongLong();
                  if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x()+2,Pt2->y(), Pt2->x(),Pt2->y()).toLongLong();
                  lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt1->x(),Pt2->y(),"SYMB2_M_PWF_CO3",1.0,0).toLongLong();
              }
              else if(CONumber==4)
              {
                  if(DrawVerLine) lID2=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt1->x(),Pt2->y()+2).toLongLong();
                  if(DrawHoriLine) lID1=ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",Pt1->x()-2,Pt2->y(), Pt2->x(),Pt2->y()).toLongLong();
                  lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt1->x(),Pt2->y(),"SYMB2_M_PWF_CO4",1.0,0).toLongLong();
              }
            }
        }
        /*
        //如果lID的两端均是同一个端子排的端子，且短接，则连线变为蓝色
        bool FlagCombineLine=true;
        if(DrawHoriLine||DrawVerLine)
        {
            IMxDrawLine *termline;
            if(DrawHoriLine) termline= (IMxDrawLine*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID1);
            if(DrawVerLine) termline= (IMxDrawLine*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID2);
            if(termline!=nullptr)
            {
               IMxDrawPoint *StartPoint= (IMxDrawPoint *)termline->querySubObject("StartPoint()");
               IMxDrawPoint *EndPoint= (IMxDrawPoint *)termline->querySubObject("EndPoint()");
               QString StartCoordination=QString::number(StartPoint->x(),'f',0)+".000000,"+QString::number(StartPoint->y(),'f',0)+".000000,0.000000";
               QString EndCoordination=QString::number(EndPoint->x(),'f',0)+".000000,"+QString::number(EndPoint->y(),'f',0)+".000000,0.000000";
               QSqlQuery QueryTerminal=QSqlQuery(T_ProjectDatabase);
               QString SqlStr="SELECT * FROM Terminal WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Coordinate = '"+StartCoordination+"'";
               QueryTerminal.exec(SqlStr);
qDebug()<<"SqlStr="<<SqlStr;
               if(QueryTerminal.next())
               {
                   QString TerminalStrip_ID1=QueryTerminal.value("TerminalStrip_ID").toString();
                   QString ShortJumper1=QueryTerminal.value("ShortJumper").toString();
qDebug()<<"TerminalStrip_ID1="<<TerminalStrip_ID1<<",ShortJumper1="<<ShortJumper1;
                   SqlStr="SELECT * FROM Terminal WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Coordinate = '"+EndCoordination+"'";
                   QueryTerminal.exec(SqlStr);
                   if(QueryTerminal.next())
                   {
                       QString TerminalStrip_ID2=QueryTerminal.value("TerminalStrip_ID").toString();
                       QString ShortJumper2=QueryTerminal.value("ShortJumper").toString();
qDebug()<<"TerminalStrip_ID2="<<TerminalStrip_ID2<<",ShortJumper2="<<ShortJumper2;
                       if((TerminalStrip_ID1==TerminalStrip_ID2)&&(ShortJumper1==ShortJumper2))
                       {
                           termline->dynamicCall("setColorIndex(int)",McColor::mcBlue);
                           FlagCombineLine=false;
                       }
                   }
               }
            }
        }//end of if(DrawHoriLine||DrawVerLine)
        */
        if(CONumber>0)
        {
            IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
            //更新数据库
            if(blkNode!=nullptr) InsertNodeRecordToDB(blkNode);
        }
        if(DrawHoriLine) CombineLine((IMxDrawLine*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID1));
        if(DrawVerLine) CombineLine((IMxDrawLine*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID2));
        Pt1=Pt2;  
    }
    PickPointCount=0;
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    SetCurLayer(ui->axWidget,"0");
    SetTermVisible(false);
    //timerAutoSaveDelay->start(1000);
   // ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
}
void formaxwidget::LineConnect()
{
/*
    //insert节点
    for(int i=0;i<4;i++)
    {
        SymbolName="SYMB2_M_PWF_CO"+QString::number(i+1)+".dwg";
        BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
        //if(!BlockRecordExist(SymbolName.mid(0,SymbolName.count()-4)))
        MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4));
    }*/
   if(IsDrawingMultiLib) ui->axWidget->dynamicCall("DoCommand(const int&)",125);
   else ui->axWidget->dynamicCall("DoCommand(const int&)",109);
}

//端号批标注
void formaxwidget::DoTermBatchMark()
{

}

void formaxwidget::TermBatchMark()
{
   ui->axWidget->dynamicCall("DoCommand(const int&)",121);
}

void formaxwidget::PuttingAttrDef()
{
    MxDrawUiPrPoint getPt;
    getPt.setMessage("请指定位置");
    PickPointCount=0;
    // 等用户在图上点取一个点
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawAttrDef");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    IMxDrawPoint* frstPt = getPt.value();
    if (frstPt == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;
    ui->axWidget->setProperty("TextStyle","Standard");
    qlonglong lID;
    if(StrIsNumber(m_dragText)) lID=DrawAttrDef(ui->axWidget,frstPt->x(),frstPt->y(),m_dragText,m_dragText);
    else lID=DrawAttrDef(ui->axWidget,frstPt->x(),frstPt->y(),m_dragText,"");
    emit(SignalDrawAttrDefDone(m_dragText,lID));
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
}
void formaxwidget::GetUrPoint()
{
    MxDrawUiPrPoint getPt;
    getPt.setMessage("请选择点");
    //this->hide();
    // 等用户在图上点取一个点
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    IMxDrawPoint* frstPt = getPt.value();
    if (frstPt == nullptr) {getPt.setMessage("选点操作失败");return; }  // 返回点的点对象值。
    if(IsDrawingMultiLib)
    {
        //设置基点
        IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
        database->dynamicCall("SetInsbase(QAxObject*)",frstPt->asVariant());
    }
    else emit(GetUrPoint(frstPt));
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
}
void formaxwidget::InsertNodes()
{
    for(int i=0;i<4;i++)
    {
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_CO"+QString::number(i+1)+".dwg","SYMB2_M_PWF_CO"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_BR"+QString::number(i+1)+".dwg","SYMB2_M_PWF_BR"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_CR"+QString::number(i+1)+".dwg","SYMB2_M_PWF_CR"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_TLRO"+QString::number(i+1)+".dwg","SYMB2_M_PWF_TLRO"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_TLRU"+QString::number(i+1)+".dwg","SYMB2_M_PWF_TLRU"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_TOUL"+QString::number(i+1)+".dwg","SYMB2_M_PWF_TOUL"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_TOUR"+QString::number(i+1)+".dwg","SYMB2_M_PWF_TOUR"+QString::number(i+1));
        MyInsertBlock(ui->axWidget,"C:/TBD/SymbConnLib/SYMB2_M_PWF_链接点"+QString::number(i+1)+".dwg","SYMB2_M_PWF_链接点"+QString::number(i+1));
    }
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
}


void formaxwidget::DoOpenDwgFileCommand()
{
    //如果文件存在则打开，文件不存在且文件名不为空则自动创建
    qDebug()<<"OpenDwgFile "<<dwgFileName;
    QFileInfo file(dwgFileName);
    if(file.exists())
    {
        ui->axWidget->dynamicCall("OpenDwgFile(QString)",dwgFileName);
        ui->axWidget->dynamicCall("ZoomAll()");
    }
    else
    {
        if(dwgFileName=="") return;
        QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
        QFile::copy(SourceFileName,dwgFileName);
        ui->axWidget->dynamicCall("OpenDwgFile(QString)",dwgFileName);
        ui->axWidget->dynamicCall("ZoomAll()");
    }

}

void formaxwidget::DoEditMultiLib()
{
    ui->axWidget->dynamicCall("OpenDwgFile(QString)",MultiLibFilePath);
    ui->axWidget->dynamicCall("ZoomAll()");
    ui->axWidget->dynamicCall("ZoomScale(double)",2);
    SetCurLayer(ui->axWidget,"0");
}

void formaxwidget::EditMultiLib(QString FileName)
{
   MultiLibFilePath=FileName;
   ui->axWidget->dynamicCall("DoCommand(const int&)",124);
}

void formaxwidget::DoEditSymbolCommand()
{
qDebug()<<"DoEditSymbolCommand,path="<<"C:/TBD/SYMB2LIB/"+SymbolName;
    ui->axWidget->dynamicCall("OpenDwgFile(QString)","C:/TBD/SYMB2LIB/"+SymbolName);
    ui->axWidget->dynamicCall("ZoomAll()");
    ui->axWidget->dynamicCall("ZoomScale(double)",2);
    SetCurLayer(ui->axWidget,"0");
    ui->axWidget->dynamicCall("DoCommand(const int&)",103);
}
void formaxwidget::DoSymbolAttribute()
{ 
qDebug()<<"DoSymbolAttribute";
    dlgSymbolAttribute->move(QApplication::desktop()->screenGeometry().width()-dlgSymbolAttribute->width()-30,QApplication::desktop()->screenGeometry().height()/2-dlgSymbolAttribute->height()/2);
    if(DataBaseSymbolID=="") dlgSymbolAttribute->setWindowTitle("新建符号");
    else dlgSymbolAttribute->setWindowTitle("修改符号");
    dlgSymbolAttribute->SymbolFileName=SymbolName;
    dlgSymbolAttribute->DataBaseSymbolID=DataBaseSymbolID;
    dlgSymbolAttribute->SymbolType=SymbolType;
    dlgSymbolAttribute->FunctionDefineClass_ID=FunctionDefineClass_ID;
    dlgSymbolAttribute->tmp_MxDrawWidget=ui->axWidget;
    dlgSymbolAttribute->LoadSymbolAttribute();
    dlgSymbolAttribute->show();
    IsDoingSymbolEdit=true;
    QApplication::processEvents();
}

void formaxwidget::EraseTerms(IMxDrawBlockReference *blkEnty)//在符号编辑模式下需要删除插入块中的端子
{
   IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )blkEnty->querySubObject("BlockTableRecord()");
   IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
   // 循环得到所有实体
   for (; !iter->Done(); iter->Step(true, false))
   {
       // 得到遍历器当前的实体
       IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
       if(EntyIsErased(ui->axWidget,ent)) continue;//去除erase的实体
       if(ent->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
       {
           ent->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
           if(ui->axWidget->dynamicCall("IsOk()").toString()!="true") continue;
           ent->dynamicCall("Erase()");
       }
   }
    ui->axWidget->dynamicCall("Regen()");
}

void formaxwidget::SplitLineByTerminal(IMxDrawBlockReference *BlkEnty)
{
    QString HandleLine="";
    //QList<IMxDrawPoint*> ListOnLinePoint;
    //ListOnLinePoint.clear();
    IMxDrawLine *CrossLine;
    IMxDrawPoint* PtTermPos=(IMxDrawPoint *)BlkEnty->querySubObject("Position()");
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("LINE",5020);
    filter->AddStringEx("CONNECT", 8);
    ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtTermPos->asVariant(),filter->asVariant());
    for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
    {
        CrossLine=  (IMxDrawLine *)ss->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        HandleLine=CrossLine->dynamicCall("handle()").toString();
        break;
    }
    if(HandleLine=="") return;
    SetCurLayer(ui->axWidget,"CONNECT");
    IMxDrawPoint *StartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
    IMxDrawPoint *EndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
    ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtTermPos->x(),PtTermPos->y(),StartPoint->x(),StartPoint->y());
    ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",PtTermPos->x(),PtTermPos->y(),EndPoint->x(),EndPoint->y());
    //查看该连线是否有Wire定义（是否相交）
    //创建选择集对象
    IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter2 =new MxDrawResbuf();
    filter2->AddStringEx("INSERT",5020);
    ss2->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, ((IMxDrawPoint *)CrossLine->querySubObject("StartPoint()"))->asVariant(), ((IMxDrawPoint *)CrossLine->querySubObject("EndPoint()"))->asVariant(),filter2->asVariant());
    qDebug()<<"ss2.Count()="<<ss2->Count();
    for (int i = 0; i < ss2->Count(); i++)
    {
        IMxDrawEntity* entCross = (IMxDrawEntity *)ss2->querySubObject("Item(int)",i);
        if(entCross->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
        {
            IMxDrawBlockReference *BlkWire=(IMxDrawBlockReference *)entCross;
            if(BlkWire->dynamicCall("GetBlockName()").toString()=="SPS_CDP")
            {
                //移动Wire定义（端子位置，Wire定义位置，导线端点坐标）
                IMxDrawPoint* PtWirePos=(IMxDrawPoint *)BlkWire->querySubObject("Position()");
                bool IsStartPoint=false;
                if((StartPoint->x()<PtWirePos->x())&&(PtWirePos->x()<PtTermPos->x())) IsStartPoint=true;
                if((StartPoint->y()<PtWirePos->y())&&(PtWirePos->y()<PtTermPos->y())) IsStartPoint=true;
                if(IsStartPoint)
                {
                    PtWirePos->setX((StartPoint->x()+PtTermPos->x())/2);
                    PtWirePos->setY((StartPoint->y()+PtTermPos->y())/2);

                }
                else
                {
                    PtWirePos->setX((EndPoint->x()+PtTermPos->x())/2);
                    PtWirePos->setY((EndPoint->y()+PtTermPos->y())/2);
                }
                BlkWire->dynamicCall("SetPosition(QAxObject*)",PtWirePos->asVariant());
                QSqlQuery QueryWires(T_ProjectDatabase);
                QString StrSql="SELECT * FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle = '"+BlkWire->dynamicCall("handle()").toString()+"'";
                QueryWires.exec(StrSql);
                if(QueryWires.next())
                  AddAttrToWireBlock(BlkWire,0,QueryWires.value("ConnectionNumber").toString(),QueryWires.value("Color").toString(),QueryWires.value("Diameters").toString());

                StrSql= "UPDATE Wires SET Position=:Position WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle = '"+BlkWire->dynamicCall("handle()").toString()+"'";
                QueryWires.prepare(StrSql);
                QString InsertionPoint=QString::number(((IMxDrawPoint *)BlkWire->querySubObject("Position()"))->x(),'f',0)+".000000";
                InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkWire->querySubObject("Position()"))->y(),'f',0)+".000000";
                InsertionPoint+=",0.000000";
                QueryWires.bindValue(":Position",InsertionPoint);
                QueryWires.exec();
            }
        }
    }
    //删除原直线
    ui->axWidget->dynamicCall("Erase(qlonglong)",CrossLine->ObjectID());
    ui->axWidget->dynamicCall("UpdateDisplay()");
}

//查看PtPosition处是否有导线相连，如果有则延长该导线至ConnectorPosition
void formaxwidget::CheckAndUpdateTermLine(IMxDrawPoint *ConnectorPosition,IMxDrawPoint *PtPosition)
{
    if(ConnectorPosition==nullptr) return;
    if(PtPosition==nullptr) return;
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("LINE",5020);
    filter->AddStringEx("CONNECT", 8);
    ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtPosition->asVariant(),filter->asVariant());
    for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawLine * CrossLine=  (IMxDrawLine *)ss->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        IMxDrawPoint *StartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
        IMxDrawPoint *EndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
        if(PointsIsCovered(StartPoint,PtPosition))
            CrossLine->dynamicCall("SetStartPoint(QAxObject*)",ConnectorPosition->asVariant());
        else if(PointsIsCovered(EndPoint,PtPosition))
            CrossLine->dynamicCall("SetEndPoint(QAxObject*)",ConnectorPosition->asVariant());
    }
    ui->axWidget->dynamicCall("UpdateDisplay()");
}

void formaxwidget::DealTerminalBlock(double Posx,double Posy)
{
    DoAddTerminalCommand("Terminal",SymbolIdInDB,true,Posx,Posy);
    return;
    //设置属性块文字
    SetCurLayer(ui->axWidget,"LY_Symb2");
    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Posx,Posy,SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    //将DbId写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(SymbolIdInDB));
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","LD_SYMB2_SPECIAL",0,"端子");


    DrawAutoConnectLine(0,SymbolName.mid(0,SymbolName.size()-4),Posx,Posy,nullptr);
    //WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块

    //在数据库中找到SymbolID对应的符号名称，分为ES2_XXX和SPS_XXX两种
    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SymbolIdInDB));
    QueryTerminal.exec(temp);
    if(!QueryTerminal.next()) return;
    //将FunDefine写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,QueryTerminal.value("FunDefine").toString());
    QString TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toString();

    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+TerminalStrip_ID);
    QueryTerminalStrip.exec(temp);
    if(!QueryTerminalStrip.next()) return;
    QString TerminalTag;
    QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+QString::number(SymbolIdInDB)+"'");
    QueryTerminalTerm.exec(temp);

    while(QueryTerminalTerm.next())
    {
        //找到端点并添加块属性
        FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"端子/插针代号",QueryTerminal.value("Designation").toString());//端子/插针代号
    }
    IsLoadingSymbol=false;
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    //更新Terminal表，包括Page_ID，Handle，Coordinate
    QSqlQuery queryTerminal(T_ProjectDatabase);
    QString tempSQL=QString("UPDATE Terminal SET Page_ID=:Page_ID,Symbol=:Symbol,Handle=:Handle,Coordinate=:Coordinate WHERE Terminal_ID= "+QString::number(SymbolIdInDB));
    queryTerminal.prepare(tempSQL);
    queryTerminal.bindValue(":Page_ID",QString::number(Page_IDInDB));
    queryTerminal.bindValue(":Symbol",SymbolName.mid(0,SymbolName.size()-4));
    queryTerminal.bindValue(":Handle",blkEnty->dynamicCall("handle()").toString());
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
qDebug()<<"blkEnty InsertionPoint="<<InsertionPoint;
    queryTerminal.bindValue(":Coordinate",InsertionPoint);
    queryTerminal.exec();

    //更新TerminalTerm表，包括Conn_Coordinate
    int TermCount=GetTermEnty(ui->axWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
    //int TermCount=GetDwgTermCount(BlkPath);
qDebug()<<"BlkPath="<<BlkPath<<",GetDwgTermCount,TermCount="<<TermCount;
    for(int i=0;i<TermCount;i++)
    {
        tempSQL=QString("UPDATE TerminalTerm SET Conn_Coordinate=:Conn_Coordinate WHERE Terminal_ID= '"+QString::number(SymbolIdInDB)+"' AND ConnNum_Logic='"+QString::number(i+1)+"'");

        QueryTerminalTerm.prepare(tempSQL);

        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkEnty,QString::number(i+1))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkEnty,QString::number(i+1))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
qDebug()<<":Conn_Coordinate="<<InsertionPoint;
        QueryTerminalTerm.bindValue(":Conn_Coordinate",InsertionPoint);
        QueryTerminalTerm.exec();
    }

    QSqlQuery QueryProjectStructure = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryTerminalStrip.value("ProjectStructure_ID").toString());
    QueryProjectStructure.exec(temp);

    //如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
    if(GetProjectStructureIDByPageID(Page_IDInDB)==QueryTerminalStrip.value("ProjectStructure_ID").toString())
      TerminalTag="-"+QueryTerminalStrip.value("DT").toString();
    else
      TerminalTag="+"+QueryProjectStructure.value("Structure_INT").toString()+"-"+QueryTerminalStrip.value("DT").toString();

    //查看附近(同一行或者同一列)的同端子排的端子，如果存在则不显示设备标识符
    if(!CheckTerminalBeside(SymbolIdInDB,ui->axWidget)) FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"设备标识符(显示)",TerminalTag);
    else FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"设备标识符(显示)","");
    ui->axWidget->dynamicCall("UpdateDisplay()");
}

void formaxwidget::DoLoadTerminal()
{
    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    while(ListLoadingDbID.count()>0)
    {
        SymbolIdInDB=ListLoadingDbID.at(0);
        /*
        QString SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SymbolIdInDB);
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next())  SymbolName=QueryTerminal.value("Symbol").toString()+".dwg";
        GetListAllDirSymbols(SymbolName.mid(0,SymbolName.size()-4));
        PickPointCount=0;
        MxDrawUiPrPoint getPt;
        ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
        IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
        IsLoadingSymbol=true;
        getPt.setMessage("请指定位置");
        if (getPt.go() != McUiPrStatus::mcOk) {qDebug()<<"getPt.go()!= McUiPrStatus::mcOk";IsLoadingSymbol=false;return;}
        IMxDrawPoint* frstPt = GetGridPtVal(getPt.value());
        if (frstPt == nullptr) {qDebug()<<"frstPt == nullptr";getPt.setMessage("位置无效");IsLoadingSymbol=false;return; }  // 返回点的点对象值。
        DealTerminalBlock(frstPt->x(),frstPt->y());
        */
        DoAddTerminalCommand("Terminal",SymbolIdInDB,false,0,0);
        ListLoadingDbID.removeAt(0);
    }
    IsLoadingSymbol=false;
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    //更新导航窗口
    emit(UpdateProjectTerminals());
}

bool formaxwidget::DoAddTerminalCommand(QString LayerName,int Terminal_ID,bool SetPos,double Posx,double Posy)
{
qDebug()<<"DoAddTerminalCommand,Terminal_ID="<<Terminal_ID;
    //由用户选择一个点放置
    MxDrawUiPrPoint getPt;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawPoint* TerminalPos;
    if(!SetPos)
    {
        IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
        IsLoadingSymbol=true;
        getPt.setMessage("请指定位置");
        // 等用户在图上点取一个点
        PickPointCount=0;
        if(getPt.go() != McUiPrStatus::mcOk)
        {
            IsLoadingSymbol=false;
            return false;
        }
        TerminalPos = GetGridPtVal(getPt.value());
        if (TerminalPos == nullptr)    // 返回点的点对象值。
        {
            IsLoadingSymbol=false;
            return false;
        }
        TerminalPos->setX(GetGridPosVal(TerminalPos->x()));
        TerminalPos->setY(GetGridPosVal(TerminalPos->y()));
        PickPointCount++;
    }
    else
    {
        MxDrawPoint* pt= new MxDrawPoint();
        TerminalPos=(IMxDrawPoint *)pt;
        TerminalPos->setX(Posx);
        TerminalPos->setY(Posy);
    }

    //设置属性块文字
    SetCurLayer(ui->axWidget,LayerName);
    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",TerminalPos->x(),TerminalPos->y(),SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();

    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(blkEnty==nullptr)
    {
        IsLoadingSymbol=false;
        return false;
    }
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","LD_SYMB2_SPECIAL",0,"端子");
    WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )blkEnty->querySubObject("BlockTableRecord()");
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");

    SelectTerminalStrip_ID=GetUnitStripIDBySymbolID(QString::number(Terminal_ID),1);
    SelectTerminal_ID=Terminal_ID;
    QString AddTerminalTag;
    int AddTerminalDesignation;

    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString tempSQL="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+QString::number(SelectTerminalStrip_ID);
    QueryVar.exec(tempSQL);
    if(QueryVar.next()) AddTerminalTag=QueryVar.value("DT").toString();
    else return false;
    tempSQL="SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SelectTerminal_ID);
    QueryVar.exec(tempSQL);
    if(QueryVar.next()) AddTerminalDesignation=QueryVar.value("Designation").toInt();
    else return false;
    /*
    //更新Terminal表，包括Page_ID，Handle，Coordinate
    QSqlQuery queryTerminal(T_ProjectDatabase);
    tempSQL=QString("UPDATE Terminal SET Page_ID=:Page_ID,Handle=:Handle,Coordinate=:Coordinate,LeftTerm=:LeftTerm,RightTerm=:RightTerm WHERE Terminal_ID= "+QString::number(SelectTerminal_ID));
    queryTerminal.prepare(tempSQL);
    queryTerminal.bindValue(":Page_ID",QString::number(Page_IDInDB));
    //queryTerminal.bindValue(":Symbol",SymbolName.mid(0,SymbolName.size()-4));
    queryTerminal.bindValue(":Handle",blkEnty->dynamicCall("handle()").toString());
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    queryTerminal.bindValue(":Coordinate",InsertionPoint);
    queryTerminal.bindValue(":LeftTerm","1");
    queryTerminal.bindValue(":RightTerm","2");
    queryTerminal.exec();
    */
    //更新TerminalInstance表，包括Page_ID，Handle，Coordinate
    QSqlQuery queryTerminalInstance(T_ProjectDatabase);
    QString SqlStr =  "INSERT INTO TerminalInstance (TerminalInstanceID,Terminal_ID,Designation,TerminalStrip_ID,Page_ID,Symbol,Handle,Coordinate,LeftTerm,RightTerm)"
                            "VALUES (:TerminalInstanceID,:Terminal_ID,:Designation,:TerminalStrip_ID,:Page_ID,:Symbol,:Handle,:Coordinate,:LeftTerm,:RightTerm)";
  qDebug()<<"SqlStr="<<SqlStr;
    queryTerminalInstance.prepare(SqlStr);
    queryTerminalInstance.bindValue(":TerminalInstanceID",QString::number(GetMaxIDOfDB(T_ProjectDatabase,"TerminalInstance","TerminalInstanceID")));
    queryTerminalInstance.bindValue(":Terminal_ID",QString::number(Terminal_ID));
    queryTerminalInstance.bindValue(":Designation",QString::number(AddTerminalDesignation));
    queryTerminalInstance.bindValue(":TerminalStrip_ID",QString::number(SelectTerminalStrip_ID));
    queryTerminalInstance.bindValue(":Page_ID",QString::number(Page_IDInDB));
    queryTerminalInstance.bindValue(":Symbol",SymbolName.mid(0,SymbolName.size()-4));
    queryTerminalInstance.bindValue(":Handle",blkEnty->dynamicCall("handle()").toString());
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    queryTerminalInstance.bindValue(":Coordinate",InsertionPoint);
    queryTerminalInstance.bindValue(":LeftTerm","1");
    queryTerminalInstance.bindValue(":RightTerm","2");
    queryTerminalInstance.exec();

    //更新块属性
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(ui->axWidget,ent)) continue;//去除erase的实体
        if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
        {
            IMxDrawAttributeDefinition *attrib=(IMxDrawAttributeDefinition *)ent;
            //qDebug()<<"find McDbAttributeDefinition="<<attrib->dynamicCall("Tag()").toString();
            if(attrib->dynamicCall("Tag()").toString()=="设备标识符(显示)")
                AddAttrToBlock(ui->axWidget,blkEnty,attrib,AddTerminalTag);
            if(attrib->dynamicCall("Tag()").toString()=="端子/插针代号")
                AddAttrToBlock(ui->axWidget,blkEnty,attrib,QString::number(AddTerminalDesignation));
            if(SymbolName.mid(0,SymbolName.size()-4)=="ES2_S_TERM_2P")
            {
                //默认连接点是1和2，可通过按shift切换成2和1 1和1 2和2
                if(attrib->dynamicCall("Tag()").toString()=="左连接点")
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,"1");
                if(attrib->dynamicCall("Tag()").toString()=="右连接点")
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,"2");
            }
            else if(SymbolName.mid(0,SymbolName.size()-4)=="ES2_S_TERM_4P")
            {
                //默认连接点是1和2，可通过按shift切换成2和1 1和1 2和2
                if(attrib->dynamicCall("Tag()").toString()=="左连接点")
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,"1");
                if(attrib->dynamicCall("Tag()").toString()=="右连接点")
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,"2");
                if(attrib->dynamicCall("Tag()").toString()=="上连接点")
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,"");
                if(attrib->dynamicCall("Tag()").toString()=="下连接点")
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,"");
            }
        }
    }
    IsLoadingSymbol=false;
    SetCurLayerVisible(ui->axWidget,"LY_Attdef",true);
    SetCurLayer(ui->axWidget,"0");

qDebug()<<"分割导线,查看插入点是否有连线";
    //分割导线,查看插入点是否有连线
    IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter2=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter2->AddStringEx("LINE",5020);
    filter2->AddStringEx("CONNECT", 8);
    ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",TerminalPos->asVariant(),filter2->asVariant());
    for(int j=0;j<ss2->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawLine * CrossLine=  (IMxDrawLine *)ss2->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        //如果是从中间分隔导线，则导线代号根据插入点的位置自动分配
        SplitLineByTerminal(blkEnty);
    }
    /*
qDebug()<<"如果插入端子与Connector节点重合，则将Connector节点删除并延长Connector各端点的导线";
    //如果插入端子与Connector节点重合，则将Connector节点删除并延长Connector各端点的导线
    IMxDrawSelectionSet *ss4= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter4=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter4->AddStringEx("INSERT",5020);
    filter4->AddStringEx("CONNECT", 8);
    ss4->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",TerminalPos->asVariant(),filter4->asVariant());
    for(int j=0;j<ss4->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawBlockReference * EntyConnector=  (IMxDrawBlockReference *)ss4->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)EntyConnector)) continue;//去除erase的实体
        IMxDrawPoint *ConnectorPosition=(IMxDrawPoint *)EntyConnector->querySubObject("Position()");
        QSqlQuery QueryConnector = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM Connector WHERE Connector_Handle = '"+EntyConnector->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
        QueryConnector.exec(SqlStr);
        if(QueryConnector.next())
        {
qDebug()<<"Find Connector";
            MxDrawPoint* ptConnector= new MxDrawPoint();
            IMxDrawPoint *ptxConnector=(IMxDrawPoint *)ptConnector;
            if(QueryConnector.value("C_Coordinate").toString()!="")
            {
qDebug()<<"C_Coordinate!=空";
               //查看该处是否有导线，如果有则延长该导线
               ptxConnector->setX(QueryConnector.value("C_Coordinate").toString().split(",").at(0).toDouble());
               ptxConnector->setY(QueryConnector.value("C_Coordinate").toString().split(",").at(1).toDouble());
               CheckAndUpdateTermLine(ConnectorPosition,ptxConnector);
            }
            if(QueryConnector.value("G_Coordinate").toString()!="")
            {
qDebug()<<"G_Coordinate!=空";
               //查看该处是否有导线，如果有则延长该导线
               ptxConnector->setX(QueryConnector.value("G_Coordinate").toString().split(",").at(0).toDouble());
               ptxConnector->setY(QueryConnector.value("G_Coordinate").toString().split(",").at(1).toDouble());
               CheckAndUpdateTermLine(ConnectorPosition,ptxConnector);
            }
            if(QueryConnector.value("Coordinate_1").toString()!="")
            {
qDebug()<<"Coordinate_1!=空";
               //查看该处是否有导线，如果有则延长该导线
               ptxConnector->setX(QueryConnector.value("Coordinate_1").toString().split(",").at(0).toDouble());
               ptxConnector->setY(QueryConnector.value("Coordinate_1").toString().split(",").at(1).toDouble());
               CheckAndUpdateTermLine(ConnectorPosition,ptxConnector);
            }
            if(QueryConnector.value("Coordinate_2").toString()!="")
            {
qDebug()<<"Coordinate_2!=空";
               //查看该处是否有导线，如果有则延长该导线
               ptxConnector->setX(QueryConnector.value("Coordinate_2").toString().split(",").at(0).toDouble());
               ptxConnector->setY(QueryConnector.value("Coordinate_2").toString().split(",").at(1).toDouble());
               CheckAndUpdateTermLine(ConnectorPosition,ptxConnector);
            }
            if(QueryConnector.value("Coordinate_3").toString()!="")
            {
qDebug()<<"Coordinate_3!=空";
               //查看该处是否有导线，如果有则延长该导线
               ptxConnector->setX(QueryConnector.value("Coordinate_3").toString().split(",").at(0).toDouble());
               ptxConnector->setY(QueryConnector.value("Coordinate_3").toString().split(",").at(1).toDouble());
               CheckAndUpdateTermLine(ConnectorPosition,ptxConnector);
            }
        }
        EntyConnector->dynamicCall("Erase()");
    }*/
    /*
qDebug()<<"查看与插入端子直连的端子，如果是同一个端子排，则默认是短接的";
    //查看与插入端子直连的端子，如果是同一个端子排，则默认是短接的
    IMxDrawSelectionSet *ss3= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter3=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter3->AddStringEx("LINE",5020);
    filter3->AddStringEx("CONNECT", 8);
    ss3->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",TerminalPos->asVariant(),filter3->asVariant());
qDebug()<<"ss3->dynamicCall(Count()).toInt()="<<ss3->dynamicCall("Count()").toInt();
    for(int j=0;j<ss3->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawLine * CrossLine=  (IMxDrawLine *)ss3->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        IMxDrawPoint *StartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
        IMxDrawPoint *EndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
        IMxDrawPoint *AnthorPoint;
        if(PointsIsCovered(StartPoint,TerminalPos)) AnthorPoint=EndPoint;
        if(PointsIsCovered(EndPoint,TerminalPos)) AnthorPoint=StartPoint;
qDebug()<<"get AnthorPoint";
        if(AnthorPoint==nullptr) continue;
        IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        filter->AddStringEx("INSERT",5020);
        filter->AddStringEx("Terminal", 8);
        ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",AnthorPoint->asVariant(),filter->asVariant());
qDebug()<<"ss->dynamicCall(Count()).toInt()="<<ss->dynamicCall("Count()").toInt();
        IMxDrawBlockReference * AnotherTerm;
        bool FindAnotherTerm=false;
        for(int k=0;k<ss->dynamicCall("Count()").toInt();k++)
        {
            AnotherTerm=  (IMxDrawBlockReference *)ss->querySubObject("Item(int)",k);
            if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)AnotherTerm)) continue;//去除erase的实体
            FindAnotherTerm=true;
        }
        if(!FindAnotherTerm) continue;
        //如果SelectTerminal_ID的ShortJumper为空，则查看AnotherTerm与blkEnty是否是同一个端子排
        QString tempSQL="SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SelectTerminal_ID);
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QueryVar.exec(tempSQL);
        if(QueryVar.next())
        {
           if(QueryVar.value("ShortJumper").toString()=="")
           {
               tempSQL="SELECT * FROM Terminal WHERE Handle = '"+AnotherTerm->dynamicCall("handle()").toString()+"' AND TerminalStrip_ID = '"+QString::number(SelectTerminalStrip_ID)+"'";
               QueryVar.exec(tempSQL);
               if(QueryVar.next())
               {
                   CrossLine->dynamicCall("setColorIndex(int)",McColor::mcBlue);
                   QString AnotherTerminal_ID=QueryVar.value("Terminal_ID").toString();
                   //更新端子短接数据库
                   if(QueryVar.value("ShortJumper").toString()!="")
                   {
                       QString ShortJumper=QueryVar.value("ShortJumper").toString();
                       QString StrSql="UPDATE Terminal SET ShortJumper=:ShortJumper WHERE Terminal_ID = "+QString::number(SelectTerminal_ID);
                       QueryVar.prepare(StrSql);
                       QueryVar.bindValue(":ShortJumper",ShortJumper);
                       QueryVar.exec();
                   }
                   else
                   {
                       int CurSearchTagIndex=1;
                       QString CurSearchTag;
                       while(1)
                       {
                           for(int i=0;i<CurSearchTagIndex;i++) CurSearchTag+="*";
                           QString StrSql="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QString::number(SelectTerminalStrip_ID)+"' AND ShortJumper = '"+CurSearchTag+"'";
                           QueryVar.exec(StrSql);
                           if(!QueryVar.next()) break;
                       }
                       QString StrSql="UPDATE Terminal SET ShortJumper=:ShortJumper WHERE Terminal_ID = "+QString::number(SelectTerminal_ID);
                       QueryVar.prepare(StrSql);
                       QueryVar.bindValue(":ShortJumper",CurSearchTag);
                       QueryVar.exec();
                       StrSql="UPDATE Terminal SET ShortJumper=:ShortJumper WHERE Terminal_ID = "+AnotherTerminal_ID;
                       QueryVar.prepare(StrSql);
                       QueryVar.bindValue(":ShortJumper",CurSearchTag);
                       QueryVar.exec();
                   }
                   //新插入的端子默认不显示端子排代号
                   UpdateBlockAttr(blkEnty,"设备标识符(显示)","");
               }
           }//if(QueryVar.value("ShortJumper").toString()=="")
           else
           {
               tempSQL="SELECT * FROM Terminal WHERE Handle = '"+AnotherTerm->dynamicCall("handle()").toString()+"' AND TerminalStrip_ID = '"+QString::number(SelectTerminalStrip_ID)+"' AND ShortJumper = '"+QueryVar.value("ShortJumper").toString()+"'";
               qDebug()<<"tempSQL="<<tempSQL;
               QueryVar.exec(tempSQL);
               if(QueryVar.next())
               {
                   CrossLine->dynamicCall("setColorIndex(int)",McColor::mcBlue);
                   UpdateBlockAttr(blkEnty,"设备标识符(显示)","");
               }
           }
        }
    }*/
qDebug()<<"end UpdateProjectTerminals";
    emit(UpdateProjectTerminals());
    return true;
}

void formaxwidget::UpdateTermLineShortage(QString TerminalHandle,QStringList ShortageLines)
{
    IMxDrawBlockReference *TermEnty=(IMxDrawBlockReference *)ui->axWidget->querySubObject("HandleToObject(const QString)",TerminalHandle);
    IMxDrawPoint *PtTerminal=(IMxDrawPoint *)TermEnty->querySubObject("Position()");
    IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter2=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter2->AddStringEx("LINE",5020);
    filter2->AddStringEx("CONNECT", 8);
    ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtTerminal->asVariant(),filter2->asVariant());
    for(int j=0;j<ss2->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawLine * CrossLine=  (IMxDrawLine *)ss2->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        IMxDrawPoint *StartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
        IMxDrawPoint *EndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
        IMxDrawPoint *AnthorPoint;
        if((fabs(StartPoint->x()-PtTerminal->x())>0.1)||(fabs(StartPoint->y()-PtTerminal->y())>0.1))
             AnthorPoint=StartPoint;
        if((fabs(EndPoint->x()-PtTerminal->x())>0.1)||(fabs(EndPoint->y()-PtTerminal->y())>0.1))
             AnthorPoint=EndPoint;
        if(AnthorPoint==nullptr) continue;
        IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        filter->AddStringEx("INSERT",5020);
        filter->AddStringEx("Terminal", 8);
        ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",AnthorPoint->asVariant(),filter->asVariant());
        IMxDrawBlockReference * AnotherTerm;
        for(int k=0;k<ss->dynamicCall("Count()").toInt();k++)
        {
            AnotherTerm=  (IMxDrawBlockReference *)ss->querySubObject("Item(int)",k);
            if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)AnotherTerm)) continue;//去除erase的实体
        }
        if(AnotherTerm==nullptr) continue;
        if(!ShortageLines.contains(AnotherTerm->dynamicCall("handle()").toString()))
        {
            CrossLine->dynamicCall("setColorIndex(int)",McColor::mcGreen);
        }
        else
        {
            CrossLine->dynamicCall("setColorIndex(int)",McColor::mcBlue);
        }
    }
}

void formaxwidget::DoMultiLibSymbolLoad()
{
    MxDrawUiPrPoint getPt;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    SetCurLayer(ui->axWidget,"LY_Symb2");
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
    IsLoadingSymbol=true;
    while(1)
    {
        // 等用户在图上点取一个点
        PickPointCount=0;
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            IsLoadingSymbol=false;
            break;
        }
        Pt1 = GetGridPtVal(getPt.value());
        if (Pt1 == nullptr) break;   // 返回点的点对象值。
        Pt1->setX(GetGridPosVal(Pt1->x()));
        Pt1->setY(GetGridPosVal(Pt1->y()));
        PickPointCount++;

        //设置属性块文字
        lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt1->x(),Pt1->y(),SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();

        IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
        if(blkEnty==nullptr) break;
        IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )blkEnty->querySubObject("BlockTableRecord()");
        IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
        //更新块属性
        for (; !iter->Done(); iter->Step(true, false))
        {
            // 得到遍历器当前的实体
            IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
            if(EntyIsErased(ui->axWidget,ent)) continue;//去除erase的实体
            if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
            {
                IMxDrawAttributeDefinition *attrib=(IMxDrawAttributeDefinition *)ent;
                if(StrIsNumber(attrib->dynamicCall("Tag()").toString()))
                {
                    AddAttrToBlock(ui->axWidget,blkEnty,attrib,attrib->dynamicCall("Tag()").toString());
                }
            }
        }
    }
    IsLoadingSymbol=false;
    SetCurLayer(ui->axWidget,"0");
}

bool formaxwidget::DoLoadSymbolCommand(QString LayerName)
{
    //由用户选择一个点放置

    MxDrawUiPrPoint getPt;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);

    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
    IsLoadingSymbol=true;
    while(1)
    {
 qDebug()<<"请指定位置";
        getPt.setMessage("请指定位置,按Shift键取消自动连线");
        // 等用户在图上点取一个点
        PickPointCount=0;
        if (getPt.go() != McUiPrStatus::mcOk)
        {
            IsLoadingSymbol=false;
            return false;
        }
        Pt1 = GetGridPtVal(getPt.value());
        if (Pt1 == nullptr) {IsLoadingSymbol=false;return false;}   // 返回点的点对象值。
        Pt1->setX(GetGridPosVal(Pt1->x()));
        Pt1->setY(GetGridPosVal(Pt1->y()));
        PickPointCount++;

        //设置属性块文字
        SetCurLayer(ui->axWidget,LayerName);
 qDebug()<<"SetCurLayer";
        lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Pt1->x(),Pt1->y(),SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();

        IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
        if(blkEnty==nullptr) break;      
        if(IsDoingSymbolEdit) {EraseTerms(blkEnty); continue;}
        CutLine(blkEnty);//用端点截断导线
        if(!SymbolName.contains("SYMB2_M_PWF_"))
        {
            //查看符号是否在黑盒范围内，如果是的话则不显示设备标识符，如果在不是本元件的黑盒内则不支持放置
            //查看Symbol是否在黑盒内部，如果不是的话返回0，如果是并且黑盒和Symbol是同元件则返回EquipmentID，如果是并且黑盒和Symbol是不同元件则返回-1
            WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块
            int  BlackBoxVal=CheckBlackBox(ui->axWidget,Pt1->x(),Pt1->y(),0);
    qDebug()<<"CheckBlackBox="<<BlackBoxVal;
            IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )blkEnty->querySubObject("BlockTableRecord()");
            IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
            // 循环得到所有实体
            QString DT;
            IMxDrawResbuf *resp=(IMxDrawResbuf *)blkEnty->querySubObject("GetXData(QString)","LD_SYMB1LIB_XRECORD");
            if(resp!=nullptr)
            {
                for(int j=0;j<resp->Count();j++)
                {
                    if(resp->AtString(j)=="推荐标号") DT=resp->AtString(j+1);
                }
            }
            int DTIndex=1;
            //这里需要区分是否为端子或插针，如果是添加端子，则不标记实际端号，只标记序号Designation，则添加拓展数据LD_SYMB2_SPECIAL为端子，在插入后弹出编辑窗口设置端子的端子排代号和序号
            //如果是添加插针，则不标记实际端号，只标记序号Designation，添加拓展数据LD_SYMB2_SPECIAL为插针，在插入后弹出编辑窗口设置插针的元件代号和序号
            QString SymbolDesc= GetSymbolDescBySymb2Lib_ID(Symb2Lib_ID);
            /*
            if(SymbolDesc=="端子")
            {
                blkEnty->dynamicCall("SetxDataString(QString,int,QString)","LD_SYMB2_SPECIAL",0,"端子");
                //在数据库中检索DT的后缀数字
                QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                while(1)
                {
                   QString SqlStr="SELECT * FROM TerminalStrip WHERE DT = '"+DT+QString::number(DTIndex)+"'";
                   QuerySearch.exec(SqlStr);
                   if(!QuerySearch.next()) break;
                   DTIndex++;
                }
            }
            else*/
            {
                if(SymbolDesc=="插针") blkEnty->dynamicCall("SetxDataString(QString,int,QString)","LD_SYMB2_SPECIAL",0,"插针");
                //在数据库中检索DT的后缀数字
                QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                while(1)
                {
                   QString SqlStr="SELECT * FROM Equipment WHERE DT = '"+DT+QString::number(DTIndex)+"'";
                   QuerySearch.exec(SqlStr);
                   if(!QuerySearch.next()) break;
                   DTIndex++;
                }
            }
            DT=DT+QString::number(DTIndex);
            QString Designation="";
            if(SymbolDesc=="插针") Designation="1";
            int MaxUnit_ID;
            bool FindSimilarBeside=false;
            //if(SymbolDesc!="端子")
            {
                if(BlackBoxVal==0)//Symbol不在黑盒内部
                {
                    //如果是插针，则查看附近又有同行或者同列的插针，如果有则合并，序号加1
                    if(SymbolDesc=="插针")
                    {
                        QString SymbolNow=blkEnty->dynamicCall("GetBlockName()").toString();
                        QString SymbolNowNum=SymbolNow.mid(SymbolNow.lastIndexOf("-")+1,SymbolNow.count()-SymbolNow.lastIndexOf("-")-1);
                        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString StrPosx=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
                        QString StrPosy=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
                        QString SqlStr = "SELECT * FROM Symbol WHERE Symbol_Category = '插针' AND Page_ID = '"+QString::number(Page_IDInDB)+"' AND (Coordinate LIKE '"+StrPosx+",%' OR Coordinate LIKE '%,"+StrPosy+",%')";
                        QuerySearch.exec(SqlStr);
                        bool FlagFirstIn=true;
                        double minDeltaVal;
                        while(QuerySearch.next())
                        {
                            if(QuerySearch.value("Symbol_Handle").toString()=="") continue;
                            QString SymbolSearch=QuerySearch.value("Symbol").toString();
                            QString SymbolSearchNum=SymbolSearch.mid(SymbolSearch.lastIndexOf("-")+1,SymbolSearch.count()-SymbolSearch.lastIndexOf("-")-1);
                            if(!StrIsNumber(SymbolSearchNum)) continue;
                            if((SymbolNowNum.toInt()%2)!=(SymbolSearchNum.toInt()%2)) continue;
                            QString CoordinateSearch=QuerySearch.value("InsertionPoint").toString();
                            if(CoordinateSearch.split(",").count()!=3) continue;
                            if(CoordinateSearch.split(",").at(0)==StrPosx)
                            {
                                if(FlagFirstIn) minDeltaVal=fabs(CoordinateSearch.split(",").at(1).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y());
                                else
                                {
                                    if(minDeltaVal<fabs(CoordinateSearch.split(",").at(1).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y())) continue;
                                }
                                FlagFirstIn=false;
                                FindSimilarBeside=true;
                            }
                            if(CoordinateSearch.split(",").at(1)==StrPosy)
                            {
                                if(FlagFirstIn) minDeltaVal=fabs(CoordinateSearch.split(",").at(0).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x());
                                else
                                {
                                    if(minDeltaVal<fabs(CoordinateSearch.split(",").at(0).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x())) continue;
                                }
                                FlagFirstIn=false;
                                FindSimilarBeside=true;
                            }
                            if(FindSimilarBeside)
                            {
                                MaxUnit_ID=QuerySearch.value("Equipment_ID").toInt();
                                QSqlQuery QuerySearchEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(MaxUnit_ID);
                                QuerySearchEquipment.exec(SqlStr);
                                if(QuerySearchEquipment.next()) DT=QuerySearchEquipment.value("DT").toString();

                                //找到元件中Designation最大的
                                QSqlQuery QuerySearchDesignation = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QuerySearch.value("Equipment_ID").toString()+"'";
                                QuerySearchDesignation.exec(SqlStr);
                                int MaxLastNum=1;
                                while(QuerySearchDesignation.next())
                                {
                                    if(GetStrLastNum(QuerySearchDesignation.value("Designation").toString())>=MaxLastNum)
                                        MaxLastNum=GetStrLastNum(QuerySearchDesignation.value("Designation").toString())+1;
                                }
                                Designation=QString::number(MaxLastNum);
                                break;
                            }
                        }
                    }
                    if(!FindSimilarBeside)
                    {
                        MaxUnit_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
                        //更新T_ProjectDatabase数据库的Equipment表
                        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString tempSQL = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Eqpt_Category)"
                                          "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Eqpt_Category)");
                        QueryVar.prepare(tempSQL);
                        QueryVar.bindValue(":Equipment_ID",MaxUnit_ID);
                        QueryVar.bindValue(":DT",DT);
                        QueryVar.bindValue(":ProjectStructure_ID",GetProjectStructureIDByPageID(Page_IDInDB));
                        QueryVar.bindValue(":Eqpt_Category","普通元件");//普通元件还是PLC元件
                        QueryVar.exec();
                    }
                    SelectEquipment_ID=MaxUnit_ID;
                    SelectSymbol_ID=0;
                }
                else MaxUnit_ID=BlackBoxVal;//Symbol在黑盒内部
            }
            /*
            else
            {
                //查看附近又有同行或者同列的插针，如果有则合并，序号加1
                QString TerminalNow=blkEnty->dynamicCall("GetBlockName()").toString();
                QString TerminalNowNum=TerminalNow.mid(TerminalNow.lastIndexOf("-")+1,TerminalNow.count()-TerminalNow.lastIndexOf("-")-1);
                QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                QString StrPosx=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
                QString StrPosy=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
                QString SqlStr = "SELECT * FROM Terminal WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND (Coordinate LIKE '"+StrPosx+",%' OR Coordinate LIKE '%,"+StrPosy+",%')";
                QuerySearch.exec(SqlStr);
                double minDeltaVal;
                bool FlagFirstIn=true;
                while(QuerySearch.next())
                {
                    if(QuerySearch.value("Handle").toString()=="") continue;
                    QString SymbolSearch=QuerySearch.value("Symbol").toString();
                    QString SymbolSearchNum=SymbolSearch.mid(SymbolSearch.lastIndexOf("-")+1,SymbolSearch.count()-SymbolSearch.lastIndexOf("-")-1);
                    if(!StrIsNumber(SymbolSearchNum)) continue;
                    if((TerminalNowNum.toInt()%2)!=(SymbolSearchNum.toInt()%2)) continue;
                    QString CoordinateSearch=QuerySearch.value("Coordinate").toString();
                    if(CoordinateSearch.split(",").count()!=3) continue;
                    if(CoordinateSearch.split(",").at(0)==StrPosx)
                    {
                        if(FlagFirstIn) minDeltaVal=fabs(CoordinateSearch.split(",").at(1).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y());
                        else
                        {
                            if(minDeltaVal<fabs(CoordinateSearch.split(",").at(1).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y())) continue;
                        }
                        FlagFirstIn=false;
                        FindSimilarBeside=true;
                    }
                    if(CoordinateSearch.split(",").at(1)==StrPosy)
                    {
                        if(FlagFirstIn) minDeltaVal=fabs(CoordinateSearch.split(",").at(0).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x());
                        else
                        {
                            if(minDeltaVal<fabs(CoordinateSearch.split(",").at(0).toDouble()-((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x())) continue;
                        }
                        FlagFirstIn=false;
                        FindSimilarBeside=true;
                    }
                    if(FindSimilarBeside)
                    {
                        MaxUnit_ID=QuerySearch.value("TerminalStrip_ID").toInt();
                        QSqlQuery QuerySearchTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr = "SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+QString::number(MaxUnit_ID);
                        QuerySearchTerminalStrip.exec(SqlStr);
                        if(QuerySearchTerminalStrip.next()) DT=QuerySearchTerminalStrip.value("DT").toString();

                        //找到元件中Designation最大的
                        QSqlQuery QuerySearchDesignation = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QuerySearch.value("TerminalStrip_ID").toString()+"'";
                        QuerySearchDesignation.exec(SqlStr);
                        int MaxLastNum=1;
                        while(QuerySearchDesignation.next())
                        {
                            if(GetStrLastNum(QuerySearchDesignation.value("Designation").toString())>=MaxLastNum)
                                MaxLastNum=GetStrLastNum(QuerySearchDesignation.value("Designation").toString())+1;
                        }
                        Designation=QString::number(MaxLastNum);
                        break;
                    }
                }
                if(!FindSimilarBeside)
                {
                    MaxUnit_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalStrip","TerminalStrip_ID");
                    //更新T_ProjectDatabase数据库的TerminalStrip表
                    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    QString tempSQL = QString("INSERT INTO TerminalStrip (TerminalStrip_ID,DT,ProjectStructure_ID)"
                                      "VALUES (:TerminalStrip_ID,:DT,:ProjectStructure_ID)");
                    QueryVar.prepare(tempSQL);
                    QueryVar.bindValue(":TerminalStrip_ID",MaxUnit_ID);
                    QueryVar.bindValue(":DT",DT);
                    QueryVar.bindValue(":ProjectStructure_ID",GetProjectStructureIDByPageID(Page_IDInDB));
                    QueryVar.exec();
                }
                SelectTerminalStrip_ID=MaxUnit_ID;
                SelectTerminal_ID=0;
            }*/

            //更新块属性
            for (; !iter->Done(); iter->Step(true, false))
            {
                // 得到遍历器当前的实体
                IMxDrawEntity* ent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
                if(EntyIsErased(ui->axWidget,ent)) continue;//去除erase的实体
                if(ent->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
                {
                    IMxDrawAttributeDefinition *attrib=(IMxDrawAttributeDefinition *)ent;
    //qDebug()<<"find McDbAttributeDefinition="<<attrib->dynamicCall("Tag()").toString();
                    if(attrib->dynamicCall("Tag()").toString()=="设备标识符(显示)")
                    {
                        if((BlackBoxVal==0)&&(!FindSimilarBeside)) AddAttrToBlock(ui->axWidget,blkEnty,attrib,"-"+DT);
                        else AddAttrToBlock(ui->axWidget,blkEnty,attrib,"");
                    }

                    if((SymbolDesc=="端子")||(SymbolDesc=="插针"))
                    {
                       if(attrib->dynamicCall("Tag()").toString()=="端子/插针代号") AddAttrToBlock(ui->axWidget,blkEnty,attrib,Designation);
                    }
                    else
                    {
                        if(StrIsNumber(attrib->dynamicCall("Tag()").toString())&&(SymbolDesc!="元件连接点")) AddAttrToBlock(ui->axWidget,blkEnty,attrib,attrib->dynamicCall("Tag()").toString());
                        else if(attrib->dynamicCall("Tag()").toString()=="连接点代号（带显示设备标识符）") AddAttrToBlock(ui->axWidget,blkEnty,attrib,DT+":1");
                        else if(attrib->dynamicCall("Tag()").toString()=="连接点代号（全部）") AddAttrToBlock(ui->axWidget,blkEnty,attrib,"1");
                        else AddAttrToBlock(ui->axWidget,blkEnty,attrib,"");
                    }
                }
            }

            //更新T_ProjectDatabase数据库的Symbol表和Symb2TermInfo表
            int SymbId;
            //if(SymbolDesc=="端子") SymbId=UpdateTerminalInfoBySymb2Lib_ID(Symb2Lib_ID,ui->axWidget,blkEnty,QString::number(Page_IDInDB),QString::number(MaxUnit_ID),Designation);
            //else
            SymbId=UpdateSymbolInfoBySymb2Lib_ID(Symb2Lib_ID,ui->axWidget,blkEnty,QString::number(Page_IDInDB),QString::number(MaxUnit_ID),Designation);
            //如果为端子或插针，弹出属性窗
            //if(SymbolDesc=="端子")  emit(SigalShowTerminalAttr(SymbId));
            //else
            if(SymbolDesc=="插针")  emit(SigalShowSpurAttr(SymbId));
            SelectSymbol_ID=SymbId;
            //if(SymbolDesc=="端子") emit(UpdateProjectTerminals());
            //else
            emit(UpdateProjectUnits());
        }//end of if(!SymbolName.contains("SYMB2_M_PWF_"))
        DrawAutoConnectLine(0,SymbolName.mid(0,SymbolName.size()-4),Pt1->x(),Pt1->y(),nullptr);
        if(LayerName=="CONNECT") break;
    }

    IsLoadingSymbol=false;
    SetCurLayerVisible(ui->axWidget,"LY_Attdef",true);
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    return true;
    //ui->axWidget->dynamicCall("Regen()");
}
void formaxwidget::UpdateLinkBlk(IMxDrawBlockReference *blkNode,int Link_ID,QString RetStrLinkTag,QString RetStrLinkTextPosition)
{
    //查看是否有关联的链接点
    QSqlQuery QueryCounterLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Link WHERE Link_Label = '"+RetStrLinkTag+"' AND Link_ID <> "+QString::number(Link_ID);
    QueryCounterLink.exec(SqlStr);
    bool CounterLinkExist=false;
    int CounterLinkID=0;
    if(QueryCounterLink.next())//存在关联的链接点
    {
       CounterLinkExist=true;
       QString LinkText=GetPageNameByPageID(QueryCounterLink.value("Page_ID").toInt());
       //if(QueryCounterLink.value("Link_PageArea").toString()!="") LinkText+="."+QueryCounterLink.value("Link_PageArea").toString();
       LoadLinkText(ui->axWidget,blkNode,RetStrLinkTag,LinkText,RetStrLinkTextPosition,blkNode->dynamicCall("GetBlockName()").toString());

       //更新被关联的链接点数据库及其图形,注意关联链接点可能不在当前图纸
       CounterLinkID=QueryCounterLink.value("Link_ID").toInt();
       SqlStr ="UPDATE Link SET CounterLink_ID=:CounterLink_ID WHERE Link_ID = "+QString::number(CounterLinkID);
       QueryCounterLink.prepare(SqlStr);
       QueryCounterLink.bindValue(":CounterLink_ID",QString::number(Link_ID));
       QueryCounterLink.exec();

       LinkText=GetPageNameByPageID(Page_IDInDB);
qDebug()<<"存在关联的链接点,CounterLinkID="<<CounterLinkID<<", LinkText="<<LinkText;
       emit(UpdateCounterLink(CounterLinkID,LinkText));
    }
    else//不存在关联的链接点
    {
        LoadLinkText(ui->axWidget,blkNode,RetStrLinkTag,"",RetStrLinkTextPosition,blkNode->dynamicCall("GetBlockName()").toString());
        //修改原数据库关联的链接点
        QSqlQuery QueryLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM Link WHERE Link_ID = "+QString::number(Link_ID);
        QueryLink.exec(SqlStr);
        if(QueryLink.next())
        {
            if(QueryLink.value("CounterLink_ID").toString()!="")
            {
                emit(UpdateCounterLink(QueryLink.value("CounterLink_ID").toInt(),""));
                SqlStr ="UPDATE Link SET CounterLink_ID=:CounterLink_ID WHERE Link_ID = "+QueryLink.value("CounterLink_ID").toString();
                QueryCounterLink.prepare(SqlStr);
                QueryCounterLink.bindValue(":CounterLink_ID","");
                QueryCounterLink.exec();
            }
        }
    }
    //更新数据库
    QSqlQuery QueryLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr ="UPDATE Link SET Link_Name=:Link_Name,Link_Handle=:Link_Handle,InsertionPoint=:InsertionPoint,Coordinate_1=:Coordinate_1,C_Coordinate=:C_Coordinate,CounterLink_ID=:CounterLink_ID"
                                    " WHERE Link_ID = "+QString::number(Link_ID);
    QueryLink.prepare(SqlStr);
    QueryLink.bindValue(":Link_Name",SymbolName.mid(0,SymbolName.count()-4));
    QueryLink.bindValue(":Link_Handle",blkNode->dynamicCall("handle()").toString());

    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkNode->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkNode->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryLink.bindValue(":InsertionPoint",InsertionPoint);

    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"1")->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"1")->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryLink.bindValue(":Coordinate_1",InsertionPoint);

    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"C")->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"C")->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryLink.bindValue(":C_Coordinate",InsertionPoint);

    if(CounterLinkExist) QueryLink.bindValue(":CounterLink_ID",QString::number(CounterLinkID));
    else QueryLink.bindValue(":CounterLink_ID","");
    QueryLink.exec();
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
}
void formaxwidget::InsertNodeRecordToDB(IMxDrawBlockReference *blkNode)
{
    QString blkName=blkNode->dynamicCall("GetBlockName()").toString();
    //更新数据库
    QSqlQuery QueryConnector = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = QString("INSERT INTO Connector (Connector_ID,Page_ID,Connector_Name,Connector_Handle,InsertionPoint,C_Coordinate,G_Coordinate,Coordinate_1,Coordinate_2,Coordinate_3)"
                      "VALUES (:Connector_ID,:Page_ID,:Connector_Name,:Connector_Handle,:InsertionPoint,:C_Coordinate,:G_Coordinate,:Coordinate_1,:Coordinate_2,:Coordinate_3)");
    QueryConnector.prepare(SqlStr);
    int Connector_ID=GetMaxIDOfDB(T_ProjectDatabase,"Connector","Connector_ID");
    QueryConnector.bindValue(":Connector_ID",Connector_ID);
    QueryConnector.bindValue(":Page_ID",QString::number(Page_IDInDB));
    QueryConnector.bindValue(":Connector_Name",blkName);
    QueryConnector.bindValue(":Connector_Handle",blkNode->dynamicCall("handle()").toString());

    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkNode->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkNode->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryConnector.bindValue(":InsertionPoint",InsertionPoint);

    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"C")->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"C")->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryConnector.bindValue(":C_Coordinate",InsertionPoint);

    if(blkName.contains("SYMB2_M_PWF_CR"))
    {
        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"G")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"G")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryConnector.bindValue(":G_Coordinate",InsertionPoint);
    }
    else QueryConnector.bindValue(":G_Coordinate","");

    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"1")->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"1")->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
    QueryConnector.bindValue(":Coordinate_1",InsertionPoint);

    if(!blkName.contains("SYMB2_M_PWF_CO"))
    {
        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"2")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"2")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryConnector.bindValue(":Coordinate_2",InsertionPoint);
    }
    else QueryConnector.bindValue(":Coordinate_2","");


    if(blkName.contains("SYMB2_M_PWF_BR"))
    {
        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"3")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkNode,"3")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryConnector.bindValue(":Coordinate_3",InsertionPoint);
    }
    else QueryConnector.bindValue(":Coordinate_3","");
    QueryConnector.exec();
    //将DbId写入到blkEnty的拓展数据中
qDebug()<<"SetxDataString,DbId="<<QString::number(Connector_ID);
    blkNode->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(Connector_ID));
}

void formaxwidget::DoNodeLoad()
{ 
    if(!DoLoadSymbolCommand("CONNECT")) return;
    IMxDrawBlockReference *blkNode= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(blkNode==nullptr) return;
qDebug()<<"blkNode!=nullptr";
    if(SymbolName.contains("SYMB2_M_PWF_链接点"))
    {
        DialogLinkEdit *dlg=new DialogLinkEdit(this);
        dlg->AttrMode=1;
        dlg->Page_ID=Page_IDInDB;
        dlg->LoadLinkInfo(0);   
        dlg->show();
        dlg->exec();
        if(dlg->Canceled)
        {
            if(blkNode!=nullptr) blkNode->dynamicCall("Erase()");
            //删除记录
            QSqlQuery QueryLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr ="DELETE FROM Link WHERE Link_ID = "+QString::number(dlg->Link_ID);
            QueryLink.exec(SqlStr);
            delete dlg;
            return;
        }
        UpdateLinkBlk(blkNode,dlg->Link_ID,dlg->RetStrLinkTag,dlg->RetStrLinkTextPosition);
        blkNode->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(dlg->Link_ID));
        delete dlg;
        return;
    }
    InsertNodeRecordToDB(blkNode);
}

//上端子
void formaxwidget::TerminalAdd(QString Terminal_ID)
{
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString tempSQL="SELECT * FROM Terminal WHERE Terminal_ID = "+Terminal_ID;
    QueryVar.exec(tempSQL);
    if(QueryVar.next())
    {
        SymbolName=QueryVar.value("Symbol").toString()+".dwg";
        BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
        MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4));
        SymbolIdInDB=Terminal_ID.toInt();
        ui->axWidget->dynamicCall("DoCommand(const int&)",123);
    }
}

void formaxwidget::NodeLoad(QString NodeName)
{
   FlagAutoConnectLine=true;
   SymbolName=NodeName+".dwg";
   BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
   //MyInsertBlock(ui->axWidget,BlkPath,NodeName);
   ui->axWidget->dynamicCall("DoCommand(const int&)",113);
}

void formaxwidget::GetListAllDirSymbols(QString BlkName)
{
    QString SearchSymbol=BlkName;
    int Index=SearchSymbol.lastIndexOf("-");
    if(Index>=0) SearchSymbol=SearchSymbol.mid(0,Index+1);
    QString SearchFilePath;
    if(SearchSymbol.contains("SPS_")) SearchFilePath="C:/TBD/SPS/";
    else SearchFilePath="C:/TBD/SYMB2LIB/";
    //检索有几种样式
    QStringList filters;//获取所选文件类型过滤器
    filters<<QString(SearchSymbol+"*.dwg");//文件过滤
    //定义迭代器并设置过滤器
    ListAllDirSymbols.clear();
    QDirIterator dir_iterator(SearchFilePath,filters,QDir::Files | QDir::NoSymLinks);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();
        ListAllDirSymbols.append(file_info.fileName());
    }
}

void formaxwidget::InsertAllDirSymbol(QString BlkName)
{
    //同时Insert该符号的所有方向的块到块表
    GetListAllDirSymbols(BlkName);
 qDebug()<<"ListAllDirSymbols count="<<ListAllDirSymbols.count();
    for(int i=0;i<ListAllDirSymbols.count();i++)
    {
        if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+ListAllDirSymbols.at(i);
        else BlkPath="C:/TBD/SYMB2LIB/"+ListAllDirSymbols.at(i);
        qDebug()<<MyInsertBlock(ui->axWidget,BlkPath,ListAllDirSymbols.at(i).mid(0,ListAllDirSymbols.at(i).count()-4));
    }
}
void formaxwidget::SymbolLoad(QString BlockFileName,QString SymbolID)
{

   Symb2Lib_ID=SymbolID;
   SymbolName=BlockFileName;
   //添加块到块表
   QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg

   if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
   else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
   QFileInfo file(BlkPath);
   if(!file.exists()) return;

   InsertAllDirSymbol(BlkName);
   if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
   else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
   //MyInsertBlock(ui->axWidget,BlkPath,BlkName);

   GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",BlkPath);
   IMxDrawResbuf *resp=readGlobalVar(GlobalBackAxWidget,"LD_SYMB1LIB_DICITIONARY","LD_SYMB1LIB_XRECORD");
   if(resp==nullptr)
   {
       qDebug()<<"resp==nullptr";
       return;
   }
   BlkResp->RemoveAll();
   BlkResp->AddStringEx("LD_SYMB1LIB_XRECORD",1001);
   for(int i=0;i<resp->Count();i++)
   {
qDebug()<<resp->AtString(i);
       BlkResp->AddStringEx(resp->AtString(i),1000);
   }

   if(IsDrawingMultiLib)
   {
       ui->axWidget->dynamicCall("DoCommand(const int&)",126);
       FlagAutoConnectLine=false;
   }
   else
   {
       ui->axWidget->dynamicCall("DoCommand(const int&)",101);
       FlagAutoConnectLine=true;
   }
}
bool formaxwidget::BlockRecordExist(QString BlkName)
{
    IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
    IMxDrawBlockTable* blkTable = (IMxDrawBlockTable*)database->querySubObject("GetBlockTable()");
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* ) blkTable->querySubObject("GetAt(QString,bool)",BlkName ,true);
    return blkRec!=nullptr;
}

void formaxwidget::on_axWidget_DynWorldDraw(double dX, double dY, IDispatch *pWorldDraw, IDispatch *pData, int &pRet)
{
    QAxObject *m_pCustomEntity_temp = new QAxObject((IUnknown*)pData );
    IMxDrawCustomEntity* m_pCustomEntity = (IMxDrawCustomEntity*)(m_pCustomEntity_temp);
    QString sGuid = m_pCustomEntity->dynamicCall("Guid").toString();
    pRet = 0;
    QAxObject *m_pWorldDraw_temp = new QAxObject((IUnknown*)pWorldDraw);
    IMxDrawWorldDraw* m_pWorldDraw = (IMxDrawWorldDraw*)m_pWorldDraw_temp;
    //m_pWorldDraw->setProperty("TextStyle","Standard");
    if(sGuid == "DrawMText")
    {
       if(PickPointCount==0)
       {
         m_pWorldDraw->dynamicCall("DrawMText(double,double,double,const QString&)",dX,dY,2.5,LoadingTextStr);
       }
    }
    else if(sGuid == "LoadingSymbol")
    {
       UpdateCursorPos=true;
       if(PickPointCount==0)
       {
  //qDebug()<<"PutCursorInGrid";
         PutCursorInGrid(1,dX,dY);
  //qDebug()<<"m_pWorldDraw DrawBlockReference,SymbolName="<<SymbolName.mid(0,SymbolName.size()-4);
         m_pWorldDraw->dynamicCall("DrawBlockReference(double,double, QString,double,double)",dX,dY,SymbolName.mid(0,SymbolName.size()-4),1.0,0);
  //qDebug()<<"DrawAutoConnectLine";
         DrawAutoConnectLine(1,SymbolName.mid(0,SymbolName.size()-4),dX,dY,m_pWorldDraw);
       }
    }
    else if(sGuid == "LoadingWholeUnit")
    {
        UpdateCursorPos=true;
        if(PickPointCount==0)
        {
          PutCursorInGrid(1,dX,dY);
          DrawWholeUnit(1,dX,dY,m_pWorldDraw);
        }
    }
    else if(sGuid == "DrawAttrDef")
    {
        qDebug()<<"DrawAttrDef,PickPointCount="<<PickPointCount;

       if(PickPointCount==0)
       {
           if(m_dragText.contains("设备标识符"))
           {
               m_pWorldDraw->SetColor(QColorToInt(QColor(255,0,0)));
               m_pWorldDraw->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",dX,dY+1.25,m_dragText,2.5,0,0,2);
           }
           else
           {
               m_pWorldDraw->SetColor(QColorToInt(QColor(255,255,0)));
               m_pWorldDraw->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",dX,dY+1,m_dragText,2,0,0,2);
           }
       }
    }
    else if(sGuid=="DrawConnectLine")
    {
        UpdateCursorPos=true;
        if(PickPointCount==1)
        {        
            PutCursorInGrid(1,dX,dY);
            MxDrawPoint* curPt_temp = new MxDrawPoint();
            curPt_temp->setX(dX);
            curPt_temp->setY(dY);//termline->dynamicCall("SetLineType(QString)","MyDotLineType");
            if(IsDrawingMultiLib)
            {
                m_pWorldDraw->SetColor(QColorToInt(QColor(255,0,255)));
                m_pWorldDraw->dynamicCall("SetLineType(QString)","MyDotLineType");
            }
            else
            {
                m_pWorldDraw->SetColor(QColorToInt(QColor(0,255,0)));
                //m_pWorldDraw->dynamicCall("SetLineType(QString)","MyDotLineType");
            }

            m_pWorldDraw->SetLineWidth(0);
            //画线，考虑是先水平后垂直还是先垂直后水平
            double XDelta=dX-Pt1->x();
            double YDelta=dY-Pt1->y();
            if(XDelta<0) XDelta=-XDelta;
            if(YDelta<0) YDelta=-YDelta;
            if(ConnectLineDir==0)
            {
                if(XDelta>YDelta) ConnectLineDir=1;//先水平后垂直
                else ConnectLineDir=2;//先垂直后水平
            }
            //只有在挪到与初始点水平或垂直的位置才可以更改画线方向
            if(ConnectLineDir!=0)
            {
                if(XDelta<minDelta) ConnectLineDir=2;
                if(YDelta<minDelta) ConnectLineDir=1;
            }

            if(ConnectLineDir==1) //先水平后垂直
            {
                m_pWorldDraw->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), dX,Pt1->y());
                m_pWorldDraw->dynamicCall("DrawLine(double,double,double,double)",dX,Pt1->y(), dX,dY);
            }
            else //先垂直后水平
            {
                m_pWorldDraw->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),Pt1->y(), Pt1->x(),dY);
                m_pWorldDraw->dynamicCall("DrawLine(double,double,double,double)",Pt1->x(),dY, dX,dY);
            }
        }
    }
    else if(sGuid=="DrawMultiLine")
    {
        UpdateCursorPos=true;
        if(IsDrawingMultiLine)
        {         
            PutCursorInGrid(1,dX,dY);
            m_pWorldDraw->SetColor(QColorToInt(QColor(0,255,0)));
            m_pWorldDraw->SetLineWidth(0);
            //找到所有PORT的边界点
            double minX,maxX,minY,maxY;
            bool firstin=true;
            stPoint PickPoint;
            for(int i=0;i<listSelectPort.count();i++)
            {
                if(firstin)
                {
                    firstin=false;
                    minX=listSelectPort.at(i).x;
                    maxX=listSelectPort.at(i).x;
                    minY=listSelectPort.at(i).y;
                    maxY=listSelectPort.at(i).y;
                }
                if(listSelectPort.at(i).x<minX) minX=listSelectPort.at(i).x;
                if(listSelectPort.at(i).y<minY) minY=listSelectPort.at(i).y;
                if(listSelectPort.at(i).x>maxX) maxX=listSelectPort.at(i).x;
                if(listSelectPort.at(i).y>maxY) maxY=listSelectPort.at(i).y;
            }
            //根据边界点位置确定是先画横线还是先画竖线
            if((dY>minY)&&(dY<maxY))
            {
                MultiLineDir=1;//0:未确定 1:先水平后垂直 2：先垂直后水平
            }
            else if((dX>minX)&&(dX<maxX))
            {
                MultiLineDir=2;//0:未确定 1:先水平后垂直 2：先垂直后水平
            }
            else
            {
                if((MultiLineDir!=1)&&(MultiLineDir!=2)) MultiLineDir=1;//默认先水平后垂直
            }

            double minPortx=0;
            double minPorty=0;
            firstin=true;
            for(int i=0;i<listSelectPort.count();i++)
            {
                //根据鼠标位置确定线的方向
                if(firstin){ firstin=false;minPortx=listSelectPort.at(i).x;minPorty=listSelectPort.at(i).y;}
                if(listSelectPort.at(i).x<minPortx) minPortx=listSelectPort.at(i).x;
                if(listSelectPort.at(i).y<minPorty) minPorty=listSelectPort.at(i).y;
                //qDebug()<<"最小ptx="<<minPortx<<" 最小pty="<<minPorty;
            }

            for(int i=0;i<listSelectPort.count();i++)
            {
               //根据鼠标位置确定线的方向
               DrawPoints.clear();
               PickPoint.x=listSelectPort.at(i).x;
               PickPoint.y=listSelectPort.at(i).y;
               DrawPoints.append(PickPoint);
               //需要确定连线终点位置，因为是多线绘制，终点位置并非用户选择的终点位置。
               //如果是先水平后垂直，则终点位置x坐标为用户选择的终点x坐标+当前端点的y坐标-最低（y坐标最小）的端点y坐标;;;y坐标为用户选择的y坐标
               //如果是先垂直后水平，则终点位置y坐标为用户选择的终点y坐标+当前端点的x坐标-最低（x坐标最小）的端点x坐标;;;x坐标为用户选择的x坐标
               if(DrawMode!=3) MultiLineDir=DrawMode;
               if(MultiLineDir==1)//0:未确定 1:先水平后垂直 2：先垂直后水平
               {
                   PickPoint.x=dX+listSelectPort.at(i).y-minPorty;
                   PickPoint.y=dY;
               }
               else if(MultiLineDir==2)//0:未确定 1:先水平后垂直 2：先垂直后水平
               {
                   PickPoint.y=dY+listSelectPort.at(i).x-minPortx;
                   PickPoint.x=dX;
               }
               DrawPoints.append(PickPoint);

               DrawTypicalLine(DrawPoints,MultiLineDir,1,m_pWorldDraw);
            }
        }
    }
    else if (sGuid == "DrawCustBox")
    {
        UpdateCursorPos=true;
        if(PickPointCount==1)
        {
            PutCursorInGrid(1,dX,dY);
            MxDrawPoint* curPt_temp = new MxDrawPoint();//正确
            curPt_temp->setX(dX);
            curPt_temp->setY(dY);
            IMxDrawPoint* curPt = (IMxDrawPoint*)curPt_temp;
            m_pWorldDraw->SetColor(QColorToInt(QColor(255,255,255)));
            m_pWorldDraw->SetLineWidth(0);
            m_pWorldDraw->DrawLine(Pt1->x(),Pt1->y(),curPt_temp->x(), Pt1->y());
            m_pWorldDraw->DrawLine(curPt_temp->x(), Pt1->y(),curPt_temp->x(), curPt_temp->y());
            m_pWorldDraw->DrawLine(curPt_temp->x(), curPt_temp->y(),Pt1->x(), curPt_temp->y());
            m_pWorldDraw->DrawLine(Pt1->x(), curPt_temp->y(),Pt1->x(), Pt1->y());
        }
    }
    else if(sGuid == "CableDefining")
    {
        UpdateCursorPos=true;
        if(PickPointCount==1)
        {          
            PutCursorInGrid(1,dX,dY);
            m_pWorldDraw->SetLineWidth(0);
            m_pWorldDraw->SetColor(QColorToInt(QColor(255,255,255)));
            m_pWorldDraw->setProperty("LineType","MyDotLineType");
            m_pWorldDraw->DrawLine(Pt1->x(),Pt1->y(),dX, dY);
        }
    }
}

void formaxwidget::DoSelectEntitys()
{
qDebug()<<"DoSelectEntitys()";
    MxDrawUiPrPoint getPt;
    int RetCode;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawCustBox");
    QList<IMxDrawEntity*> ListGetEnty;
    int PickEntyCount=0;
    //bool SelectDone=false;
    while(true)
    {
        PickPointCount=0;
        getPt.setMessage("请选择图形，按回车结束选择，已选择"+QString::number(PickEntyCount)+"个");
        RetCode=getPt.go();
        if(RetCode==McUiPrStatus::mcNone)//回车
        {
            qDebug()<<"McUiPrStatus::mcNone";
            IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
            for(int i=0;i<ListGetEnty.count();i++)
            {
                filter->AddObjectId(ListGetEnty.at(i)->ObjectID());
            }
            qDebug()<<"Get database";
            IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
            MxDrawIdMapping *IdMapping=new MxDrawIdMapping();
            IMxDrawIdMapping *pIdMapping=(IMxDrawIdMapping *)IdMapping;
            qDebug()<<"Wblock";
            IMxDrawPoint *basePoint=(IMxDrawPoint*)database->querySubObject("Insbase()");
            //设置基点为选择图形的中心点
            IMxDrawDatabase *newdatabase=(IMxDrawDatabase *)database->querySubObject("Wblock(QAxObject*,QAxObject*,QAxObject*)",filter->asVariant(),basePoint->asVariant(),pIdMapping->asVariant());
            if(newdatabase!=nullptr) // 保存为dwg文件
            {
                qDebug()<<"SaveAs C:/TBD/SYMB2LIB/"+NewSymbolDwgName;
                newdatabase->dynamicCall("SaveAs(QString,int)","C:/TBD/SYMB2LIB/"+NewSymbolDwgName,10);
                FlagNewLib=true;
                //emit(SignalSelectDone(1));
            }
            else qDebug()<<"nullptr";
            qDebug()<<"break";
            break;
        }
        else if(RetCode==McUiPrStatus::mcCancel)//取消
        {
            qDebug()<<"McUiPrStatus::mcCancel";
            emit(SignalSelectDone(0));
            break;
        }
        else if (RetCode == McUiPrStatus::mcOk)
        {
            Pt1 = getPt.value();
            if (Pt1 == nullptr) continue;   // 返回点的点对象值。
            IMxDrawSelectionSet *ssPt= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
            IMxDrawResbuf *filterPt=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
            ssPt->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",Pt1->asVariant(),filterPt->asVariant());
            bool FindEnty=false;
            for(int i=0;i<ssPt->dynamicCall("Count()").toInt();i++)
            {
                IMxDrawEntity *entySelect=  (IMxDrawEntity *)ssPt->querySubObject("Item(int)",i);
                if(EntyIsErased(ui->axWidget,entySelect)) continue;//去除erase的实体
                FindEnty=true;
                ListGetEnty.append(entySelect);
                entySelect->dynamicCall("Highlight(bool)",true);
                PickEntyCount++;
            }
            if(FindEnty) continue;
            else
            {
                PickPointCount++;
                if (getPt.go() != McUiPrStatus::mcOk) continue;
                Pt2 = getPt.value();
                if (Pt2 == nullptr) continue;   // 返回点的点对象值。
                IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
                //创建过滤对象
                MxDrawResbuf* filter =new MxDrawResbuf();
                ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
                qDebug()<<"ss.Count()="<<ss->Count();
                for (int i = 0; i < ss->Count(); i++)
                {
                    IMxDrawEntity* entCrossing = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
                    if(entCrossing==nullptr) continue;
                    if(EntyIsErased(ui->axWidget,entCrossing)) continue;
                    ListGetEnty.append(entCrossing);
                    entCrossing->dynamicCall("Highlight(bool)",true);
                    PickEntyCount++;
                }
            }
        }//else if (RetCode == McUiPrStatus::mcOk)
    }//while(1)
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    for(int i=0;i<ListGetEnty.count();i++)
    {
        ListGetEnty.at(i)->dynamicCall("Highlight(bool)",false);
    }

}

void formaxwidget::SelectEntitys()
{
   ui->axWidget->dynamicCall("DoCommand(const int&)",120);
}

void formaxwidget::EditSymbol()
{
qDebug()<<"EditSymbol";
    ui->axWidget->dynamicCall("DoCommand(const int&)",102);
}
void formaxwidget::WriteUserDataToBlkEnty()//将符号dwg文件的拓展数据写入到块
{
qDebug()<<"WriteUserDataToBlkEnty,BlkPath="<<BlkPath;
    IMxDrawBlockReference *blk=(IMxDrawBlockReference *)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(blk==nullptr)
    {
        qDebug()<<"blk==nullptr";
        return;
    }

    if(BlkResp!=nullptr)//Symbol_Tag仅仅是符号创建时的初始值，为符号标号做初始化用，后续实际标号为TEXTHANDLE对应的文字
    {
        blk->dynamicCall("SetXData(QVariant)",BlkResp->asVariant()) ;
    }
}
void formaxwidget::ChangeWholeUnitTermsGap(QString Mode)//改变WholeUnitTermsGap
{
    if(PickPointCount!=0) return;
    if(!IsDrawingWholeUnit) return;
    if(Mode=="增加") WholeUnitTermsGap+=2;
    if(Mode=="减小") {if(WholeUnitTermsGap>2) WholeUnitTermsGap-=2;}
}
void formaxwidget::RotateEnty()//旋转正在拖入的块
{
qDebug()<<"RotateEnty,SymbolName="<<SymbolName<<" PickPointCount="<<PickPointCount<<" IsLoadingSymbol="<<IsLoadingSymbol;
    if(PickPointCount==0)
    {
        //如果正在动态绘制symbol，旋转时重新insert块并更改块名
       if(IsLoadingSymbol)
       {
           if(SymbolName.contains("SYMB2_M_PWF_"))
           {
               if(SymbolName.contains("SYMB2_M_PWF_CO"))
               {
                   if(SymbolName.mid(14,1)=="1") SymbolName="SYMB2_M_PWF_CO2.dwg";
                   else if(SymbolName.mid(14,1)=="2") SymbolName="SYMB2_M_PWF_CO3.dwg";
                   else if(SymbolName.mid(14,1)=="3") SymbolName="SYMB2_M_PWF_CO4.dwg";
                   else if(SymbolName.mid(14,1)=="4") SymbolName="SYMB2_M_PWF_CO1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_BR"))
               {
                   if(SymbolName.mid(14,1)=="1") SymbolName="SYMB2_M_PWF_BR2.dwg";
                   else if(SymbolName.mid(14,1)=="2") SymbolName="SYMB2_M_PWF_BR3.dwg";
                   else if(SymbolName.mid(14,1)=="3") SymbolName="SYMB2_M_PWF_BR4.dwg";
                   else if(SymbolName.mid(14,1)=="4") SymbolName="SYMB2_M_PWF_BR1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_CR"))
               {
                   if(SymbolName.mid(14,1)=="1") SymbolName="SYMB2_M_PWF_CR2.dwg";
                   else if(SymbolName.mid(14,1)=="2") SymbolName="SYMB2_M_PWF_CR3.dwg";
                   else if(SymbolName.mid(14,1)=="3") SymbolName="SYMB2_M_PWF_CR4.dwg";
                   else if(SymbolName.mid(14,1)=="4") SymbolName="SYMB2_M_PWF_CR1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_TLRO"))
               {
                   if(SymbolName.mid(16,1)=="1") SymbolName="SYMB2_M_PWF_TLRO2.dwg";
                   else if(SymbolName.mid(16,1)=="2") SymbolName="SYMB2_M_PWF_TLRO3.dwg";
                   else if(SymbolName.mid(16,1)=="3") SymbolName="SYMB2_M_PWF_TLRO4.dwg";
                   else if(SymbolName.mid(16,1)=="4") SymbolName="SYMB2_M_PWF_TLRO1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_TLRU"))
               {
                   if(SymbolName.mid(16,1)=="1") SymbolName="SYMB2_M_PWF_TLRU2.dwg";
                   else if(SymbolName.mid(16,1)=="2") SymbolName="SYMB2_M_PWF_TLRU3.dwg";
                   else if(SymbolName.mid(16,1)=="3") SymbolName="SYMB2_M_PWF_TLRU4.dwg";
                   else if(SymbolName.mid(16,1)=="4") SymbolName="SYMB2_M_PWF_TLRU1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_TOUL"))
               {
                   if(SymbolName.mid(16,1)=="1") SymbolName="SYMB2_M_PWF_TOUL2.dwg";
                   else if(SymbolName.mid(16,1)=="2") SymbolName="SYMB2_M_PWF_TOUL3.dwg";
                   else if(SymbolName.mid(16,1)=="3") SymbolName="SYMB2_M_PWF_TOUL4.dwg";
                   else if(SymbolName.mid(16,1)=="4") SymbolName="SYMB2_M_PWF_TOUL1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_TOUR"))
               {
                   if(SymbolName.mid(16,1)=="1") SymbolName="SYMB2_M_PWF_TOUR2.dwg";
                   else if(SymbolName.mid(16,1)=="2") SymbolName="SYMB2_M_PWF_TOUR3.dwg";
                   else if(SymbolName.mid(16,1)=="3") SymbolName="SYMB2_M_PWF_TOUR4.dwg";
                   else if(SymbolName.mid(16,1)=="4") SymbolName="SYMB2_M_PWF_TOUR1.dwg";
               }
               else if(SymbolName.contains("SYMB2_M_PWF_链接点"))
               {
                   if(SymbolName.mid(15,1)=="1") SymbolName="SYMB2_M_PWF_链接点2.dwg";
                   else if(SymbolName.mid(15,1)=="2") SymbolName="SYMB2_M_PWF_链接点3.dwg";
                   else if(SymbolName.mid(15,1)=="3") SymbolName="SYMB2_M_PWF_链接点4.dwg";
                   else if(SymbolName.mid(15,1)=="4") SymbolName="SYMB2_M_PWF_链接点1.dwg";
               }           
               BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
               MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4));
           }
           else
           {
               for(int i=0;i<ListAllDirSymbols.count();i++)
               {
                   if(ListAllDirSymbols.at(i)==SymbolName)
                   {
                       if(i==(ListAllDirSymbols.count()-1))
                       {
                           SymbolName=ListAllDirSymbols.at(0);
                       }
                       else SymbolName=ListAllDirSymbols.at(i+1);
                       if(SymbolName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
                       else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
                       break;
                   }
               }
           }
       }
    }
    ui->axWidget->dynamicCall("UpdateDisplay()");
    //ui->axWidget->dynamicCall("Regen()");

}

QAxWidget* formaxwidget::GetAxWidget()
{
    return ui->axWidget;
}

QString formaxwidget::GetSymbolNameByDir(QString StrSymbolName,QString StrDir)
{
    //同时Insert该符号的所有方向的块到块表
    QString SearchSymbol=StrSymbolName;
    int Index=SearchSymbol.lastIndexOf("-");
    if(Index>=0) SearchSymbol=SearchSymbol.mid(0,Index+1);
    QString SearchFilePath;
    if(SearchSymbol.contains("SPS_")) SearchFilePath="C:/TBD/SPS/";
    else SearchFilePath="C:/TBD/SYMB2LIB/";
    //检索有几种样式
    QStringList filters;//获取所选文件类型过滤器
    filters<<QString(SearchSymbol+"*.dwg");//文件过滤
    //定义迭代器并设置过滤器
    ListAllDirSymbols.clear();
    QDirIterator dir_iterator(SearchFilePath,filters,QDir::Files | QDir::NoSymLinks);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();
        QStringList ListBlockTermData=GetBlockTermData(ui->axWidget,file_info.fileName().mid(0,file_info.fileName().count()-4),1);
        if(ListBlockTermData.count()!=2) continue;
        if(ListBlockTermData.at(0)==StrDir) return file_info.fileName();
    }
    return "";
}

//Mode=0:ui->axWidget Mode=1:pDrawWorldDraw
void formaxwidget::DrawWholeUnit(int Mode,double Posx,double Posy,IMxDrawWorldDraw *pDrawWorldDraw)
{
    QSqlQuery QuerySymbol(T_ProjectDatabase);
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString sqlstr;
    int TermIndex=0,AllTermCount=0;
    double BlkPosx=Posx;
    double BlkPosy=Posy;
    //第一个端口基点为Posx，Posy
    sqlstr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(UnitIdInDB)+"' AND Symbol <> '' ORDER BY Symbol_ID DESC";
    QuerySymbol.exec(sqlstr);
    while(QuerySymbol.next()) AllTermCount++;
    if(AllTermCount<=0) return;
    SetCurLayer(ui->axWidget,"LY_Symb2");
    //绘制围框

    double minPosx=Posx-6;
    double maxPosx;
    if(LoadAllUnitMode==1) maxPosx=Posx+WholeUnitTermsGap*(AllTermCount-1)+6;//全部端口向上
    else if(LoadAllUnitMode==2) maxPosx=Posx+WholeUnitTermsGap*(AllTermCount-1)+6;//全部端口向下
    else if(LoadAllUnitMode==3) maxPosx=Posx+WholeUnitTermsGap*((AllTermCount-1)/2)+6;//3：奇数向上，偶数向下
    else if(LoadAllUnitMode==4) maxPosx=Posx+WholeUnitTermsGap*((AllTermCount-1)/2)+6;//4：奇数向下，偶数向上
    else if(LoadAllUnitMode==5) maxPosx=Posx+WholeUnitTermsGap*(AllTermCount-AllTermCount/2-1)+6;//5:前半部分向上，后面向下
    else if(LoadAllUnitMode==6) maxPosx=Posx+WholeUnitTermsGap*(AllTermCount-AllTermCount/2-1)+6;//6：前半部分向下，后面向上
    double maxPosy,minPosy;
    if(LoadAllUnitMode==2) {minPosy=Posy-4;maxPosy=minPosy+20;}
    else {maxPosy=Posy+4;minPosy=maxPosy-20;}


    QString DT_Handle;
    QString Box_Handle;
    if(Mode==1)
    {
qDebug()<<"pDrawWorldDraw DrawLine";
        pDrawWorldDraw->SetColor(QColorToInt(QColor(255,0,255)));
        pDrawWorldDraw->setProperty("LineType","MyDotLineType");
        pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)", minPosx,maxPosy,maxPosx,maxPosy);
        pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)", maxPosx,maxPosy,maxPosx,minPosy);
        pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)", maxPosx,minPosy,minPosx,minPosy);
        pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)", minPosx,minPosy,minPosx,maxPosy);
    }
    else
    {
        ui->axWidget->dynamicCall("PathMoveTo(double,double)",minPosx,maxPosy);
        ui->axWidget->dynamicCall("PathLineTo(double,double)",maxPosx,maxPosy);
        ui->axWidget->dynamicCall("PathLineTo(double,double)",maxPosx,minPosy);
        ui->axWidget->dynamicCall("PathLineTo(double,double)",minPosx,minPosy);
        ui->axWidget->dynamicCall("PathLineTo(double,double)",minPosx,maxPosy);
        qlonglong lID=ui->axWidget->dynamicCall("DrawPathToPolyline()").toLongLong();
        IMxDrawPolyline *EntyBox= (IMxDrawPolyline*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
        Box_Handle=EntyBox->dynamicCall("handle()").toString();
        EntyBox->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
        EntyBox->dynamicCall("SetLineType(QString)","MyDotLineType");

        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        sqlstr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(UnitIdInDB);
        QueryEquipment.exec(sqlstr);
        if(QueryEquipment.next())
        {
            QString SymbolTag;//如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
            if(GetProjectStructureIDByPageID(Page_IDInDB)==QueryEquipment.value("ProjectStructure_ID").toString())
              SymbolTag="-"+QueryEquipment.value("DT").toString();
            else
              SymbolTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();
            lID=ui->axWidget->dynamicCall("DrawMText(double,double,const QString&,double,double,double,short)",minPosx-3,(minPosy+maxPosy)/2,SymbolTag,2.5,0,PI/2,5).toLongLong();
            IMxDrawMText* DTMText= (IMxDrawMText*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
            DT_Handle=DTMText->dynamicCall("handle()").toString();
            DTMText->dynamicCall("setColorIndex(int)",McColor::mcCyan);
            DTMText->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPCPXRECT_XRECT",0,Box_Handle);
            EntyBox->dynamicCall("SetxDataString(QString,int,QString)","LD_GROUPCPXRECT_TEXT",0,DT_Handle);
        }
    }
    //如果Symbol存在FunDefine为黑盒或PLC盒子的记录，则更新，若不存在则创建
    sqlstr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(UnitIdInDB)+"' AND (FunDefine = '黑盒' OR FunDefine = 'PLC 盒子')";
    QuerySymbol.exec(sqlstr);
    if(QuerySymbol.next())
    {
        QSqlQuery QueryUpdate = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        sqlstr="UPDATE Symbol SET Page_ID=:Page_ID,DT_Handle=:DT_Handle,Symbol_Handle=:Symbol_Handle WHERE Symbol_ID= "+QuerySymbol.value("Symbol_ID").toString();
        QueryUpdate.prepare(sqlstr);
        QueryUpdate.bindValue(":Page_ID",QString::number(Page_IDInDB));
        QueryUpdate.bindValue(":DT_Handle",DT_Handle);
        QueryUpdate.bindValue(":Symbol_Handle",Box_Handle);
        QueryUpdate.exec();
    }
    else
    {
        QSqlQuery QueryInsert = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        sqlstr =  "INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol_Category,DT_Handle,Symbol_Handle,Symbol_Remark,FunDefine)"
                                "VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol_Category,:DT_Handle,:Symbol_Handle,:Symbol_Remark,:FunDefine)";
        QueryInsert.prepare(sqlstr);
        QueryInsert.bindValue(":Symbol_ID",QString::number(GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID")));
        QueryInsert.bindValue(":Page_ID",QString::number(Page_IDInDB));
        QueryInsert.bindValue(":Equipment_ID",QString::number(UnitIdInDB));
        QueryInsert.bindValue(":Symbol_Category","组合元件盒子");
        QueryInsert.bindValue(":DT_Handle",DT_Handle);
        QueryInsert.bindValue(":Symbol_Handle",Box_Handle);
        QueryInsert.bindValue(":Symbol_Remark","组合元件盒子");
        QueryInsert.bindValue(":FunDefine","黑盒");
        QueryInsert.exec();
    }

    sqlstr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(UnitIdInDB)+"' AND Symbol <> '' ORDER BY Symbol_ID ASC";
    QuerySymbol.exec(sqlstr);
    while(QuerySymbol.next())
    {
        TermIndex++;
        //Mode=1:全部向上 Mode=2:全部向下 Mode=3：奇数向上，偶数向下 Mode=4：奇数向下，偶数向上  mode=5:前半部分向上，后面向下  Mode=6：前半部分向下，后面向上
        if(LoadAllUnitMode==1)//全部端口向上
        {
            SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向上");
            BlkPosx=Posx+WholeUnitTermsGap*(TermIndex-1);
        }
        else if(LoadAllUnitMode==2)//全部端口向下
        {
            SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向下");
            BlkPosx=Posx+WholeUnitTermsGap*(TermIndex-1);
        }
        else if(LoadAllUnitMode==3)//3：奇数向上，偶数向下
        {
            if((TermIndex%2)==1)
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向上");
                BlkPosy=Posy;
            }
            else
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向下");
                BlkPosy=Posy-12;
            }
            BlkPosx=Posx+WholeUnitTermsGap*((TermIndex-1)/2);
        }
        else if(LoadAllUnitMode==4)//4：奇数向下，偶数向上
        {
            if((TermIndex%2)==1)
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向下");
                BlkPosy=Posy-12;
            }
            else
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向上");
                BlkPosy=Posy;
            }
            BlkPosx=Posx+WholeUnitTermsGap*((TermIndex-1)/2);
        }
        else if(LoadAllUnitMode==5)//5:前半部分向上，后面向下
        {
            if(TermIndex<=(AllTermCount/2))
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向上");
                BlkPosy=Posy;
                BlkPosx=Posx+WholeUnitTermsGap*(TermIndex-1);
            }
            else
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向下");
                BlkPosy=Posy-12;
                BlkPosx=Posx+WholeUnitTermsGap*(TermIndex-AllTermCount/2-1);
            }
        }
        else if(LoadAllUnitMode==6)//6：前半部分向下，后面向上
        {
            if(TermIndex<=(AllTermCount/2))
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向下");
                BlkPosy=Posy-12;
                BlkPosx=Posx+WholeUnitTermsGap*(TermIndex-1);
            }
            else
            {
                SymbolName=GetSymbolNameByDir(QuerySymbol.value("Symbol").toString(),"向上");
                BlkPosy=Posy;
                BlkPosx=Posx+WholeUnitTermsGap*(TermIndex-AllTermCount/2-1);
            }
        }
        if(Mode==1)
        {
            pDrawWorldDraw->SetColor(QColorToInt(QColor(255,255,255)));
            pDrawWorldDraw->dynamicCall("DrawBlockReference(double,double, QString,double,double)",BlkPosx,BlkPosy,SymbolName.mid(0,SymbolName.size()-4),1.0,0);
        }
        else if(Mode==0)
        {
            lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",BlkPosx,BlkPosy,SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();
            IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
            //将DbId写入到blkEnty的拓展数据中
            blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QuerySymbol.value("Symbol_ID").toString());
            //将FunDefine写入到blkEnty的拓展数据中
            blkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,QuerySymbol.value("FunDefine").toString());
            blkEnty->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,QuerySymbol.value("Symbol_Category").toString());
            //WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块
            //在数据库中找到SymbolID对应的符号名称，分为ES2_XXX和SPS_XXX两种
            QString Symbol_Category=QuerySymbol.value("Symbol_Category").toString();
            QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            sqlstr = "SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QuerySymbol.value("Symbol_ID").toString()+"'";
            QuerySymb2TermInfo.exec(sqlstr);
            while(QuerySymb2TermInfo.next())
            {
                //找到端点并添加块属性
                QString ConnNum_Logic=QuerySymb2TermInfo.value("ConnNum_Logic").toString();
                QString ConnNum=QuerySymb2TermInfo.value("ConnNum").toString();
                QString ConnDesc=QuerySymb2TermInfo.value("ConnDesc").toString();
                FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,ConnNum_Logic,ConnNum);//连接点代号
                FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"符号的连接点描述["+ConnNum_Logic+"]",ConnDesc);//连接点描述
                FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"连接点代号（全部）",ConnNum);//连接点代号（全部）
                FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"连接点描述（全部）",ConnDesc);//连接点描述（全部）
            }
            //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
            //更新Symbol表，包括Page_ID，Symbol_Handle，InsertionPoint
            QSqlQuery queryUpdateSymbol(T_ProjectDatabase);
            sqlstr="UPDATE Symbol SET Page_ID=:Page_ID,Symbol=:Symbol,Symbol_Handle=:Symbol_Handle,Box_Handle=:Box_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID= "+QuerySymbol.value("Symbol_ID").toString();
            queryUpdateSymbol.prepare(sqlstr);
            queryUpdateSymbol.bindValue(":Page_ID",QString::number(Page_IDInDB));
            queryUpdateSymbol.bindValue(":Symbol",SymbolName.mid(0,SymbolName.size()-4));
            queryUpdateSymbol.bindValue(":Symbol_Handle",blkEnty->dynamicCall("handle()").toString());
            queryUpdateSymbol.bindValue(":Box_Handle",Box_Handle);
            QString InsertionPoint;
            InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            //qDebug()<<"blkEnty InsertionPoint="<<InsertionPoint;
            queryUpdateSymbol.bindValue(":InsertionPoint",InsertionPoint);
            queryUpdateSymbol.exec();

            //更新Symb2TermInfo表，包括Conn_Coordinate，ConnDirection
            int TermCount=GetTermEnty(ui->axWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
            //int TermCount=GetDwgTermCount(BlkPath);
            qDebug()<<"BlkPath="<<BlkPath<<",GetDwgTermCount,TermCount="<<TermCount;
            for(int i=0;i<TermCount;i++)
            {
                sqlstr="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate,ConnDirection=:ConnDirection,Internal=:Internal WHERE Symbol_ID= '"+QuerySymbol.value("Symbol_ID").toString()+"' AND ConnNum_Logic='"+QString::number(i+1)+"'";
                QuerySymb2TermInfo.prepare(sqlstr);
                double TermPosx=GetSymbolBlockTermPos(ui->axWidget,blkEnty,QString::number(i+1))->x();
                double TermPosy=GetSymbolBlockTermPos(ui->axWidget,blkEnty,QString::number(i+1))->y();
                InsertionPoint=QString::number(TermPosx,'f',0)+".000000";
                InsertionPoint+=","+QString::number(TermPosy,'f',0)+".000000";
                InsertionPoint+=",0.000000";

                //qDebug()<<":Conn_Coordinate="<<InsertionPoint;
                QuerySymb2TermInfo.bindValue(":Conn_Coordinate",InsertionPoint);

                QStringList listTermInfo=GetBlockTermData(ui->axWidget,blkEnty->dynamicCall("GetBlockName()").toString(),i+1);//GetDwgTermData(BlkPath,i+1);
                //qDebug()<<"listTermInfo="<<listTermInfo;
                if(listTermInfo.count()==2)
                {
                    //qDebug()<<"listTermInfo.count()==2,listTermInfo.at(0)="<<listTermInfo.at(0);
                    QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
                    if(listTermInfo.at(1)=="是")
                        QuerySymb2TermInfo.bindValue(":Internal",1);
                    else QuerySymb2TermInfo.bindValue(":Internal",0);
                }
                else
                {
                    //qDebug()<<"listTermInfo.count()!=2";
                    QuerySymb2TermInfo.bindValue(":ConnDirection","");
                    QuerySymb2TermInfo.bindValue(":Internal",0);
                }
                QuerySymb2TermInfo.exec();
            }//end of for(int i=0;i<TermCount;i++)
        }
    }//end of while(QuerySymbol.next())
    SetCurLayer(ui->axWidget,"0");
}

void formaxwidget::DoLoadWholeUnit()
{
    PickPointCount=0;
    MxDrawUiPrPoint getPt;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingWholeUnit");
    IsDrawingWholeUnit=true;
    WholeUnitTermsGap=12;
    getPt.setMessage("请指定位置,按1键减小连接点间距,按2键增大连接点间距");
    if (getPt.go() != McUiPrStatus::mcOk) {IsDrawingWholeUnit=false;return;}
    IMxDrawPoint* frstPt = GetGridPtVal(getPt.value());
    if (frstPt == nullptr) {getPt.setMessage("位置无效");IsDrawingWholeUnit=false;return; }  // 返回点的点对象值。
    PickPointCount++;   
    ui->axWidget->setProperty("TextStyle","Standard");
    //设置属性块文字
    SetCurLayer(ui->axWidget,"LY_Symb2");
    DrawWholeUnit(0,frstPt->x(),frstPt->y(),nullptr);
    IsDrawingWholeUnit=false;
qDebug()<<"SaveDwgFile,dwgFileName="<<dwgFileName;
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
   //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    //更新导航窗口
    emit(UpdateProjectUnits());
}

void formaxwidget::DoLoadUnitStamp()
{
    PickPointCount=0;
    MxDrawUiPrPoint getPt;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
    IsLoadingSymbol=true;
    getPt.setMessage("请指定位置");
    if (getPt.go() != McUiPrStatus::mcOk) {qDebug()<<"getPt.go()!= McUiPrStatus::mcOk";IsLoadingSymbol=false;return;}
    IMxDrawPoint* frstPt = GetGridPtVal(getPt.value());
    if (frstPt == nullptr) {qDebug()<<"frstPt == nullptr";getPt.setMessage("位置无效");IsLoadingSymbol=false;return; }  // 返回点的点对象值。
    SetCurLayer(ui->axWidget,"LY_Symb2");
    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",frstPt->x(),frstPt->y(),SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();
    IMxDrawBlockReference *BlkEnty= (IMxDrawBlockReference*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    //将blkEnty炸散
    IMxDrawResbuf *RespExplode =(IMxDrawResbuf *)BlkEnty->querySubObject("Explode()");
    BlkEnty->dynamicCall("Erase()");
    //将RespExplode打包成一个编组
    ui->axWidget->dynamicCall("CreateGroup(QString,QVariant)",QString::number(UnitIdInDB),RespExplode->asVariant());
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    for(int i=0;i<RespExplode->dynamicCall("Count()").toInt();i++)
    {
        IMxDrawEntity *EntyExplode= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespExplode->dynamicCall("AtObjectId(int)",i).toLongLong());
        if(EntyIsErased(ui->axWidget,EntyExplode)) continue;

        if(EntyExplode->dynamicCall("ObjectName()").toString()!="McDbBlockReference") continue;
        IMxDrawBlockReference *BlkExplode=(IMxDrawBlockReference *)EntyExplode;
        //查看BlkExplode的块属性文字，并更新数据库
        QString SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(UnitIdInDB)+"'";
        QuerySymbol.exec(SqlStr);
        QString CurSymbol_ID;
        while(QuerySymbol.next())
        {
           QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
           SqlStr = "SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QuerySymbol.value("Symbol_ID").toString()+"'";
           QuerySymb2TermInfo.exec(SqlStr);
           int ResultCnt=0;
           bool FindSymbol=true;
           while(QuerySymb2TermInfo.next())
           {
               ResultCnt++;
               if(GetBlockAttrTextString(BlkExplode,QuerySymb2TermInfo.value("ConnNum_Logic").toString())!=QuerySymb2TermInfo.value("ConnNum").toString())
               {
                   FindSymbol=false;
                   break;
               }
           }
           if(ResultCnt==0) FindSymbol=false;
           if(FindSymbol)
           {
               CurSymbol_ID=QuerySymbol.value("Symbol_ID").toString();
               break;
           }
        }
        if(CurSymbol_ID!="")
        {
            BlkExplode->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,CurSymbol_ID);
            BlkExplode->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,QuerySymbol.value("FunDefine").toString());
            BlkExplode->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,QuerySymbol.value("Symbol_Category").toString());
            BlkExplode->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Remark",0,QuerySymbol.value("Symbol_Remark").toString());

            QSqlQuery QueryUpdateSymbol(T_ProjectDatabase);
            QString StrSql="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle WHERE Symbol_ID = "+CurSymbol_ID;
            QueryUpdateSymbol.prepare(StrSql);
            QueryUpdateSymbol.bindValue(":Page_ID",QString::number(Page_IDInDB));
            QueryUpdateSymbol.bindValue(":Symbol_Handle",BlkExplode->dynamicCall("handle()").toString());
            QueryUpdateSymbol.exec();

            //更新Symb2TermInfo表，包括Conn_Coordinate，ConnDirection
            int TermCount=GetTermEnty(ui->axWidget,BlkExplode->dynamicCall("GetBlockName()").toString()).count();
            QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
            for(int i=0;i<TermCount;i++)
            {
                QString sqlstr="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate,ConnDirection=:ConnDirection,Internal=:Internal WHERE Symbol_ID= '"+QuerySymbol.value("Symbol_ID").toString()+"' AND ConnNum_Logic='"+QString::number(i+1)+"'";
                QuerySymb2TermInfo.prepare(sqlstr);
                double TermPosx=GetSymbolBlockTermPos(ui->axWidget,BlkExplode,QString::number(i+1))->x();
                double TermPosy=GetSymbolBlockTermPos(ui->axWidget,BlkExplode,QString::number(i+1))->y();
                QString InsertionPoint=QString::number(TermPosx,'f',0)+".000000";
                InsertionPoint+=","+QString::number(TermPosy,'f',0)+".000000";
                InsertionPoint+=",0.000000";

                //qDebug()<<":Conn_Coordinate="<<InsertionPoint;
                QuerySymb2TermInfo.bindValue(":Conn_Coordinate",InsertionPoint);

                QStringList listTermInfo=GetBlockTermData(ui->axWidget,BlkExplode->dynamicCall("GetBlockName()").toString(),i+1);//GetDwgTermData(BlkPath,i+1);
                //qDebug()<<"listTermInfo="<<listTermInfo;
                if(listTermInfo.count()==2)
                {
                    //qDebug()<<"listTermInfo.count()==2,listTermInfo.at(0)="<<listTermInfo.at(0);
                    QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
                    if(listTermInfo.at(1)=="是")
                        QuerySymb2TermInfo.bindValue(":Internal",1);
                    else QuerySymb2TermInfo.bindValue(":Internal",0);
                }
                else
                {
                    //qDebug()<<"listTermInfo.count()!=2";
                    QuerySymb2TermInfo.bindValue(":ConnDirection","");
                    QuerySymb2TermInfo.bindValue(":Internal",0);
                }
                QuerySymb2TermInfo.exec();
            }//end of for(int i=0;i<TermCount;i++)
        }
    }
    emit(UpdateProjectUnits());
}

void formaxwidget::DoLoadSymbolSpur()
{    
    //PickPointCount++;
    ui->axWidget->setProperty("TextStyle","Standard");
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    while(ListLoadingDbID.count()>0)
    {
        SymbolIdInDB=ListLoadingDbID.at(0);
        QString SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB);
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())  SymbolName=QuerySymbol.value("Symbol").toString()+".dwg";
        GetListAllDirSymbols(SymbolName.mid(0,SymbolName.size()-4));
        PickPointCount=0;
        MxDrawUiPrPoint getPt;
        ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
        IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
        IsLoadingSymbol=true;
        getPt.setMessage("请指定位置,按Shift键取消自动连线");
        if (getPt.go() != McUiPrStatus::mcOk) {qDebug()<<"getPt.go()!= McUiPrStatus::mcOk";IsLoadingSymbol=false;return;}
        IMxDrawPoint* frstPt = GetGridPtVal(getPt.value());
        if (frstPt == nullptr) {qDebug()<<"frstPt == nullptr";getPt.setMessage("位置无效");IsLoadingSymbol=false;return; }  // 返回点的点对象值。
        DealSymbolSpurBlock(frstPt->x(),frstPt->y());
        ListLoadingDbID.removeAt(0);
    }
    IsLoadingSymbol=false;
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    //更新导航窗口
    emit(UpdateProjectUnits());
}

void formaxwidget::DealSymbolSpurBlock(double Posx,double Posy)
{
    //查看功能子块是否在本元件的黑盒范围内，如果是的话则不显示设备标识符，如果在不是本元件的黑盒内则不支持放置
    //查看Symbol是否在黑盒内部，如果不是的话返回0，如果是并且黑盒和Symbol是同元件则返回1，如果是并且黑盒和Symbol是不同元件则返回-1
    int  BlackBoxVal=CheckBlackBox(ui->axWidget,Posx,Posy,SymbolIdInDB);
qDebug()<<"CheckBlackBox="<<BlackBoxVal;
    if(BlackBoxVal<0) {QMessageBox::warning(nullptr, "提示", " 元件代号与盒子代号不一致，不支持放置！");return;}
    SetCurLayer(ui->axWidget,"LY_Symb2");
    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Posx,Posy,SymbolName.mid(0,SymbolName.size()-4),1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
qDebug()<<"draw blk over";

    CutLine(blkEnty);//用端点截断导线
    //将DbId写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,QString::number(SymbolIdInDB));
    DrawAutoConnectLine(0,SymbolName.mid(0,SymbolName.size()-4),Posx,Posy,nullptr);
    WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块

    //在数据库中找到SymbolID对应的符号名称，分为ES2_XXX和SPS_XXX两种
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB));
    QuerySymbol.exec(temp);
    if(!QuerySymbol.next()) return;
    //将FunDefine写入到blkEnty的拓展数据中
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,QuerySymbol.value("FunDefine").toString());
    blkEnty->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,QuerySymbol.value("Symbol_Category").toString());
    QString Equipment_ID=QuerySymbol.value("Equipment_ID").toString();
    QString Symbol_Category=QuerySymbol.value("Symbol_Category").toString();
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM Equipment WHERE Equipment_ID = "+Equipment_ID);
    QueryEquipment.exec(temp);
    if(!QueryEquipment.next()) return;
    QString SymbolTag;//如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
    if(GetProjectStructureIDByPageID(Page_IDInDB)==QueryEquipment.value("ProjectStructure_ID").toString())
      SymbolTag="-"+QueryEquipment.value("DT").toString();
    else
      SymbolTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();

    QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QString::number(SymbolIdInDB)+"'");
    QuerySymb2TermInfo.exec(temp);
    while(QuerySymb2TermInfo.next())
    {
        //找到端点并添加块属性
        QString ConnNum_Logic=QuerySymb2TermInfo.value("ConnNum_Logic").toString();
        QString ConnNum=QuerySymb2TermInfo.value("ConnNum").toString();
        QString ConnDesc=QuerySymb2TermInfo.value("ConnDesc").toString();

        if(Symbol_Category!="元件连接点") FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,ConnNum_Logic,ConnNum);//连接点代号
        FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"符号的连接点描述["+ConnNum_Logic+"]",ConnDesc);//连接点描述
        FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"连接点代号（带显示设备标识符）",SymbolTag+":"+ConnNum);
        FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"连接点代号（全部）",ConnNum);
        FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"连接点描述（全部）",ConnDesc);
    }

    IsLoadingSymbol=false;
    //ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",1);
    //更新Symbol表，包括Page_ID，Symbol_Handle，InsertionPoint
    QSqlQuery querySymbol(T_ProjectDatabase);
    QString tempSQL=QString("UPDATE Symbol SET Page_ID=:Page_ID,Symbol=:Symbol,Symbol_Handle=:Symbol_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID= "+QString::number(SymbolIdInDB));
    querySymbol.prepare(tempSQL);
    querySymbol.bindValue(":Page_ID",QString::number(Page_IDInDB));
    querySymbol.bindValue(":Symbol",SymbolName.mid(0,SymbolName.size()-4));
    querySymbol.bindValue(":Symbol_Handle",blkEnty->dynamicCall("handle()").toString());
    QString InsertionPoint;
    InsertionPoint=QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->x(),'f',0)+".000000";
    InsertionPoint+=","+QString::number(((IMxDrawPoint *)blkEnty->querySubObject("Position()"))->y(),'f',0)+".000000";
    InsertionPoint+=",0.000000";
qDebug()<<"blkEnty InsertionPoint="<<InsertionPoint;
    querySymbol.bindValue(":InsertionPoint",InsertionPoint);
    querySymbol.exec();

    if(!CheckSpinBeside(SymbolIdInDB,ui->axWidget))
    {
        if(BlackBoxVal<=0) FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"设备标识符(显示)",SymbolTag);
        else FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"设备标识符(显示)","");
    }
    else FindAttrDefAndAddAttrToBlock(ui->axWidget,blkEnty,"设备标识符(显示)","");
    ui->axWidget->dynamicCall("UpdateDisplay()");
    //更新Symb2TermInfo表，包括Conn_Coordinate，ConnDirection
    int TermCount=GetTermEnty(ui->axWidget,blkEnty->dynamicCall("GetBlockName()").toString()).count();
    //int TermCount=GetDwgTermCount(BlkPath);
qDebug()<<"BlkPath="<<BlkPath<<",GetDwgTermCount,TermCount="<<TermCount;

    for(int i=0;i<TermCount;i++)
    {
        tempSQL=QString("UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate,ConnDirection=:ConnDirection,Internal=:Internal WHERE Symbol_ID= '"+QString::number(SymbolIdInDB)+"' AND ConnNum_Logic='"+QString::number(i+1)+"'");

        QuerySymb2TermInfo.prepare(tempSQL);
        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,blkEnty,QString::number(i+1))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,blkEnty,QString::number(i+1))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
//qDebug()<<":Conn_Coordinate="<<InsertionPoint;
        QuerySymb2TermInfo.bindValue(":Conn_Coordinate",InsertionPoint);

        QStringList listTermInfo=GetBlockTermData(ui->axWidget,blkEnty->dynamicCall("GetBlockName()").toString(),i+1);//GetDwgTermData(BlkPath,i+1);
//qDebug()<<"listTermInfo="<<listTermInfo;
        if(listTermInfo.count()==2)
        {
            //qDebug()<<"listTermInfo.count()==2,listTermInfo.at(0)="<<listTermInfo.at(0);
            QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
            if(listTermInfo.at(1)=="是")
              QuerySymb2TermInfo.bindValue(":Internal",1);
            else QuerySymb2TermInfo.bindValue(":Internal",0);
        }
        else
        {
            qDebug()<<"listTermInfo.count()!=2";
            QuerySymb2TermInfo.bindValue(":ConnDirection","");
            QuerySymb2TermInfo.bindValue(":Internal",0);
        }
        QuerySymb2TermInfo.exec();
    }
}


void formaxwidget::DoLoadEqualDistance()//等距绘制
{
    if(ListLoadingDbID.count()<1) return;
    bool OriginalAutoConnect=FlagAutoConnectLine;
    FlagAutoConnectLine=false;
    PickPointCount=0;
    MxDrawUiPrPoint getPt;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    SymbolIdInDB=ListLoadingDbID.at(0);
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    if(CurEqualDrawMode==0) SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB);
    else if(CurEqualDrawMode==1) SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SymbolIdInDB);
    QuerySearch.exec(SqlStr);
    if(QuerySearch.next())  SymbolName=QuerySearch.value("Symbol").toString()+".dwg";
    GetListAllDirSymbols(SymbolName.mid(0,SymbolName.size()-4));
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("LoadingSymbol");
    IsLoadingSymbol=true;
    getPt.setMessage("请指定第一个绘制位置");
    if (getPt.go() != McUiPrStatus::mcOk) {qDebug()<<"getPt.go()!= McUiPrStatus::mcOk";IsLoadingSymbol=false;FlagAutoConnectLine=OriginalAutoConnect;return;}
    IMxDrawPoint* frstPt = GetGridPtVal(getPt.value());
    if (frstPt == nullptr) {qDebug()<<"frstPt == nullptr";getPt.setMessage("位置无效");IsLoadingSymbol=false;FlagAutoConnectLine=OriginalAutoConnect;return; }  // 返回点的点对象值。
    ui->axWidget->setProperty("TextStyle","Standard");
    if(CurEqualDrawMode==0) DealSymbolSpurBlock(frstPt->x(),frstPt->y());
    else if(CurEqualDrawMode==1)  DealTerminalBlock(frstPt->x(),frstPt->y());
    ListLoadingDbID.removeAt(0);

    if(ListLoadingDbID.count()>=1)
    {
        getPt.setMessage("请指定第二个绘制位置");
        SymbolIdInDB=ListLoadingDbID.at(0);
        if(CurEqualDrawMode==0) SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB);
        else if(CurEqualDrawMode==1) SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SymbolIdInDB);
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())  SymbolName=QuerySearch.value("Symbol").toString()+".dwg";
        GetListAllDirSymbols(SymbolName.mid(0,SymbolName.size()-4));
        if (getPt.go() != McUiPrStatus::mcOk) {qDebug()<<"getPt.go()!= McUiPrStatus::mcOk";IsLoadingSymbol=false;return;}
        IMxDrawPoint* SecondPt = GetGridPtVal(getPt.value());
        if (SecondPt == nullptr) {qDebug()<<"frstPt == nullptr";getPt.setMessage("位置无效");IsLoadingSymbol=false;return; }  // 返回点的点对象值。
        if(CurEqualDrawMode==0) DealSymbolSpurBlock(SecondPt->x(),SecondPt->y());
        else if(CurEqualDrawMode==1)  DealTerminalBlock(SecondPt->x(),SecondPt->y());
        ListLoadingDbID.removeAt(0);

        double Posx=SecondPt->x(),Posy=SecondPt->y(),deltax=SecondPt->x()-frstPt->x(),deltay=SecondPt->y()-frstPt->y();
        while(ListLoadingDbID.count()>0)
        {
            Posx+=deltax;
            Posy+=deltay;
            SymbolIdInDB=ListLoadingDbID.at(0);
            if(CurEqualDrawMode==0) SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB);
            else if(CurEqualDrawMode==1) SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SymbolIdInDB);
            QuerySearch.exec(SqlStr);
            if(QuerySearch.next())  SymbolName=QuerySearch.value("Symbol").toString()+".dwg";
            //GetListAllDirSymbols(SymbolName.mid(0,SymbolName.size()-4));
            if(CurEqualDrawMode==0) DealSymbolSpurBlock(Posx,Posy);
            else if(CurEqualDrawMode==1)  DealTerminalBlock(Posx,Posy);
            ListLoadingDbID.removeAt(0);
        }
    }
    FlagAutoConnectLine=OriginalAutoConnect;
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
   // ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
    //更新导航窗口
    if(CurEqualDrawMode==0) emit(UpdateProjectUnits());
    else if(CurEqualDrawMode==1) emit(UpdateProjectTerminals());
}

void formaxwidget::LoadEqualDistance(QList<int> List_DbID,int Mode)//等距绘制
{
qDebug()<<"LoadEqualDistance,List_DbID="<<List_DbID<<",Mode="<<Mode;
    ListLoadingDbID=List_DbID;
    CurEqualDrawMode=Mode;
    QSqlQuery Query = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    for(int i=0;i<List_DbID.count();i++)
    {
        if(Mode==0) SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(List_DbID.at(i));
        else if(Mode==1) SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(List_DbID.at(i));
        Query.exec(SqlStr);
        if(Query.next())
        {
            SymbolName=Query.value("Symbol").toString()+".dwg";
            //判断当前数据库中，是有指定的块名
            IMxDrawDatabase *database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
            IMxDrawBlockTable* blkTable = (IMxDrawBlockTable*)database->querySubObject("GetBlockTable()");
            if (blkTable->Has(SymbolName.mid(0,SymbolName.size()-4)))
            {
                // 已经插入.
                continue;
            }
            //添加块到块表
            QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg
            if(Mode==0)
            {
                if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
                else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
            }
            else if(Mode==1)
                BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
            QFileInfo file(BlkPath);
            if(!file.exists()) return;
            MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4));
            //ListAllDirSymbols.clear();
            //InsertAllDirSymbol(BlkName);
        }
    }
    IsLoadingSymbol=true;
qDebug()<<"118";
    ui->axWidget->dynamicCall("DoCommand(const int&)",118);
}

void formaxwidget::LoadTerminal(QList<int> ListSymbol_ID)
{
    FlagAutoConnectLine=true;
    ListLoadingDbID=ListSymbol_ID;
    //判断选择的子块是否已经绘制
    //在数据库中找到SymbolID对应的符号名称，分为ES2_XXX和SPS_XXX两种
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;

    SymbolIdInDB=ListLoadingDbID.at(0);
    SqlStr= "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(SymbolIdInDB);
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return;
    IsLoadingSymbol=true;
    for(int i=0;i<ListLoadingDbID.count();i++)
    {
        SymbolName=QuerySymbol.value("Symbol").toString()+".dwg";
        //添加块到块表
        QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg
        //if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
        //else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
        BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
        QFileInfo file(BlkPath);
        if(!file.exists()) return;
        MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4));
        //InsertAllDirSymbol(BlkName);
    }
    ui->axWidget->dynamicCall("DoCommand(const int&)",108);
}

void formaxwidget::LoadUnitStamp(QString MultiLibName)
{
    SymbolName=MultiLibName;
    //添加块到块表
    QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg
    BlkPath="C:/TBD/UserData/MultiLib/"+MultiLibName.mid(0,MultiLibName.indexOf("."))+"/"+MultiLibName;
    QFileInfo file(BlkPath);
    if(!file.exists()) return;
    MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4));
    ui->axWidget->dynamicCall("DoCommand(const int&)",127);
}

void formaxwidget::LoadWholeUnit(int UnitID,int Mode)
{
    FlagAutoConnectLine=true;
    //判断选择的元件是否已经绘制某一条子块
    //在数据库中找到SymbolID对应的符号名称，分为ES2_XXX和SPS_XXX两种
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(UnitID)+"' AND Symbol_Handle <> ''";
    QuerySymbol.exec(temp);
    if(QuerySymbol.next())
    {
       QMessageBox::warning(nullptr, "提示", " 无法整体绘制，存在已绘制的功能子块！");
       return;
    }
    UnitIdInDB=UnitID;
    LoadAllUnitMode=Mode;
    //添加块到块表
    temp = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(UnitID)+"' AND Symbol <> ''";
    QuerySymbol.exec(temp);
    while(QuerySymbol.next())
    {
        SymbolName=QuerySymbol.value("Symbol").toString()+".dwg";
        //添加块到块表
        QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg
        if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
        else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
        QFileInfo file(BlkPath);
        if(!file.exists()) return;
        InsertAllDirSymbol(BlkName);
    }
    ui->axWidget->dynamicCall("DoCommand(const int&)",115);
}

void formaxwidget::LoadSymbolSpur(QList<int> ListSymbol_ID)//int SymbolID)
{
    FlagAutoConnectLine=true;
    ListLoadingDbID=ListSymbol_ID;
    //判断选择的子块是否已经绘制
    //在数据库中找到SymbolID对应的符号名称，分为ES2_XXX和SPS_XXX两种
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;

    SymbolIdInDB=ListLoadingDbID.at(0);
    SqlStr= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(SymbolIdInDB);
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return;
    //区分是绘制黑盒还是绘制功能子块
    if((QuerySymbol.value("Symbol_Category").toString()=="组合元件盒子")||(QuerySymbol.value("Symbol_Category").toString()=="PLC盒子"))
    {
        ui->axWidget->dynamicCall("DoCommand(const int&)",116);
        ListLoadingDbID.removeAt(0);
    }
    else
    {
        IsLoadingSymbol=true;
        for(int i=0;i<ListLoadingDbID.count();i++)
        {
            SymbolName=QuerySymbol.value("Symbol").toString()+".dwg";
            //添加块到块表
            QString BlkName=SymbolName.mid(0,SymbolName.size()-4);//去掉.dwg
            if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
            else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
            QFileInfo file(BlkPath);
            if(!file.exists()) return;
            InsertAllDirSymbol(BlkName);
        }
        /*
        if(BlkName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
        else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",BlkPath);
        IMxDrawResbuf *resp=readGlobalVar(GlobalBackAxWidget,"LD_SYMB1LIB_DICITIONARY","LD_SYMB1LIB_XRECORD");
        if(resp!=nullptr)
        {
            BlkResp->RemoveAll();
            BlkResp->AddStringEx("LD_SYMB1LIB_XRECORD",1001);
            for(int i=0;i<resp->Count();i++)
            {
                BlkResp->AddStringEx(resp->AtString(i),1000);
            }
        }*/
        ui->axWidget->dynamicCall("DoCommand(const int&)",106);
    }
}

void formaxwidget::SetTerminalHighLight()
{
    ui->axWidget->dynamicCall("DoCommand(const int&)",117);
}
IMxDrawEntity *EntySymbolSpurHighLight;
void formaxwidget::DoSetSymbolSpurHighLight()
{
    QSqlQuery querySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+DataBaseSymbolID;
    querySymbol.exec(SqlStr);
    if(!querySymbol.next()) return;
    QString Symbol_Handle=querySymbol.value("Symbol_Handle").toString();
    qDebug()<<"Symbol_Handle="<<Symbol_Handle;
    QString InsertionPoint=querySymbol.value("InsertionPoint").toString();
    QStringList ListPosStr=InsertionPoint.split(",");
    if(ListPosStr.count()!=3) return;
    double dCenterX=ListPosStr.at(0).toDouble();
    double dCenterY=ListPosStr.at(1).toDouble();
    ui->axWidget->dynamicCall("ZoomAll()");
    ui->axWidget->dynamicCall("ZoomScale(double)",0.1);
    ui->axWidget->dynamicCall("ZoomCenter(double,double)",dCenterX,dCenterY);

    if(EntySymbolSpurHighLight!=nullptr) EntySymbolSpurHighLight->dynamicCall("Highlight(bool)",false);
    EntySymbolSpurHighLight=(IMxDrawEntity*)ui->axWidget->querySubObject("HandleToObject(const QString)",Symbol_Handle);
    if(EntySymbolSpurHighLight!=nullptr)  EntySymbolSpurHighLight->dynamicCall("Highlight(bool)",true);
}

void formaxwidget::SetSymbolSpurHighLight()
{
    ui->axWidget->dynamicCall("DoCommand(const int&)",107);
}
IMxDrawEntity *EntyTerminalHighLight;
void formaxwidget::DoSetTerminalHighLight()
{
    QSqlQuery queryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID= "+DataBaseTerminalInstanceID;
    queryTerminalInstance.exec(SqlStr);
    if(queryTerminalInstance.next())
    {
        QString Symbol_Handle=queryTerminalInstance.value("Handle").toString();
        qDebug()<<"Symbol_Handle="<<Symbol_Handle;
        QString InsertionPoint=queryTerminalInstance.value("Coordinate").toString();
        QStringList ListPosStr=InsertionPoint.split(",");
        if(ListPosStr.count()!=3) return;
        double dCenterX=ListPosStr.at(0).toDouble();
        double dCenterY=ListPosStr.at(1).toDouble();
        ui->axWidget->dynamicCall("ZoomAll()");
        ui->axWidget->dynamicCall("ZoomScale(double)",0.1);
        ui->axWidget->dynamicCall("ZoomCenter(double,double)",dCenterX,dCenterY);

        if(EntyTerminalHighLight!=nullptr) EntyTerminalHighLight->dynamicCall("Highlight(bool)",false);
        EntyTerminalHighLight=(IMxDrawEntity*)ui->axWidget->querySubObject("HandleToObject(const QString)",Symbol_Handle);
        if(EntyTerminalHighLight!=nullptr)  EntyTerminalHighLight->dynamicCall("Highlight(bool)",true);
    }
}

void formaxwidget::DeleteRecordOfEntity(qlonglong DeleteEntyID)
{
qDebug()<<"DeleteRecordOfEntity,DeleteEntyID="<<DeleteEntyID;
    IMxDrawEntity *BlkDelete= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",DeleteEntyID);
    if(BlkDelete==nullptr) return;
    QString HandleDelete=BlkDelete->dynamicCall("handle()").toString();
    QString SymbolIdForDb=BlkDelete->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();

    // 如果当前删除的不是块引用，尝试获取其所属的块引用，用于同步数据库
    IMxDrawEntity *BlkDeleteForDb = BlkDelete;
    QString ObjName = BlkDelete->dynamicCall("ObjectName()").toString();
    if(ObjName!="McDbBlockReference")
    {
        QVariant ownerIdVar = BlkDelete->dynamicCall("OwnerId()");
        QSet<qlonglong> visitedOwnerIds;
        while(ownerIdVar.isValid())
        {
            qlonglong ownerId = ownerIdVar.toLongLong();
            if(ownerId<=0 || visitedOwnerIds.contains(ownerId)) break;
            visitedOwnerIds.insert(ownerId);
            IMxDrawEntity *OwnerEntity = (IMxDrawEntity*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ownerId);
            if(OwnerEntity==nullptr) break;
            QString ownerName = OwnerEntity->dynamicCall("ObjectName()").toString();
            if(ownerName=="McDbBlockReference")
            {
                BlkDeleteForDb = OwnerEntity;
                HandleDelete=BlkDeleteForDb->dynamicCall("handle()").toString();
                QString DbIdFromOwner=BlkDeleteForDb->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
                if(!DbIdFromOwner.isEmpty()) SymbolIdForDb=DbIdFromOwner;
                break;
            }
            ownerIdVar = OwnerEntity->dynamicCall("OwnerId()");
        }
        if((BlkDeleteForDb!=BlkDelete)&&BlkDeleteForDb->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
        {
            BlkDelete=BlkDeleteForDb;
        }
    }
    //if((BlkDelete->dynamicCall("ObjectName()").toString()!="McDbBlockReference")&&(BlkDelete->dynamicCall("ObjectName()").toString()!="McDbLine")) continue;

    if(BlkDelete->dynamicCall("ObjectName()").toString()=="McDbAttributeDefinition")
    {
       emit(SignalDrawAttrDefDelete(((IMxDrawAttributeDefinition *)BlkDelete)->dynamicCall("Tag()").toString(),DeleteEntyID));
    }
    bool IsBox=false;
    QString BoxText;
    BlkDelete->dynamicCall("GetxDataString2(QString,int)","LD_GROUPCPXRECT_TEXT",0).toString();
    if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")//黑盒
    {
        qDebug()<<"LD_GROUPCPXRECT_TEXT";
        IsBox=true;
        IMxDrawMText *EntyBoxMText=(IMxDrawMText *)ui->axWidget->querySubObject("HandleToObject(const QString)",BlkDelete->dynamicCall("GetxDataString2(QString,int)","LD_GROUPCPXRECT_TEXT",0).toString());
        if(EntyBoxMText!=nullptr)
        {
            BoxText=EntyBoxMText->dynamicCall("Contents()").toString();
            EntyBoxMText->dynamicCall("Erase()");
        }
    }
    BlkDelete->dynamicCall("GetxDataString2(QString,int)","LD_GROUPCPXRECT_XRECT",0).toString();
    if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")//黑盒文字
    {
        qDebug()<<"LD_GROUPCPXRECT_XRECT";
        IsBox=true;
        IMxDrawMText *EntyBoxMText=(IMxDrawMText *)BlkDelete;
        BoxText=EntyBoxMText->dynamicCall("Contents()").toString();
        HandleDelete=BlkDelete->dynamicCall("GetxDataString2(QString,int)","LD_GROUPCPXRECT_XRECT",0).toString();
        qDebug()<<"HandleDelete="<<HandleDelete;
        BlkDelete=(IMxDrawEntity*)ui->axWidget->querySubObject("HandleToObject(const QString)",HandleDelete);
        if(BlkDelete==nullptr) return;
    }
    if(IsBox)//更新黑盒内的功能子块块属性
    {
        qDebug()<<"IsBox";
        IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        //创建过滤对象
        MxDrawResbuf* filter =new MxDrawResbuf();
        filter->AddStringEx("INSERT",5020);
        filter->AddStringEx("LY_Symb2",8);
        //找到polyline内的vertex
        qDebug()<<"BlkDelete="<<BlkDelete->dynamicCall("ObjectName()").toString();
        int VCnt=((IMxDrawPolyline *)BlkDelete)->property("NumVerts").toInt();
        qDebug()<<"VCnt="<<VCnt;
        if(VCnt>=4)
        {
            Pt1=(IMxDrawPoint*)((IMxDrawPolyline *)BlkDelete)->querySubObject("GetPointAt(int)",0);
            Pt2=(IMxDrawPoint*)((IMxDrawPolyline *)BlkDelete)->querySubObject("GetPointAt(int)",2);
            ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, Pt1->asVariant(), Pt2->asVariant(),filter->asVariant());
            for (int i = 0; i < ss->Count(); i++)
            {
                qDebug()<<"i="<<i;
                IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
                if(ent==nullptr) continue;
                if(EntyIsErased(ui->axWidget,ent)) continue;
                qDebug()<<"UpdateBlockAttr,BoxText="<<BoxText;
                UpdateBlockAttr((IMxDrawBlockReference*)ent,"设备标识符(显示)",BoxText);
            }//当前框选的符号处理
        }
    }
    qDebug()<<"更新T_ProjectDatabase的Symbol表";
    //更新T_ProjectDatabase的Symbol表
    QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    bool SymbolFound=false;
    if(HandleDelete!="")
    {
        SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Symbol_Handle='"+HandleDelete+"'";
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next()) SymbolFound=true;
    }
    if((!SymbolFound)&&StrIsNumber(SymbolIdForDb)&&SymbolIdForDb!="")
    {
        SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+SymbolIdForDb;
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next()) SymbolFound=true;
    }
    if(SymbolFound)
    {
        int Symbol_ID=QuerySymbol.value("Symbol_ID").toInt();
        QString SqlStr="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbol.prepare(SqlStr);
        QuerySymbol.bindValue(":Page_ID","");
        QuerySymbol.bindValue(":Symbol_Handle","");
        QuerySymbol.bindValue(":InsertionPoint","");
        QuerySymbol.exec();
        //更新T_ProjectDatabase的Symb2TermInfo表
        QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        SqlStr="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate,ConnDirection=:ConnDirection WHERE Symbol_ID = '"+QString::number(Symbol_ID)+"'";
        QuerySymb2TermInfo.prepare(SqlStr);
        QuerySymb2TermInfo.bindValue(":Conn_Coordinate","");
        QuerySymb2TermInfo.bindValue(":ConnDirection","");
        QuerySymb2TermInfo.exec();
    }
    qDebug()<<"更新T_ProjectDatabase的Symbol表结束";
    //更新T_ProjectDatabase的Terminal表
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle='"+HandleDelete+"'";
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        int TerminalInstanceID=QueryTerminalInstance.value("TerminalInstanceID").toInt();
        SqlStr="DELETE FROM TerminalInstance WHERE TerminalInstanceID = "+QString::number(TerminalInstanceID);
        QueryTerminalInstance.exec(SqlStr);
        /*
        //更新T_ProjectDatabase的TerminalTerm表
        QSqlQuery QueryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        SqlStr="UPDATE TerminalTerm SET Conn_Coordinate=:Conn_Coordinate WHERE Terminal_ID = '"+QString::number(Terminal_ID)+"'";
        QueryTerminalTerm.prepare(SqlStr);
        QueryTerminalTerm.bindValue(":Conn_Coordinate","");
        QueryTerminalTerm.exec();*/
    }

    //更新T_ProjectDatabase的Connector表
    QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
    SqlStr =  "DELETE FROM Connector WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Connector_Handle='"+HandleDelete+"'";
    QueryConnector.exec(SqlStr);

    //更新T_ProjectDatabase的Link表
    QSqlQuery QueryLink=QSqlQuery(T_ProjectDatabase);
    //如果Link有配对则删除配对信息并更新图形
    SqlStr = "SELECT * FROM Link WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Link_Handle='"+HandleDelete+"'";
    QueryLink.exec(SqlStr);
    if(QueryLink.next())
    {
        //更新链接点文字和箭头方向
        QString CounterLink_ID=QueryLink.value("CounterLink_ID").toString();
        emit(UpdateCounterLink(QueryLink.value("CounterLink_ID").toInt(),""));
        SqlStr="UPDATE Link SET CounterLink_ID=:CounterLink_ID WHERE Link_ID = "+CounterLink_ID;
        QueryLink.prepare(SqlStr);
        QueryLink.bindValue(":CounterLink_ID","");
        QueryLink.exec();
    }

    SqlStr =  "DELETE FROM Link WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Link_Handle='"+HandleDelete+"'";
    QueryLink.exec(SqlStr);

    //更新T_ProjectDatabase的Wires表和Cable表
    //确认是Wire还是Cable
    SqlStr="";
    if((BlkDelete->dynamicCall("ObjectName()").toString()=="McDbLine")||(BlkDelete->dynamicCall("ObjectName()").toString()=="McDbBlockReference"))
    {
        SqlStr =  "SELECT * FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle='"+HandleDelete+"'";
    }
    else if(BlkDelete->dynamicCall("ObjectName()").toString()=="McDbMText")
    {
        SqlStr =  "SELECT * FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND TextHandle='"+HandleDelete+"'";
    }
    if(SqlStr!="")
    {
        QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
        QueryWires.exec(SqlStr);
        if(QueryWires.next())
        {
            bool IsCable=false;
            QString Cable_ID=QueryWires.value("Cable_ID").toString();
            if(QueryWires.value("TextHandle").toString()!=""&&(BlkDelete->dynamicCall("ObjectName()").toString()=="McDbLine")) IsCable=true;
            if(BlkDelete->dynamicCall("ObjectName()").toString()=="McDbMText") IsCable=true;
            if(IsCable)//是电缆
            {
                IMxDrawEntity *EntyText=(IMxDrawEntity *)ui->axWidget->querySubObject("HandleToObject(const QString)",QueryWires.value("TextHandle").toString());
                if(EntyText!=nullptr) EntyText->dynamicCall("Erase()");

                QSqlQuery QueryCable=QSqlQuery(T_ProjectDatabase);
                SqlStr =  "DELETE FROM Cable WHERE Cable_ID = "+Cable_ID;
                QueryCable.exec(SqlStr);
                //删除对应的Wire
                SqlStr =  "SELECT * FROM Wires WHERE Cable_ID = '"+Cable_ID+"'";
                QueryWires.exec(SqlStr);
                while(QueryWires.next())
                {
                    QString WireHandle=QueryWires.value("Handle").toString();
                    qDebug()<<"WireHandle="<<WireHandle;
                    IMxDrawEntity *EntyDelete=(IMxDrawEntity *)ui->axWidget->querySubObject("HandleToObject(const QString)",WireHandle);
                    if(EntyDelete!=nullptr) EntyDelete->dynamicCall("Erase()");
                    qDebug()<<"Erase";
                }
                SqlStr =  "DELETE FROM Wires WHERE Cable_ID = '"+Cable_ID+"'";
                QueryWires.exec(SqlStr);
            }
            else//是连线定义
            {
                QString WireHandle=QueryWires.value("Handle").toString();
                IMxDrawEntity *EntyDelete=(IMxDrawEntity *)ui->axWidget->querySubObject("HandleToObject(const QString)",WireHandle);
                if(EntyDelete!=nullptr) EntyDelete->dynamicCall("Erase()");
                SqlStr =  "DELETE FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle='"+HandleDelete+"'";
                QueryWires.exec(SqlStr);
            }
        }
    }
    if(!EntyIsErased(ui->axWidget,BlkDelete)) BlkDelete->dynamicCall("Erase()");
}

QString formaxwidget::GetSymbolTag(IMxDrawBlockReference *BlkModifyed)
{
    if(GetBlockAttrTextString(BlkModifyed,"设备标识符(显示)")!="") return GetBlockAttrTextString(BlkModifyed,"设备标识符(显示)");

    //找到黑盒的代号
    double posx=((IMxDrawPoint *)BlkModifyed->querySubObject("Position()"))->x();
    double posy=((IMxDrawPoint *)BlkModifyed->querySubObject("Position()"))->y();
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    MxDrawResbuf* filter =new MxDrawResbuf();
    filter->AddStringEx("LWPOLYLINE",5020);
    filter->AddStringEx("0",8);
    ss->dynamicCall("AllSelect(QVariant)",filter->asVariant());
qDebug()<<"AllSelect,ss->Count()="<<ss->Count();
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(ui->axWidget,ent)) continue;
        ent->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString();
        if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
        {
            //查看Symbol是否在黑盒内部
            int VCnt=((IMxDrawPolyline *)ent)->property("NumVerts").toInt();
 qDebug()<<"VCnt="<<VCnt;
            if(VCnt>=4)
            {
                Pt1=(IMxDrawPoint*)((IMxDrawPolyline *)ent)->querySubObject("GetPointAt(int)",0);
                Pt2=(IMxDrawPoint*)((IMxDrawPolyline *)ent)->querySubObject("GetPointAt(int)",2);
                bool InBoxRange=true;
                if(((posx<Pt1->x())&&(posx<Pt2->x()))||((posx>Pt1->x())&&(posx>Pt2->x()))) InBoxRange=false;
                if(((posy<Pt1->y())&&(posy<Pt2->y()))||((posy>Pt1->y())&&(posy>Pt2->y()))) InBoxRange=false;
                if(InBoxRange)
                {
                    QString MTextHandle=ent->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString();
                    QString StrMText=((IMxDrawMText *)ui->axWidget->querySubObject("HandleToObject(const QString)",MTextHandle))->Contents();
                    return StrMText;
                    //return StrMText.mid(StrMText.lastIndexOf("-")+1,StrMText.count()-StrMText.lastIndexOf("-")-1);
                }// end of if(InBoxRange)
            }//end of if(VCnt>=4)
        }//end of if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
    }
    return "";
}
void formaxwidget::PasteEnty(qlonglong EntyID)
{
    IMxDrawEntity *EntyModifyed= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",EntyID);
    if(EntyModifyed->dynamicCall("ObjectName()").toString()!="McDbBlockReference") return;
    IMxDrawBlockReference *BlkModifyed=(IMxDrawBlockReference *)EntyModifyed;
    if(BlkModifyed->dynamicCall("GetBlockName()").toString().contains("ES2_")||BlkModifyed->dynamicCall("GetBlockName()").toString().contains("SPS_"))//功能子块或端子
    {
        if(BlkModifyed->dynamicCall("GetxDataString2(QString,int)","LD_SYMB2_SPECIAL",0).toString()=="端子")
        {

        }
        else
        {
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
            QuerySymbol.exec(SqlStr);
            if(QuerySymbol.next())
            {
                int Equipment_ID;
                QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
                SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
                QueryEquipment.exec(SqlStr);
                if(QueryEquipment.next())
                {
                    Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
                    //如果当前Symbol的DbId对应的数据库中Symbol_Handle为空，则为剪切，更新数据库即可，如果Symbol_Handle不为空，则插入新记录
                    if(QuerySymbol.value("Symbol_Handle").toString()=="")
                    {
                        UpdateDBSymbolInfoByBlkEnty(ui->axWidget,BlkModifyed,QString::number(Page_IDInDB),QString::number(Equipment_ID));
                        emit(SignalUpdateSpur(BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toInt()));
                    }
                    else
                      emit(SignalUpdateSpur(InsertDBSymbolInfoByBlkEnty(ui->axWidget,BlkModifyed,QString::number(Page_IDInDB),QString::number(Equipment_ID))));
                }
            }
        }
    }
}

//撤销操作，可能是撤销删除，撤销更改代号（含合并）或端号，撤销移动
void formaxwidget::UndoEnty(QString EntyHandle)
{
    IMxDrawEntity *EntyModifyed= (IMxDrawEntity*)ui->axWidget->querySubObject("HandleToObject(const QString)",EntyHandle);
    if(EntyModifyed->dynamicCall("ObjectName()").toString()!="McDbBlockReference") return;
    IMxDrawBlockReference *BlkModifyed=(IMxDrawBlockReference *)EntyModifyed;
qDebug()<<"undo enty dbid="<<BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
    if(BlkModifyed->dynamicCall("GetBlockName()").toString().contains("ES2_")||BlkModifyed->dynamicCall("GetBlockName()").toString().contains("SPS_"))//功能子块或端子
    {
        if(BlkModifyed->dynamicCall("GetxDataString2(QString,int)","LD_SYMB2_SPECIAL",0).toString()=="端子")
        {

        }
        else//是功能子块
        {
            //如果当前符号被删除，则是撤销插入元件或绘制功能子块,删除数据库中Symbol和Symb2TermInfo
            //如果符号IsErased,如果该符号在数据库中不存在，则绘制该符号，如果该符号在数据库中存在，则删除该符号
            if(EntyIsErased(ui->axWidget,EntyModifyed))
            {
                QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                QString SqlStr;
                if(StrIsNumber(BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString()))
                    SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
                else
                    SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Symbol_Handle = '"+EntyHandle+"'";
                QuerySearch.exec(SqlStr);
                if(QuerySearch.next())
                {
                    qDebug()<<"UndoEnty,EntyIsErased,record existed";
                    DeleteRecordOfEntity(EntyModifyed->ObjectID());
                    return;
                }
                else
                {
                    qDebug()<<"UndoEnty,EntyIsErased,record not existed";
                    for(int i=ListDeletedEntyInfo.count()-1;i>=0;i--)
                    {
                        qDebug()<<"EntyHandle="<<EntyHandle;
qDebug()<<"ListDeletedEntyInfo["<<i<<"]="<<ListDeletedEntyInfo.at(i);
                        QStringList ListEntyInfo=ListDeletedEntyInfo.at(i).split("￤");
                        if(ListEntyInfo.at(0)==EntyHandle)
                        {
                            qlonglong lID=ui->axWidget->dynamicCall("DrawEntity(QAxObject*)",EntyModifyed->asVariant()).toLongLong();
                            EntyModifyed=(IMxDrawEntity*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
                            BlkModifyed=(IMxDrawBlockReference *)EntyModifyed;
                            BlkModifyed->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,ListEntyInfo.at(1));
                            BlkModifyed->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,ListEntyInfo.at(2));
                            BlkModifyed->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,ListEntyInfo.at(3));
                            BlkModifyed->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Remark",0,ListEntyInfo.at(4));
                            for(int j=0;j<(ListEntyInfo.count()-5)/2;j++)
                            {
                               FindAttrDefAndAddAttrToBlock(ui->axWidget,BlkModifyed,ListEntyInfo.at(5+2*j),ListEntyInfo.at(5+2*j+1));
                            }
                            break;
                        }
                    }
                }
            }
 qDebug()<<"UndoEnty,EntyIs not Erased";
            //根据元件代号确定Equipment_ID，如果当前的元件代号在数据库中不存在，则根据RemovedUnitsInfo插入元件
            int Equipment_ID;
            QString CurSymbolTag=GetSymbolTag(BlkModifyed);
 qDebug()<<"CurSymbolTag="<<CurSymbolTag;
            QString StrGaoceng="";
            if(CurSymbolTag.contains("="))
            {
                StrGaoceng=CurSymbolTag.mid(CurSymbolTag.indexOf("=")+1,CurSymbolTag.indexOf("+")-CurSymbolTag.indexOf("=")-1);
            }
            QString StrPos="";
            if(CurSymbolTag.contains("+"))
            {
                StrPos=CurSymbolTag.mid(CurSymbolTag.indexOf("+")+1,CurSymbolTag.indexOf("-")-CurSymbolTag.indexOf("+")-1);
            }
            QString ProjectStructure_ID;
            if(!CurSymbolTag.contains("=")) GetPageGaocengAndPos(Page_IDInDB,StrGaoceng,StrPos);
            ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
 qDebug()<<"StrGaoceng="<<StrGaoceng<<",StrPos="<<StrPos<<",ProjectStructure_ID="<<ProjectStructure_ID;
            CurSymbolTag=CurSymbolTag.mid(CurSymbolTag.lastIndexOf("-")+1,CurSymbolTag.count()-CurSymbolTag.lastIndexOf("-")-1);
  qDebug()<<"CurSymbolTag="<<CurSymbolTag;
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+CurSymbolTag+"' AND ProjectStructure_ID = '"+ProjectStructure_ID+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())//当前的元件代号在数据库存在，确定Equipment_ID
            {
                Equipment_ID=QueryEquipment.value("Equipment_ID").toInt();
  qDebug()<<"当前的元件代号在数据库中存在，Equipment_ID="<<Equipment_ID;
            }
            else//当前的元件代号在数据库中不存在，可能是元件代号被修改或者元件被删除，如果DbID对应的Symbol也不存在，则根据RemovedUnitsInfo插入元件
            {
qDebug()<<"当前的元件代号在数据库中不存在";
                QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                if(StrIsNumber(BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString()))
                    SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
                else
                    SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Symbol_Handle = '"+EntyHandle+"'";
                QuerySymbol.exec(SqlStr);
                if(!QuerySymbol.next())
                {
qDebug()<<"DbID对应的Symbol也不存在，则根据RemovedUnitsInfo插入元件，RemovedUnitsInfo.count()="<<RemovedUnitsInfo.count();
                    //DT,ProjectStructure_ID,Type,Spec,Eqpt_Category,Name,Desc,PartCode,OrderNum,Factory,Remark,TVariable,TModel
                     for(int i=RemovedUnitsInfo.count()-1;i>=0;i--)
                     {
                      qDebug()<<RemovedUnitsInfo.at(i).split(",").at(0);
                      qDebug()<<RemovedUnitsInfo.at(i).split(",").at(1);
                         if((RemovedUnitsInfo.at(i).split(",").at(0)==CurSymbolTag)&&(RemovedUnitsInfo.at(i).split(",").at(1)==ProjectStructure_ID))
                         {
                             Equipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
                             //更新T_ProjectDatabase数据库的Equipment表
                             QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                             QString tempSQL = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Spec,Eqpt_Category,Name,Desc,PartCode,OrderNum,Factory,Remark,TVariable,TModel)"
                                               "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Spec,:Eqpt_Category,:Name,:Desc,:PartCode,:OrderNum,:Factory,:Remark,:TVariable,:TModel)");
                             QueryVar.prepare(tempSQL);
                             QueryVar.bindValue(":Equipment_ID",Equipment_ID);
                             QueryVar.bindValue(":DT",RemovedUnitsInfo.at(i).split(",").at(0));
                             QueryVar.bindValue(":ProjectStructure_ID",RemovedUnitsInfo.at(i).split(",").at(1));
                             QueryVar.bindValue(":Type",RemovedUnitsInfo.at(i).split(",").at(2));
                             QueryVar.bindValue(":Spec",RemovedUnitsInfo.at(i).split(",").at(3));
                             QueryVar.bindValue(":Eqpt_Category",RemovedUnitsInfo.at(i).split(",").at(4));//普通元件还是PLC元件
                             QueryVar.bindValue(":Name",RemovedUnitsInfo.at(i).split(",").at(5));
                             QueryVar.bindValue(":Desc",RemovedUnitsInfo.at(i).split(",").at(6));
                             QueryVar.bindValue(":PartCode",RemovedUnitsInfo.at(i).split(",").at(7));
                             QueryVar.bindValue(":OrderNum",RemovedUnitsInfo.at(i).split(",").at(8));
                             QueryVar.bindValue(":Factory",RemovedUnitsInfo.at(i).split(",").at(9));
                             QueryVar.bindValue(":Remark",RemovedUnitsInfo.at(i).split(",").at(10));
                             QueryVar.bindValue(":TVariable",RemovedUnitsInfo.at(i).split(",").at(11));
                             QueryVar.bindValue(":TModel",RemovedUnitsInfo.at(i).split(",").at(12));
                             QueryVar.exec();
                             break;
                         }
                     }
                }
            }//end of //当前的元件代号在数据库中不存在，根据RemovedUnitsInfo插入元件
            //更新T_ProjectDatabase的Symbol表
qDebug()<<"DbId="<<BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            if(StrIsNumber(BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString()))
                SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+BlkModifyed->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
            else
                SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Symbol_Handle = '"+EntyHandle+"'";
            QuerySymbol.exec(SqlStr);
            //注意这里如果数据库的Handle和BlkModifyed的Handle不同，则是粘贴，在元件下插入一条功能子块
            if(QuerySymbol.next())//Symbol记录存在，为符号修改，则更新记录，需要查看数据库中Symbol对应的元件代号与当前的元件代号是否相同，如果不同则改成当前的元件代号对应的元件
            {
qDebug()<<"记录存在则更新记录";
                QString UnitDTInDB;
                SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
                QueryEquipment.exec(SqlStr);
                if(QueryEquipment.next())  UnitDTInDB=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();
                QString TotalSymbolTag=CurSymbolTag;
                TotalSymbolTag="="+StrGaoceng+"+"+StrPos+"-"+CurSymbolTag;
qDebug()<<"TotalSymbolTag="<<TotalSymbolTag+",UnitDTInDB="<<UnitDTInDB;
                if(TotalSymbolTag==UnitDTInDB)//数据库中Symbol对应的元件代号与当前的元件代号相同，当前操作为撤销符号属性修改
                {
                    Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
                    UpdateDBSymbolInfoByBlkEnty(ui->axWidget,BlkModifyed,QString::number(Page_IDInDB),QString::number(Equipment_ID));
                }
                else//数据库中Symbol对应的元件代号与当前的元件代号不同，当前操作为撤销修改元件代号,这里可能存在其他图纸中存在联动被修改元件代号的符号
                {
 qDebug()<<"当前操作为撤销修改元件代号";
                    //更新T_ProjectDatabase数据库的Equipment表
                    //如果Equipment_ID与QuerySymbol.value("Equipment_ID").toString()不同，则删除QuerySymbol.value("Equipment_ID").toString()，否则更新QuerySymbol.value("Equipment_ID").toString()
                    if(Equipment_ID!=QuerySymbol.value("Equipment_ID").toInt())//Equipment_ID与QuerySymbol.value("Equipment_ID").toString()不同，则删除QuerySymbol.value("Equipment_ID").toString()
                    {
                        QSqlQuery QueryEquipmentDelete = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr="DELETE FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
                        QueryEquipmentDelete.exec(SqlStr);
                        UpdateDBSymbolInfoByBlkEnty(ui->axWidget,BlkModifyed,QString::number(Page_IDInDB),QString::number(Equipment_ID));
                    }
                    else//Equipment_ID与QuerySymbol.value("Equipment_ID").toString()相同，更新QuerySymbol.value("Equipment_ID").toString()
                    {
                         Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
                         QSqlQuery QueryEquipmentUpdate = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                         SqlStr="UPDATE Equipment SET DT=:DT,ProjectStructure_ID=:ProjectStructure_ID WHERE Equipment_ID = "+QString::number(Equipment_ID);
                         QueryEquipmentUpdate.prepare(SqlStr);
                         QueryEquipmentUpdate.bindValue(":DT",CurSymbolTag);
                         QueryEquipmentUpdate.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
                         QueryEquipmentUpdate.exec();
                    }

                    //查找其他图纸中当前元件的功能子块，修改元件代号
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"' AND Page_ID <> '"+QString::number(Page_IDInDB)+"'";
                    QuerySearch.exec(SqlStr);
                    while(QuerySearch.next())
                    {
                        if(QuerySearch.value("Page_ID").toString()=="") continue;
                        emit(SignalUpdateDwgBlkTagByPage_ID(QuerySearch.value("Page_ID").toInt(),QuerySearch.value("Symbol_Handle").toString(),TotalSymbolTag,QueryEquipment.value("ProjectStructure_ID").toString()));
                    }
                }
            }//end of if(QuerySymbol.next())
            else//如果Symbol记录不存在(当前操作为撤销删除功能子块或撤销删除元件)则插入记录，
            {
 qDebug()<<"Symbol记录不存在(功能子块被删除或者元件被删除)则插入记录";
                InsertDBSymbolInfoByBlkEnty(ui->axWidget,BlkModifyed,QString::number(Page_IDInDB),QString::number(Equipment_ID));
            }
        }//end of //是功能子块
    }//功能子块或端子
}
//如果是粘贴，需要更新DbID，可以通过数据库的Handle和当前Handle不同来判断是粘贴
void formaxwidget::on_axWidget_ObjectModifyed(const qlonglong &lId, bool isErase)
{
//qDebug()<<"on_axWidget_ObjectModifyed";
    if(IsDoingCommand) return;
    for(int i=0;i<ListSelectEntys.count();i++)
    {
        if(ListSelectEntys.at(i)->dynamicCall("ObjectID()").toLongLong()==lId) return;
    }
    IMxDrawEntity *EntyAppend= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lId);
    //if(EntyAppend->dynamicCall("ObjectName()").toString()!="McDbBlockReference") return;
    ListSelectEntys.append(EntyAppend);
    qDebug()<<"ListSelectEntys append,type="<<EntyAppend->dynamicCall("ObjectName()").toString();
    return;
}
void formaxwidget::EntyGridEdit(qlonglong EntyID)
{
    IMxDrawEntity *EntyMove= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",EntyID);
    qDebug()<<"ObjectName="<<EntyMove->dynamicCall("ObjectName()").toString();
    if(EntyMove->dynamicCall("ObjectName()").toString()!="McDbBlockReference") return;
    IMxDrawBlockReference *BlkMove=(IMxDrawBlockReference *)EntyMove;
    //更新T_ProjectDatabase的Symbol表
    QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Symbol_Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
    QuerySymbol.exec(SqlStr);
    if(QuerySymbol.next())
    {
        int Symbol_ID=QuerySymbol.value("Symbol_ID").toInt();
        emit(SignalUpdateSpur(Symbol_ID));
        SqlStr="UPDATE Symbol SET InsertionPoint=:InsertionPoint WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbol.prepare(SqlStr);
        QString InsertionPoint;
        InsertionPoint=QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QuerySymbol.bindValue(":InsertionPoint",InsertionPoint);
        QuerySymbol.exec();
        //更新T_ProjectDatabase的Symb2TermInfo表
        QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QString::number(Symbol_ID)+"'";
        QuerySymb2TermInfo.exec(SqlStr);
        while(QuerySymb2TermInfo.next())
        {
            QString ConnNum_Logic=QuerySymb2TermInfo.value("ConnNum_Logic").toString();
            int Symb2TermInfo_ID=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toInt();
            QSqlQuery QuerySymb2TermInfoUpdate=QSqlQuery(T_ProjectDatabase);
            InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,ConnNum_Logic)->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,ConnNum_Logic)->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            SqlStr="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate WHERE Symb2TermInfo_ID = "+QString::number(Symb2TermInfo_ID);
            QuerySymb2TermInfoUpdate.prepare(SqlStr);
            QuerySymb2TermInfoUpdate.bindValue(":Conn_Coordinate",InsertionPoint);
            QuerySymb2TermInfoUpdate.exec();
        }
    }

    //更新T_ProjectDatabase的Terminal表
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        int TerminalInstanceID=QueryTerminalInstance.value("TerminalInstanceID").toInt();
        emit(SignalUpdateTerminal(QueryTerminalInstance.value("Terminal_ID").toInt()));
        SqlStr="UPDATE TerminalInstance SET Coordinate=:Coordinate WHERE TerminalInstanceID = "+QString::number(TerminalInstanceID);
        QueryTerminalInstance.prepare(SqlStr);
        QString InsertionPoint;
        InsertionPoint=QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryTerminalInstance.bindValue(":Coordinate",InsertionPoint);
        QueryTerminalInstance.exec();
        /*
        //更新T_ProjectDatabase的TerminalTerm表
        QSqlQuery QueryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+QString::number(Terminal_ID)+"'";
        QueryTerminalTerm.exec(SqlStr);
        while(QueryTerminalTerm.next())
        {
            QString ConnNum_Logic=QueryTerminalTerm.value("ConnNum_Logic").toString();
            int TerminalTerm_ID=QueryTerminalTerm.value("TerminalTerm_ID").toInt();
            QSqlQuery QueryTerminalTermInfoUpdate=QSqlQuery(T_ProjectDatabase);
            InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,ConnNum_Logic)->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,ConnNum_Logic)->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            SqlStr="UPDATE TerminalTerm SET Conn_Coordinate=:Conn_Coordinate WHERE TerminalTerm_ID = "+QString::number(TerminalTerm_ID);
            QueryTerminalTermInfoUpdate.prepare(SqlStr);
            QueryTerminalTermInfoUpdate.bindValue(":Conn_Coordinate",InsertionPoint);
            QueryTerminalTermInfoUpdate.exec();
        }*/
    }

    //更新T_ProjectDatabase的Connector表
    QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Connector WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Connector_Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
    QueryConnector.exec(SqlStr);
    if(QueryConnector.next())
    {
        SqlStr="UPDATE Connector SET InsertionPoint=:InsertionPoint,C_Coordinate=:C_Coordinate,G_Coordinate=:G_Coordinate,Coordinate_1=:Coordinate_1,Coordinate_2=:Coordinate_2,Coordinate_3=:Coordinate_3 WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Connector_Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
        QueryConnector.prepare(SqlStr);
        QString InsertionPoint=QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryConnector.bindValue(":InsertionPoint",InsertionPoint);
        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"C")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"C")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryConnector.bindValue(":C_Coordinate",InsertionPoint);

        if(BlkMove->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_CR"))
        {
            InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"G")->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"G")->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            QueryConnector.bindValue(":G_Coordinate",InsertionPoint);
        }
        else QueryConnector.bindValue(":G_Coordinate","");

        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"1")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"1")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryConnector.bindValue(":Coordinate_1",InsertionPoint);

        if(!BlkMove->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_CO"))
        {
            InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"2")->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"2")->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            QueryConnector.bindValue(":Coordinate_2",InsertionPoint);
        }
        else QueryConnector.bindValue(":Coordinate_2","");

        if(BlkMove->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_BR"))
        {
            InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"3")->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"3")->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            QueryConnector.bindValue(":Coordinate_3",InsertionPoint);
        }
        else QueryConnector.bindValue(":Coordinate_3","");
        QueryConnector.exec();
    }


    //更新T_ProjectDatabase的Link表
    QSqlQuery QueryLink=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Link WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Link_Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
qDebug()<<"QueryLink SqlStr="<<SqlStr;
    QueryLink.exec(SqlStr);
    if(QueryLink.next())
    {
        SqlStr="UPDATE Link SET InsertionPoint=:InsertionPoint,Coordinate_1=:Coordinate_1,C_Coordinate=:C_Coordinate WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Link_Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
qDebug()<<"QueryLink UPDATE SqlStr="<<SqlStr;
        QueryLink.prepare(SqlStr);
        QString InsertionPoint=QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryLink.bindValue(":InsertionPoint",InsertionPoint);
        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"1")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"1")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryLink.bindValue(":Coordinate_1",InsertionPoint);

        InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"C")->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkMove,"C")->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryLink.bindValue(":C_Coordinate",InsertionPoint);
        QueryLink.exec();
    }

    //更新T_ProjectDatabase的Wires表
    QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
    QueryWires.exec(SqlStr);
    if(QueryWires.next())
    {
        SqlStr="UPDATE Wires SET Position=:Position WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle='"+BlkMove->dynamicCall("handle()").toString()+"'";
        QueryWires.prepare(SqlStr);
        QString InsertionPoint=QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->x(),'f',0)+".000000";
        InsertionPoint+=","+QString::number(((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->y(),'f',0)+".000000";
        InsertionPoint+=",0.000000";
        QueryWires.bindValue(":Position",InsertionPoint);
        QueryWires.exec();
    }
}

void formaxwidget::on_axWidget_CommandWillStart(const QString &sCmdName)
{
qDebug()<<"on_axWidget_CommandWillStart,sCmdName"<<sCmdName;
     ListSelectEntys.clear();

     if((sCmdName=="GridEdit")||(sCmdName=="Mx_PasteClip"))
     {
         ListInitGridEditPos.clear();
         DoingGridEdit=true;
         for(int i=0;i<RespSelectedModifyId->dynamicCall("Count()").toInt();i++)
         {
             IMxDrawEntity *EntyMove= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespSelectedModifyId->dynamicCall("AtObjectId(int)",i).toLongLong());
             if(EntyIsErased(ui->axWidget,EntyMove)) continue;
             if(EntyMove->dynamicCall("ObjectName()").toString()!="McDbBlockReference") continue;
             //记录初始位置
             ListInitGridEditPos.append((IMxDrawPoint *)EntyMove->querySubObject("Position()"));           
         }
     }
qDebug()<<"on_axWidget_CommandWillStart,over";
}

void formaxwidget::on_axWidget_CommandEnded(const QString &sCmdName)
{
    //根据当前执行的指令更新数据库   
    LastCommandName=sCmdName;
    qDebug()<<"on_axWidget_CommandEnded,sCmdName"<<sCmdName;

    bool hasNewConnectLine = false;
    for (int i = 0; i < ListSelectEntys.count(); ++i)
    {
        IMxDrawEntity *enty = ListSelectEntys.at(i);
        if(enty==nullptr) continue;
        if(EntyIsErased(ui->axWidget,enty)) continue;
        if(enty->dynamicCall("ObjectName()").toString()!="McDbLine") continue;
        if(enty->dynamicCall("Layer()").toString()!="CONNECT") continue;
        const QString lineHandle = enty->dynamicCall("handle()").toString();
        if(lineHandle.isEmpty()) continue;
        QSqlQuery queryCheck(T_ProjectDatabase);
        queryCheck.prepare("SELECT 1 FROM Line WHERE Wires_Handle = ? LIMIT 1");
        queryCheck.bindValue(0, lineHandle);
        if(queryCheck.exec() && !queryCheck.next())
        {
            hasNewConnectLine = true;
            break;
        }
    }
    if(sCmdName=="MXOCXSYS_ImpMxDrawXCommand")
    {
        if(FlagSetSymbolSpurHighLight) ui->axWidget->dynamicCall("DoCommand(const int&)",107);
        FlagSetSymbolSpurHighLight=false;
        if(FlagSetTerminalHighLight) ui->axWidget->dynamicCall("DoCommand(const int&)",117);
        FlagSetTerminalHighLight=false;
        ListSelectEntys.clear();
        if(FlagNewLib) emit(SignalSelectDone(1));
        FlagNewLib=false;
        emit(SignalSetCurMdiActive());       
        //if(FirstOpen) InitAxwidget();
        //FirstOpen=false;
    }
    if(sCmdName=="MXOCXSYS_CommandInImp")//保存完成
    {
        if(WaitingForSaveDwg)
        {
            WaitingForSaveDwg=false;
            IsSavedBeforeClose=true;
            ui->axWidget->dynamicCall("DoCommand(const int&)",122);
            return;
        }
    }

    if((sCmdName=="Mx_DeleteHotKey")||(sCmdName=="Mx_CutClip"))
    {
        qDebug()<<"Mx_DeleteHotKey||Mx_CutClip";
        IsDoingCommand=true;
        //for(int i=0;i<ListSelectEntys.count();i++)
        for(int i=0;i<RespSelectedModifyId->dynamicCall("Count()").toInt();i++)
            DeleteRecordOfEntity(RespSelectedModifyId->dynamicCall("AtObjectId(int)",i).toLongLong());
        ListSelectEntys.clear();
        emit(UpdateProjectUnits());
        emit(UpdateProjectTerminals());
        IsDoingCommand=false;
    }    
    else if(sCmdName=="GridEdit")
    {
        qDebug()<<"GridEdit";
        DoingGridEdit=false;
        IsDoingCommand=true;
qDebug()<<"RespSelectedModifyId count="<<RespSelectedModifyId->dynamicCall("Count()").toInt();
        for(int i=0;i<RespSelectedModifyId->dynamicCall("Count()").toInt();i++)
        {

            IMxDrawEntity *EntyMove= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespSelectedModifyId->dynamicCall("AtObjectId(int)",i).toLongLong());
            if(EntyIsErased(ui->axWidget,EntyMove)) continue;
            if(EntyMove->dynamicCall("ObjectName()").toString()!="McDbBlockReference") continue;
            IMxDrawBlockReference *BlkMove=(IMxDrawBlockReference *)EntyMove;
            IMxDrawPoint *PtInputCursor=(IMxDrawPoint *)ui->axWidget->querySubObject("GetInputCursorPos()");
            double Posx=PtInputCursor->x();
            double Posy=PtInputCursor->y();
            PutCursorInGrid(0,Posx,Posy);
            PtInputCursor->setX(Posx);
            PtInputCursor->setY(Posy);
            BlkMove->dynamicCall("GetxDataString2(QString,QString)","DbId",0).toString();
            if(ui->axWidget->dynamicCall("IsOk()").toString()=="true")
            {
                if(CheckBlackBox(ui->axWidget,Posx,Posy,BlkMove->dynamicCall("GetxDataString2(QString,QString)","DbId",0).toInt())<0)
                {
                      BlkMove->dynamicCall("SetPosition(QAxObject*)",ListInitGridEditPos.at(i)->asVariant());
                      continue;
                }
            }

            if(!IsDoingSymbolEdit)
            {
                Posx=((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->x();
                Posy=((IMxDrawPoint *)BlkMove->querySubObject("Position()"))->y();
                PutCursorInGrid(1,Posx,Posy);
                PtInputCursor->setX(Posx);
                PtInputCursor->setY(Posy);
                BlkMove->dynamicCall("SetPosition(QAxObject*)",PtInputCursor->asVariant());
            }

            EntyGridEdit(RespSelectedModifyId->dynamicCall("AtObjectId(int)",i).toLongLong());
        }
        ListSelectEntys.clear();
        IsDoingCommand=false;
    }
    else if(sCmdName=="U")//撤销
    {
        qDebug()<<"do U,ListSelectEntys.count()="<<ListSelectEntys.count();
        IsDoingCommand=true;
        for(int i=0;i<ListSelectEntys.count();i++)
        {
            qDebug()<<"handle="<<ListSelectEntys.at(i)->dynamicCall("handle()").toString()<<"iserased="<<EntyIsErased(ui->axWidget,ListSelectEntys.at(i));
            IMxDrawEntity *EntyUndo= ListSelectEntys.at(i);
            if(EntyUndo->dynamicCall("ObjectName()").toString()!="McDbBlockReference") continue;
            UndoEnty(ListSelectEntys.at(i)->handle());
            IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)EntyUndo;
            BlkEnty->dynamicCall("AssertWriteEnabled()");
        }
        ListSelectEntys.clear();
        emit(UpdateProjectUnits());
        emit(UpdateProjectTerminals());
        IsDoingCommand=false;
    }
    else if(sCmdName=="Mx_PasteClip")//粘贴
    {
 qDebug()<<"do Mx_PasteClip,ListSelectEntys.count()="<<ListSelectEntys.count();
        IsDoingCommand=true;
        DoingGridEdit=false;
        for(int i=0;i<ListSelectEntys.count();i++)
        {
            IMxDrawEntity *EntyPaste= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",ListSelectEntys.at(i)->dynamicCall("ObjectID()").toLongLong());
            if(EntyIsErased(ui->axWidget,EntyPaste)) continue;
            IMxDrawBlockReference *BlkPaste=(IMxDrawBlockReference *)EntyPaste;
            IMxDrawPoint *PtInputCursor=(IMxDrawPoint *)ui->axWidget->querySubObject("GetInputCursorPos()");
            double Posx=PtInputCursor->x();
            double Posy=PtInputCursor->y();
            PutCursorInGrid(0,Posx,Posy);
            PtInputCursor->setX(Posx);
            PtInputCursor->setY(Posy);
            BlkPaste->dynamicCall("GetxDataString2(QString,QString)","DbId",0).toString();
            if(ui->axWidget->dynamicCall("IsOk()").toString()!="true") continue;
            if(CheckBlackBox(ui->axWidget,Posx,Posy,BlkPaste->dynamicCall("GetxDataString2(QString,QString)","DbId",0).toInt())<0)
            {
                BlkPaste->dynamicCall("Erase()");
                continue;
            }
            else
            {
                 //根据坐标位置偏移设置被复制的块的位置
                if(!IsDoingSymbolEdit)
                {
                    Posx=((IMxDrawPoint *)BlkPaste->querySubObject("Position()"))->x();
                    Posy=((IMxDrawPoint *)BlkPaste->querySubObject("Position()"))->y();
                    PutCursorInGrid(1,Posx,Posy);
                    PtInputCursor->setX(Posx);
                    PtInputCursor->setY(Posy);
                    BlkPaste->dynamicCall("SetPosition(QAxObject*)",PtInputCursor->asVariant());
                }
            }
            PasteEnty(ListSelectEntys.at(i)->dynamicCall("ObjectID()").toLongLong());
        }
        ListSelectEntys.clear();
        emit(UpdateProjectUnits());
        emit(UpdateProjectTerminals());
        IsDoingCommand=false;
    }
    else
    {
        qDebug()<<"else";
        ListSelectEntys.clear();
    }

    if(hasNewConnectLine && Page_IDInDB>0)
    {
        if(!dwgFileName.isEmpty())
        {
            ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
        }
        emit(ConnectLinesChanged(Page_IDInDB));
    }
//qDebug()<<"END";
}

//在执行粘贴、撤销等操作时，遍历当前dwg的块，更新对应的数据库
void formaxwidget::UpdateBlkDB(int Mode)//0:粘贴 1：撤销 2：剪切
{
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT",5020);
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    for(int i=0;i<Cnt;i++)
    {
       IMxDrawBlockReference *BlkEnty = (IMxDrawBlockReference*)ss1->querySubObject("Item(int)",i);
       if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)BlkEnty)) continue;//去除erase的实体
       if(BlkEnty->dynamicCall("Layer()").toString()=="LY_Symb2")//元件子块或者端子
       {         
           //（撤销修改代号操作并合并操作）如果Symbol数据库中存在该符号，则检查符号代号在Equipment中是否存在，如果Equipment中不存在该代号，则在dwg的字典中查找该符号的型号并更新Equipment数据库和Symbol中的Equipment_ID
           //（撤销移动、修改代号无合并操作）如果Symbol数据库中存在该符号，则检查符号代号在Equipment中是否存在，如果Equipment中存在该代号,则检查Symbol数据库的Equipment_ID是否正确，检查Symbol的InsertionPoint是否正确，如果InsertionPoint不正确则更新Symbol对应的Symb2TermInfo
           //（复制粘贴操作）如果Symbol数据库中不存在该符号，则检查符号代号在Equipment中是否存在，如果Equipment中存在该代号,则根据块拓展数据中的DbId更新Symbol表
           //（撤销删除操作）如果Symbol数据库中不存在该符号，则检查符号代号在Equipment中是否存在，如果Equipment中不存在该代号,则在dwg的字典中查找该符号的型号并更新Equipment数据库和Symbol表
           //撤销粘贴操作
           //撤销添加子块操作
           if(Mode==0)//复制粘贴操作
           {
               if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("ES2_")||BlkEnty->dynamicCall("GetBlockName()").toString().contains("SPS_"))
               {
                   QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
                   QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+BlkEnty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
                   QuerySymbol.exec(SqlStr);
                   if(QuerySymbol.next())
                   {
                       QString TagStr=GetBlockAttrTextString(BlkEnty,"设备标识符(显示)");
                       if(TagStr.contains("-")) TagStr=TagStr.mid(TagStr.indexOf("-")+1,TagStr.count()-TagStr.indexOf("-")-1);
                       QSqlQuery QueryEquipment= QSqlQuery(T_ProjectDatabase);
                       SqlStr="SELECT * FROM Equipment WHERE DT = '"+TagStr+"'";
                       QueryEquipment.exec(SqlStr);
                       if(QueryEquipment.next()) InsertDBSymbolInfoByBlkEnty(ui->axWidget,BlkEnty,QString::number(Page_IDInDB),QueryEquipment.value("Equipment_ID").toString());
                   }
               }
               else if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("ES2_"))
               {

               }
           }
       }
       else if(BlkEnty->dynamicCall("Layer()").toString()=="LY_CDP")//Wire
       {

       }
       else if(BlkEnty->dynamicCall("Layer()").toString()=="CONNECT")//节点
       {

       }
    }
    emit(UpdateProjectUnits());
}
void formaxwidget::on_axWidget_SelectModified(IDispatch *pAryId, IDispatch *pModifyId, bool isAdd)
{
qDebug()<<"on_axWidget_SelectModified";
    QAxObject *m_pCustomEntity_temp = new QAxObject((IUnknown*)pModifyId );
    RespSelectedModifyId = (IMxDrawResbuf *)(m_pCustomEntity_temp);
}

//更新已绘制的符号块，如果SymbolName与原绘制的块不一致，则重新插入块并绘制 ，然后更新代号
IMxDrawBlockReference* formaxwidget::UpdateSymbolBlock(QString Handle,QString StrSymbolName)
{
    IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)ui->axWidget->querySubObject("HandleToObject(const QString)",Handle);
    if(BlkEnty==nullptr) return BlkEnty;
    if(BlkEnty->dynamicCall("GetBlockName()").toString()==StrSymbolName) return BlkEnty;
    QString OriginalDbId=BlkEnty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString();
    QString FunDefine=BlkEnty->dynamicCall("GetxDataString2(QString,int)","FunDefine",0).toString();
    QString Symbol_Category=BlkEnty->dynamicCall("GetxDataString2(QString,int)","Symbol_Category",0).toString();
    SymbolName=StrSymbolName+".dwg";
    IMxDrawPoint *point = (IMxDrawPoint *)BlkEnty->querySubObject("Position()");
    if(BlkEnty!=nullptr) BlkEnty->dynamicCall("Erase()");
    //添加块到块表
    if(SymbolName.contains("SYMB2_M_PWF_")) BlkPath="C:/TBD/SymbConnLib/"+SymbolName;
    else if(SymbolName.contains("SPS_")) BlkPath="C:/TBD/SPS/"+SymbolName;
    else BlkPath="C:/TBD/SYMB2LIB/"+SymbolName;
    if(!MyInsertBlock(ui->axWidget,BlkPath,SymbolName.mid(0,SymbolName.count()-4))) return nullptr;
    if(SymbolName.contains("SYMB2_M_PWF_")) SetCurLayer(ui->axWidget,"CONNECT");
    else SetCurLayer(ui->axWidget,"LY_Symb2");
    lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",point->x(),point->y(),SymbolName.mid(0,SymbolName.count()-4),1.0,0).toLongLong();
    BlkEnty= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    BlkEnty->dynamicCall("SetxDataString(QString,int,QString)","DbId",0,OriginalDbId);
    //将FunDefine写入到blkEnty的拓展数据中
    BlkEnty->dynamicCall("SetxDataString(QString,int,QString)","FunDefine",0,FunDefine);
    BlkEnty->dynamicCall("SetxDataString(QString,int,QString)","Symbol_Category",0,Symbol_Category);
    BlkEnty->dynamicCall("AssertWriteEnabled()");
    //WriteUserDataToBlkEnty();//将符号dwg文件的拓展数据写入到块
    SetCurLayer(ui->axWidget,"0");
    return BlkEnty;
}
void formaxwidget::ShowCableAttr(IMxDrawEntity *EntyCableLine,int Mode,int Cable_ID)//Mode=1 Add , Mode=2 Modify
{
    IMxDrawMText *CableMText;
    //电缆定义窗口
    DialogCableDefine *dlg=new DialogCableDefine(this);
    dlg->AttrMode=Mode;
    dlg->Page_ID=Page_IDInDB;
    if(Mode==1) dlg->LoadCableInfo(0);
    else
    {
        dlg->LoadCableInfo(Cable_ID);
    }
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled)
    {
        if(Mode==1) if(EntyCableLine!=nullptr) EntyCableLine->dynamicCall("Erase()");
    }
    else
    {
        QSqlQuery QueryCable=QSqlQuery(T_ProjectDatabase);
        QString tempSQL="SELECT * FROM Cable WHERE Cable_ID = "+QString::number(dlg->Cable_ID);
qDebug()<<"tempSQL="<<tempSQL;
        QueryCable.exec(tempSQL);
        if(QueryCable.next())
        {
            QString CableMTextString=QueryCable.value("CableNum").toString()+"\n"+QueryCable.value("Type").toString()+"  "+QueryCable.value("Structure").toString();
            if(Mode==1)
            {
                //绘制电缆MText，位置为Pt2边上，颜色为洋红
                SetCurLayer(ui->axWidget,"LY_CDP");
                //ui->axWidget->setProperty("DrawCADColor", QColorToInt(QColor(255,0,255)));
                double CableMTextx,CableMTexty,rotation;
                int Attachment=5;
                if(fabs(Pt2->x()-Pt1->x())<minDelta)//垂直
                {
                    CableMTextx=Pt2->x();
                    rotation=PI/2;
                    if(Pt2->y()>Pt1->y())
                    {
                       CableMTexty= Pt2->y()+2;
                       Attachment=4;//middle left
                    }
                    else
                    {
                       CableMTexty= Pt2->y()-2;
                       Attachment=6;//middle right
                    }
                }
                else
                {
                    CableMTexty=Pt2->y();
                    rotation=0;
                    if(Pt2->x()>Pt1->x())
                    {
                       CableMTextx= Pt2->x()+2;
                       Attachment=4;//middle left
                    }
                    else
                    {
                       CableMTextx= Pt2->x()-2;
                       Attachment=6;//middle right
                    }
                }
                SetCurLayer(ui->axWidget,"LY_CDP");
                qlonglong lID=ui->axWidget->dynamicCall("DrawMText(double,double,const QString&,double,double,double,short)",CableMTextx,CableMTexty,CableMTextString,3,0,rotation,Attachment).toLongLong();
                CableMText= (IMxDrawMText*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
                CableMText->dynamicCall("setColorIndex(int)",McColor::mcMagenta);
                CableMText->dynamicCall("blockSignals(bool)",true);
                //更新T_ProjectDatabase数据库的Wires表
                QSqlQuery QueryWires = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                int MaxWires_ID=GetMaxIDOfDB(T_ProjectDatabase,"Wires","Wires_ID");
                //更新T_ProjectDatabase数据库的Wires表
                tempSQL = "INSERT INTO Wires (Wires_ID,Cable_ID,Symbol,Handle,Page_ID,TextHandle)"
                                  "VALUES (:Wires_ID,:Cable_ID,:Symbol,:Handle,:Page_ID,:TextHandle)";
                QueryWires.prepare(tempSQL);
                QueryWires.bindValue(":Wires_ID",MaxWires_ID);
                QueryWires.bindValue(":Cable_ID",QString::number(dlg->Cable_ID));
                QueryWires.bindValue(":Symbol","SPS_LINE");
                QueryWires.bindValue(":Handle",EntyCableLine->dynamicCall("handle()").toString());
                QueryWires.bindValue(":Page_ID",QString::number(Page_IDInDB));
                QueryWires.bindValue(":TextHandle",CableMText->dynamicCall("handle()").toString());
                QueryWires.exec();
qDebug()<<"ListSelectEntys.count()="<<ListSelectEntys.count();
                //绘制电缆直线与连线相交处的导线定义
                for(int i=0;i<ListSelectEntys.count();i++)
                {
                    IMxDrawPoints* pts=(IMxDrawPoints*)ListSelectEntys.at(i)->querySubObject("IntersectWith(IDispatch*,int)",EntyCableLine->asVariant(),McExtendOption::mcExtendNone);
                    if(pts->dynamicCall("Count()").toInt()==1)
                    {
                        SymbolName="SPS_CDP.dwg";
                        BlkPath="C:/TBD/SPS/SPS_CDP.dwg";
                        MyInsertBlock(ui->axWidget,BlkPath,"SPS_CDP");
                        lBlockID=ui->axWidget->dynamicCall("DrawBlockReference(double,double, QString,double,double)",((IMxDrawPoint*)pts->querySubObject("Item(int)",0))->x(),((IMxDrawPoint*)pts->querySubObject("Item(int)",0))->y(),"SPS_CDP",1.0,0).toLongLong();
                        IMxDrawBlockReference *blkLineDefine= (IMxDrawBlockReference*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
                        //更新T_ProjectDatabase数据库的Wires表
                        int MaxWires_ID=GetMaxIDOfDB(T_ProjectDatabase,"Wires","Wires_ID");
                        //更新T_ProjectDatabase数据库的Wires表
                        tempSQL = "INSERT INTO Wires (Wires_ID,Cable_ID,Symbol,Handle,Page_ID,Position,AuxiliaryLine)"
                                          "VALUES (:Wires_ID,:Cable_ID,:Symbol,:Handle,:Page_ID,:Position,:AuxiliaryLine)";
                        QueryWires.prepare(tempSQL);
                        QueryWires.bindValue(":Wires_ID",MaxWires_ID);
                        QueryWires.bindValue(":Cable_ID",QString::number(dlg->Cable_ID));
                        QueryWires.bindValue(":Symbol","SPS_CDP");
                        QueryWires.bindValue(":Handle",blkLineDefine->dynamicCall("handle()").toString());
                        QueryWires.bindValue(":Page_ID",QString::number(Page_IDInDB));
                        QueryWires.bindValue(":Position",QString::number(((IMxDrawPoint*)pts->querySubObject("Item(int)",0))->x(),'f',0)+".000000,"+QString::number(((IMxDrawPoint*)pts->querySubObject("Item(int)",0))->y(),'f',0)+".000000,0.000000");
                        QueryWires.bindValue(":AuxiliaryLine",EntyCableLine->dynamicCall("handle()").toString());
                        QueryWires.exec();
                    }
                }
            }
            else
            {
                CableMText->dynamicCall("SetContents(QString)",CableMTextString);
            }
            CableMText->dynamicCall("SetxDataString(QString,int,QString)","FUZHULINEHANDLE",0,EntyCableLine->dynamicCall("handle()").toString());
            EntyCableLine->dynamicCall("SetxDataString(QString,int,QString)","DLNATTR_TEXTHANDLE",0,CableMText->dynamicCall("handle()").toString());
        }
    }
    ui->axWidget->dynamicCall("UpdateDisplay()");   
    SetCurLayer(ui->axWidget,"0");
    //timerAutoSaveDelay->start(1000);
    //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);//自动保存图纸
}

IMxDrawPoint* formaxwidget::GetBesideTermPtVal(IMxDrawPoint* Pt)//在2*2栅格内找到最近的接线点坐标
{
qDebug()<<"Pt->x()="<<Pt->x()<<",Pt->y()="<<Pt->y();
    if (Pt == nullptr) return nullptr;   // 返回点的点对象值。
    Pt=GetGridPtVal(Pt);
    //如果Pt在某根连线上，则返回Pt
    IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter2=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter2->AddStringEx("LINE",5020);
    filter2->AddStringEx("CONNECT", 8);
    ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",Pt->asVariant(),filter2->asVariant());
    for(int j=0;j<ss2->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawLine * CrossLine=  (IMxDrawLine *)ss2->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        return Pt;
    }

    //return Pt;
    MxDrawPoint *Select_Pt1=new MxDrawPoint();
    IMxDrawPoint *SelectPt1=(IMxDrawPoint *)Select_Pt1;
    SelectPt1->setX(Pt->x()-2);
    SelectPt1->setY(Pt->y()+2);
    MxDrawPoint *Select_Pt2=new MxDrawPoint();
    IMxDrawPoint *SelectPt2=(IMxDrawPoint *)Select_Pt2;
    SelectPt2->setX(Pt->x()+2);
    SelectPt2->setY(Pt->y()-2);
    double BesideX=Pt->x(),BesideY=Pt->y();
    bool FirstFind=true;
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    //创建过滤对象
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, SelectPt1->asVariant(), SelectPt2->asVariant(),filter->asVariant());
    for (int i = 0; i < ss->Count(); i++)
    {
        IMxDrawEntity* ent = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
        if(ent==nullptr) continue;
        if(EntyIsErased(ui->axWidget,ent)) continue;
        if(ent->dynamicCall("ObjectName()").toString()!="McDbBlockReference") continue;
        IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)ent;
        //if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF")) continue;
        IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )BlkEnty->querySubObject("BlockTableRecord()");
        IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
        // 循环得到所有实体
        for (; !iter->Done(); iter->Step(true, false))
        {
            // 得到遍历器当前的实体
            IMxDrawEntity* Subent = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
            if(EntyIsErased(ui->axWidget,Subent)) continue;//去除erase的实体
            if(Subent->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
            {
                Subent->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
                if(ui->axWidget->dynamicCall("IsOk()").toString()!="true") continue;
                int VCnt=Subent->property("NumVerts").toInt();
                if(VCnt!=2) continue;
                double x=0;
                double y=0;
                for(int k=0;k<VCnt;k++)
                {
                    IMxDrawPoint* pt= (IMxDrawPoint*)Subent->querySubObject("GetPointAt(int)",k);
                    x+=pt->x()/2;
                    y+=pt->y()/2;
                }
                x=((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x()+x-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x();
                y=((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y()+y-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y();
qDebug()<<"x="<<x<<",y="<<y;
                //除非刚好是连接器的节点，否则排除连接器
                if(BlkEnty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF"))
                {
                   if((fabs(x-Pt->x())<0.1)&&(fabs(y-Pt->y())<0.1))  return Pt;
                   else continue;
                }

                if(FirstFind)
                {
                   BesideX=x;BesideY=y;
                }
                else
                {
                   if(((x-Pt->x())*(x-Pt->x())+(y-Pt->y())*(y-Pt->y()))<((BesideX-Pt->x())*(BesideX-Pt->x())+(BesideY-Pt->y())*(BesideY-Pt->y())))
                   {
                       BesideX=x;BesideY=y;
                   }
                }
qDebug()<<"BesideX="<<BesideX<<",BesideY="<<BesideY;
                FirstFind=false;
            }
        }
    }
    //BesideX,BesideY不能有其他连线
    SelectPt1->setX(BesideX);
    SelectPt1->setY(BesideY);
    ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",SelectPt1->asVariant(),filter2->asVariant());
    for(int j=0;j<ss2->dynamicCall("Count()").toInt();j++)
    {
        IMxDrawLine * CrossLine=  (IMxDrawLine *)ss2->querySubObject("Item(int)",j);
        if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
        return Pt;
    }
    Pt->setX(BesideX);
    Pt->setY(BesideY);
    return Pt;
}

IMxDrawPoint* formaxwidget::GetGridPtVal(IMxDrawPoint* Pt)
{
    if (Pt == nullptr) return nullptr;   // 返回点的点对象值。
    Pt->setX(GetGridPosVal(Pt->x()));
    Pt->setY(GetGridPosVal(Pt->y()));
    UpdateCursorPos=true;
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","OSMODE",0);//取消对象捕捉
    return Pt;
}

double formaxwidget::GetGridPosVal(double Val)
{
    if((int(Val)%2)==0) return int(Val);
    else return Val>0?int(Val)+1:int(Val)-1;
}

void formaxwidget::PutCursorInGrid(int Mode,double &dX,double &dY)
{
    dX=GetGridPosVal(dX);
    dY=GetGridPosVal(dY);
    if(Mode==0) ui->axWidget->dynamicCall("SetInputCursorPos(double,double)",dX,dY);
}

void formaxwidget::SendUpdateTerminalSignalToMainWindow()
{
    emit(UpdateProjectTerminals());
}

//插入新端子排并设定新插入图纸的端子
void formaxwidget::NewTerminalStrip()
{
    QString StrProTag,StrGaoceng,StrPos;
    GetPageGaocengAndPos(Page_IDInDB,StrGaoceng,StrPos);
    StrProTag+="="+StrGaoceng+"+"+StrPos;
    DialogTerminalAttr *dlg=new DialogTerminalAttr(this);
    connect(dlg,SIGNAL(UpdateProjectTerminals()),this,SLOT(SendUpdateTerminalSignalToMainWindow()));
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    dlg->setWindowTitle("新建端子排");
    dlg->StrProTag=StrProTag;
    dlg->LoadInfo(1,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        QDialog *dialogDesignation =new QDialog();
        dialogDesignation->setWindowTitle("请择插入的端子片");
        dialogDesignation->setMinimumSize(QSize(300,60));
        QFormLayout *formlayoutDesignation = new QFormLayout(dialogDesignation);
        QComboBox *m_CbDesignation = new QComboBox(dialogDesignation);
        QSqlQuery QueryTerminal(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+dlg->CurTerminalStrip_ID+"'";
        QueryTerminal.exec(StrSql);
        while(QueryTerminal.next())
        {
           m_CbDesignation->addItem(QueryTerminal.value("Designation").toString());
        }

        QHBoxLayout *layoutBtn = new QHBoxLayout(nullptr);
        QPushButton *pushbuttonOK = new QPushButton(dialogDesignation);
        pushbuttonOK->setText("确认");
        QPushButton *pushbuttonCancel = new QPushButton(dialogDesignation);
        pushbuttonCancel->setText("取消");
        layoutBtn->addWidget(pushbuttonOK);
        layoutBtn->addWidget(pushbuttonCancel);
        formlayoutDesignation->addRow(m_CbDesignation);
        formlayoutDesignation->addRow(layoutBtn);
        QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogDesignation,SLOT(accept()));
        if (dialogDesignation->exec()==QDialog::Accepted)
        {
           int Designation=m_CbDesignation->currentText().toInt();
           StrSql="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+dlg->CurTerminalStrip_ID+"' AND Designation = '"+QString::number(Designation)+"'";
           QueryTerminal.exec(StrSql);
           if(QueryTerminal.next())
             LoadTerminal({QueryTerminal.value("Terminal_ID").toInt()});
        }
    }
    delete dlg;
}

void formaxwidget::AddExistedTerminal()//插入已有端子
{
    DialogAddTerminal *dlg=new DialogAddTerminal();
    dlg->setWindowTitle("上端子");
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //绘制端子
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString tempSQL="SELECT * FROM TerminalStrip WHERE DT = '"+dlg->DT+"'";
        QueryVar.exec(tempSQL);
        if(QueryVar.next())
        {
            tempSQL="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryVar.value("TerminalStrip_ID").toString()+"' AND Designation = '"+QString::number(dlg->Designation)+"'";
            QueryVar.exec(tempSQL);
            if(QueryVar.next())
            {
                //formMdi->AddTerminalTag=dlg->DT;
                //formMdi->AddTerminalDesignation=dlg->Designation;
                TerminalAdd(QueryVar.value("Terminal_ID").toString());
            }
        }
    }
    delete dlg;
}

//切换至普通导线
void formaxwidget::TransformToLine()
{
    IMxDrawLine *Line= (IMxDrawLine*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespSelectedModifyId->dynamicCall("AtObjectId(int)",0).toLongLong());
    Line->dynamicCall("setColorIndex(int)",McColor::mcGreen);
}

//切换至短接片
void formaxwidget::TransformToShortageLine()
{
    IMxDrawLine *Line= (IMxDrawLine*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespSelectedModifyId->dynamicCall("AtObjectId(int)",0).toLongLong());
    IMxDrawPoint *StartPoint=(IMxDrawPoint *)Line->querySubObject("StartPoint()");
    IMxDrawPoint *EndPoint=(IMxDrawPoint *)Line->querySubObject("EndPoint()");
    //如果导线两端连着端子，则可以选择切换至短接片
    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
    filter->AddStringEx("INSERT",5020);
    filter->AddStringEx("Terminal", 8);
    ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",StartPoint->asVariant(),filter->asVariant());
    if(ss->dynamicCall("Count()").toInt()==1)
    {
        IMxDrawBlockReference *OneTerminal=(IMxDrawBlockReference *)ss->querySubObject("Item(int)",0);
        if(!EntyIsErased(ui->axWidget,(IMxDrawEntity *)OneTerminal))
        {
            IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
            IMxDrawResbuf *filter2=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
            filter2->AddStringEx("INSERT",5020);
            filter2->AddStringEx("Terminal", 8);
            ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",EndPoint->asVariant(),filter2->asVariant());
            if(ss2->dynamicCall("Count()").toInt()==1)
            {
                IMxDrawBlockReference *AnotherTerminal=(IMxDrawBlockReference *)ss2->querySubObject("Item(int)",0);
                if(!EntyIsErased(ui->axWidget,(IMxDrawEntity *)AnotherTerminal))
                {
                    QString tempSQL="SELECT * FROM Terminal WHERE Handle = '"+OneTerminal->dynamicCall("handle()").toString()+"'AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
                    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    QueryVar.exec(tempSQL);
                    if(QueryVar.next())
                    {
                       QString OneTerminal_ID=QueryVar.value("Terminal_ID").toString();
                       QString OneTerminalStrip_ID=QueryVar.value("TerminalStrip_ID").toString();
                       if(QueryVar.value("ShortJumper").toString()=="")
                       {
                           tempSQL="SELECT * FROM Terminal WHERE Handle = '"+AnotherTerminal->dynamicCall("handle()").toString()+"' AND TerminalStrip_ID = '"+OneTerminalStrip_ID+"'";
                           QueryVar.exec(tempSQL);
                           if(QueryVar.next())
                           {
                               Line->dynamicCall("setColorIndex(int)",McColor::mcBlue);
                               QString AnotherTerminal_ID=QueryVar.value("Terminal_ID").toString();
                               //更新端子短接数据库
                               if(QueryVar.value("ShortJumper").toString()!="")
                               {
                                   QString ShortJumper=QueryVar.value("ShortJumper").toString();
                                   QString StrSql="UPDATE Terminal SET ShortJumper=:ShortJumper WHERE Terminal_ID = "+OneTerminal_ID;
                                   QueryVar.prepare(StrSql);
                                   QueryVar.bindValue(":ShortJumper",ShortJumper);
                                   QueryVar.exec();
                               }
                               else
                               {
                                   int CurSearchTagIndex=1;
                                   QString CurSearchTag;
                                   while(1)
                                   {
                                       for(int i=0;i<CurSearchTagIndex;i++) CurSearchTag+="*";
                                       QString StrSql="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+OneTerminalStrip_ID+"' AND ShortJumper = '"+CurSearchTag+"'";
                                       QueryVar.exec(StrSql);
                                       if(!QueryVar.next()) break;
                                   }
                                   QString StrSql="UPDATE Terminal SET ShortJumper=:ShortJumper WHERE Terminal_ID = "+OneTerminal_ID;
                                   QueryVar.prepare(StrSql);
                                   QueryVar.bindValue(":ShortJumper",CurSearchTag);
                                   QueryVar.exec();
                                   StrSql="UPDATE Terminal SET ShortJumper=:ShortJumper WHERE Terminal_ID = "+AnotherTerminal_ID;
                                   QueryVar.prepare(StrSql);
                                   QueryVar.bindValue(":ShortJumper",CurSearchTag);
                                   QueryVar.exec();
                               }
                               //新插入的端子默认不显示端子排代号
                               UpdateBlockAttr(AnotherTerminal,"设备标识符(显示)","");
                           }
                       }//if(QueryVar.value("ShortJumper").toString()=="")
                       else
                       {
                           tempSQL="SELECT * FROM Terminal WHERE Handle = '"+AnotherTerminal->dynamicCall("handle()").toString()+"' AND TerminalStrip_ID = '"+OneTerminalStrip_ID+"' AND ShortJumper = '"+QueryVar.value("ShortJumper").toString()+"'";
                           qDebug()<<"tempSQL="<<tempSQL;
                           QueryVar.exec(tempSQL);
                           if(QueryVar.next())
                           {
                               Line->dynamicCall("setColorIndex(int)",McColor::mcBlue);
                               UpdateBlockAttr(AnotherTerminal,"设备标识符(显示)","");
                           }
                       }
                    }
                }//end of if(!EntyIsErased(ui->axWidget,(IMxDrawEntity *)AnotherTerminal))
            }//end of if(ss2->dynamicCall("Count()").toInt()==1)
        }//end of if(!EntyIsErased(ui->axWidget,(IMxDrawEntity *)OneTerminal))
    }//end of if(ss->dynamicCall("Count()").toInt()==1)
    ui->axWidget->dynamicCall("UpdateDisplay()");
}

void formaxwidget::on_axWidget_MouseEvent(int lType, double dX, double dY, int &lRet)
{
//qDebug()<<"lType="<<lType;
    if (lType == 1)// 鼠标移动
    {
        if(UpdateCursorPos&&(!IsDoingSymbolEdit))
        {
            PutCursorInGrid(0,dX,dY);
            UpdateCursorPos=false;
        }
        if(DoingGridEdit&&(!IsDoingSymbolEdit))
        {
            PutCursorInGrid(0,dX,dY);
        }
    }
    else if (lType == 3)// 鼠标右键按下.
    {
        //可以选择插入新端子或已有端子
        QMenu tree_menu;
        tree_menu.clear();
        QAction actNewTerminalStrip("插入新端子排", this);
        tree_menu.addAction(&actNewTerminalStrip);
        connect(&actNewTerminalStrip,SIGNAL(triggered()),this,SLOT(NewTerminalStrip()));
        QAction actAddExistedTerminal("插入已有端子", this);
        tree_menu.addAction(&actAddExistedTerminal);
        connect(&actAddExistedTerminal,SIGNAL(triggered()),this,SLOT(AddExistedTerminal()));
        /*
        QAction actTransformToLine("切换至普通导线", this);
        QAction actTransformToShortageLine("切换至短接片", this);
        //如果选中了线段，可切换成普通导线或者是短接片
qDebug()<<"RespSelectedModifyId->dynamicCall(Count()).toInt()="<<RespSelectedModifyId->dynamicCall("Count()").toInt();
        if(RespSelectedModifyId->dynamicCall("Count()").toInt()==1)
        {
            IMxDrawEntity *Enty= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespSelectedModifyId->dynamicCall("AtObjectId(int)",0).toLongLong());
            if(!EntyIsErased(ui->axWidget,Enty))
            {
qDebug()<<"Enty->dynamicCall(ObjectName()).toString()="<<Enty->dynamicCall("ObjectName()").toString();
qDebug()<<"Enty->dynamicCall(Layer()).toString()="<<Enty->dynamicCall("Layer()").toString();
               if((Enty->dynamicCall("ObjectName()").toString()=="McDbLine")&&(Enty->dynamicCall("Layer()").toString()=="CONNECT"))
               {
qDebug()<<"Enty->dynamicCall(colorIndex()).toInt()="<<Enty->dynamicCall("colorIndex()").toInt()<<"McColor::mcBlue="<<McColor::mcBlue<<"McColor::mcGreen="<<McColor::mcGreen;
                   if(Enty->dynamicCall("colorIndex()").toInt()==McColor::mcBlue)
                   {
                       tree_menu.addAction(&actTransformToLine);
                       connect(&actTransformToLine,SIGNAL(triggered()),this,SLOT(TransformToLine()));
                   }
                   else if(Enty->dynamicCall("colorIndex()").toInt()==McColor::mcGreen)
                   {
 qDebug()<<"切换至短接片";
                       tree_menu.addAction(&actTransformToShortageLine);
                       connect(&actTransformToShortageLine,SIGNAL(triggered()),this,SLOT(TransformToShortageLine()));
                   }
               }
            }
        }*/
        tree_menu.exec(QCursor::pos());
    }
    else if (lType == 4)// 鼠标左键双击.
    {
        // 构建选择集，找到鼠标左建双击下的实体。
        IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        MxDrawPoint point;
        IMxDrawEntity * enty;
        QString sName;

        //筛选出块
        filter->RemoveAll();
        //filter->AddStringEx("INSERT",5020);//5020是DXF码，代表"INSERT"是类型字符串
        point.setX(dX);
        point.setY(dY);
        ss1->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",point.asVariant(),filter->asVariant());
        if(ss1->dynamicCall("Count()").toInt()==1)
        {
            enty=  (IMxDrawEntity *)ss1->querySubObject("Item(int)",0);
            if(EntyIsErased(ui->axWidget,enty)) return;//去除erase的实体
            enty->dynamicCall("Highlight(bool)",false);
            sName = enty->dynamicCall("ObjectName()").toString();
            if(sName == "McDbLine")//区分是连线还是电缆
            {
                if(enty->dynamicCall("Layer()").toString()=="CONNECT") //选择的是连线
                {
                    IMxDrawLine *entyLine=(IMxDrawLine *)enty;
                    //查看该连线是否有Wire定义（是否相交）
                    bool HasWireDefine=false;
                    //创建选择集对象
                    IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
                    //创建过滤对象
                    MxDrawResbuf* filter =new MxDrawResbuf();
                    filter->AddStringEx("INSERT",5020);
                    ss->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetCrossing, ((IMxDrawPoint *)entyLine->querySubObject("StartPoint()"))->asVariant(), ((IMxDrawPoint *)entyLine->querySubObject("EndPoint()"))->asVariant(),filter->asVariant());
                    qDebug()<<"ss.Count()="<<ss->Count();
                    for (int i = 0; i < ss->Count(); i++)
                    {
                        IMxDrawEntity* entCross = (IMxDrawEntity *)ss->querySubObject("Item(int)",i);
                        if(entCross->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
                        {
                            IMxDrawBlockReference *BlkWire=(IMxDrawBlockReference *)entCross;
                            if(BlkWire->dynamicCall("GetBlockName()").toString()=="SPS_CDP")
                            {
                                QSqlQuery QueryWires(T_ProjectDatabase);
                                QString StrSql="SELECT * FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle = '"+BlkWire->dynamicCall("handle()").toString()+"'";
                                QueryWires.exec(StrSql);
                                if(QueryWires.next())
                                {
                                    HasWireDefine=true;
                                    ShowWireAttr(BlkWire,QueryWires.value("Wires_ID").toInt());
                                    break;
                                }
                            }
                        }
                    }
                    if(!HasWireDefine) LineDefine();
                }
                else if(enty->dynamicCall("Layer()").toString()=="LY_CDP") //选择的是电缆
                {
                    QSqlQuery QueryWires(T_ProjectDatabase);
                    QString StrSql="SELECT * FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND Handle = '"+enty->dynamicCall("handle()").toString()+"'";
                    QueryWires.exec(StrSql);
                    if(QueryWires.next())  ShowCableAttr(enty,2,QueryWires.value("Cable_ID").toInt());
                }
            }
            else if(sName == "McDbAttributeDefinition")
            {
                DialogAttrDefSet *dlg = new DialogAttrDefSet(this,(IMxDrawAttributeDefinition *)enty,nullptr,nullptr);
                dlg->setModal(true);
                dlg->show();
                dlg->exec();
                delete dlg;
            }
            else if(sName == "McDbAttribute")
            {
                DialogAttrDefSet *dlg = new DialogAttrDefSet(this,nullptr,(IMxDrawAttribute *)enty,nullptr);
                dlg->setModal(true);
                dlg->show();
                dlg->exec();
                delete dlg;
            }
            else if(sName == "McDbMText")
            {
                if(enty->dynamicCall("Layer()").toString()!="LY_CDP")
                {/*
                    IMxDrawMText *mText=(IMxDrawMText *)enty;
                    DialogAttrDefSet *dlg = new DialogAttrDefSet(this,nullptr,nullptr,mText);
                    dlg->setModal(true);
                    dlg->show();
                    dlg->exec();
                    delete dlg;*/
                    return;
                }
                QSqlQuery QueryWires(T_ProjectDatabase);
                QString StrSql="SELECT Cable_ID FROM Wires WHERE Page_ID = '"+QString::number(Page_IDInDB)+"' AND TextHandle = '"+enty->dynamicCall("handle()").toString()+"'";
                QueryWires.exec(StrSql);
                if(QueryWires.next()) //选择的是电缆
                {
                    ShowCableAttr(enty,2,QueryWires.value(0).toInt());
                }
            }
            else if(sName == "McDbBlockReference")
            {
 qDebug()<<"Layer is "<<enty->dynamicCall("Layer()").toString();
                if(enty->dynamicCall("Layer()").toString()=="Terminal")//设置端子属性
                {
                    /*
                    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    QString SqlStr = "SELECT * FROM Terminal WHERE Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
                    QueryTerminal.exec(SqlStr);
                    if(QueryTerminal.next())
                    {
                       emit(SigalShowTerminalAttr(QueryTerminal.value("Terminal_ID").toInt()));
                    }*/
                    QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    QString SqlStr = "SELECT * FROM TerminalInstance WHERE Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
                    QueryTerminalInstance.exec(SqlStr);
                    if(QueryTerminalInstance.next())
                    {
                       emit(SigalShowTerminalAttr(0,QueryTerminalInstance.value("TerminalInstanceID").toInt()));
                    }
                }
                else if(enty->dynamicCall("Layer()").toString()=="LY_CDP")
                {
                    QSqlQuery QueryWires(T_ProjectDatabase);
                    QString StrSql="SELECT Wires_ID FROM Wires WHERE Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
                    QueryWires.exec(StrSql);
                    if(QueryWires.next())//选中的为连接定义
                    {
                        IMxDrawBlockReference* blkRef=(IMxDrawBlockReference*)enty;
                        ShowWireAttr(blkRef,QueryWires.value("Wires_ID").toInt());
                    }
                }
                else if(enty->dynamicCall("Layer()").toString()=="CONNECT")
                {
                    QSqlQuery QueryConnector(T_ProjectDatabase);
                    QString StrSql="SELECT * FROM Connector WHERE Connector_Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
qDebug()<<"StrSql="<<StrSql;
                    QueryConnector.exec(StrSql);
                    if(QueryConnector.next())//选中的为节点
                    {
qDebug()<<"Connector_Name="<<QueryConnector.value("Connector_Name").toString();
                        IMxDrawBlockReference* blkRef=(IMxDrawBlockReference*)enty;
                        DialogConnectAttr *dlg=new DialogConnectAttr(this);
                        int OriginalDir=0;
                        if(QueryConnector.value("Connector_Name").toString().contains("SYMB2_M_PWF_TLRU"))
                        {
                            OriginalDir=QueryConnector.value("Connector_Name").toString().mid(16,1).toInt();
                            dlg->LoadConnectAttr("SYMB2_M_PWF_TLRU",OriginalDir);
                        }
                        else if(QueryConnector.value("Connector_Name").toString().contains("SYMB2_M_PWF_TLRO"))
                        {
                            OriginalDir=QueryConnector.value("Connector_Name").toString().mid(16,1).toInt();
                            dlg->LoadConnectAttr("SYMB2_M_PWF_TLRO",OriginalDir);
                        }
                        else if(QueryConnector.value("Connector_Name").toString().contains("SYMB2_M_PWF_TOUR"))//SYMB2_M_PWF_TOUR2
                        {
                            OriginalDir=QueryConnector.value("Connector_Name").toString().mid(16,1).toInt();
                            dlg->LoadConnectAttr("SYMB2_M_PWF_TOUR",OriginalDir);
                        }
                        else if(QueryConnector.value("Connector_Name").toString().contains("SYMB2_M_PWF_TOUL"))
                        {
                            OriginalDir=QueryConnector.value("Connector_Name").toString().mid(16,1).toInt();
                            dlg->LoadConnectAttr("SYMB2_M_PWF_TOUL",OriginalDir);
                        }
                        else return;
                        dlg->setModal(true);
                        dlg->show();
                        dlg->exec();
                        if(dlg->Canceled) return;
                        if(dlg->Dir!=OriginalDir)
                        {
                            //更新dwg和数据库
                            IMxDrawBlockReference *BlkEnty=UpdateSymbolBlock(blkRef->dynamicCall("handle()").toString(),dlg->ConnectName+QString::number(dlg->Dir));
                            //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字                      
                            if(BlkEnty!=nullptr)
                            {                               
                                int Connector_ID=QueryConnector.value("Connector_ID").toInt();
                                //更新Connector表
                                QSqlQuery QueryConnectorUpdate=QSqlQuery(T_ProjectDatabase);
                                QString tempSQL="UPDATE Connector SET Connector_Name=:Connector_Name,Connector_Handle=:Connector_Handle,C_Coordinate=:C_Coordinate,G_Coordinate=:G_Coordinate,Coordinate_1=:Coordinate_1,Coordinate_2=:Coordinate_2,Coordinate_3=:Coordinate_3 WHERE Connector_ID = "+QString::number(Connector_ID);
                                QueryConnectorUpdate.prepare(tempSQL);
                                QueryConnectorUpdate.bindValue(":Connector_Name",BlkEnty->dynamicCall("GetBlockName()").toString());
                                QueryConnectorUpdate.bindValue(":Connector_Handle",BlkEnty->dynamicCall("handle()").toString());

                                QString InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"C")->x(),'f',0)+".000000";
                                InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"C")->y(),'f',0)+".000000";
                                InsertionPoint+=",0.000000";
                                QueryConnectorUpdate.bindValue(":C_Coordinate",InsertionPoint);

                                if(SymbolName.contains("SYMB2_M_PWF_CR"))
                                {
                                    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"G")->x(),'f',0)+".000000";
                                    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"G")->y(),'f',0)+".000000";
                                    InsertionPoint+=",0.000000";
                                    QueryConnectorUpdate.bindValue(":G_Coordinate",InsertionPoint);
                                }
                                else QueryConnectorUpdate.bindValue(":G_Coordinate","");

                                InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"1")->x(),'f',0)+".000000";
                                InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"1")->y(),'f',0)+".000000";
                                InsertionPoint+=",0.000000";
                                QueryConnectorUpdate.bindValue(":Coordinate_1",InsertionPoint);

                                if(!SymbolName.contains("SYMB2_M_PWF_CO"))
                                {
                                    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"2")->x(),'f',0)+".000000";
                                    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"2")->y(),'f',0)+".000000";
                                    InsertionPoint+=",0.000000";
                                    QueryConnectorUpdate.bindValue(":Coordinate_2",InsertionPoint);
                                }
                                else QueryConnectorUpdate.bindValue(":Coordinate_2","");


                                if(SymbolName.contains("SYMB2_M_PWF_BR"))
                                {
                                    InsertionPoint=QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"3")->x(),'f',0)+".000000";
                                    InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(ui->axWidget,BlkEnty,"3")->y(),'f',0)+".000000";
                                    InsertionPoint+=",0.000000";
                                    QueryConnectorUpdate.bindValue(":Coordinate_3",InsertionPoint);
                                }
                                else QueryConnectorUpdate.bindValue(":Coordinate_3","");

                                QueryConnectorUpdate.exec();
                                //timerAutoSaveDelay->start(1000);
                                //ui->axWidget->dynamicCall("SaveDwgFile(QString)",dwgFileName);
                            }
                        }
                    }
                    QSqlQuery QueryLink(T_ProjectDatabase);
                    StrSql="SELECT * FROM Link WHERE Link_Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
                    QueryLink.exec(StrSql);
                    if(QueryLink.next())//选中的为链接点定义
                    {
                        IMxDrawBlockReference* blkNode=(IMxDrawBlockReference*)enty;
                        DialogLinkEdit *dlg=new DialogLinkEdit(this);
                        dlg->AttrMode=2;
                        dlg->Page_ID=Page_IDInDB;
                        dlg->LoadLinkInfo(QueryLink.value("Link_ID").toInt());
                        dlg->setModal(true);
                        dlg->show();
                        dlg->exec();
                        if(dlg->Canceled) return;
                        //更新链接点文字和箭头方向
                        UpdateLinkBlk(blkNode,dlg->Link_ID,dlg->RetStrLinkTag,dlg->RetStrLinkTextPosition);
                    }
                }
                else if(enty->dynamicCall("Layer()").toString()=="LY_Symb2")
                {
 qDebug()<<"是否为端子？"<<enty->dynamicCall("GetxDataString2(QString,int)","LD_SYMB2_SPECIAL",0).toString();
                    //区分是功能子块还是端子还是连接定义
 qDebug()<<"DbId="<<enty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toInt();
                    //if(enty->dynamicCall("GetxDataString2(QString,int)","LD_SYMB2_SPECIAL",0).toString()!="端子")
                    {
                        if(enty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toInt()>0)
                          emit(SigalShowSpurAttr(enty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toInt()));
                        else//修改块注释
                        {
                            IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)enty;
                            for (int  j = 0; j < BlkEnty->dynamicCall("AttributeCount()").toInt(); j++)
                            {
                                // 得到块引用中所有的属性
                                IMxDrawAttribute *attrib = (IMxDrawAttribute *)BlkEnty->querySubObject("AttributeItem(int)",j);
                                //if(attrib->dynamicCall("Tag()").toString().contains("设备标识符"))
                                {
                                    DialogAttrDefSet *dlg = new DialogAttrDefSet(this,nullptr,attrib,nullptr);
                                    dlg->setModal(true);
                                    dlg->show();
                                    dlg->exec();
                                    if(!dlg->Canceled) BlkEnty->dynamicCall("AssertWriteEnabled()");
                                    delete dlg;
                                }
                            }
                        }
                    }
                    /*
                    else//端子
                    {
                        emit(SigalShowTerminalAttr(0,enty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toInt()));
                    }*/
                }
            }
        }//筛选出块      
    }//if (lType == 4)// 鼠标左键双击.
}

void formaxwidget::ShiftTerminalConnect()//切换选中的端子的连接点
{
    if(RespSelectedModifyId->dynamicCall("Count()").toInt()!=1) return;
    IMxDrawEntity *Enty= (IMxDrawEntity*) ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",RespSelectedModifyId->dynamicCall("AtObjectId(int)",0).toLongLong());
    if(EntyIsErased(ui->axWidget,Enty)) return;
    if(Enty->dynamicCall("ObjectName()").toString()!="McDbBlockReference") return;

    IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)Enty;
    QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM TerminalInstance WHERE Handle = '"+BlkEnty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"'";
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        QString LeftTerm=QueryTerminalInstance.value("LeftTerm").toString();
        QString RightTerm=QueryTerminalInstance.value("RightTerm").toString();
        QString UpTerm=QueryTerminalInstance.value("UpTerm").toString();
        QString DownTerm=QueryTerminalInstance.value("DownTerm").toString();
        //QString FunDefine=QueryTerminal.value("FunDefine").toString();
        if(LeftTerm=="1") LeftTerm="2";  else LeftTerm="1";
        if(RightTerm=="1") RightTerm="2";  else RightTerm="1";
        if(UpTerm=="1") UpTerm="2";  else UpTerm="1";
        if(DownTerm=="1") DownTerm="2";  else DownTerm="1";
        UpdateBlockAttr(BlkEnty,"左连接点",LeftTerm);
        UpdateBlockAttr(BlkEnty,"右连接点",RightTerm);
        UpdateBlockAttr(BlkEnty,"上连接点",UpTerm);
        UpdateBlockAttr(BlkEnty,"下连接点",DownTerm);
        QSqlQuery QueryTerminalUpdate(T_ProjectDatabase);
        SqlStr="UPDATE TerminalInstance SET LeftTerm=:LeftTerm,RightTerm=:RightTerm,UpTerm=:UpTerm,DownTerm=:DownTerm WHERE TerminalInstanceID = "+QueryTerminalInstance.value("TerminalInstanceID").toString();
        QueryTerminalUpdate.prepare(SqlStr);
        QueryTerminalUpdate.bindValue(":LeftTerm",LeftTerm);
        QueryTerminalUpdate.bindValue(":RightTerm",RightTerm);
        QueryTerminalUpdate.bindValue(":UpTerm",UpTerm);
        QueryTerminalUpdate.bindValue(":DownTerm",DownTerm);
        QueryTerminalUpdate.exec();
    }
    ui->axWidget->dynamicCall("UpdateDisplay()");
}

void formaxwidget::on_axWidget_MxKeyDown(int lVk, int &pRet)
{
    qDebug()<<"KeyDown 按下的按键的序号"<<lVk;
    if(lVk==9)  RotateEnty();//Tab键
    if(lVk==49) ChangeWholeUnitTermsGap("减小");//1键
    if(lVk==50) ChangeWholeUnitTermsGap("增加");//2键
    if(lVk==16)
    {
        FlagAutoConnectLine=FlagAutoConnectLine?false:true;//shift键
        ShiftTerminalConnect();
    }
}

//Mode=0:ui->axWidget画自动连线  Mode=1:pDrawWorldDraw画自动连线
void formaxwidget::DrawAutoConnectLine(int Mode,QString SymbolName,double BlkPosx,double BlkPosy,IMxDrawWorldDraw *pDrawWorldDraw)
{
//qDebug()<<"DrawAutoConnectLine,SymbolName="<<SymbolName<<",BlkPosx="<<BlkPosx<<",BlkPosy="<<BlkPosy;
    //计算端口的位置
    if(!FlagAutoConnectLine) return;
    MxDrawPoint* pt= new MxDrawPoint();
    IMxDrawPoint *ptx=(IMxDrawPoint *)pt;
    static double LastTermx,LastTermy;
    static QString LastTermDir;
    static IMxDrawPoint* ConnectPt;
    IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
    IMxDrawBlockTable* blkTable = (IMxDrawBlockTable*)database->querySubObject("GetBlockTable()");
    IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )blkTable->querySubObject("GetAt(QString,bool)",SymbolName ,true);
    IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
    // 循环得到所有实体
    for (; !iter->Done(); iter->Step(true, false))
    {
        // 得到遍历器当前的实体
        IMxDrawEntity* entTerm = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
        if(EntyIsErased(ui->axWidget,entTerm)) continue;//去除erase的实体
        if(entTerm->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
        {
            entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString();
            if(ui->axWidget->dynamicCall("IsOk()").toString()!="true") continue;
            int VCnt=entTerm->property("NumVerts").toInt();
            if(VCnt!=2) continue;
            double x=0;
            double y=0;
            for(int k=0;k<VCnt;k++)
            {
                IMxDrawPoint* pt= (IMxDrawPoint*) entTerm->querySubObject("GetPointAt(int)",k);
                x+=pt->x()/2;
                y+=pt->y()/2;
            }
            ptx->setX(BlkPosx+x-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->x());
            ptx->setY(BlkPosy+y-((IMxDrawPoint *)blkRec->querySubObject("Origin()"))->y());
//qDebug()<<"before FindAutoConnectPt,Ptx="<<ptx->x()<<",Pty="<<ptx->y()<<",LD_PARTLIB_DOTCONDIRECT="<<entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString();
            if((LastTermx!=ptx->x())||(LastTermy!=ptx->y())||LastTermDir!=entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString())
            {
                ConnectPt=FindAutoConnectPt(ptx->x(),ptx->y(),entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString());
                //qDebug()<<"FindAutoConnectPt";
            }
            LastTermx=ptx->x();LastTermy=ptx->y();LastTermDir=entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString();
            if(ConnectPt==nullptr) continue;
            if(Mode==0)
            {
                SetCurLayer(ui->axWidget,"CONNECT");
                ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",ptx->x(),ptx->y(), ConnectPt->x(),ConnectPt->y());
            }
            else
            {
                pDrawWorldDraw->SetColor(QColorToInt(QColor(0,255,0)));
                pDrawWorldDraw->SetLineWidth(0);
                pDrawWorldDraw->dynamicCall("DrawLine(double,double,double,double)",ptx->x(),ptx->y(), ConnectPt->x(),ConnectPt->y());
            }
        }
    }
}

IMxDrawPoint* formaxwidget::FindAutoConnectPt(double Ptx,double Pty,QString LD_PARTLIB_DOTCONDIRECT)
{
   if((LD_PARTLIB_DOTCONDIRECT!="向上")&&(LD_PARTLIB_DOTCONDIRECT!="向下")&&(LD_PARTLIB_DOTCONDIRECT!="向左")&&(LD_PARTLIB_DOTCONDIRECT!="向右")) return nullptr;
   QString AutoConnectPtDir;
   if(LD_PARTLIB_DOTCONDIRECT=="向上") AutoConnectPtDir="向下";
   else if(LD_PARTLIB_DOTCONDIRECT=="向下") AutoConnectPtDir="向上";
   else if(LD_PARTLIB_DOTCONDIRECT=="向左") AutoConnectPtDir="向右";
   else if(LD_PARTLIB_DOTCONDIRECT=="向右") AutoConnectPtDir="向左";
//qDebug()<<"AutoConnectPtDir="<<AutoConnectPtDir<<"Ptx="<<Ptx<<"Pty="<<Pty;;
   MxDrawPoint* tempPt= new MxDrawPoint();
   IMxDrawPoint *pt=(IMxDrawPoint *)tempPt;
   bool FindAutoConnectEnty=false;
   for(int i=0;i<100;i++)
   {
       if(LD_PARTLIB_DOTCONDIRECT=="向上")
       {
           pt->setX(Ptx);
           pt->setY(Pty+2*i+2);
       }
       else if(LD_PARTLIB_DOTCONDIRECT=="向下")
       {
           pt->setX(Ptx);
           pt->setY(Pty-2*i-2);
       }
       else if(LD_PARTLIB_DOTCONDIRECT=="向左")
       {
           pt->setX(Ptx-2*i-2);
           pt->setY(Pty);
       }
       else if(LD_PARTLIB_DOTCONDIRECT=="向右")
       {
           pt->setX(Ptx+2*i+2);
           pt->setY(Pty);
       }
//qDebug()<<"SelectAtPoint"<<pt->x()<<","<<pt->y();
       IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
       IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
       filter->AddStringEx("INSERT",5020);
       ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",pt->asVariant(),filter->asVariant());
//qDebug()<<"count="<<ss->dynamicCall("Count()").toInt();
       for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
       {
           IMxDrawBlockReference *enty=  (IMxDrawBlockReference *)ss->querySubObject("Item(int)",j);
           if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)enty)) return nullptr;//去除erase的实体
           QString sName = enty->dynamicCall("ObjectName()").toString();
           if((enty->dynamicCall("Layer()").toString()!="CONNECT")&&(enty->dynamicCall("Layer()").toString()!="LY_Symb2")) continue;
           //查看当前块是端子还是符号还是Connect还是Link还是Wire（剔除）
           QSqlQuery QuerySearch(T_ProjectDatabase);
           QString Conn_Coordinate=QString::number(pt->x(),'f',0)+".000000,"+QString::number(pt->y(),'f',0)+".000000,0.000000";
           QString StrSql;
           QStringList ListLD_SYMB1LIB_TERMPOINT,ListCoordinate;
//qDebug()<<"Conn_Coordinate="<<Conn_Coordinate;
           if(enty->dynamicCall("Layer()").toString()=="CONNECT")//Connect还是Link还是Wire（剔除）
           {
               if(enty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点"))//Link
               {
                   ListLD_SYMB1LIB_TERMPOINT<<"C"<<"1";
                   ListCoordinate<<"C_Coordinate"<<"Coordinate_1";
               }
               else if(enty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_"))//Connect
               {
                   ListLD_SYMB1LIB_TERMPOINT<<"C"<<"G"<<"1"<<"2"<<"3";
                   ListCoordinate<<"C_Coordinate"<<"G_Coordinate"<<"Coordinate_1"<<"Coordinate_2"<<"Coordinate_3";
               }
           }
           else if(enty->dynamicCall("Layer()").toString()=="LY_Symb2")//端子或符号
           {
               ListCoordinate<<"Conn_Coordinate";
           }
//qDebug()<<"ListCoordinate="<<ListCoordinate;
           for(int k=0;k<ListCoordinate.count();k++)
           {
               if(enty->dynamicCall("Layer()").toString()=="CONNECT")//Connect还是Link还是Wire（剔除）
               {
                   if(enty->dynamicCall("GetBlockName()").toString().contains("SYMB2_M_PWF_链接点"))//Link
                       StrSql="SELECT * FROM Link WHERE Link_Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"' AND "+ListCoordinate.at(k)+" = '"+Conn_Coordinate+"'";
                   else
                       StrSql="SELECT * FROM Connector WHERE Connector_Handle = '"+enty->dynamicCall("handle()").toString()+"' AND Page_ID = '"+QString::number(Page_IDInDB)+"' AND "+ListCoordinate.at(k)+" = '"+Conn_Coordinate+"'";
               }
               else if(enty->dynamicCall("Layer()").toString()=="LY_Symb2")//端子或符号
               {
                   if(enty->dynamicCall("GetxDataString2(QString,int)","LD_SYMB2_SPECIAL",0).toString()=="端子")
                       StrSql="SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+enty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString()+"' AND "+ListCoordinate.at(k)+" = '"+Conn_Coordinate+"'";
                   else
                       StrSql="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+enty->dynamicCall("GetxDataString2(QString,int)","DbId",0).toString()+"' AND "+ListCoordinate.at(k)+" = '"+Conn_Coordinate+"'";
               }
//qDebug()<<"StrSql="<<StrSql;
               QuerySearch.exec(StrSql);
               if(QuerySearch.next())
               {
                   IMxDrawDatabase* database = (IMxDrawDatabase*)ui->axWidget->querySubObject("GetDatabase()");
                   IMxDrawBlockTableRecord* blkRec =(IMxDrawBlockTableRecord* )enty->querySubObject("BlockTableRecord()");
                   IMxDrawBlockTableRecordIterator* iter = (IMxDrawBlockTableRecordIterator*)blkRec->querySubObject("NewIterator()");
                   // 循环得到所有实体
                   for (; !iter->Done(); iter->Step(true, false))
                   {
                       // 得到遍历器当前的实体
                       IMxDrawEntity* entTerm = (IMxDrawEntity*)iter->querySubObject("GetEntity()");
                       if(EntyIsErased(ui->axWidget,entTerm)) continue;//去除erase的实体
                       if(entTerm->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
                       {
//qDebug()<<"Find entTerm,LD_SYMB1LIB_TERMPOINT="<<entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString()<<"LD_SYMB1LIB_TERMPOINT="<<entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString();
                           if(enty->dynamicCall("Layer()").toString()=="LY_Symb2")
                           {
                              if(entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString()!=QuerySearch.value("ConnNum_Logic").toString()) continue;
                           }
                           else
                           {
                             if(entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString()!=ListLD_SYMB1LIB_TERMPOINT.at(k)) continue;
                           }
                           if(entTerm->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString()==AutoConnectPtDir)
                           {
                               //pt必须没有接线
                               IMxDrawSelectionSet *ss2= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
                               IMxDrawResbuf *filter2=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
                               filter2->AddStringEx("LINE",5020);
                               filter2->AddStringEx("CONNECT", 8);
                               ss2->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",pt->asVariant(),filter2->asVariant());
                               for(int j=0;j<ss2->dynamicCall("Count()").toInt();j++)
                               {
                                   IMxDrawLine * CrossLine=  (IMxDrawLine *)ss2->querySubObject("Item(int)",j);
                                   if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
                                   return nullptr;
                               }
                               return pt;
                           }
                           else
                               return nullptr;
                       }
                   }
                   FindAutoConnectEnty=true;
                   break;
               }//end of if(QuerySearch.next())
           }//end of for(int k=0;k<ListLD_SYMB1LIB_TERMPOINT.count();k++)
           if(FindAutoConnectEnty) break;
       }//end of for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
       if(FindAutoConnectEnty) break;
   }//end of for(int i=0;i<100;i++)
   return nullptr;
}

void formaxwidget::CutLine(IMxDrawBlockReference *BlkEnty)//用端点截断导线
{
    QList<IMxDrawPolyline*> listTerm=GetTermEnty(ui->axWidget,BlkEnty->dynamicCall("GetBlockName()").toString());
    QString HandleLine="";
    bool FindTargetLine=false;
    QList<IMxDrawPoint*> ListOnLinePoint;
    ListOnLinePoint.clear();
    IMxDrawLine *CrossLine;
qDebug()<<"listTerm.count()="<<listTerm.count();
    for(int i=0;i<listTerm.count();i++)
    {
        IMxDrawPoint* PtTermPos=GetSymbolBlockTermPos(ui->axWidget,BlkEnty,listTerm.at(i)->dynamicCall("GetxDataString2(QString,QString)","LD_SYMB1LIB_TERMPOINT",0).toString());
        IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)ui->axWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidget->querySubObject("NewResbuf()");
        filter->AddStringEx("LINE",5020);
        filter->AddStringEx("CONNECT", 8);
        ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",PtTermPos->asVariant(),filter->asVariant());
        for(int j=0;j<ss->dynamicCall("Count()").toInt();j++)
        {
            CrossLine=  (IMxDrawLine *)ss->querySubObject("Item(int)",j);
            if(EntyIsErased(ui->axWidget,(IMxDrawEntity *)CrossLine)) continue;//去除erase的实体
            if(HandleLine=="")
            {
                HandleLine=CrossLine->dynamicCall("handle()").toString();
                ListOnLinePoint.append(PtTermPos);
                break;
            }
            else if(HandleLine==CrossLine->dynamicCall("handle()").toString())
            {
                FindTargetLine=true;
                ListOnLinePoint.append(PtTermPos);
                break;
            }
        }
        if(FindTargetLine) break;
    }
    if(HandleLine=="") return;
    if(ListOnLinePoint.count()<2) return;
qDebug()<<"ListOnLinePoint.count()="<<ListOnLinePoint.count();
    SetCurLayer(ui->axWidget,"CONNECT");
    IMxDrawPoint *StartPoint=(IMxDrawPoint *)CrossLine->querySubObject("StartPoint()");
    IMxDrawPoint *EndPoint=(IMxDrawPoint *)CrossLine->querySubObject("EndPoint()");
    int LineCase=0;
    if(ListOnLinePoint.count()==1)//如果只有1个端口在导线上
    {
        //查看端点与直线哪一端比较近
        if((GetLineDir(CrossLine)=="垂直")&&(fabs(StartPoint->y()-ListOnLinePoint.at(0)->y())<fabs(EndPoint->y()-ListOnLinePoint.at(0)->y())))
            LineCase=1;//ListOnLinePoint.at(0)与StartPoint近
        if((GetLineDir(CrossLine)=="水平")&&(fabs(StartPoint->x()-ListOnLinePoint.at(0)->x())<fabs(EndPoint->x()-ListOnLinePoint.at(0)->x())))
            LineCase=1;//ListOnLinePoint.at(0)与StartPoint近
        if(LineCase==1)
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",ListOnLinePoint.at(0)->x(),ListOnLinePoint.at(0)->y(),EndPoint->x(),EndPoint->y());
        else
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",ListOnLinePoint.at(0)->x(),ListOnLinePoint.at(0)->y(),StartPoint->x(),StartPoint->y());
    }
    else if(ListOnLinePoint.count()==2)//如果有2个端口在导线上
    {
        //比较2个端口与导线端点的相对位置
        if(GetLineDir(CrossLine)=="垂直")
        {
            if(ListOnLinePoint.at(0)->y()<ListOnLinePoint.at(1)->y())
            {
                if(StartPoint->y()<EndPoint->y()) LineCase=1;
                else LineCase=2;
            }
            else
            {
                if(StartPoint->y()<EndPoint->y()) LineCase=3;
                else LineCase=4;
            }
        }
        if(GetLineDir(CrossLine)=="水平")
        {
            if(ListOnLinePoint.at(0)->x()<ListOnLinePoint.at(1)->x())
            {
                if(StartPoint->x()<EndPoint->x()) LineCase=1;
                else LineCase=2;
            }
            else
            {
                if(StartPoint->x()<EndPoint->x()) LineCase=3;
                else LineCase=4;
            }
        }
        if(LineCase==1)
        {
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",StartPoint->x(),StartPoint->y(),ListOnLinePoint.at(0)->x(),ListOnLinePoint.at(0)->y());
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",EndPoint->x(),EndPoint->y(),ListOnLinePoint.at(1)->x(),ListOnLinePoint.at(1)->y());
        }
        else if(LineCase==2)
        {
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",EndPoint->x(),EndPoint->y(),ListOnLinePoint.at(0)->x(),ListOnLinePoint.at(0)->y());
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",StartPoint->x(),StartPoint->y(),ListOnLinePoint.at(1)->x(),ListOnLinePoint.at(1)->y());
        }
        else if(LineCase==3)
        {
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",StartPoint->x(),StartPoint->y(),ListOnLinePoint.at(1)->x(),ListOnLinePoint.at(1)->y());
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",EndPoint->x(),EndPoint->y(),ListOnLinePoint.at(0)->x(),ListOnLinePoint.at(0)->y());

        }
        else if(LineCase==4)
        {
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",EndPoint->x(),EndPoint->y(),ListOnLinePoint.at(1)->x(),ListOnLinePoint.at(1)->y());
            ui->axWidget->dynamicCall("DrawLine(double,double,double,double)",StartPoint->x(),StartPoint->y(),ListOnLinePoint.at(0)->x(),ListOnLinePoint.at(0)->y());
        }
    }
    //删除原直线
    ui->axWidget->dynamicCall("Erase(qlonglong)",CrossLine->ObjectID());
    ui->axWidget->dynamicCall("UpdateDisplay()");
}
void formaxwidget::InitAxwidget()
{
    layertypes.clear();
    stLayerPara layer;
    layer.Name="CONNECT"; layer.color=QColor(0,255,0); layer.Wight=McLineWeight::mcLnWt009;layer.LineType="Continuous"; layertypes.append(layer);//导线图层
    layer.Name="LY_Attdef"; layer.color=QColor(255,255,0); layer.Wight=McLineWeight::mcLnWt009;layer.LineType="Continuous"; layertypes.append(layer);//块属性文本
    layer.Name="LY_AttTerm"; layer.color=QColor(255,255,0); layer.Wight=McLineWeight::mcLnWt009;layer.LineType="Continuous"; layertypes.append(layer);//连接点代号
    layer.Name="LY_CDP";layer.color=QColor(0,255,0); layer.Wight=McLineWeight::mcLnWt009;layer.LineType="Continuous"; layertypes.append(layer);//连接定义
    CreateLayer();//初始化层

    styles.clear();
    stTextStyle style;
    //style.Name="WIRE_PIN";style.Font="complex.shx";style.Width=0.8;style.Hieight=2; styles.append(style);
    //style.Name="Standard";style.Font="Standard.shx";style.Width=0.2;style.Hieight=2; styles.append(style);
    CreateTextStyle();//初始化层
    // 修改对像真颜色保存不对问题，把文件格式保存高版本就行。31表示AutoCAD 2013.
    //ui->axWidget->dynamicCall("CallLongParam1(const QString&,int)","Mx_SetDefaultDwgVersion", 31);
    SetGridStyle();

    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","OSMODE",0);
    ui->axWidget->dynamicCall("AddTextStyle2(const QString&,const QString&,double)","MyTrueTypeStyle", "黑体", 0.7);
    ui->axWidget->dynamicCall("AddLinetype(const QString&,const QString&)","MyDotLineType","3,-3");

    //ui->axWidget->dynamicCall("DoCommand(const int&)",114);
    ui->axWidget->setProperty("TextStyle","Standard");
}
void formaxwidget::on_axWidget_OpenFileComplete()
{
    qDebug()<<"on_axWidget_OpenFileComplete";
    InitAxwidget();
}

void formaxwidget::on_axWidget_InitComplete()
{
qDebug()<<"on_axWidget_InitComplete,dwgFileName="<<dwgFileName;
    if(dwgFileName!="") ui->axWidget->dynamicCall("DoCommand(const int&)",100);
}



//绘制诊断链路
void formaxwidget::DrawDiagnoseLinkRoad(QList<int> ListSymbolID)
{
    QSqlQuery QuerySymbol(T_ProjectDatabase);
    QString StrSql;
    for(int SymbolID:ListSymbolID)
    {
        StrSql="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(SymbolID);
        QuerySymbol.exec(StrSql);
        if(QuerySymbol.next())
        {
           QString StrAllLinkRoad=QuerySymbol.value("LinkRoad").toString();
           //根据链路中的源端口优先级进行重新排序
           QStringList ListAllLinkRoad;
           while(1)
           {
               if(!(StrAllLinkRoad.contains("[")&&StrAllLinkRoad.contains("]"))) break;
               int index1=StrAllLinkRoad.indexOf("[");
               int index2=StrAllLinkRoad.indexOf("]");
               ListAllLinkRoad.append(StrAllLinkRoad.mid(index1+1,index2-index1-1));
               StrAllLinkRoad=StrAllLinkRoad.mid(index2+1,StrAllLinkRoad.count()-index2-1);
           }
           if(ListAllLinkRoad.count()<2) continue;
           for(int i=0;i<ListAllLinkRoad.count();i++)
           {
               QString StrSourceConn=ListAllLinkRoad.at(i).split(";").last();
               if((StrSourceConn.split(",").count()!=2)||(StrSourceConn.split(",").at(1)!="0"))
               {
                   ListAllLinkRoad.removeAt(i);
                   continue;
               }
               int SourcePrior=GetSourcePriorBySymbolID(StrSourceConn.split(",").at(0));
               if(SourcePrior<0)
               {
                   ListAllLinkRoad.removeAt(i);
                   continue;
               }
               for(int j=i;j<ListAllLinkRoad.count();j++)
               {
                   QString StrCompareSourceConn=ListAllLinkRoad.at(j).split(";").last();
                   if((StrCompareSourceConn.split(",").count()!=2)||(StrCompareSourceConn.split(",").at(1)!="0")) continue;
                   int CompareSourcePrior=GetSourcePriorBySymbolID(StrCompareSourceConn.split(",").at(0));
                   if(SourcePrior<CompareSourcePrior)
                   {
                       //i j 互换
                       QString tmpStr=ListAllLinkRoad[i];
                       ListAllLinkRoad[i]=ListAllLinkRoad[j];
                       ListAllLinkRoad[j]=tmpStr;
                   }
               }
           }
           //ListAllLinkRoad依次绘制,优先级靠后的跟在优先级靠前的后面 从坐标（50，250）开始绘制
           QString HighPriorSourceConnID=ListAllLinkRoad.at(0).split(";").last().split(",").at(0);
           //根据源端口优先级和终端器件的端口来判断绘制顺序，高优先级源端口在前，确定源端口后,确定对应的终端端口所有的链路
           while(1)
           {
               if(ListAllLinkRoad.count()<=0) break;
               QStringList CurListLinkRoad=ListAllLinkRoad.first().split(";");
               QString ExecConnID=CurListLinkRoad.first().split(",").at(0);
               QString SourceConnID=CurListLinkRoad.last().split(",").at(0);
               //绘制第一个高优先级的源端口链路
/*
               if(SourceConnID==HighPriorSourceConnID)
               //在数据库查看本源端口是否已绘制
               QSqlQuery QueryDiagnoseLinkRoad(T_ProjectDatabase);
               StrSql="SELECT * FROM DiagnoseLinkRoad WHERE SymbolLineID= "+SourceConnID+" AND Type = 0";
               QueryDiagnoseLinkRoad.exec(StrSql);
               if(QueryDiagnoseLinkRoad.next())
               {
                   //本源端口已绘制,顺着源端口链路生成分支
                   while(1)
                   {
                       ParentRoadID=QueryDiagnoseLinkRoad.value("RoadID").toInt();
                       CurListLinkRoad.removeLast();
                       if(CurListLinkRoad.count()<=1) break;//绘制完成
                       StrSql="SELECT * FROM DiagnoseLinkRoad WHERE SymbolLineID = "+CurListLinkRoad.last().split(",").at(0)+" AND Type ="+CurListLinkRoad.last().split(",").at(1);
                       QueryDiagnoseLinkRoad.exec(StrSql);
                       if(!QueryDiagnoseLinkRoad.next())//找到没有绘制节点
                           break;
                   }
               }
               int RoadID=GetMaxIDOfDB(T_ProjectDatabase,"DiagnoseLinkRoad","RoadID");
               StrSql = "INSERT INTO DiagnoseLinkRoad (RoadID,ParentRoadID,SymbolLineID,Type)"
                        "VALUES (:RoadID,:ParentRoadID,:SymbolLineID,:Type)";
               QueryDiagnoseLinkRoad.prepare(StrSql);
               QueryDiagnoseLinkRoad.bindValue(":RoadID",RoadID);
               QueryDiagnoseLinkRoad.bindValue(":ParentRoadID",ParentRoadID);
               QueryDiagnoseLinkRoad.bindValue(":SymbolLineID",CurListLinkRoad.last().split(",").at(0));
               QueryDiagnoseLinkRoad.bindValue(":Type",CurListLinkRoad.last().split(",").at(1));
               QueryDiagnoseLinkRoad.exec();

*/
               //绘制所有该终端端口的链路并更新ListAllLinkRoad
               for(int i=ListAllLinkRoad.count()-1;i>=0;i--)
               {

               }
           }
           for(QString OneLinkRoad:ListAllLinkRoad)
           {
               QStringList ListOneLinkRoad=OneLinkRoad.split(";");
               if(ListOneLinkRoad.count()<1) continue;

               for(int i=ListOneLinkRoad.count()-1;i>=0;i--)
               {
                   if(ListOneLinkRoad.at(i).split(",").count()!=2) break;
                   QString SymbolLineID=ListOneLinkRoad.at(i).split(",").at(0);
                   QString Type=ListOneLinkRoad.at(i).split(",").at(1);
                   //如果是源端口，查看已生成的DiagnoseLinkRoad表中是否存在该端口（不存在则看是否是优先级最高的源端口，是则画在最前面，不是则跟在高优先级源端口链路后面）。如果不是源端口，则根据所在链路绘制干路或者子块
                   if(i==(ListOneLinkRoad.count()-1))//是源端口
                   {

                   }

               }
           }
        }
    }//end of for(int SymbolID:ListSymbolID)
}

//诊断可视化用，将块变红色
bool formaxwidget::SetEntityRed(QString Handle)
{
//qDebug()<<"SetEntityRed,Handle="<<Handle;
    int OriginalColor=0xFFFFFF;
    IMxDrawEntity *Enty=(IMxDrawEntity *)ui->axWidget->querySubObject("HandleToObject(const QString)",Handle);
    if(Enty==nullptr) return false;
    if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
    {
        IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
        if(blkEnty->dynamicCall("GetBlockName()").toString()=="SPS_CDP") OriginalColor=0x00FF00;//导线定义 绿色
        else OriginalColor=0xFFFFFF;//白色
    }
    else OriginalColor=0x00FF00;//导线 绿色

    OriginalColor=0x00FF00;//导线 绿色
//qDebug()<<"OriginalColor="<<OriginalColor;
    // 准备闪烁颜色.
    MxDrawResbuf* colors = new MxDrawResbuf();
    colors->AddLong(255);
    colors->AddLong(OriginalColor);
    ui->axWidget->dynamicCall("SetTwinkeColor(QVariant)",colors->asVariant());
    // 设置闪烁间隔的时间
    ui->axWidget->dynamicCall("SetTwinkeTime(int)",500);
    // 开始闪烁
    ui->axWidget->dynamicCall("TwinkeEnt(QString)",Enty->ObjectID());

    return true;
}

void formaxwidget::LoadText(QString TextStr)
{
    LoadingTextStr=TextStr;
    ui->axWidget->dynamicCall("DoCommand(const int&)",128);
}

void formaxwidget::DoLoadText()
{
    MxDrawUiPrPoint getPt;
    getPt.setMessage("请指定文字位置");
    PickPointCount=0;

    // 等用户在图上点取一个点
    ui->axWidget->dynamicCall("SetSysVarLong(QString,int)","ORTHOMODE",0);
    IMxDrawCustomEntity* spDrawData = getPt.InitUserDraw("DrawMText");
    if (getPt.go() != McUiPrStatus::mcOk)  return;
    Pt1 = GetGridPtVal(getPt.value());
    if (Pt1 == nullptr) {getPt.setMessage("位置无效");return; }  // 返回点的点对象值。
    PickPointCount++;

    //QString BoxText_Handle;
    qlonglong lID=ui->axWidget->dynamicCall("DrawMText(double,double,const QString&,double,double,double,short)",Pt1->x(),Pt1->y(),LoadingTextStr,2.5,0,0,5).toLongLong();
    IMxDrawMText* DTMText= (IMxDrawMText*)ui->axWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
    //BoxText_Handle=DTMText->dynamicCall("handle()").toString();
    DTMText->dynamicCall("setColorIndex(int)",McColor::mcWhite);
    DTMText->SetAttachment(mcAttachmentPointTopLeft);
}



