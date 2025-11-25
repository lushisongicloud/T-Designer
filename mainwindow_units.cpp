#include "mainwindow.h"
#include "ui_mainwindow.h"
#include "equipmenttreemodel.h"
#include <ActiveQt/QAxObject>
#include <ActiveQt/QAxWidget>
#include <QTimer>
#include <QFileInfo>
#include <QFile>
#include <QDir>
#include <QStringList>
#include <QMenu>
#include <QSet>
#include <QInputDialog>
#include <QShortcut>
#include "BO/containerrepository.h"
#include "widget/containertreedialog.h"
#include "DO/containerentity.h"
#include "widget/containerhierarchyutils.h"
#include "widget/functionmanagerdialog.h"
#include "widget/functioneditdialog.h"
#include "BO/function/functionrepository.h"
#include "demo_projectbuilder.h"

using namespace ContainerHierarchy;

void MainWindow::updateCounterLink(int Link_ID,QString LinkText)
{
    qDebug()<<"updateCounterLink,Link_ID="<<Link_ID<<"LinkText="<<LinkText;
    QSqlQuery QueryCounterLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Link WHERE Link_ID = "+QString::number(Link_ID);
    QueryCounterLink.exec(SqlStr);
    if(!QueryCounterLink.next()) return;
    QString dwgfilename=GetPageNameByPageID(QueryCounterLink.value("Page_ID").toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"dwgfilename="<<dwgfilename<<" dwgfilepath="<<dwgfilepath<<"blk handle="<<QueryCounterLink.value("Link_Handle").toString();
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    IMxDrawBlockReference *blkNode;
    //查看是否已经打开改图纸
    bool DwgOpened=false;
    int MdiIndex=0;
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            blkNode= (IMxDrawBlockReference*) ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->querySubObject("HandleToObject(const QString)",QueryCounterLink.value("Link_Handle").toString());
            DwgOpened=true;
            MdiIndex=i;
            break;
        }
    }
    qDebug()<<"DwgOpened="<<DwgOpened<<" ,MdiIndex="<<MdiIndex;
    if(!DwgOpened)
    {
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath);
        blkNode= (IMxDrawBlockReference*) GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryCounterLink.value("Link_Handle").toString());
    }
    if(blkNode==nullptr) {qDebug()<<"blkNode=null";return;}
    QString RetStrLinkTextPosition;
    if(QueryCounterLink.value("LinkText_Location").toString()=="0") RetStrLinkTextPosition="箭头";
    else RetStrLinkTextPosition="箭尾";
    if(DwgOpened) LoadLinkText(((formaxwidget *)ui->mdiArea->subWindowList().at(MdiIndex)->widget())->GetAxWidget(),blkNode,QueryCounterLink.value("Link_Label").toString(),LinkText,RetStrLinkTextPosition,QueryCounterLink.value("Link_Name").toString());
    else LoadLinkText(GlobalBackAxWidget,blkNode,QueryCounterLink.value("Link_Label").toString(),LinkText,RetStrLinkTextPosition,QueryCounterLink.value("Link_Name").toString());
    if(!DwgOpened) //((formaxwidget *)ui->mdiArea->subWindowList().at(MdiIndex)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
        GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}
void MainWindow::DeleteDwgTerminalByPageAndHandle(QString Page_ID,QString Handle)
{
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"DeleteDwgSymbolByPageAndHandle,dwgfilepath="<<dwgfilepath<<"Handle="<<Handle;
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->DeleteEnty(Handle);
            return;
        }
    }
    bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    qDebug()<<"DeleteDwgTerminalByPageAndHandle,OpenDwgFile "<<opened;
    IMxDrawEntity *EntyDelete=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",Handle);
    if(EntyDelete!=nullptr) EntyDelete->dynamicCall("Erase()");
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::UpdateDwgBlkTagByPage_ID(int Page_ID,QString Handle,QString TagStr,QString ProjectStructure_ID)
{
    QString dwgfilename=GetPageNameByPageID(Page_ID);
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->querySubObject("HandleToObject(const QString)",Handle);
            if(BlkEnty!=nullptr)
            {
                if(GetProjectStructureIDByPageID(Page_ID)==ProjectStructure_ID)
                    UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr.mid(TagStr.lastIndexOf("-"),TagStr.count()-TagStr.lastIndexOf("-")));
                else
                    UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr);
                //((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
                return;
            }
        }
    }
    const bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    Q_UNUSED(opened);
    IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",Handle);
    if(BlkEnty!=nullptr)
    {
        if(GetProjectStructureIDByPageID(Page_ID)==ProjectStructure_ID)
            UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr.mid(TagStr.lastIndexOf("-"),TagStr.count()-TagStr.lastIndexOf("-")));
        else
            UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr);
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::DeleteGroup(QString Page_ID,QString GroupName)
{
    qDebug()<<"DeleteGroup";
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("DeleteGroup(QString)",GroupName);
            return;
        }
    }
    const bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    Q_UNUSED(opened);
    GlobalBackAxWidget->dynamicCall("DeleteGroup(QString)",GroupName);
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::DeleteDwgSymbolByPageAndHandle(QString Page_ID,QString Symbol_Handle)
{
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"DeleteDwgSymbolByPageAndHandle,dwgfilepath="<<dwgfilepath<<"Symbol_Handle="<<Symbol_Handle;
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->DeleteEnty(Symbol_Handle);
            return;
        }
    }
    bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<opened;
    IMxDrawEntity *EntyDelete=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",Symbol_Handle);
    if(EntyDelete!=nullptr)
    {
        //如果是黑盒，删除对应的MText
        QString LD_GROUPCPXRECT_TEXT=EntyDelete->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString();
        if(GlobalBackAxWidget->dynamicCall("IsOk()").toString()=="true")
        {
            IMxDrawMText *EntyMText=(IMxDrawMText *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",LD_GROUPCPXRECT_TEXT);
            if(EntyMText!=nullptr) EntyMText->dynamicCall("Erase()");
        }
        EntyDelete->dynamicCall("Erase()");
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::SlotSpurAttr()
{
    ShowSpurAttr(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
}

void MainWindow::UpdateTerminalInstanceByTerminalInstance_ID(int TerminalInstance_ID)
{
    //如果符号名称发生变化，则删除原图块并重新绘制图块
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID= "+QString::number(TerminalInstance_ID);
    QueryTerminalInstance.exec(SqlStr);
    while(QueryTerminalInstance.next())
    {
        if(QueryTerminalInstance.value("Handle").toString()=="") return;
        QString Page_ID=QueryTerminalInstance.value("Page_ID").toString();
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        qDebug()<<"dwgfilepath="<<dwgfilepath;
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) return;

        formaxwidget *formMxdraw;
        bool DwgIsOpened=false;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
                DwgIsOpened=true;
                break;
            }
        }
        if(!DwgIsOpened) {formMxdraw=new formaxwidget(this,dwgfilepath,Page_ID.toInt());formMxdraw->setVisible(false);}
        IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",QueryTerminalInstance.value("Handle").toString());

        //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字
        if(BlkEnty!=nullptr)
        {
            QSqlQuery QueryTerminalStrip=QSqlQuery(T_ProjectDatabase);
            QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QueryTerminalInstance.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(SqlStr);
            if(QueryTerminalStrip.next())
            {
                qDebug()<<"端子/插针代号="<<QueryTerminalInstance.value("Designation").toString();
                //如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
                QString TerminalTag;
                TerminalTag=QueryTerminalStrip.value("DT").toString();
                if(CheckTerminalBeside(TerminalInstance_ID,formMxdraw->GetAxWidget())) TerminalTag="";
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TerminalTag);
                UpdateBlockAttr(BlkEnty,"端子/插针代号",QueryTerminalInstance.value("Designation").toString());
                UpdateBlockAttr(BlkEnty,"左连接点",QueryTerminalInstance.value("LeftTerm").toString());
                UpdateBlockAttr(BlkEnty,"右连接点",QueryTerminalInstance.value("RightTerm").toString());
                UpdateBlockAttr(BlkEnty,"上连接点",QueryTerminalInstance.value("UpTerm").toString());
                UpdateBlockAttr(BlkEnty,"下连接点",QueryTerminalInstance.value("DownTerm").toString());

            }
            formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
        }
        if(!DwgIsOpened) delete formMxdraw;
    }
}

void MainWindow::UpdateTerminalByTerminal_ID(int Terminal_ID)
{
    //如果符号名称发生变化，则删除原图块并重新绘制图块
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE Terminal_ID= '"+QString::number(Terminal_ID)+"'";
    QueryTerminalInstance.exec(SqlStr);
    while(QueryTerminalInstance.next())
    {
        if(QueryTerminalInstance.value("Handle").toString()=="") return;
        QString Page_ID=QueryTerminalInstance.value("Page_ID").toString();
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        qDebug()<<"dwgfilepath="<<dwgfilepath;
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) return;

        formaxwidget *formMxdraw;
        bool DwgIsOpened=false;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
                DwgIsOpened=true;
                break;
            }
        }
        if(!DwgIsOpened) {formMxdraw=new formaxwidget(this,dwgfilepath,Page_ID.toInt());formMxdraw->setVisible(false);}
        IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",QueryTerminalInstance.value("Handle").toString());
        //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字
        if(BlkEnty!=nullptr)
        {
            QSqlQuery QueryTerminalStrip=QSqlQuery(T_ProjectDatabase);
            QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QueryTerminalInstance.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(SqlStr);
            if(QueryTerminalStrip.next())
            {
                //如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
                QString TerminalTag;
                TerminalTag=QueryTerminalStrip.value("DT").toString();

                if(CheckTerminalBeside(Terminal_ID,formMxdraw->GetAxWidget())) TerminalTag="";
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TerminalTag);
                UpdateBlockAttr(BlkEnty,"端子/插针代号",QueryTerminalInstance.value("Designation").toString());
                UpdateBlockAttr(BlkEnty,"左连接点",QueryTerminalInstance.value("LeftTerm").toString());
                UpdateBlockAttr(BlkEnty,"右连接点",QueryTerminalInstance.value("RightTerm").toString());
                UpdateBlockAttr(BlkEnty,"上连接点",QueryTerminalInstance.value("UpTerm").toString());
                UpdateBlockAttr(BlkEnty,"下连接点",QueryTerminalInstance.value("DownTerm").toString());

            }
            formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
        }
        if(!DwgIsOpened) delete formMxdraw;
    }
}

void MainWindow::UpdateSpurBySymbol_ID(int Symbol_ID)
{
    qDebug()<<"UpdateSpurBySymbol_ID,Symbol_ID="<<Symbol_ID;
    //如果符号名称发生变化，则删除原图块并重新绘制图块
    QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(Symbol_ID);
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return;
    if(QuerySymbol.value("Symbol_Handle").toString()=="") return;
    QString Page_ID=QuerySymbol.value("Page_ID").toString();
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"dwgfilepath="<<dwgfilepath;
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    formaxwidget *formMxdraw;
    bool DwgIsOpened=false;
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
            DwgIsOpened=true;
            break;
        }
    }
    if(!DwgIsOpened) {formMxdraw=new formaxwidget(this,dwgfilepath,Page_ID.toInt());formMxdraw->setVisible(false);}

    if((QuerySymbol.value("Symbol").toString()=="")&&(QuerySymbol.value("FunDefine").toString()=="黑盒"))//黑盒
    {
        QString DT_Handle=QuerySymbol.value("DT_Handle").toString();
        IMxDrawMText* DTMText=(IMxDrawMText *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",DT_Handle);
        int Equipment_ID=GetUnitStripIDBySymbolID(QString::number(Symbol_ID),0);
        QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID);
        QueryEquipment.exec(SqlStr);
        QueryEquipment.next();
        QString SymbolTag;
        if(GetProjectStructureIDByPageID(QuerySymbol.value("Page_ID").toInt())==QueryEquipment.value("ProjectStructure_ID").toString())
            SymbolTag="-"+QueryEquipment.value("DT").toString();
        else
            SymbolTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();

        DTMText->dynamicCall("SetContents(QString)",SymbolTag);
        formMxdraw->GetAxWidget()->dynamicCall("UpdateDisplay()");
        return;
    }

    IMxDrawBlockReference *BlkEnty=formMxdraw->UpdateSymbolBlock(QuerySymbol.value("Symbol_Handle").toString(),QuerySymbol.value("Symbol").toString());
    //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字
    if(BlkEnty!=nullptr)
    {
        QString Symbol_Category=QuerySymbol.value("Symbol_Category").toString();
        QString OriginalHandle=QuerySymbol.value("Symbol_Handle").toString();
        qDebug()<<"OriginalHandle="<<OriginalHandle<<" now="<<BlkEnty->dynamicCall("handle()").toString();
        //更新Symbol表
        QSqlQuery QuerySymbolUpdate=QSqlQuery(T_ProjectDatabase);
        QString tempSQL="UPDATE Symbol SET Symbol_Handle=:Symbol_Handle WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbolUpdate.prepare(tempSQL);
        QuerySymbolUpdate.bindValue(":Symbol_Handle",BlkEnty->dynamicCall("handle()").toString());
        QuerySymbolUpdate.exec();

        QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QuerySymbol.value("Equipment_ID").toString();
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QString SymbolTag;
            QSqlQuery QueryProjectStructure = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryEquipment.value("ProjectStructure_ID").toString());
            QueryProjectStructure.exec(SqlStr);
            qDebug()<<"CheckProjectStructure_IDSameOrNot,"<<GetProjectStructureIDByPageID(QuerySymbol.value("Page_ID").toInt())<<" ,"<<QueryEquipment.value("ProjectStructure_ID").toString();
            if(GetProjectStructureIDByPageID(QuerySymbol.value("Page_ID").toInt())==QueryEquipment.value("ProjectStructure_ID").toString())
                SymbolTag="-"+QueryEquipment.value("DT").toString();
            else
                SymbolTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();

            //如果在结构盒内部，则SymbolTag为-Tag
            int  StructBoxVal=CheckStructBox(formMxdraw->GetAxWidget(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y());
            if(StructBoxVal>0) SymbolTag="-"+QueryEquipment.value("DT").toString();

            if(CheckSpinBeside(Symbol_ID,formMxdraw->GetAxWidget())) SymbolTag="";
            int  BlackBoxVal=CheckBlackBox(formMxdraw->GetAxWidget(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y(),Symbol_ID);
            //查看Symbol是否在黑盒内部，如果不是的话返回0，如果是并且黑盒和Symbol是同元件则返回Equipment_ID，如果是并且黑盒和Symbol是不同元件则返回-1
            if(BlackBoxVal!=0) SymbolTag="";
            //这里需要判断是否在黑盒内
            if(OriginalHandle!=BlkEnty->dynamicCall("handle()").toString())
                FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"设备标识符(显示)",SymbolTag);
            else
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)",SymbolTag);
        }
        if(Symbol_Category=="插针")
        {
            if(OriginalHandle!=BlkEnty->dynamicCall("handle()").toString())
                FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"端子/插针代号",QuerySymbol.value("Designation").toString());
            else
                UpdateBlockAttr(BlkEnty,"端子/插针代号",QuerySymbol.value("Designation").toString());
        }
        //更新Symb2TermInfo表
        //更新Symb2TermInfo表，包括Conn_Coordinate，ConnDirection
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QString::number(Symbol_ID)+"'";
        QuerySymb2TermInfo.exec(SqlStr);
        while(QuerySymb2TermInfo.next())
        {
            //如果Symbol_Category是插针，则不添加连接点代号和连接点描述，添加端子/插针代号
            //找到端点并添加块属性
            QString ConnNum_Logic=QuerySymb2TermInfo.value("ConnNum_Logic").toString();
            QString ConnNum=QuerySymb2TermInfo.value("ConnNum").toString();
            QString ConnDesc=QuerySymb2TermInfo.value("ConnDesc").toString();
            if(Symbol_Category!="插针")
            {
                if(OriginalHandle!=BlkEnty->dynamicCall("handle()").toString())
                {
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,ConnNum_Logic,ConnNum);//连接点代号
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"符号的连接点描述["+ConnNum_Logic+"]",ConnDesc);//连接点描述
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"连接点描述（全部）",ConnDesc);//连接点描述（全部）
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"连接点代号（带显示设备标识符）",QueryEquipment.value("DT").toString()+":"+ConnNum);//连接点代号
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"连接点代号（全部）",ConnNum);//连接点代号（全部）
                }
                else
                {
                    UpdateBlockAttr(BlkEnty,ConnNum_Logic,ConnNum);//连接点代号
                    UpdateBlockAttr(BlkEnty,"符号的连接点描述["+ConnNum_Logic+"]",ConnDesc);
                    UpdateBlockAttr(BlkEnty,"连接点描述（全部）",ConnDesc);
                    UpdateBlockAttr(BlkEnty,"连接点代号（带显示设备标识符）",QueryEquipment.value("DT").toString()+":"+ConnNum);//连接点代号
                    UpdateBlockAttr(BlkEnty,"连接点代号（全部）",ConnNum);
                }
            }
            SqlStr="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate WHERE Symb2TermInfo_ID= "+QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString();
            QSqlQuery QueryUpdate = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QueryUpdate.prepare(SqlStr);
            QString InsertionPoint=QString::number(GetSymbolBlockTermPos(formMxdraw->GetAxWidget(),BlkEnty,ConnNum_Logic)->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(formMxdraw->GetAxWidget(),BlkEnty,ConnNum_Logic)->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            QueryUpdate.bindValue(":Conn_Coordinate",InsertionPoint);
            QueryUpdate.exec();
        }
        formMxdraw->GetAxWidget()->dynamicCall("UpdateDisplay()");
        if(!DwgIsOpened) formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
    }
    if(!DwgIsOpened) delete formMxdraw;
}

void MainWindow::ShowSpurAttr(int Symbol_ID)
{
    DialogBranchAttr *dlgBranchAttr=new DialogBranchAttr(this);
    //dlgBranchAttr->move(QApplication::desktop()->screenGeometry().width()/2-dlgBranchAttr->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgBranchAttr->height()/2);
    dlgBranchAttr->LoadSymbolInfo(QString::number(Symbol_ID));
    dlgBranchAttr->show();
    dlgBranchAttr->exec();
    qDebug()<<"dlgBranchAttr->RetCode="<<dlgBranchAttr->RetCode;
    if(dlgBranchAttr->RetCode==1)
    {
        //如果符号发生变化，则删除原图块并重新绘制图块
        QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
        int Equipment_ID=0;
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
        UpdateSpurBySymbol_ID(Symbol_ID);

        SelectEquipment_ID=Equipment_ID;
        SelectSymbol_ID=Symbol_ID;

        if(dlgBranchAttr->DTChanged)
        {
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"' AND Symbol_ID <> "+QString::number(Symbol_ID);
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                UpdateSpurBySymbol_ID(QuerySymbol.value("Symbol_ID").toInt());
            }
        }
        //更新导航窗口
        LoadProjectUnits();
    }
    else if(dlgBranchAttr->RetCode==2)//显示元件属性窗口
    {
        QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
        int Equipment_ID=0;
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
        SelectEquipment_ID=Equipment_ID;
        SelectSymbol_ID=Symbol_ID;
        LoadProjectUnits();
        ShowUnitAttr();
    }
}

bool MainWindow::GetTerminalTagVisible(int TerminalInstanceID,bool Update,bool Visible)
{
    QSqlQuery QueryTerminalInstance= QSqlQuery(T_ProjectDatabase);
    //QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(Terminal_ID);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+QString::number(TerminalInstanceID);
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        QString TerminalHandle=QueryTerminalInstance.value("Handle").toString();
        if(TerminalHandle=="") return true;
        QString Page_ID=QueryTerminalInstance.value("Page_ID").toString();
        QSqlQuery queryPage=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Page WHERE Page_ID= "+Page_ID;
        queryPage.exec(SqlStr);
        if(!queryPage.next()) return true;
        //查看是否已经打开改图纸
        bool AlreadyOpened=false;
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                AlreadyOpened=true;
                break;
            }
        }
        if(!AlreadyOpened) return true;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
            if(formMxdraw->Page_IDInDB==Page_ID.toInt())
            {
                IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",TerminalHandle);
                if(!Update)
                {
                    if(GetBlockAttrTextString(BlkEnty,"设备标识符(显示)")=="") return false;
                    else return true;
                }
                else
                {
                    if(Visible)
                    {
                        QSqlQuery QueryTerminalStrip= QSqlQuery(T_ProjectDatabase);
                        QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+QueryTerminalInstance.value("TerminalStrip_ID").toString();
                        QueryTerminalStrip.exec(SqlStr);
                        if(QueryTerminalStrip.next())
                            UpdateBlockAttr(BlkEnty,"设备标识符(显示)",QueryTerminalStrip.value("DT").toString());
                    }
                    else
                        UpdateBlockAttr(BlkEnty,"设备标识符(显示)","");
                    formMxdraw->GetAxWidget()->dynamicCall("UpdateDisplay()");
                }
                break;
            }
        }
    }
    return false; //Lu ToDo 默认返回值
}

//Mode=0:图纸中双击显示属性 Mode=1:导航栏右键显示端子属性
void MainWindow::ShowTerminalAttr(int Mode,int ID)
{
    DialogSingleTermAttr *dlg=new DialogSingleTermAttr(this);
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    if(Mode==1) dlg->SetCbShowTagVisible(false);
    else if(Mode==0)
    {
        dlg->SetCbShowTagVisible(true);
        dlg->TerminalTagVisible=GetTerminalTagVisible(ID,false,true);
        qDebug()<<"dlg->TerminalTagVisible="<<dlg->TerminalTagVisible;
    }
    int Terminal_ID;
    if(Mode==0) Terminal_ID=GetTerminal_IDByTerminalInstanceID(ID);
    else Terminal_ID=ID;
    if(Mode==0) dlg->LoadInfo(Terminal_ID,ID);
    else dlg->LoadInfo(Terminal_ID,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //如果符号名称发生变化，则删除原图块并重新绘制图块
        QSqlQuery QueryTerminal= QSqlQuery(T_ProjectDatabase);
        int TerminalStrip_ID=0;
        QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(Terminal_ID);
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next())
        {
            TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toInt();
        }
        qDebug()<<"UpdateTerminalByTerminal_ID,ID="<<ID<<",Terminal_ID="<<Terminal_ID<<",Mode="<<Mode;
        if(Mode==0) UpdateTerminalInstanceByTerminalInstance_ID(ID);
        else UpdateTerminalByTerminal_ID(Terminal_ID);
        qDebug()<<"GetTerminalTagVisible";

        qDebug()<<"GetTerminalTagVisible over";
        SelectTerminalStrip_ID=TerminalStrip_ID;
        SelectTerminal_ID=Terminal_ID;
        if(Mode==0) GetTerminalTagVisible(ID,true,dlg->TerminalTagVisible);

        if(dlg->DTChanged)
        {
            SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QString::number(TerminalStrip_ID)+"' AND Terminal_ID <> "+QString::number(Terminal_ID);
            QueryTerminal.exec(SqlStr);
            while(QueryTerminal.next())
            {
                UpdateTerminalByTerminal_ID(QueryTerminal.value("Terminal_ID").toInt());
            }
        }

        //更新导航窗口
        LoadProjectTerminals();
    }
}
void MainWindow::SlotTerminalStripAttr()
{
    SelectTerminalStrip_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
    SelectTerminal_ID=0;
    ShowTerminalStripAttr(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
}

void MainWindow::SlotTerminalAttr()
{
    //Mode=0:图纸中双击显示属性 Mode=1:导航栏右键显示端子属性
    ShowTerminalAttr(1,ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
}
void MainWindow::ShowTerminalStripAttr(int TerminalStrip_ID)
{
    QSqlQuery QueryTerminalStrip_ID=QSqlQuery(T_ProjectDatabase);
    QString SqlStr=QString("SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(TerminalStrip_ID));
    QueryTerminalStrip_ID.exec(SqlStr);
    if(!QueryTerminalStrip_ID.next()) return;
    QString ProjectStructure_ID=QueryTerminalStrip_ID.value("ProjectStructure_ID").toString();
    qDebug()<<"ProjectStructure_ID="<<ProjectStructure_ID;
    QSqlQuery QueryProjectStructure=QSqlQuery(T_ProjectDatabase);
    SqlStr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID= "+ProjectStructure_ID);
    QueryProjectStructure.exec(SqlStr);
    if(!QueryProjectStructure.next()) return;
    QString StrProTag,StrGaoceng,StrPos;
    StrPos=QueryProjectStructure.value("Structure_INT").toString();
    StrProTag+="+"+StrPos;
    qDebug()<<"StrProTag="<<StrProTag;
    DialogTerminalAttr *dlg=new DialogTerminalAttr(this);
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    dlg->setWindowTitle("端子排属性");
    dlg->StrProTag=StrProTag;
    dlg->LoadInfo(2,TerminalStrip_ID);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) {delete dlg;return;}

    QSqlQuery QueryTerminal=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(TerminalStrip_ID)+"'";
    QueryTerminal.exec(SqlStr);
    while(QueryTerminal.next())
    {
        UpdateTerminalByTerminal_ID(QueryTerminal.value("Terminal_ID").toInt());
    }

    LoadProjectTerminals();
    delete dlg;
}

void MainWindow::ShowUnitAttrByEquipment_ID(int Equipment_ID)
{
    QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
    QString SqlStr=QString("SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID));
    QueryEquipment.exec(SqlStr);
    if(!QueryEquipment.next()) return;
    QString StrProTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt());
    //DialogUnitAttr *dlg=new DialogUnitAttr(this);
    //dlgUnitAttr->setGeometry(ui->mdiArea->x(),ui->mdiArea->y(),ui->mdiArea->width()+100,ui->mdiArea->height());
    //dlgUnitAttr->move(QApplication::desktop()->screenGeometry().width()/2-dlgUnitAttr->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgUnitAttr->height()/2);
    dlgUnitAttr->setWindowTitle("元件属性");
    dlgUnitAttr->StrProTag=StrProTag;
    dlgUnitAttr->LoadInfo(2,Equipment_ID);
    dlgUnitAttr->UnitTagChanged=false;
    dlgUnitAttr->UnitTypeChanged=false;
    dlgUnitAttr->setModal(true);
    dlgUnitAttr->show();
    dlgUnitAttr->exec();
    if(dlgUnitAttr->Canceled) {return;}
    SelectEquipment_ID=Equipment_ID;
    SelectSymbol_ID=0;
    if(dlgUnitAttr->UnitTypeChanged)
    {
        qDebug()<<"UnitTypeChanged";
        QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"元件型号改变，是否删除原元件下的功能子块?",
                                                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);
        if(result==QMessageBox::Yes)
        {
            QSqlQuery QueryDeleteSymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(SelectEquipment_ID)+"'";
            QueryDeleteSymbol.exec(SqlStr);
            while(QueryDeleteSymbol.next())
            {
                QString Symbol_ID=QueryDeleteSymbol.value("Symbol_ID").toString();
                //删除已绘制的符号
                if(QueryDeleteSymbol.value("Symbol_Handle").toString()!="")
                {
                    DeleteDwgSymbolByPageAndHandle(QueryDeleteSymbol.value("Page_ID").toString(),QueryDeleteSymbol.value("Symbol_Handle").toString());
                }
                QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                QString temp =  QString("DELETE FROM Symb2TermInfo WHERE Symbol_ID = '"+Symbol_ID+"'");
                querySymb2TermInfo.exec(temp);
            }
            SqlStr =  QString("DELETE FROM Symbol WHERE Equipment_ID= '"+QString::number(SelectEquipment_ID)+"'");
            QueryDeleteSymbol.exec(SqlStr);
        }
        //更新Symbol表和Symb2TermInfo表
        AddSymbTblAndSymb2TermInfoTbl(dlgUnitAttr->LibEquipment_ID,QString::number(SelectEquipment_ID),"",dlgUnitAttr->ListSymbolSpurInfo);
    }
    else
    {
        qDebug()<<"else";
        //如果标号修改了，则更新标号
        if(dlgUnitAttr->UnitTagChanged)
        {
            qDebug()<<"UnitTagChanged";
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+dlgUnitAttr->CurEquipment_ID+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")
                {
                    UpdateSpurBySymbol_ID(QuerySymbol.value("Symbol_ID").toInt());
                }
            }
        }
    }
    LoadProjectUnits();
}

void MainWindow::ShowUnitAttr()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
    ShowUnitAttrByEquipment_ID(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
}

void MainWindow::NewTerminalStrip()//新建端子排
{
    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增端子排；如果是高层，则在高层下的第一个位置新增端子排；如果是位置，则在位置下新增端子排
    QString StrProTag,StrGaoceng,StrPos;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        qDebug()<<"项目";
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在高层
        {
            StrGaoceng=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            qDebug()<<"StrGaoceng="<<StrGaoceng;
            if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->rowCount()>0)//存在位置
                StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
            qDebug()<<"StrPos="<<StrPos;
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        qDebug()<<"高层";
        StrGaoceng=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        qDebug()<<"StrGaoceng="<<StrGaoceng;
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在位置
        {
            StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            qDebug()<<"StrPos="<<StrPos;
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        qDebug()<<"位置";
        StrPos=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        if(ui->treeViewTerminal->currentIndex().parent().isValid())//高层
        {
            StrGaoceng=ui->treeViewTerminal->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
    }
    StrProTag+="="+StrGaoceng+"+"+StrPos;
    DialogTerminalAttr *dlg=new DialogTerminalAttr(this);
    connect(dlg,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    dlg->setWindowTitle("新建端子排");
    dlg->StrProTag=StrProTag;
    dlg->LoadInfo(1,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        LoadProjectTerminals();
    }
    //如果端子符号变更，需要更新dwg文件中的符号

    delete dlg;

}

int MainWindow::PasteTerminalByTerminal_ID(int TerminalStrip_ID,int Terminal_ID)
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID= "+QString::number(Terminal_ID);
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next()) return 0;

    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = QString("INSERT INTO Terminal (Terminal_ID,TerminalStrip_ID,Designation,Symbol,Terminalfunction,TerminalType,TerminalName,PartCode,FunctionText,FunDefine,Factory,OrderNum) "
                     "VALUES (:Terminal_ID,:TerminalStrip_ID,:Designation,:Symbol,:Terminalfunction,:TerminalType,:TerminalName,:PartCode,:FunctionText,:FunDefine,:Factory,:OrderNum)");
    QueryVar.prepare(SqlStr);
    int MaxTerminal_ID=GetMaxIDOfDB(T_ProjectDatabase,"Terminal","Terminal_ID");
    QueryVar.bindValue(":Terminal_ID",MaxTerminal_ID);
    QueryVar.bindValue(":TerminalStrip_ID",QString::number(TerminalStrip_ID));
    QueryVar.bindValue(":Designation",QuerySearch.value("Designation").toString());
    QueryVar.bindValue(":Symbol",QuerySearch.value("Symbol").toString());
    QueryVar.bindValue(":Terminalfunction",QuerySearch.value("Terminalfunction").toString());
    QueryVar.bindValue(":TerminalType",QuerySearch.value("TerminalType").toString());
    QueryVar.bindValue(":TerminalName",QuerySearch.value("TerminalName").toString());
    QueryVar.bindValue(":PartCode",QuerySearch.value("PartCode").toString());
    QueryVar.bindValue(":FunctionText",QuerySearch.value("FunctionText").toString());
    QueryVar.bindValue(":FunDefine",QuerySearch.value("FunDefine").toString());
    QueryVar.bindValue(":Factory",QuerySearch.value("Factory").toString());
    QueryVar.bindValue(":OrderNum",QuerySearch.value("OrderNum").toString());
    QueryVar.exec();

    SqlStr="SELECT * FROM TerminalTerm WHERE Terminal_ID= '"+QString::number(Terminal_ID)+"'";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum) "
                         "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum)");
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":TerminalTerm_ID",GetMaxIDOfDB(T_ProjectDatabase,"TerminalTerm","TerminalTerm_ID"));
        QueryVar.bindValue(":Terminal_ID",QString::number(MaxTerminal_ID));
        QueryVar.bindValue(":ConnNum_Logic",QuerySearch.value("ConnNum_Logic").toString());
        QueryVar.bindValue(":ConnNum",QuerySearch.value("ConnNum").toString());
        QueryVar.exec();
    }
    return MaxTerminal_ID;
}

int MainWindow::PasteSpurBySymbol_ID(int Equipment_ID,int Symbol_ID)
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(Symbol_ID);
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next()) return 0;

    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Designation,Symbol_Handle,Symbol_Remark,FunDefine,FuncType,SourceConn,ExecConn,SourcePrior)"
             " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Designation,:Symbol_Handle,:Symbol_Remark,:FunDefine,:FuncType,:SourceConn,:ExecConn,:SourcePrior)";
    QuerySymbol.prepare(SqlStr);
    int MaxSymbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");
    QuerySymbol.bindValue(":Symbol_ID",MaxSymbol_ID);
    QuerySymbol.bindValue(":Page_ID","");
    QuerySymbol.bindValue(":Equipment_ID",QString::number(Equipment_ID));
    QuerySymbol.bindValue(":Symbol",QuerySearch.value("Symbol").toString());
    QuerySymbol.bindValue(":Symbol_Category",QuerySearch.value("Symbol_Category").toString());
    QuerySymbol.bindValue(":Symbol_Desc",QuerySearch.value("Symbol_Desc").toString());
    QuerySymbol.bindValue(":Designation",QuerySearch.value("Designation").toString());
    QuerySymbol.bindValue(":Symbol_Handle","");
    QuerySymbol.bindValue(":Symbol_Remark",QuerySearch.value("Symbol_Remark").toString());
    QuerySymbol.bindValue(":FunDefine",QuerySearch.value("FunDefine").toString());
    QuerySymbol.bindValue(":FuncType",QuerySearch.value("FuncType").toString());
    QuerySymbol.bindValue(":SourceConn",QuerySearch.value("SourceConn").toBool());
    QuerySymbol.bindValue(":ExecConn",QuerySearch.value("ExecConn").toBool());
    QuerySymbol.bindValue(":SourcePrior",QuerySearch.value("SourcePrior").toString());
    QuerySymbol.exec();

    SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = QString("INSERT INTO Symb2TermInfo (Symb2TermInfo_ID,Symbol_ID,ConnNum_Logic,ConnNum,ConnDirection,Internal,ConnDesc,TestCost)"
                         "VALUES (:Symb2TermInfo_ID,:Symbol_ID,:ConnNum_Logic,:ConnNum,:ConnDirection,:Internal,:ConnDesc,:TestCost)");
        QuerySymb2TermInfo.prepare(SqlStr);
        QuerySymb2TermInfo.bindValue(":Symb2TermInfo_ID",GetMaxIDOfDB(T_ProjectDatabase,"Symb2TermInfo","Symb2TermInfo_ID"));
        QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(MaxSymbol_ID));
        QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QuerySearch.value("ConnNum_Logic").toString());
        QuerySymb2TermInfo.bindValue(":ConnNum",QuerySearch.value("ConnNum").toString());
        QuerySymb2TermInfo.bindValue(":ConnDirection",QuerySearch.value("ConnDirection").toString());
        QuerySymb2TermInfo.bindValue(":Internal",QuerySearch.value("Internal").toString());
        QuerySymb2TermInfo.bindValue(":ConnDesc",QuerySearch.value("ConnDesc").toString());
        QuerySymb2TermInfo.bindValue(":TestCost",QuerySearch.value("TestCost").toString());
        QuerySymb2TermInfo.exec();
    }
    return MaxSymbol_ID;
}

void MainWindow::PasteSpur()//粘贴功能子块
{
    if(CopySymbol_ID<=0) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="元件")
    {
        SelectSymbol_ID=PasteSpurBySymbol_ID(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt(),CopySymbol_ID);
        SelectEquipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
    }
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            SelectSymbol_ID=PasteSpurBySymbol_ID(QuerySearch.value("Equipment_ID").toInt(),CopySymbol_ID);
            SelectEquipment_ID=QuerySearch.value("Equipment_ID").toInt();
        }
    }
    LoadProjectUnits();
}

void MainWindow::PasteTerminalStrip()//粘贴端子排
{
    QString StrProTag,StrGaoceng,StrPos;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在高层
        {
            StrGaoceng=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->rowCount()>0)//存在位置
                StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        StrGaoceng=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在位置
        {
            StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        StrPos=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        if(ui->treeViewTerminal->currentIndex().parent().isValid())//高层
        {
            StrGaoceng=ui->treeViewTerminal->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
    }
    QString ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(CopyTerminalStrip_ID);
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next()) return;

    int MaxTerminalStrip_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalStrip","TerminalStrip_ID");
    //更新T_ProjectDatabase数据库的Equipment表
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = QString("INSERT INTO TerminalStrip (TerminalStrip_ID,DT,ProjectStructure_ID) VALUES (:TerminalStrip_ID,:DT,:ProjectStructure_ID)");
    QueryVar.prepare(SqlStr);
    QueryVar.bindValue(":TerminalStrip_ID",MaxTerminalStrip_ID);
    QueryVar.bindValue(":DT",GetStrRemoveLastNum(QuerySearch.value("DT").toString())+QString::number(GetStrLastNum(QuerySearch.value("DT").toString())+1));
    QueryVar.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
    QueryVar.exec();

    SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(CopyTerminalStrip_ID)+"'";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        PasteTerminalByTerminal_ID(MaxTerminalStrip_ID,QuerySearch.value("Terminal_ID").toInt());
    }
    SelectTerminalStrip_ID=MaxTerminalStrip_ID;
    SelectTerminal_ID=0;
    LoadProjectTerminals();
}

//void MainWindow::PasteUnit()//粘贴元件
//{
//    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增元件；如果是高层，则在高层下的第一个位置新增元件；如果是位置，则在位置下新增元件
//    QString StrProTag,StrGaoceng,StrPos;
//    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
//    {
//        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在高层
//        {
//            StrGaoceng=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
//            if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->rowCount()>0)//存在位置
//                StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
//        }
//    }
//    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
//    {
//        StrGaoceng=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
//        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在位置
//        {
//            StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
//        }
//    }
//    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
//    {
//        StrPos=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
//        if(ui->treeViewUnits->currentIndex().parent().isValid())//高层
//        {
//            StrGaoceng=ui->treeViewUnits->currentIndex().parent().data(Qt::DisplayRole).toString();
//        }
//    }
//    QString ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
//    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
//    QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(CopyEquipment_ID);
//    QuerySearch.exec(SqlStr);
//    if(!QuerySearch.next()) return;

//    int MaxEquipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
//    //更新T_ProjectDatabase数据库的Equipment表
//    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
//    SqlStr = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Eqpt_Category,Name,Desc,PartCode,SymbRemark,OrderNum,Factory,TModel,Structure,RepairInfo,Picture)"
//                     "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Eqpt_Category,:Name,:Desc,:PartCode,:SymbRemark,:OrderNum,:Factory,:TModel,:Structure,:RepairInfo,:Picture)");
//    QueryVar.prepare(SqlStr);
//    QueryVar.bindValue(":Equipment_ID",MaxEquipment_ID);
//    QueryVar.bindValue(":DT",GetStrRemoveLastNum(QuerySearch.value("DT").toString())+QString::number(GetStrLastNum(QuerySearch.value("DT").toString())+1));
//    QueryVar.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
//    QueryVar.bindValue(":Type",QuerySearch.value("Type").toString());
//    QueryVar.bindValue(":Eqpt_Category",QuerySearch.value("Eqpt_Category").toString());//普通元件还是PLC元件
//    QueryVar.bindValue(":Name",QuerySearch.value("Name").toString());
//    QueryVar.bindValue(":Desc",QuerySearch.value("Desc").toString());
//    QueryVar.bindValue(":PartCode",QuerySearch.value("PartCode").toString());
//    QueryVar.bindValue(":SymbRemark",QuerySearch.value("SymbRemark").toString());
//    QueryVar.bindValue(":OrderNum",QuerySearch.value("OrderNum").toString());
//    QueryVar.bindValue(":Factory",QuerySearch.value("Factory").toString());
//    QueryVar.bindValue(":TModel",QuerySearch.value("TModel").toString());
//    QueryVar.bindValue(":Structure",QuerySearch.value("Structure").toString());
//    QueryVar.bindValue(":RepairInfo",QuerySearch.value("RepairInfo").toString());
//    QueryVar.bindValue(":Picture",QuerySearch.value("Picture").toString());
//    QueryVar.exec();

//    SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(CopyEquipment_ID)+"'";
//    QuerySearch.exec(SqlStr);
//    while(QuerySearch.next())
//    {
//        PasteSpurBySymbol_ID(MaxEquipment_ID,QuerySearch.value("Symbol_ID").toInt());
//    }
//    SelectEquipment_ID=MaxEquipment_ID;
//    SelectSymbol_ID=0;
//    LoadProjectUnits();
//}
void MainWindow::PasteUnit()//粘贴元件
{
    // 弹出对话框询问需要粘贴的元件数量
    bool ok;
    int pasteCount = QInputDialog::getInt(this, tr("粘贴元件数量"), tr("请输入要粘贴的元件数量:"), 1, 1, INT_MAX, 1, &ok);
    if (!ok) return; // 用户取消了输入，直接返回

    QString StrProTag,StrGaoceng,StrPos;
    if(!resolveGaocengPosForIndex(ui->treeViewUnits->currentIndex(),StrGaoceng,StrPos))
    {
        QMessageBox::warning(this,tr("粘贴元件"),tr("请先在树中选择有效的高层/位置节点。"));
        return;
    }

    // 循环粘贴逻辑
    int MaxEquipment_ID = 0;
    for (int i = 0; i < pasteCount; ++i) {
        QString ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(CopyEquipment_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) return;

        MaxEquipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Eqpt_Category,Name,Desc,PartCode,SymbRemark,OrderNum,Factory,TModel,Structure,RepairInfo,Picture)"
                         "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Eqpt_Category,:Name,:Desc,:PartCode,:SymbRemark,:OrderNum,:Factory,:TModel,:Structure,:RepairInfo,:Picture)");
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":Equipment_ID",MaxEquipment_ID);
        QueryVar.bindValue(":DT",GetStrRemoveLastNum(QuerySearch.value("DT").toString())+QString::number(GetStrLastNum(QuerySearch.value("DT").toString())+1));
        QueryVar.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
        QueryVar.bindValue(":Type",QuerySearch.value("Type").toString());
        QueryVar.bindValue(":Eqpt_Category",QuerySearch.value("Eqpt_Category").toString());//普通元件还是PLC元件
        QueryVar.bindValue(":Name",QuerySearch.value("Name").toString());
        QueryVar.bindValue(":Desc",QuerySearch.value("Desc").toString());
        QueryVar.bindValue(":PartCode",QuerySearch.value("PartCode").toString());
        QueryVar.bindValue(":SymbRemark",QuerySearch.value("SymbRemark").toString());
        QueryVar.bindValue(":OrderNum",QuerySearch.value("OrderNum").toString());
        QueryVar.bindValue(":Factory",QuerySearch.value("Factory").toString());
        QueryVar.bindValue(":TModel",QuerySearch.value("TModel").toString());
        QueryVar.bindValue(":Structure",QuerySearch.value("Structure").toString());
        QueryVar.bindValue(":RepairInfo",QuerySearch.value("RepairInfo").toString());
        QueryVar.bindValue(":Picture",QuerySearch.value("Picture").toString());
        QueryVar.exec();

        SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(CopyEquipment_ID)+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            PasteSpurBySymbol_ID(MaxEquipment_ID,QuerySearch.value("Symbol_ID").toInt());
        }
        CopyEquipment_ID = MaxEquipment_ID;
    }

    // 设置最后一次粘贴的Equipment_ID和Symbol_ID
    SelectEquipment_ID = MaxEquipment_ID;
    SelectSymbol_ID = 0;
    LoadProjectUnits();
}
void MainWindow::CopySpur()
{
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    CopySymbol_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
}

void MainWindow::CopyTerminalStrip()//复制端子排
{
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子排") return;
    CopyTerminalStrip_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
}

void MainWindow::CopyUnit()//复制元件
{
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
    CopyEquipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
}

void MainWindow::NewUnit()
{
    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增元件；如果是高层，则在高层下的第一个位置新增元件；如果是位置，则在位置下新增元件
    QString StrProTag,StrGaoceng,StrPos;
    resolveGaocengPosForIndex(ui->treeViewUnits->currentIndex(),StrGaoceng,StrPos);
    StrProTag+="="+StrGaoceng+"+"+StrPos;
    //DialogUnitAttr *dlg=new DialogUnitAttr(this);
    //dlgUnitAttr->setGeometry(ui->mdiArea->x(),ui->mdiArea->y(),ui->mdiArea->width(),ui->mdiArea->height());
    connect(dlgUnitAttr,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
    //connect(dlg,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
    //dlgUnitAttr->move(QApplication::desktop()->screenGeometry().width()/2-dlgUnitAttr->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgUnitAttr->height()/2);
    dlgUnitAttr->setWindowTitle("新建元件");
    dlgUnitAttr->StrProTag=StrProTag;
    dlgUnitAttr->InitUIInfo();
    dlgUnitAttr->LoadInfo(1,0);
    dlgUnitAttr->setModal(true);
    dlgUnitAttr->show();
    dlgUnitAttr->exec();
}

void MainWindow::DeleteTerminalStrip()
{
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子排") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除端子排?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewTerminal->selectionModel()->selectedIndexes().count();i++)
    {
        int TerminalStrip_ID=ui->treeViewTerminal->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
        SelectTerminalStrip_ID=0;
        SelectTerminal_ID=0;

        QSqlQuery query=QSqlQuery(T_ProjectDatabase);
        QString temp =  QString("DELETE FROM TerminalStrip WHERE TerminalStrip_ID="+QString::number(TerminalStrip_ID));
        query.exec(temp);
        temp="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(TerminalStrip_ID)+"'";
        query.exec(temp);
        while(query.next())
        {
            QString Terminal_ID=query.value("Terminal_ID").toString();
            //删除已绘制的符号
            if(query.value("Handle").toString()!="") DeleteDwgTerminalByPageAndHandle(query.value("Page_ID").toString(),query.value("Handle").toString());
            QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM queryTerminalTerm WHERE Terminal_ID = '"+Terminal_ID+"'");
            queryTerminalTerm.exec(temp);
        }
        temp =  QString("DELETE FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(TerminalStrip_ID)+"'");
        query.exec(temp);
    }
    LoadProjectTerminals();
}

void MainWindow::DeleteTerminal()
{
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除端子?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    SelectTerminalStrip_ID=0;
    SelectTerminal_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
    QSqlQuery query=QSqlQuery(T_ProjectDatabase);
    QString temp =  "DELETE FROM TerminalTerm WHERE Terminal_ID= '"+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt())+"'";
    query.exec(temp);

    temp= "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
    query.exec(temp);
    if(query.next())
    {
        DeleteDwgTerminalByPageAndHandle(query.value("Page_ID").toString(),query.value("Handle").toString());
    }

    temp =  "DELETE FROM Terminal WHERE Terminal_ID= "+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
    query.exec(temp);
    LoadProjectTerminals();
}

void MainWindow::NewSpurTemplate()
{
    DialogUnitManage *dlg=new DialogUnitManage(this);
    dlg->setModal(true);
    dlg->SetStackWidget(0);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    qDebug()<<"EquipmentTemplate_ID="<<dlg->EquipmentTemplate_ID;
    if(dlg->EquipmentTemplate_ID<=0) {delete dlg;return;}
    //确认当前的元件Equipment_ID
    int Equipment_ID=0;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="元件")
    {
        Equipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
    }
    qDebug()<<"Equipment_ID="<<Equipment_ID;
    SelectSymbol_ID=AddSymbTblAndSymb2TermInfoTbl(dlg->CurEquipment_ID,QString::number(Equipment_ID),QString::number(dlg->EquipmentTemplate_ID),{});
    SelectEquipment_ID=Equipment_ID;
    LoadProjectUnits();
    delete dlg;
}

void MainWindow::NewTerminal()//新建端子
{
    int TerminalStrip_ID=0;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="端子")
    {
        QSqlQuery QueryTerminal=QSqlQuery(T_ProjectDatabase);
        QString SqlStr= "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next())
        {
            TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toInt();
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="端子排")
    {
        TerminalStrip_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
    }

    DialogNewSpur *dlg =new DialogNewSpur(this,1);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    //检查是否与已有端号重复
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    for(int i=0;i<dlg->ListTermNum.count();i++)
    {
        SqlStr= "SELECT * FROM Terminal WHERE TerminalStrip_ID = "+QString::number(TerminalStrip_ID)+" AND Designation = '"+dlg->ListTermNum.at(i)+"'";
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"存在增加端子与已有序号重复，是否继续添加端子?",
                                                                    QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

            if(result!=QMessageBox::Yes)
            {
                return;
            }
        }
    }


    int Terminal_ID;
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    for(int i=0;i<dlg->SpurCount;i++)
    {
        QString SqlStr = QString("INSERT INTO Terminal (Terminal_ID,TerminalStrip_ID,Designation,Symbol,Terminalfunction,TerminalType,TerminalName,PartCode,FunctionText,FunDefine,Factory,OrderNum) "
                                 "VALUES (:Terminal_ID,:TerminalStrip_ID,:Designation,:Symbol,:Terminalfunction,:TerminalType,:TerminalName,:PartCode,:FunctionText,:FunDefine,:Factory,:OrderNum)");
        QueryVar.prepare(SqlStr);
        Terminal_ID=GetMaxIDOfDB(T_ProjectDatabase,"Terminal","Terminal_ID");
        QueryVar.bindValue(":Terminal_ID",Terminal_ID);
        QueryVar.bindValue(":TerminalStrip_ID",QString::number(TerminalStrip_ID));
        QueryVar.bindValue(":Designation",dlg->ListTermNum.at(i));
        QueryVar.bindValue(":Symbol",dlg->SPSName);
        QueryVar.bindValue(":Terminalfunction","");
        QueryVar.bindValue(":TerminalType","");
        QueryVar.bindValue(":TerminalName","");
        QueryVar.bindValue(":PartCode","");
        QueryVar.bindValue(":FunctionText","");
        QueryVar.bindValue(":FunDefine",dlg->FunctionDefineName);
        QueryVar.bindValue(":Factory","");
        QueryVar.bindValue(":OrderNum","");
        QueryVar.exec();
        //根据端子有几个连接点insert记录到TerminalTerm表
        QString DwgPath;
        DwgPath="C:/TBD/SPS/"+dlg->SPSName+".dwg";
        int TermCount=GetDwgTermCount(DwgPath,dlg->SPSName);
        for(int j=0;j<TermCount;j++)
        {
            int MaxTerminalTerm_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalTerm","TerminalTerm_ID");
            SqlStr = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum) "
                             "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum)");
            QueryVar.prepare(SqlStr);
            QueryVar.bindValue(":TerminalTerm_ID",MaxTerminalTerm_ID);
            QueryVar.bindValue(":Terminal_ID",QString::number(Terminal_ID));
            QueryVar.bindValue(":ConnNum_Logic",QString::number(j+1));
            QueryVar.bindValue(":ConnNum",QString::number(j+1));
            QueryVar.exec();
        }
    }
    SelectTerminalStrip_ID=TerminalStrip_ID;
    SelectTerminal_ID=Terminal_ID;
    LoadProjectTerminals();
    delete dlg;
}


void MainWindow::SlotNewSpur()
{
    //确认当前的元件Equipment_ID
    int Equipment_ID=0;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="元件")
    {
        Equipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
    }

    DialogNewSpur *dlg =new DialogNewSpur(this,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    QString Symbol_Category="",FunDefine="",Symbol_Desc="";
    QSqlQuery QueryFunctionDefineClass = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+dlg->FunctionDefineClass_ID+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    QueryFunctionDefineClass.next();

    FunDefine=QueryFunctionDefineClass.value("FunctionDefineName").toString();
    Symbol_Desc=QueryFunctionDefineClass.value("Desc").toString();
    SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QueryFunctionDefineClass.value("ParentNo").toString()+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    QueryFunctionDefineClass.next();
    SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QueryFunctionDefineClass.value("ParentNo").toString()+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    QueryFunctionDefineClass.next();
    Symbol_Category=QueryFunctionDefineClass.value("FunctionDefineName").toString();
    int Symbol_ID;
    qDebug()<<"dlg->SpurCount="<<dlg->SpurCount;
    for(int i=0;i<dlg->SpurCount;i++)
    {
        SqlStr = "INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Designation,Symbol_Handle,Symbol_Remark,FunDefine,InsertionPoint)"
                 " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Designation,:Symbol_Handle,:Symbol_Remark,:FunDefine,:InsertionPoint)";
        QuerySymbol.prepare(SqlStr);
        Symbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");
        QuerySymbol.bindValue(":Symbol_ID",Symbol_ID);
        QuerySymbol.bindValue(":Page_ID","");
        QuerySymbol.bindValue(":Equipment_ID",QString::number(Equipment_ID));
        QuerySymbol.bindValue(":Symbol",dlg->SPSName);
        QuerySymbol.bindValue(":Symbol_Category",Symbol_Category);
        QuerySymbol.bindValue(":Symbol_Desc",Symbol_Desc);
        QuerySymbol.bindValue(":Designation","");
        QString DwgPath="C:/TBD/SPS/"+dlg->SPSName+".dwg";
        QuerySymbol.bindValue(":Symbol_Remark",GetDwgDicData(DwgPath,dlg->SPSName,"推荐名称"));
        QuerySymbol.bindValue(":FunDefine",FunDefine);
        QuerySymbol.bindValue(":Symbol_Handle","");
        QuerySymbol.bindValue(":InsertionPoint","");
        QuerySymbol.exec();

        for(int j=0;j<dlg->TermCount;j++)
        {
            //更新Symb2TermInfo表
            QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = QString("INSERT INTO Symb2TermInfo (Symb2TermInfo_ID,Symbol_ID,ConnNum_Logic,ConnNum,ConnDirection,Internal,ConnDesc,TestCost)"
                             "VALUES (:Symb2TermInfo_ID,:Symbol_ID,:ConnNum_Logic,:ConnNum,:ConnDirection,:Internal,:ConnDesc,:TestCost)");
            QuerySymb2TermInfo.prepare(SqlStr);
            QuerySymb2TermInfo.bindValue(":Symb2TermInfo_ID",GetMaxIDOfDB(T_ProjectDatabase,"Symb2TermInfo","Symb2TermInfo_ID"));
            QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(Symbol_ID));
            QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QString::number(j+1));
            if(dlg->ListTermNum.count()==dlg->TermCount) QuerySymb2TermInfo.bindValue(":ConnNum",dlg->ListTermNum.at(j));
            else QuerySymb2TermInfo.bindValue(":ConnNum",QString::number(j+1));
            //根据dwg文件确定连接点连线方向
            QStringList listTermInfo=GetDwgTermData(DwgPath,dlg->SPSName,j+1);
            if(listTermInfo.count()==2)
            {
                QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
                if(listTermInfo.at(1)=="是")
                    QuerySymb2TermInfo.bindValue(":Internal",1);
                else QuerySymb2TermInfo.bindValue(":Internal",0);
            }
            else
            {
                QuerySymb2TermInfo.bindValue(":ConnDirection","");
                QuerySymb2TermInfo.bindValue(":Internal",0);
            }
            QuerySymb2TermInfo.bindValue(":ConnDesc","");
            QuerySymb2TermInfo.bindValue(":TestCost","");
            QuerySymb2TermInfo.exec();
        }
    }
    SelectEquipment_ID=Equipment_ID;
    SelectSymbol_ID=Symbol_ID;
    LoadProjectUnits();

    delete dlg;
}

void MainWindow::DeleteSpur()
{
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="功能子块") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除功能子块?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
    {
        int Symbol_ID=ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
        qDebug()<<"Symbol_ID="<<Symbol_ID;
        QSqlQuery query=QSqlQuery(T_ProjectDatabase);
        QString temp =  "DELETE FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
        query.exec(temp);

        temp= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
        query.exec(temp);
        if(query.next())
        {
            DeleteDwgSymbolByPageAndHandle(query.value("Page_ID").toString(),query.value("Symbol_Handle").toString());
        }
        temp =  "DELETE FROM Symbol WHERE Symbol_ID= "+QString::number(Symbol_ID);
        query.exec(temp);
        SelectEquipment_ID=0;
        SelectSymbol_ID=0;
    }

    LoadProjectUnits();
}
void MainWindow::DeleteUnit()
{
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="元件") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除元件?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
    {
        int Equipment_ID=ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
        SelectEquipment_ID=0;
        SelectSymbol_ID=0;
        QString StrUnitsInfo;
        QSqlQuery query=QSqlQuery(T_ProjectDatabase);
        QString temp="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID);
        query.exec(temp);
        if(query.next())
        {
            qDebug()<<"add info to RemovedUnitsInfo";
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
        temp =  QString("DELETE FROM Equipment WHERE Equipment_ID="+QString::number(Equipment_ID));
        query.exec(temp);
        temp="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(Equipment_ID)+"'";
        query.exec(temp);
        QStringList ListPageID;
        while(query.next())
        {
            QString Symbol_ID=query.value("Symbol_ID").toString();
            //删除已绘制的符号
            if(query.value("Symbol_Handle").toString()!="") DeleteDwgSymbolByPageAndHandle(query.value("Page_ID").toString(),query.value("Symbol_Handle").toString());
            if(!ListPageID.contains(query.value("Page_ID").toString())) ListPageID.append(query.value("Page_ID").toString());
            QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM Symb2TermInfo WHERE Symbol_ID = '"+Symbol_ID+"'");
            querySymb2TermInfo.exec(temp);
        }
        //删除编组
        if(ListPageID.count()==1) DeleteGroup(ListPageID.at(0),QString::number(Equipment_ID));

        temp =  QString("DELETE FROM Symbol WHERE Equipment_ID= '"+QString::number(Equipment_ID)+"'");
        query.exec(temp);
    }
    LoadProjectUnits();
}

void MainWindow::ShowTerminalInDwgByTerminalID(QString TerminalID)
{
    QSqlQuery queryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE Terminal_ID= '"+TerminalID+"'";
    queryTerminalInstance.exec(SqlStr);
    if(queryTerminalInstance.next())
    {
        QString Terminal_Handle=queryTerminalInstance.value("Handle").toString();
        if(Terminal_Handle=="") return;
        QString Page_ID=queryTerminalInstance.value("Page_ID").toString();
        QSqlQuery queryPage=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Page WHERE Page_ID= "+Page_ID;
        queryPage.exec(SqlStr);
        if(!queryPage.next()) return;
        qDebug()<<"Page_ID="<<Page_ID;

        //查看是否已经打开改图纸
        bool AlreadyOpened=false;
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                AlreadyOpened=true;
                break;
            }
        }
        if(!AlreadyOpened) OpenDwgPageByPageID(Page_ID.toInt());//打开对应的图纸

        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
            qDebug()<<"formMxdraw->Page_IDInDB="<<formMxdraw->Page_IDInDB;
            if(formMxdraw->Page_IDInDB==Page_ID.toInt())
            {
                ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
                formMxdraw->DataBaseTerminalInstanceID=queryTerminalInstance.value("TerminalInstanceID").toString();
                if(AlreadyOpened) formMxdraw->SetTerminalHighLight();
                else formMxdraw->FlagSetTerminalHighLight=true;
                break;
            }
        }
    }

}

void MainWindow::ShowTerminalInDwg()
{
    if(!ui->treeViewTerminal->currentIndex().isValid()) return;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    ShowTerminalInDwgByTerminalID(QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt()));
}

void MainWindow::ShowSpurInDwgBySymbolID(QString SymbolID)
{
    QSqlQuery querySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+SymbolID;
    querySymbol.exec(SqlStr);
    if(!querySymbol.next()) return;
    QString Symbol_Handle=querySymbol.value("Symbol_Handle").toString();
    if(Symbol_Handle=="") return;
    QString Page_ID=querySymbol.value("Page_ID").toString();
    QSqlQuery queryPage=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Page WHERE Page_ID= "+Page_ID;
    queryPage.exec(SqlStr);
    if(!queryPage.next()) return;
    qDebug()<<"Page_ID="<<Page_ID;

    //查看是否已经打开改图纸
    bool AlreadyOpened=false;
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            AlreadyOpened=true;
            break;
        }
    }
    if(!AlreadyOpened) OpenDwgPageByPageID(Page_ID.toInt());//打开对应的图纸

    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
        qDebug()<<"formMxdraw->Page_IDInDB="<<formMxdraw->Page_IDInDB;
        if(formMxdraw->Page_IDInDB==Page_ID.toInt())
        {
            ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
            formMxdraw->DataBaseSymbolID=SymbolID;
            if(AlreadyOpened) formMxdraw->SetSymbolSpurHighLight();
            else formMxdraw->FlagSetSymbolSpurHighLight=true;
            break;
        }
    }
}

void MainWindow::ShowSpurInDwg()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    ShowSpurInDwgBySymbolID(QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt()));

}

void MainWindow::ShowLineByUnitTargetInDwg()
{
    QStringList ListLineItemData=ui->treeViewLineByUnit->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;

    if(ListLineItemData.at(4)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(3);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(4)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(3);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowLineTargetInDwg()//转到目标
{
    QStringList ListLineItemData=ui->treeViewLineDT->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;

    if(ListLineItemData.at(4)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(3);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(4)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(3);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowLineByUnitSourceInDwg()
{
    QStringList ListLineItemData=ui->treeViewLineByUnit->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;
    if(ListLineItemData.at(2)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(1);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(2)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(1);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowLineSourceInDwg()//转到源
{
    QStringList ListLineItemData=ui->treeViewLineDT->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;
    if(ListLineItemData.at(2)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(1);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(2)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(1);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowtreeViewLineByUnitPopMenu(const QPoint &pos)
{
    if(!ui->treeViewLineByUnit->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewLineByUnit->indexAt(pos).data(Qt::WhatsThisRole).toString()!="功能子块") return;

    QAction actShowLineTarget("转到目标", this);
    tree_menu.addAction(&actShowLineTarget);
    connect(&actShowLineTarget,SIGNAL(triggered()),this,SLOT(ShowLineByUnitTargetInDwg()));
    QAction actShowLineSource("转到源", this);
    tree_menu.addAction(&actShowLineSource);
    connect(&actShowLineSource,SIGNAL(triggered()),this,SLOT(ShowLineByUnitSourceInDwg()));
    tree_menu.exec(QCursor::pos());
}

void MainWindow::ShowtreeViewLineDTPopMenu(const QPoint &pos)
{
    if(!ui->treeViewLineDT->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewLineDT->indexAt(pos).data(Qt::WhatsThisRole).toString()!="连线") return;

    QAction actShowLineTarget("转到目标", this);
    tree_menu.addAction(&actShowLineTarget);
    connect(&actShowLineTarget,SIGNAL(triggered()),this,SLOT(ShowLineTargetInDwg()));
    QAction actShowLineSource("转到源", this);
    tree_menu.addAction(&actShowLineSource);
    connect(&actShowLineSource,SIGNAL(triggered()),this,SLOT(ShowLineSourceInDwg()));
    tree_menu.exec(QCursor::pos());
}

void MainWindow::ShowtreeViewTerminalPopMenu(const QPoint &pos)
{
    if(!ui->treeViewTerminal->indexAt(pos).isValid()) return;
    bool CurPageValid=false;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(file.exists())
            {
                CurPageValid=true;
            }
        }
    }
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if((ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="项目")||(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="高层")||(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="位置"))
    {
        QAction actNewTerminalStrip("新建端子排", this);
        tree_menu.addAction(&actNewTerminalStrip);
        connect(&actNewTerminalStrip,SIGNAL(triggered()),this,SLOT(NewTerminalStrip()));
        QAction actPasteTerminal("粘贴端子排", this);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(CopyTerminalStrip_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteTerminal.setEnabled(false);
        tree_menu.addAction(&actPasteTerminal);
        connect(&actPasteTerminal,SIGNAL(triggered()),this,SLOT(PasteTerminalStrip()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="端子排")
    {
        QAction actNewTerminal("新建端子", this);
        tree_menu.addAction(&actNewTerminal);
        connect(&actNewTerminal,SIGNAL(triggered()),this,SLOT(NewTerminal()));
        QAction actTerminalAttr("端子排属性", this);
        tree_menu.addAction(&actTerminalAttr);
        connect(&actTerminalAttr,SIGNAL(triggered()),this,SLOT(SlotTerminalStripAttr()));
        QAction actDeleteTerminal("删除端子排", this);
        tree_menu.addAction(&actDeleteTerminal);
        connect(&actDeleteTerminal,SIGNAL(triggered()),this,SLOT(DeleteTerminalStrip()));
        QAction actCopyTerminal("复制端子排", this);
        tree_menu.addAction(&actCopyTerminal);
        connect(&actCopyTerminal,SIGNAL(triggered()),this,SLOT(CopyTerminalStrip()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="端子")
    {
        QAction actLoadTerminal("绘制端子", this);
        if(!CurPageValid) actLoadTerminal.setEnabled(false);
        tree_menu.addAction(&actLoadTerminal);
        connect(&actLoadTerminal,SIGNAL(triggered()),this,SLOT(SlotLoadTerminal()));
        QAction actNewTerminal("新建端子", this);
        tree_menu.addAction(&actNewTerminal);
        connect(&actNewTerminal,SIGNAL(triggered()),this,SLOT(NewTerminal()));
        QAction actTerminalAttr("端子属性", this);
        tree_menu.addAction(&actTerminalAttr);
        connect(&actTerminalAttr,SIGNAL(triggered()),this,SLOT(SlotTerminalAttr()));
        QAction actDeleteTerminal("删除端子", this);
        tree_menu.addAction(&actDeleteTerminal);
        connect(&actDeleteTerminal,SIGNAL(triggered()),this,SLOT(DeleteTerminal()));
        QAction actShowTerminalInDwg("转到图形", this);
        tree_menu.addAction(&actShowTerminalInDwg);
        connect(&actShowTerminalInDwg,SIGNAL(triggered()),this,SLOT(ShowTerminalInDwg()));
        QAction actDrawTerminalEqualDistance("等距绘制", this);
        if(!CurPageValid) actDrawTerminalEqualDistance.setEnabled(false);
        if(ui->treeViewTerminal->selectionModel()->selectedIndexes().count()<=1) actDrawTerminalEqualDistance.setEnabled(false);
        tree_menu.addAction(&actDrawTerminalEqualDistance);
        connect(&actDrawTerminalEqualDistance,SIGNAL(triggered()),this,SLOT(DrawTerminalEqualDistance()));
        tree_menu.exec(QCursor::pos());
    }
}

void MainWindow::ShowtreeViewUnitsPopMenu(const QPoint &pos)
{
    if(!ui->treeViewUnits->indexAt(pos).isValid()) return;
    bool CurPageValid=false;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(file.exists())
            {
                CurPageValid=true;
            }
        }
    }
    qDebug()<<"CurPageValid="<<CurPageValid;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if((ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="项目")||(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="高层")||(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="位置"))
    {
        QAction actNewUnit("新建元件", this);
        tree_menu.addAction(&actNewUnit);
        connect(&actNewUnit,SIGNAL(triggered()),this,SLOT(NewUnit()));
        QAction actPasteUnit("粘贴元件", this);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(CopyEquipment_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteUnit.setEnabled(false);
        tree_menu.addAction(&actPasteUnit);
        connect(&actPasteUnit,SIGNAL(triggered()),this,SLOT(PasteUnit()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="元件")
    {
        QAction actNewSpur("新建子块", this);
        tree_menu.addAction(&actNewSpur);
        connect(&actNewSpur,SIGNAL(triggered()),this,SLOT(SlotNewSpur()));
        QAction actNewSpurTemplate("新建子块(模板)", this);
        tree_menu.addAction(&actNewSpurTemplate);
        connect(&actNewSpurTemplate,SIGNAL(triggered()),this,SLOT(NewSpurTemplate()));
        QAction actUnitAttr("元件属性", this);
        tree_menu.addAction(&actUnitAttr);
        connect(&actUnitAttr,SIGNAL(triggered()),this,SLOT(ShowUnitAttr()));
        QAction actDeleteUnit("删除", this);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="元件")
            {
                actDeleteUnit.setEnabled(false);
                break;
            }
        }
        tree_menu.addAction(&actDeleteUnit);
        connect(&actDeleteUnit,SIGNAL(triggered()),this,SLOT(DeleteUnit()));
        QAction actCopyUnit("复制元件", this);
        tree_menu.addAction(&actCopyUnit);
        connect(&actCopyUnit,SIGNAL(triggered()),this,SLOT(CopyUnit()));

        QMenu LoadUnitTree_menu("整体放置");
        tree_menu.addMenu(&LoadUnitTree_menu);
        QAction actLoadUnitStamp("接线图章", this);
        LoadUnitTree_menu.addAction(&actLoadUnitStamp);
        connect(&actLoadUnitStamp,SIGNAL(triggered()),this,SLOT(LoadUnitStamp()));
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()!=1) actLoadUnitStamp.setEnabled(false);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+ui->treeViewUnits->indexAt(pos).data(Qt::UserRole).toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            QSqlQuery QuerySearchLib=QSqlQuery(T_LibDatabase);
            SqlStr="SELECT * FROM Equipment WHERE PartCode= '"+QuerySearch.value("PartCode").toString()+"'";
            QuerySearchLib.exec(SqlStr);
            if(QuerySearchLib.next())
            {
                if(QuerySearchLib.value("MultiLib").toString()=="") actLoadUnitStamp.setEnabled(false);
            }
        }
        QAction actLoadUnitAllTermsUp("全部向上", this);
        LoadUnitTree_menu.addAction(&actLoadUnitAllTermsUp);
        connect(&actLoadUnitAllTermsUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitAllTermsUp()));
        QAction actLoadUnitAllTermsDown("全部向下", this);
        LoadUnitTree_menu.addAction(&actLoadUnitAllTermsDown);
        connect(&actLoadUnitAllTermsDown,SIGNAL(triggered()),this,SLOT(LoadWholeUnitAllTermsDown()));
        QAction actLoadUnitOddTermsUp("奇数向上，偶数向下", this);
        LoadUnitTree_menu.addAction(&actLoadUnitOddTermsUp);
        connect(&actLoadUnitOddTermsUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitOddTermsUp()));
        QAction actLoadUnitEvenTermsUp("奇数向下，偶数向上", this);
        LoadUnitTree_menu.addAction(&actLoadUnitEvenTermsUp);
        connect(&actLoadUnitEvenTermsUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitEvenTermsUp()));
        QAction actLoadUnitFirstHalfUp("前半部分向上，后面向下", this);
        LoadUnitTree_menu.addAction(&actLoadUnitFirstHalfUp);
        connect(&actLoadUnitFirstHalfUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitFirstHalfUp()));
        QAction actLoadUnitLastHalfUp("前半部分向下，后面向上", this);
        LoadUnitTree_menu.addAction(&actLoadUnitLastHalfUp);
        connect(&actLoadUnitLastHalfUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitLastHalfUp()));

        QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
        QString sqlstr;
        QModelIndex equipmentIndex = ui->treeViewUnits->indexAt(pos);
        if (m_equipmentTreeModel && equipmentIndex.isValid()) {
            int childCount = m_equipmentTreeModel->rowCount(equipmentIndex);
            for (int i = 0; i < childCount; ++i)
            {
                QModelIndex symbolIndex = m_equipmentTreeModel->index(i, 0, equipmentIndex);
                int symbolId = symbolIndex.data(Qt::UserRole).toInt();
                sqlstr = QString("SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '%1'").arg(symbolId);
                QuerySymb2TermInfo.exec(sqlstr);
                int TermCount=0;
                while(QuerySymb2TermInfo.next()) TermCount++;
                if(TermCount>1)
                {
                    LoadUnitTree_menu.setEnabled(false);
                    break;
                }
            }
        }

        QAction actNewUnit("新建元件", this);
        tree_menu.addAction(&actNewUnit);
        connect(&actNewUnit,SIGNAL(triggered()),this,SLOT(NewUnit()));
        QAction actPasteSpur("粘贴子块", this);
        SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(CopySymbol_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteSpur.setEnabled(false);
        tree_menu.addAction(&actPasteSpur);
        connect(&actPasteSpur,SIGNAL(triggered()),this,SLOT(PasteSpur()));

        tree_menu.addSeparator();

        QAction actAddComponentContainers(QString("为实体元件添加元件层容器"), this);
        tree_menu.addAction(&actAddComponentContainers);
        connect(&actAddComponentContainers, &QAction::triggered, this, &MainWindow::actionAddComponentContainers);

        QAction actRemoveComponentContainers(QString("删除元件层容器"), this);
        tree_menu.addAction(&actRemoveComponentContainers);
        connect(&actRemoveComponentContainers, &QAction::triggered, this, &MainWindow::actionRemoveComponentContainers);

        QAction actAttachToHigher(QString("将实体元件层添加到高层级容器"), this);
        tree_menu.addAction(&actAttachToHigher);
        connect(&actAttachToHigher, &QAction::triggered, this, &MainWindow::actionAttachComponentsToHigher);

        ContainerRepository repo(T_ProjectDatabase);
        repo.ensureTables();

        QMenu *levelMenu = tree_menu.addMenu(QString("层级：无"));
        QModelIndex contextIndex = ui->treeViewUnits->indexAt(pos);
        int equipmentId = contextIndex.data(Qt::UserRole).toInt();
        int componentContainerId = repo.componentContainerIdForEquipment(equipmentId);
        if (componentContainerId != 0) {
            QList<int> chainIds = repo.ancestorChainIds(componentContainerId);
            if (!chainIds.isEmpty()) {
                ContainerEntity topEntity = repo.getById(chainIds.first());
                if (topEntity.id() != 0)
                    levelMenu->setTitle(QString("层级：%1").arg(describeContainer(repo, topEntity)));

                for (int id : chainIds) {
                    ContainerEntity entity = repo.getById(id);
                    if (entity.id() == 0) continue;
                    QString description = describeContainer(repo, entity);
                    if (entity.type() == ContainerType::Component) {
                        QAction *componentInfo = levelMenu->addAction(description);
                        componentInfo->setEnabled(false);
                        continue;
                    }

                    QMenu *subMenu = levelMenu->addMenu(description);

                    QAction *renameAct = subMenu->addAction(QString("重命名当前容器"));
                    connect(renameAct, &QAction::triggered, this, [this, entityId = entity.id()]() {
                        ContainerRepository repoLocal(T_ProjectDatabase);
                        if (!repoLocal.ensureTables()) return;
                        ContainerEntity current = repoLocal.getById(entityId);
                        bool ok = false;
                        QString newName = QInputDialog::getText(this, tr("重命名容器"), tr("名称"), QLineEdit::Normal, current.name(), &ok);
                        if (!ok) return;
                        newName = newName.trimmed();
                        if (newName.isEmpty()) return;
                        current.setName(newName);
                        repoLocal.update(current);
                    });

                    QList<ContainerType> childTypes = childCandidateTypes(entity.type());
                    QAction *addChildAct = subMenu->addAction(QString("添加低层级容器"));
                    if (childTypes.isEmpty()) {
                        addChildAct->setEnabled(false);
                    } else {
                        connect(addChildAct, &QAction::triggered, this, [this, entityType = entity.type(), entityId = entity.id(), childTypes]() {
                            ContainerRepository repoLocal(T_ProjectDatabase);
                            if (!repoLocal.ensureTables()) return;
                            ContainerTreeDialog dialog(this);
                            dialog.setDatabase(T_ProjectDatabase);
                            dialog.setMode(ContainerTreeDialog::Mode::Select);
                            dialog.setAllowedTypes(childTypes);
                            if (dialog.exec() != QDialog::Accepted) return;
                            ContainerEntity selected = dialog.selectedEntity();
                            if (selected.id() == 0) return;
                            if (!ContainerRepository::canContain(entityType, selected.type())) {
                                QMessageBox::warning(this, tr("错误"), tr("所选容器层级不符合要求"));
                                return;
                            }
                            if (!repoLocal.attachToParent(selected.id(), entityId)) {
                                QMessageBox::warning(this, tr("错误"), tr("添加低层级容器失败"));
                            }
                        });
                    }

                    QAction *removeComponentAct = subMenu->addAction(QString("从中删除本元件容器"));
                    bool directParent = false;
                    if (componentContainerId != 0) {
                        ContainerEntity currentComponent = repo.getById(componentContainerId);
                        directParent = (currentComponent.parentId() == entity.id());
                    }
                    removeComponentAct->setEnabled(directParent);
                    if (directParent) {
                        connect(removeComponentAct, &QAction::triggered, this, [this, componentContainerId, parentId = entity.id()]() {
                            ContainerRepository repoLocal(T_ProjectDatabase);
                            if (!repoLocal.ensureTables()) return;
                            ContainerEntity comp = repoLocal.getById(componentContainerId);
                            if (comp.parentId() != parentId) return;
                            repoLocal.attachToParent(componentContainerId, 0);
                        });
                    }

                    QList<ContainerType> parentTypes = parentCandidateTypes(entity.type());
                    QAction *attachAct = subMenu->addAction(QString("将当前层级添加到高层级容器"));
                    if (parentTypes.isEmpty()) {
                        attachAct->setEnabled(false);
                    } else {
                        connect(attachAct, &QAction::triggered, this, [this, entityId = entity.id(), entityType = entity.type(), parentTypes]() {
                            ContainerRepository repoLocal(T_ProjectDatabase);
                            if (!repoLocal.ensureTables()) return;
                            ContainerTreeDialog dialog(this);
                            dialog.setDatabase(T_ProjectDatabase);
                            dialog.setMode(ContainerTreeDialog::Mode::Select);
                            dialog.setAllowedTypes(parentTypes);
                            if (dialog.exec() != QDialog::Accepted) return;
                            ContainerEntity target = dialog.selectedEntity();
                            if (target.id() == 0) return;
                            if (!ContainerRepository::canContain(target.type(), entityType)) {
                                QMessageBox::warning(this, tr("错误"), tr("所选容器层级不符合要求"));
                                return;
                            }
                            if (!repoLocal.attachToParent(entityId, target.id())) {
                                QMessageBox::warning(this, tr("错误"), tr("加入高层级容器失败"));
                            }
                        });
                    }
                }
            }
        }

        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QAction actLoadSpur("绘制子块", this);
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()<=0) actLoadSpur.setEnabled(false);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            QString temp = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
            QuerySymbol.exec(temp);
            if(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")  {actLoadSpur.setEnabled(false);break;}
                if((QuerySymbol.value("FunDefine").toString()=="黑盒")||(QuerySymbol.value("FunDefine").toString()=="PLC 盒子"))
                {
                    if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()>1)
                    {
                        actLoadSpur.setEnabled(false);
                        break;
                    }
                }
                else
                {
                    if(QuerySymbol.value("Symbol").toString()=="")  {actLoadSpur.setEnabled(false);break;}
                }
            }
        }
        if(!CurPageValid) actLoadSpur.setEnabled(false);
        tree_menu.addAction(&actLoadSpur);
        connect(&actLoadSpur,SIGNAL(triggered()),this,SLOT(SlotLoadSpur()));
        QAction actNewSpur("新建子块", this);
        tree_menu.addAction(&actNewSpur);
        connect(&actNewSpur,SIGNAL(triggered()),this,SLOT(SlotNewSpur()));
        QAction actNewSpurTemplate("子块(模板)", this);
        tree_menu.addAction(&actNewSpurTemplate);
        connect(&actNewSpurTemplate,SIGNAL(triggered()),this,SLOT(NewSpurTemplate()));
        QAction actSpurAttr("子块属性", this);
        tree_menu.addAction(&actSpurAttr);
        connect(&actSpurAttr,SIGNAL(triggered()),this,SLOT(SlotSpurAttr()));
        QAction actDeleteSpur("删除子块", this);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="功能子块")
            {
                actDeleteSpur.setEnabled(false);
                break;
            }
        }
        tree_menu.addAction(&actDeleteSpur);
        connect(&actDeleteSpur,SIGNAL(triggered()),this,SLOT(DeleteSpur()));
        QAction actCopySpur("复制子块", this);
        tree_menu.addAction(&actCopySpur);
        connect(&actCopySpur,SIGNAL(triggered()),this,SLOT(CopySpur()));
        QAction actPasteSpur("粘贴子块", this);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(CopySymbol_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteSpur.setEnabled(false);
        tree_menu.addAction(&actPasteSpur);
        connect(&actPasteSpur,SIGNAL(triggered()),this,SLOT(PasteSpur()));
        QAction actShowSpurInDwg("转到图形", this);
        tree_menu.addAction(&actShowSpurInDwg);
        connect(&actShowSpurInDwg,SIGNAL(triggered()),this,SLOT(ShowSpurInDwg()));
        QAction actDrawSpurEqualDistance("等距绘制", this);
        if(!CurPageValid) actDrawSpurEqualDistance.setEnabled(false);
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()<=1) actDrawSpurEqualDistance.setEnabled(false);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
            QuerySymbol.exec(SqlStr);
            if(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")  {actDrawSpurEqualDistance.setEnabled(false);break;}
                if((QuerySymbol.value("FunDefine").toString()=="黑盒")||(QuerySymbol.value("FunDefine").toString()=="PLC 盒子"))  {actDrawSpurEqualDistance.setEnabled(false);break;}
            }
        }
        tree_menu.addAction(&actDrawSpurEqualDistance);
        connect(&actDrawSpurEqualDistance,SIGNAL(triggered()),this,SLOT(DrawSpurEqualDistance()));
        tree_menu.addSeparator();
        QAction actCreateFunction("创建功能", this);
        tree_menu.addAction(&actCreateFunction);
        connect(&actCreateFunction, &QAction::triggered, this, &MainWindow::createFunctionForSymbol);
        QAction actGetLinkRoad("获取信号链路", this);
        tree_menu.addAction(&actGetLinkRoad);
        connect(&actGetLinkRoad,SIGNAL(triggered()),this,SLOT(GetLinkRoad()));
        tree_menu.exec(QCursor::pos());
    }
}

void MainWindow::createFunctionForSymbol()
{
    QModelIndex index = ui->treeViewUnits->currentIndex();
    if (!index.isValid()) return;
    if (index.data(Qt::WhatsThisRole).toString() != "功能子块") return;

    const int symbolId = index.data(Qt::UserRole).toInt();
    if (symbolId <= 0) return;
    const QString symbolName = index.data(Qt::DisplayRole).toString();

    FunctionEditDialog editor(T_ProjectDatabase, this);
    editor.setSystemContext(systemEntity, ui->textEditSystemDiscription
                                           ? ui->textEditSystemDiscription->toPlainText()
                                           : QString());
    editor.setSymbol(symbolId, symbolName);
    editor.analyzeCurrentSymbol();
    if (editor.exec() != QDialog::Accepted)
        return;

    FunctionRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("提示"), tr("功能存储不可用"));
        return;
    }

    FunctionRecord record = editor.record();
    if (repo.insert(record) == 0) {
        QMessageBox::warning(this, tr("提示"), tr("保存功能失败"));
        return;
    }

    UpdateFuncTable();
    LoadAllFunction();
}

void MainWindow::on_Btn_ContainerTree_clicked()
{
    ContainerTreeDialog dialog(this);
    dialog.setDatabase(T_ProjectDatabase);
    dialog.setModal(true);
    dialog.exec();
}

void MainWindow::on_BtnFunctionManage_clicked()
{
    ContainerRepository repo(T_ProjectDatabase);
    repo.ensureTables();
    int containerId = 0;
    const QList<ContainerEntity> roots = repo.fetchRoots();
    if (!roots.isEmpty())
        containerId = roots.first().id();

    const QString systemDescription = ui->textEditSystemDiscription
            ? ui->textEditSystemDiscription->toPlainText()
            : QString();
    FunctionManagerDialog dialog(T_ProjectDatabase, containerId, systemDescription, systemEntity, this);
    dialog.exec();
    UpdateFuncTable();
    LoadAllFunction();
}

void MainWindow::actionAddComponentContainers()
{
    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("错误"), tr("数据库不可用"));
        return;
    }

    if (!ui->treeViewUnits->selectionModel()) return;
    const QModelIndexList indexes = ui->treeViewUnits->selectionModel()->selectedIndexes();
    QSet<int> equipmentIds;
    for (const QModelIndex &index : indexes) {
        if (index.column() != 0) continue;
        if (index.data(Qt::WhatsThisRole).toString() != "元件") continue;
        equipmentIds.insert(index.data(Qt::UserRole).toInt());
    }

    if (equipmentIds.isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("请选择需要处理的元件"));
        return;
    }

    int created = 0;
    int skipped = 0;
    int failed = 0;

    for (int equipmentId : equipmentIds) {
        int before = repo.componentContainerIdForEquipment(equipmentId);
        int cid = ensureComponentContainer(repo, T_ProjectDatabase, equipmentId);
        if (cid == 0) {
            ++failed;
            continue;
        }
        if (before == 0)
            ++created;
        else
            ++skipped;
    }

    QMessageBox::information(this, tr("完成"),
                             tr("新增%1，已存在%2，失败%3").arg(created).arg(skipped).arg(failed));
}

void MainWindow::actionRemoveComponentContainers()
{
    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("错误"), tr("数据库不可用"));
        return;
    }

    if (!ui->treeViewUnits->selectionModel()) return;
    const QModelIndexList indexes = ui->treeViewUnits->selectionModel()->selectedIndexes();
    QSet<int> equipmentIds;
    for (const QModelIndex &index : indexes) {
        if (index.column() != 0) continue;
        if (index.data(Qt::WhatsThisRole).toString() != "元件") continue;
        equipmentIds.insert(index.data(Qt::UserRole).toInt());
    }

    if (equipmentIds.isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("请选择需要处理的元件"));
        return;
    }

    int removed = 0;
    int skipped = 0;
    for (int equipmentId : equipmentIds) {
        int cid = repo.componentContainerIdForEquipment(equipmentId);
        if (cid == 0) {
            ++skipped;
            continue;
        }
        if (repo.deleteComponentContainerForEquipment(equipmentId))
            ++removed;
        else
            ++skipped;
    }

    QMessageBox::information(this, tr("完成"), tr("删除%1，跳过%2").arg(removed).arg(skipped));
}

void MainWindow::actionAttachComponentsToHigher()
{
    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("错误"), tr("数据库不可用"));
        return;
    }

    if (!ui->treeViewUnits->selectionModel()) return;
    const QModelIndexList indexes = ui->treeViewUnits->selectionModel()->selectedIndexes();
    QSet<int> containerIds;
    for (const QModelIndex &index : indexes) {
        if (index.column() != 0) continue;
        if (index.data(Qt::WhatsThisRole).toString() != "元件") continue;
        int equipmentId = index.data(Qt::UserRole).toInt();
        int cid = ensureComponentContainer(repo, T_ProjectDatabase, equipmentId);
        if (cid != 0) containerIds.insert(cid);
    }

    if (containerIds.isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("请选择需要处理的元件"));
        return;
    }

    QList<ContainerType> allowedParents = parentCandidateTypes(ContainerType::Component);
    ContainerTreeDialog dialog(this);
    dialog.setDatabase(T_ProjectDatabase);
    dialog.setMode(ContainerTreeDialog::Mode::Select);
    dialog.setAllowedTypes(allowedParents);
    if (dialog.exec() != QDialog::Accepted) return;

    ContainerEntity target = dialog.selectedEntity();
    if (target.id() == 0) return;
    if (!ContainerRepository::canContain(target.type(), ContainerType::Component)) {
        QMessageBox::warning(this, tr("错误"), tr("所选容器层级不符合要求"));
        return;
    }

    int attached = 0;
    int skipped = 0;
    for (int cid : containerIds) {
        if (repo.attachToParent(cid, target.id()))
            ++attached;
        else
            ++skipped;
    }

    QMessageBox::information(this, tr("完成"), tr("添加到高层级：%1，跳过：%2").arg(attached).arg(skipped));
}

bool MainWindow::pickFirstGaocengPos(QString &gaoceng, QString &pos) const
{
    QStringList gaocengList = getUniqueGaocengList();
    if (gaocengList.isEmpty()) return false;
    gaoceng = gaocengList.first();
    QStringList posList = getUniquePosListByGaoceng(gaoceng);
    if (posList.isEmpty()) return false;
    pos = posList.first();
    return true;
}

QModelIndex MainWindow::findAncestorByRole(const QModelIndex &index, const QString &roleName) const
{
    QModelIndex current = index;
    while (current.isValid()) {
        if (current.data(Qt::WhatsThisRole).toString() == roleName) {
            return current;
        }
        current = current.parent();
    }
    return QModelIndex();
}

bool MainWindow::resolveGaocengPosForIndex(const QModelIndex &index, QString &gaoceng, QString &pos) const
{
    if (!index.isValid()) {
        return pickFirstGaocengPos(gaoceng, pos);
    }
    QString type = index.data(Qt::WhatsThisRole).toString();
    if (type == "项目") {
        return pickFirstGaocengPos(gaoceng, pos);
    }
    if (type == "高层") {
        gaoceng = index.data(Qt::DisplayRole).toString();
        if (ui->CbUnitPos->currentText() != "位置" && !ui->CbUnitPos->currentText().isEmpty()) {
            pos = ui->CbUnitPos->currentText();
            return true;
        }
        QStringList posList = getUniquePosListByGaoceng(gaoceng);
        if (!posList.isEmpty()) {
            pos = posList.first();
            return true;
        }
        return false;
    }
    if (type == "位置") {
        pos = index.data(Qt::DisplayRole).toString();
        QModelIndex parent = index.parent();
        if (parent.isValid())
            gaoceng = parent.data(Qt::DisplayRole).toString();
        return !gaoceng.isEmpty() && !pos.isEmpty();
    }
    if (type == "元件" || type == "功能子块") {
        QModelIndex posIndex = findAncestorByRole(index, "位置");
        QModelIndex gaocengIndex = findAncestorByRole(index, "高层");
        if (posIndex.isValid())
            pos = posIndex.data(Qt::DisplayRole).toString();
        if (gaocengIndex.isValid())
            gaoceng = gaocengIndex.data(Qt::DisplayRole).toString();
        if (!gaoceng.isEmpty() && !pos.isEmpty()) {
            return true;
        }
    }
    return pickFirstGaocengPos(gaoceng, pos);
}
