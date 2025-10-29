#include "dialogsymbols.h"
#include "ui_dialogsymbols.h"
#include <QMessageBox>

DialogSymbols::DialogSymbols(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogSymbols)
{
    ui->setupUi(this);
    Canceled=true; 
    Model = new QStandardItemModel(0, 0,this);

    ui->treeView->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeView,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewPopMenu(QPoint)));

    ui->treeView->header()->setVisible(false);
    ui->treeView->setColumnWidth(0,50);
    ui->treeView->setModel(Model); 
    for(int i=0;i<TotalLabelNum;i++)
    {
        labels[i]=new QXlabel(this);
        lbDwgName[i]=new QLabel(this);
        labels[i]->ID=i;
        labels[i]->setStyleSheet("background-color: rgb(0, 0, 0)");
        labels[i]->setScaledContents(false);
        labels[i]->setFrameShape(QFrame::Panel);
        labels[i]->setFrameShadow(QFrame::Sunken);
        labels[i]->setLineWidth(3);
        labels[i]->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);
        labels[i]->setMinimumWidth(LabelWidth+8);
        labels[i]->setMinimumHeight(LabelHeight+8);
        lbDwgName[i]->setMinimumWidth(LabelWidth);
        lbDwgName[i]->setMaximumWidth(LabelWidth+8);
        lbDwgName[i]->setMinimumHeight(20);
        lbDwgName[i]->setAlignment(Qt::AlignHCenter);
        lbDwgName[i]->setAlignment(Qt::AlignVCenter);
        connect(labels[i], SIGNAL(doubleClicked(int)),this, SLOT(SymbolSel(int)));
        connect(labels[i], SIGNAL(Clicked(int)),this, SLOT(SymbolSelect(int)));
    }
    LoadModelFromDB("");
    QGridLayout *gridlayout = new QGridLayout;
    gridlayout->setHorizontalSpacing(4);
    gridlayout->setVerticalSpacing(4);
    gridlayout->setMargin(3);
    for(int row=0;row<TotalLabelNum/ColumnLabelNum;row++)
    {
        for(int col=0;col<ColumnLabelNum;col++)
            gridlayout->addWidget(labels[row*ColumnLabelNum+col],row*2,col,1,1); // //添加布局 0,0,1,1 行 列 行间距 列间距
        for(int col=0;col<ColumnLabelNum;col++)
            gridlayout->addWidget(lbDwgName[row*ColumnLabelNum+col],row*2+1,col,1,1); // //添加布局 0,0,1,1 行 列 行间距 列间距
    }

    ui->frame_symbol->setLayout(gridlayout);

    BaseIndex=0;

}

void DialogSymbols::ShowtreeViewPopMenu(const QPoint &pos)
{
    if(!ui->treeView->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="0")
    {
        QAction actDeleteLevel("删除", this);
        tree_menu.addAction(&actDeleteLevel);
        connect(&actDeleteLevel,SIGNAL(triggered()),this,SLOT(DeleteLevel()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="1")
    {
        QAction actDeleteLevel("删除", this);
        tree_menu.addAction(&actDeleteLevel);
        connect(&actDeleteLevel,SIGNAL(triggered()),this,SLOT(DeleteLevel()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="2")
    {
        QAction actDeleteLevel("删除", this);
        tree_menu.addAction(&actDeleteLevel);
        connect(&actDeleteLevel,SIGNAL(triggered()),this,SLOT(DeleteLevel()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="3")
    {

        QAction actNewSubLevel("新建符号", this);
        tree_menu.addAction(&actNewSubLevel);
        connect(&actNewSubLevel,SIGNAL(triggered()),this,SLOT(on_BtnNewLib_clicked()));
        QAction actDeleteLevel("删除", this);
        tree_menu.addAction(&actDeleteLevel);
        connect(&actDeleteLevel,SIGNAL(triggered()),this,SLOT(DeleteLevel()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="4")
    {
        QAction actNewSubLevel("新建符号", this);
        tree_menu.addAction(&actNewSubLevel);
        connect(&actNewSubLevel,SIGNAL(triggered()),this,SLOT(on_BtnNewLib_clicked()));
        QAction actCopySymbol("复制符号", this);
        tree_menu.addAction(&actCopySymbol);
        connect(&actCopySymbol,SIGNAL(triggered()),this,SLOT(CopySymbol()));
        QAction actMoveLevel("移动", this);
        tree_menu.addAction(&actMoveLevel);
        connect(&actMoveLevel,SIGNAL(triggered()),this,SLOT(MoveLevel()));
        QAction actDeleteLevel("删除", this);
        tree_menu.addAction(&actDeleteLevel);
        connect(&actDeleteLevel,SIGNAL(triggered()),this,SLOT(DeleteLevel()));
        QAction actAutoMakeAllDir("自动生成其余方向符号", this);
        tree_menu.addAction(&actAutoMakeAllDir);
        connect(&actAutoMakeAllDir,SIGNAL(triggered()),this,SLOT(AutoMakeAllDir()));
        QAction actRename("重命名", this);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(ReName()));
        tree_menu.exec(QCursor::pos());
    }
}

void DialogSymbols::ReName()
{
    QDialog *dialogUnitTypeEdit =new QDialog();
    dialogUnitTypeEdit->setWindowTitle("输入名称");
    dialogUnitTypeEdit->setMinimumSize(QSize(300,70));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUnitTypeEdit);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogUnitTypeEdit);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogUnitTypeEdit);
    m_label1->setText("名称");
    QLineEdit *m_LineEdit = new QLineEdit(dialogUnitTypeEdit);
    m_LineEdit->setText(ui->treeView->currentIndex().data(Qt::DisplayRole).toString());
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_LineEdit);

    layout->addLayout(linelayout1);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogUnitTypeEdit,SLOT(accept()));
    if (dialogUnitTypeEdit->exec()==QDialog::Accepted)
    {
        QString NewName=m_LineEdit->text();
        if(NewName=="")
        {
            QMessageBox::warning(nullptr, "提示", "名称为空！");
            return;
        }
        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr="UPDATE Symb2Class SET Desc=:Desc WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":Desc",NewName);
        QueryVar.exec();

        QSqlQuery QuerySearch = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QString OriginalSymb2_Name=QuerySearch.value("Symb2_Name").toString();
            QString NewSymb2_Name=OriginalSymb2_Name.mid(0,6)+NewName+OriginalSymb2_Name.mid(OriginalSymb2_Name.lastIndexOf("-"),OriginalSymb2_Name.count()-OriginalSymb2_Name.lastIndexOf("-"));
            QFile file("C:/TBD/SYMB2LIB/"+OriginalSymb2_Name+".dwg");
            if(file.exists())
            {
               if(file.isOpen()) file.close();
               file.rename("C:/TBD/SYMB2LIB/"+NewSymb2_Name+".dwg");
            }
            SqlStr="UPDATE Symb2Lib SET Symb2_Name=:Symb2_Name WHERE Symb2Lib_ID = '"+QuerySearch.value("Symb2Lib_ID").toString()+"'";
            QueryVar.prepare(SqlStr);
            QueryVar.bindValue(":Symb2_Name",NewSymb2_Name);
            QueryVar.exec();
        }
        LoadModelFromDB(ui->treeView->currentIndex().parent().data(Qt::UserRole).toString());
    }
}

QString DialogSymbols::GetFunctionDefineIDFromIndex()
{
   if(!ui->treeView->currentIndex().isValid()) return "";
   QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
   QString SqlStr,DefaultFunctionDefineName="",DefaultFunctionDefineID="";
   if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="4")
   {
       SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
       QueryVar.exec(SqlStr);
       if(QueryVar.next())
       {
           DefaultFunctionDefineName=QueryVar.value("FunctionDefineName").toString();
           SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+QueryVar.value("Parent_ID").toString()+"'";
           QueryVar.exec(SqlStr);
           if(QueryVar.next())
           {
               SqlStr="SELECT * FROM FunctionDefineClass WHERE ParentNo = '"+QueryVar.value("FuncDefID").toString()+"' AND FunctionDefineName ='"+DefaultFunctionDefineName+"'";
               QueryVar.exec(SqlStr);
               if(QueryVar.next())
               {
                  DefaultFunctionDefineID=QueryVar.value("FunctionDefineClass_ID").toString();
               }
           }
       }
   }
   else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="3")
   {
       SqlStr="SELECT * FROM Symb2Class WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
       QueryVar.exec(SqlStr);
       if(QueryVar.next()) DefaultFunctionDefineID=QueryVar.value("FuncDefID").toString();
   }

   return DefaultFunctionDefineID;
}

void DialogSymbols::MoveLevel()//移动类或者符号
{
    if(!ui->treeView->currentIndex().isValid()) return;

    //根据选择的节点确定默认节点
    QString DefaultFunctionDefineID=GetFunctionDefineIDFromIndex();

    DialogNewLib *dlg = new DialogNewLib(this);
    dlg->setModal(true);
    dlg->LoadMode(2,4,DefaultFunctionDefineID,0);//Mode=0:新建  Mode=1:复制  Mode=2:移动
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;

    if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toInt()==4)//移动符号
    {
        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr= "SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryVar.exec(SqlStr);
        int TermCount=0;
        if(QueryVar.next())
        {
           TermCount=QueryVar.value("TermCount").toInt();
        }
        CurSelectSymb2Class_ID=InsertOrUpdateSymb2Lib(1,ui->treeView->currentIndex().data(Qt::UserRole).toString(),dlg->FunctionDefineClass_ID,dlg->FileName+".dwg",TermCount);
    }
    LoadModelFromDB(CurSelectSymb2Class_ID);
}

void DialogSymbols::CopySymbol()//复制符号
{
    if(!ui->treeView->currentIndex().isValid()) return;
    //根据选择的节点确定默认节点
    QString DefaultFunctionDefineID=GetFunctionDefineIDFromIndex();

    DialogNewLib *dlg = new DialogNewLib(this);
    dlg->setModal(true);
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr= "SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
    QueryVar.exec(SqlStr);
    int TermCount=0;
    if(QueryVar.next())
    {
       TermCount=QueryVar.value("TermCount").toInt();
    }
    dlg->LoadMode(1,4,DefaultFunctionDefineID,TermCount);//Mode=0:新建  Mode=1:复制  Mode=2:移动
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;

    //创建新文件
    SqlStr= "SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
    QueryVar.exec(SqlStr);
    while(QueryVar.next())
    {
       QString SourceFileName="C:/TBD/SYMB2LIB/"+QueryVar.value("Symb2_Name").toString()+".dwg";//ES2_M_DENG-1.dwg
       QString FileName=dlg->FileName.mid(0,dlg->FileName.count()-2)+QueryVar.value("Symb2_Name").toString().mid(QueryVar.value("Symb2_Name").toString().count()-2,2);
       QString dwgFileName="C:/TBD/SYMB2LIB/"+FileName+".dwg";
       QFile::copy(SourceFileName,dwgFileName);
       TermCount=QueryVar.value("TermCount").toInt();
       CurSelectSymb2Class_ID=InsertOrUpdateSymb2Lib(0,"",dlg->FunctionDefineClass_ID,FileName+".dwg",TermCount);
    }
    delete dlg;
    LoadModelFromDB(CurSelectSymb2Class_ID);
    //emit(SignalUpdateLib());
}

void DialogSymbols::DeleteLevel()
{
    if(!ui->treeView->currentIndex().isValid()) return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"您真要删除吗?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);
    if(result!=QMessageBox::Yes)
    {
        return;
    }
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr;
    if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="4")
    {
        SqlStr="DELETE FROM Symb2Class WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryVar.exec(SqlStr);

        SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryVar.exec(SqlStr);
        while(QueryVar.next())
        {
            //删除本地库文件
            QString Path="C:/TBD/SYMB2LIB/"+QueryVar.value("Symb2_Name").toString()+".dwg";
            QFile file(Path);
            if(file.exists()) file.remove();
        }
        SqlStr="DELETE FROM Symb2Lib WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryVar.exec(SqlStr);
        LoadModelFromDB(ui->treeView->currentIndex().parent().data(Qt::UserRole).toString());
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="3")
    {
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=4
        QueryVar.exec(SqlStr);
        while(QueryVar.next())
        {
            QSqlQuery QuerySearch = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+QueryVar.value("Symb2Class_ID").toString()+"'";
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                //删除本地库文件
                QString Path="C:/TBD/SYMB2LIB/"+QuerySearch.value("Symb2_Name").toString()+".dwg";
                QFile file(Path);
                if(file.exists()) file.remove();
            }
        }
        SqlStr="DELETE FROM Symb2Class WHERE Parent_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=4
        QueryVar.exec(SqlStr);
        SqlStr="DELETE FROM Symb2Class WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=3
        QueryVar.exec(SqlStr);
        LoadModelFromDB(ui->treeView->currentIndex().parent().data(Qt::UserRole).toString());
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="2")
    {
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=3
        QueryVar.exec(SqlStr);
        while(QueryVar.next())
        {
            QSqlQuery QueryVar2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+QueryVar.value("Symb2Class_ID").toString()+"'";//level=4
            QueryVar2.exec(SqlStr);
            while(QueryVar2.next())
            {
                QSqlQuery QuerySearch = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+QueryVar2.value("Symb2Class_ID").toString()+"'";
                QuerySearch.exec(SqlStr);
                while(QuerySearch.next())
                {
                    //删除本地库文件
                    QString Path="C:/TBD/SYMB2LIB/"+QuerySearch.value("Symb2_Name").toString()+".dwg";
                    QFile file(Path);
                    if(file.exists()) file.remove();
                }
            }
            SqlStr="DELETE FROM Symb2Class WHERE Parent_ID = '"+QueryVar.value("Symb2Class_ID").toString()+"'";//level=4
            QueryVar2.exec(SqlStr);
        }
        SqlStr="DELETE FROM Symb2Class WHERE Parent_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=3
        QueryVar.exec(SqlStr);
        SqlStr="DELETE FROM Symb2Class WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=2
        QueryVar.exec(SqlStr);
        LoadModelFromDB(ui->treeView->currentIndex().parent().data(Qt::UserRole).toString());
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="1")
    {
        SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=2
        QueryVar.exec(SqlStr);
        while(QueryVar.next())
        {
            QSqlQuery QueryVar2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+QueryVar.value("Symb2Class_ID").toString()+"'";//level=3
            QueryVar2.exec(SqlStr);
            while(QueryVar2.next())
            {
                QSqlQuery QueryVar3 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM Symb2Class WHERE Parent_ID = '"+QueryVar2.value("Symb2Class_ID").toString()+"'";//level=4
                QueryVar3.exec(SqlStr);
                while(QueryVar3.next())
                {
                    QSqlQuery QuerySearch = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                    SqlStr="SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+QueryVar3.value("Symb2Class_ID").toString()+"'";
                    QuerySearch.exec(SqlStr);
                    while(QuerySearch.next())
                    {
                        //删除本地库文件
                        QString Path="C:/TBD/SYMB2LIB/"+QuerySearch.value("Symb2_Name").toString()+".dwg";
                        QFile file(Path);
                        if(file.exists()) file.remove();
                    }
                }
                SqlStr="DELETE FROM Symb2Class WHERE Parent_ID = '"+QueryVar2.value("Symb2Class_ID").toString()+"'";//level=4
                QueryVar3.exec(SqlStr);
            }
            SqlStr="DELETE FROM Symb2Class WHERE Parent_ID = '"+QueryVar.value("Symb2Class_ID").toString()+"'";//level=3
            QueryVar2.exec(SqlStr);
        }
        SqlStr="DELETE FROM Symb2Class WHERE Parent_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=2
        QueryVar.exec(SqlStr);
        SqlStr="DELETE FROM Symb2Class WHERE Symb2Class_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";//level=1
        QueryVar.exec(SqlStr);
        LoadModelFromDB(ui->treeView->currentIndex().parent().data(Qt::UserRole).toString());
    }
}

void DialogSymbols::AutoMakeAllDir()//自动生成其余方向符号
{
    if(!ui->treeView->currentIndex().isValid()) return;
    int State[4]={0,0,0,0};
    QString Symb2Class_ID=ui->treeView->currentIndex().data(Qt::UserRole).toString();
    QSqlQuery QuerySymb2Lib = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+Symb2Class_ID+"'";
    QuerySymb2Lib.exec(SqlStr);
    QString Symb2_NameSimple,TermCount;

    while(QuerySymb2Lib.next())
    {
        QString Symb2_Name=QuerySymb2Lib.value("Symb2_Name").toString();
        Symb2_NameSimple=Symb2_Name.mid(0,Symb2_Name.count()-2);
        TermCount=QuerySymb2Lib.value("TermCount").toString();
        if(Symb2_Name.contains("-1")) State[0]=1;
        if(Symb2_Name.contains("-2")) State[1]=1;
        if(Symb2_Name.contains("-3")) State[2]=1;
        if(Symb2_Name.contains("-4")) State[3]=1;
    }
qDebug()<<"State[0]="<<State[0]<<",State[1]="<<State[1]<<",State[2]="<<State[2]<<",State[3]="<<State[3]<<",Symb2_NameSimple="<<Symb2_NameSimple;
    for(int i=0;i<4;i++)
    {
        if(State[i]<=0)
        {
            for(int j=0;j<4;j++)
            {
                if(State[j]>0)
                {
                   //根据-j+1.dwg来绘制-i+1.dwg
                   QString SourceFileName="C:/TBD/SYMB2LIB/"+Symb2_NameSimple+"-"+QString::number(j+1)+".dwg";
                   QString dwgFilePath="C:/TBD/SYMB2LIB/"+Symb2_NameSimple+"-"+QString::number(i+1)+".dwg";
                   QFile::copy(SourceFileName,dwgFilePath);
qDebug()<<"SourceFileName="<<SourceFileName<<",dwgFilePath="<<dwgFilePath;
                   //更改dwg,绕着基点旋转
                   GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgFilePath);
                   double Angle;
                   if(j<i) Angle=(i-j)*PI/2.0;
                   else  Angle=2*PI-(j-i)*PI/2.0;
                   IMxDrawDatabase* database = (IMxDrawDatabase*)GlobalBackAxWidget->querySubObject("GetDatabase()");
                   IMxDrawPoint *InsbasePt =(IMxDrawPoint*)database->querySubObject("Insbase()");
                   IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
                   IMxDrawResbuf *filter=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
                   ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
                   int Cnt=ss1->dynamicCall("Count()").toInt();
                   for(int k=0;k<Cnt;k++)
                   {
                      IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",k);
                      if(Enty==nullptr) continue;
                      if(EntyIsErased(GlobalBackAxWidget,Enty)) continue;//去除erase的实体
  qDebug()<<"ObjectName="<<Enty->dynamicCall("ObjectName()").toString();
                      Enty->dynamicCall("Rotate(QAxObject*,double)",InsbasePt->asVariant(),Angle);
                      //如果是端口，则调整出线方向
                      if(Enty->dynamicCall("ObjectName()").toString()=="McDbPolyline")//是否为端口
                      {
                          QString LD_PARTLIB_DOTCONDIRECT=Enty->dynamicCall("GetxDataString2(QString,QString)","LD_PARTLIB_DOTCONDIRECT",0).toString();
qDebug()<<"LD_PARTLIB_DOTCONDIRECT="<<LD_PARTLIB_DOTCONDIRECT<<",Angle="<<Angle;
                          if(GlobalBackAxWidget->dynamicCall("IsOk()").toString()=="true")
                          {
                             if(LD_PARTLIB_DOTCONDIRECT=="向左")
                             {
                                 if(fabs(Angle*180/PI-90)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向下");
                                 if(fabs(Angle*180/PI-180)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向右");
                                 if(fabs(Angle*180/PI-270)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向上");
                             }
                             else if(LD_PARTLIB_DOTCONDIRECT=="向下")
                             {
  qDebug()<<"向下,fabs(Angle*180/PI-90)="<<fabs(Angle*180/PI-90);
                                 if(fabs(Angle*180/PI-90)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向右");
                                 if(fabs(Angle*180/PI-180)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向上");
                                 if(fabs(Angle*180/PI-270)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向左");
                             }
                             else if(LD_PARTLIB_DOTCONDIRECT=="向右")
                             {
                                 if(fabs(Angle*180/PI-90)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向上");
                                 if(fabs(Angle*180/PI-180)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向左");
                                 if(fabs(Angle*180/PI-270)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向下");
                             }
                             else if(LD_PARTLIB_DOTCONDIRECT=="向上")
                             {
qDebug()<<"向上,fabs(Angle*180/PI-90)="<<fabs(Angle*180/PI-90);
                                 if(fabs(Angle*180/PI-90)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向左");
                                 if(fabs(Angle*180/PI-180)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向下");
                                 if(fabs(Angle*180/PI-270)<0.1) Enty->dynamicCall("SetxDataString(QString,int,QString)","LD_PARTLIB_DOTCONDIRECT",0,"向右");
                             }
                          }
                      }
                   }
                   SetAllAttrDefPos(GlobalBackAxWidget,InsbasePt->x(),InsbasePt->y());
                   GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgFilePath);
                   //更新数据库
                   QSqlQuery queryInsert(T_LibDatabase);
                   SqlStr =  "INSERT INTO Symb2Lib (Symb2Lib_ID,Symb2_Name,Symb2Class_ID,_Order,TermCount)"
                             "VALUES (:Symb2Lib_ID,:Symb2_Name,:Symb2Class_ID,:_Order,:TermCount)";
                   queryInsert.prepare(SqlStr);
                   int Symb2Lib_ID=GetMaxIDOfLibDatabase(T_LibDatabase,"Symb2Lib","Symb2Lib_ID");
                   queryInsert.bindValue(":Symb2Lib_ID",QString::number(Symb2Lib_ID));
                   queryInsert.bindValue(":Symb2_Name",Symb2_NameSimple+"-"+QString::number(i+1));
                   queryInsert.bindValue(":Symb2Class_ID",Symb2Class_ID);
                   queryInsert.bindValue(":_Order",i+1);
                   queryInsert.bindValue(":TermCount",TermCount);
                   queryInsert.exec();
                   break;
                }
            }
        }
    }
    LoadModelFromDB(ui->treeView->currentIndex().data(Qt::UserRole).toString());
}

void DialogSymbols::LoadModelFromDB(QString CurSelectSymb2Class_ID)
{
    Model->clear();
    QSqlQuery QueryLevel0 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Symb2Class WHERE Level = 0 ORDER BY _Order");
    QueryLevel0.exec(temp);
    while(QueryLevel0.next())
    {
        QStandardItem *fatherItem;
        fatherItem= new QStandardItem(QIcon("C:/TBD/data/电气符号.png"),QueryLevel0.value("Desc").toString());
        fatherItem->setData(QVariant(QueryLevel0.value("Symb2Class_ID").toString()),Qt::UserRole);
        fatherItem->setData(QVariant("0"),Qt::WhatsThisRole);
        Model->appendRow(fatherItem);
        QSqlQuery QueryLevel1 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        temp = "SELECT * FROM Symb2Class WHERE Level = 1 AND Parent_ID = '"+QueryLevel0.value("Symb2Class_ID").toString()+"' ORDER BY _Order";
        QueryLevel1.exec(temp);
        while(QueryLevel1.next())
        {
            QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号大类.png"),QueryLevel1.value("Desc").toString());
            SubFatherItem->setData(QVariant(QueryLevel1.value("Symb2Class_ID").toString()),Qt::UserRole);
            SubFatherItem->setData(QVariant("1"),Qt::WhatsThisRole);
            fatherItem->appendRow(SubFatherItem);
            if(CurSelectSymb2Class_ID==QueryLevel1.value("Symb2Class_ID").toString()) ui->treeView->setCurrentIndex(SubFatherItem->index());
            QSqlQuery QueryLevel2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            temp = "SELECT * FROM Symb2Class WHERE Level = 2 AND Parent_ID = '"+QueryLevel1.value("Symb2Class_ID").toString()+"' ORDER BY _Order";
            QueryLevel2.exec(temp);
            while(QueryLevel2.next())
            {
                QStandardItem *SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号小类.png"),QueryLevel2.value("Desc").toString());
                SubSubFatherItem->setData(QVariant(QueryLevel2.value("Symb2Class_ID").toString()),Qt::UserRole);
                SubSubFatherItem->setData(QVariant("2"),Qt::WhatsThisRole);
                SubFatherItem->appendRow(SubSubFatherItem);
                if(CurSelectSymb2Class_ID==QueryLevel2.value("Symb2Class_ID").toString()) ui->treeView->setCurrentIndex(SubSubFatherItem->index());
                QSqlQuery QueryLevel3 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                temp = "SELECT * FROM Symb2Class WHERE Level = 3 AND Parent_ID = '"+QueryLevel2.value("Symb2Class_ID").toString()+"' ORDER BY _Order";
                QueryLevel3.exec(temp);
                while(QueryLevel3.next())
                {
                    QStandardItem *SubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号规格.png"),QueryLevel3.value("Desc").toString());
                    SubSubSubFatherItem->setData(QVariant(QueryLevel3.value("Symb2Class_ID").toString()),Qt::UserRole);
                    SubSubSubFatherItem->setData(QVariant("3"),Qt::WhatsThisRole);
                    SubSubFatherItem->appendRow(SubSubSubFatherItem);
                    if(CurSelectSymb2Class_ID==QueryLevel3.value("Symb2Class_ID").toString()) ui->treeView->setCurrentIndex(SubSubSubFatherItem->index());
                    QSqlQuery QueryLevel4 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                    temp = "SELECT * FROM Symb2Class WHERE Level = 4 AND Parent_ID = '"+QueryLevel3.value("Symb2Class_ID").toString()+"' ORDER BY _Order";
                    QueryLevel4.exec(temp);
                    while(QueryLevel4.next())
                    {
                        QStandardItem *SubSubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号最细分类.png"),QueryLevel4.value("Desc").toString());
                        SubSubSubSubFatherItem->setData(QVariant(QueryLevel4.value("Symb2Class_ID").toString()),Qt::UserRole);
                        SubSubSubSubFatherItem->setData(QVariant("4"),Qt::WhatsThisRole);
                        SubSubSubFatherItem->appendRow(SubSubSubSubFatherItem);
                        if(CurSelectSymb2Class_ID==QueryLevel4.value("Symb2Class_ID").toString()) ui->treeView->setCurrentIndex(SubSubSubSubFatherItem->index());

                    }
                }
            }
        }
        if(Model->rowCount()>0)
        {
            for(int i=0;i<Model->rowCount();i++)  ui->treeView->expand(Model->item(i,0)->index());
            if(CurSelectSymb2Class_ID=="")
            {
                if(Model->item(0,0)->rowCount()>0)
                {
                    ui->treeView->setCurrentIndex(Model->item(0,0)->child(0,0)->index());
                    LoadSymbolList(ui->treeView->currentIndex());
                }
            }
            else
            {
               LoadSymbolList(ui->treeView->currentIndex());
            }
        }
    }
}

void DialogSymbols::UpdateSymbols(QStringList listSymbolName,QStringList listSymbolID)
{
    QString Str;
    int i;
    QPixmap p;
    for(i=0;i<listSymbolName.count();i++)
    {
        Str=listSymbolName.at(i)+".dwg";
        QFileInfo file("C:/TBD/SYMB2LIB/"+Str);
        if(!file.exists())
        {
            QPixmap p=QPixmap("");
            labels[i]->setPixmap(p.scaled(LabelWidth,LabelHeight));
        }
        else
        {
            QString Str1=Str;
            Str1.replace("dwg","jpg");
            QFileInfo file("C:/TBD/data/SymbolDBJpg/"+Str1);
            if(!file.exists())//如果不存在dwg对应的jpg文件，则创建jpg文件
              pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/SYMB2LIB/"+Str,"C:/TBD/data/SymbolDBJpg/"+Str1,LabelWidth,LabelHeight);
            p=QPixmap("C:/TBD/data/SymbolDBJpg/"+Str1);
            labels[i]->setPixmap(p.scaled(LabelWidth,LabelHeight));
            labels[i]->UsrData=listSymbolID.at(i);
            lbDwgName[i]->setText(listSymbolName.at(i));

        }
    }
    p=QPixmap("");
    while(i<TotalLabelNum)
    {
        labels[i]->setPixmap(p);
        lbDwgName[i]->setText("");
        i++;
    }
    //delete App;
}


void DialogSymbols::SymbolSel(int id)
{
    SymbolSelect(id);
    on_Btn_Modify_clicked();
}

void DialogSymbols::SymbolSelect(int id)
{
    QString FileName;
    BlockFileName=lbDwgName[id]->text()+".dwg";
    SymbolID=labels[id]->UsrData;
qDebug()<<"SymbolID="<<SymbolID;
    //根据SymbolID检索对应的元件类别
    QSqlQuery QuerySymb2=QSqlQuery(T_LibDatabase);
    QString sqlStr=QString("SELECT * FROM Symb2Lib WHERE Symb2Lib_ID = '"+SymbolID+"'");
    QuerySymb2.exec(sqlStr);
    if(QuerySymb2.next())
    {
        SymbolType=GetTypeBySymb2Class_ID(QuerySymb2.value("Symb2Class_ID").toString());
        if(LastSelectId>=0) labels[LastSelectId]->setStyleSheet("border:0px solid black;");
        labels[id]->setStyleSheet("border:2px solid red;");
        LastSelectId=id;
    }

}

DialogSymbols::~DialogSymbols()
{
qDebug()<<"~DialogSymbols()";
    delete ui;
    for(int i=0;i<TotalLabelNum;i++) { delete labels[i];delete lbDwgName[i];}
}

void DialogSymbols::LoadSymbolList(const QModelIndex &index)
{
    QString temp;
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QStringList listSymbolName,listSymbolID;
    //确定是哪一级
    if(index.data(Qt::WhatsThisRole).toString().toInt()<=3)
    {
        temp = QString("SELECT * FROM Symb2Lib WHERE Symb2Class_ID LIKE '"+index.data(Qt::UserRole).toString()+"%' AND _Order = 1");
        QueryVar.exec(temp);

        int RecordIndex=0;
        while(QueryVar.next())
        {
           RecordIndex++;
           if(RecordIndex<=BaseIndex) continue;
           if(RecordIndex>(BaseIndex+TotalLabelNum)) continue;
           listSymbolName.append(QueryVar.value("Symb2_Name").toString());
           listSymbolID.append(QueryVar.value("Symb2Lib_ID").toString());
        }
        AllSymbolCount=RecordIndex;
        UpdateSymbols(listSymbolName,listSymbolID);
    }
    else //符号最细分类
    {
        temp = QString("SELECT * FROM Symb2Lib WHERE Symb2Class_ID = '"+index.data(Qt::UserRole).toString()+"'");
        QueryVar.exec(temp);
        int RecordIndex=0;
        while(QueryVar.next())
        {
           RecordIndex++;
           if(RecordIndex<=BaseIndex) continue;
           if(RecordIndex>(BaseIndex+TotalLabelNum)) continue;
           listSymbolName.append(QueryVar.value("Symb2_Name").toString());
           listSymbolID.append(QueryVar.value("Symb2Lib_ID").toString());
        }
        AllSymbolCount=RecordIndex;
        UpdateSymbols(listSymbolName,listSymbolID);
    }
    //默认选中第一个
    if(LastSelectId>=0) labels[LastSelectId]->setStyleSheet("border:0px solid black;");
    LastSelectId=-1;
    if(listSymbolID.count()>0)
    {
        labels[0]->setStyleSheet("border:2px solid red;");
        LastSelectId=0;
        SymbolSelect(0);
    }
}

void DialogSymbols::on_treeView_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    BaseIndex=0;
    LoadSymbolList(index);
}

void DialogSymbols::on_Btn_Modify_clicked()
{
    Canceled=false;
    RetCode=1;
    this->close();
}

void DialogSymbols::on_BtnClose_clicked()
{
    Canceled=false;
    RetCode=2;
    this->close();
}

void DialogSymbols::on_BtnPrePage_clicked()
{
    if(BaseIndex<TotalLabelNum) return;
    BaseIndex-=TotalLabelNum;
    LoadSymbolList(ui->treeView->currentIndex());
}

void DialogSymbols::on_BtnNextPage_clicked()
{
    if(BaseIndex+TotalLabelNum<=AllSymbolCount)
    {
        BaseIndex+=TotalLabelNum;
        LoadSymbolList(ui->treeView->currentIndex());
    }

}

void DialogSymbols::on_BtnFirstPage_clicked()
{
    if(BaseIndex==0) return;
    BaseIndex=0;
    LoadSymbolList(ui->treeView->currentIndex());
}

void DialogSymbols::on_BtnLastPage_clicked()
{
    if((AllSymbolCount%TotalLabelNum)!=0)  BaseIndex=AllSymbolCount/TotalLabelNum*TotalLabelNum;
    else
    {
      if(AllSymbolCount>0) BaseIndex=AllSymbolCount/TotalLabelNum-1;
    }
    LoadSymbolList(ui->treeView->currentIndex());
}


void DialogSymbols::on_BtnDelSelectSymbol_clicked()
{
    //选择具体的库文件
    if(LastSelectId<0)
    {
        QMessageBox::warning(nullptr, "提示", " 请选择要删除的库文件！");
        return;
    }
    SymbolID=labels[LastSelectId]->UsrData;

    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"您真要删除这一项库文件吗?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);
    if(result!=QMessageBox::Yes)
    {
        return;
    }
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr="DELETE FROM Symb2Lib WHERE Symb2Lib_ID = '"+SymbolID+"'";
    QueryVar.exec(SqlStr);
    //同时删除本地库文件
    QString Path="C:/TBD/SYMB2LIB/"+lbDwgName[LastSelectId]->text()+".dwg";
qDebug()<<"Path="<<Path;
    QFile file(Path);
    if(file.exists()) file.remove();
    LoadSymbolList(ui->treeView->currentIndex());
}


void DialogSymbols::on_BtnNewLib_clicked()
{
    //根据选择的节点确定默认节点
    QString DefaultFunctionDefineID=GetFunctionDefineIDFromIndex();
    DialogNewLib *dlg = new DialogNewLib(this);
    dlg->setModal(true);
    dlg->LoadMode(0,4,DefaultFunctionDefineID,0);//Mode=0:新建  Mode=1:复制  Mode=2:移动
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;

    Canceled=false;
    RetCode=3;
    Symb2_Name=dlg->FileName;
    FunctionDefineClass_ID=dlg->FunctionDefineClass_ID;
    SymbolType=dlg->SymbolType;
    delete dlg;
    this->close();
}

void DialogSymbols::on_BtnUpdateJpg_clicked()
{
    QString Str;
    int i;
    QPixmap p;
    for(i=0;i<TotalLabelNum;i++)
    {
        Str=lbDwgName[i]->text()+".dwg";
        QFileInfo file("C:/TBD/SYMB2LIB/"+Str);
        if(!file.exists())
        {
            QPixmap p=QPixmap("");
            labels[i]->setPixmap(p.scaled(LabelWidth,LabelHeight));
        }
        else
        {
            QString Str1=Str;
            Str1.replace("dwg","jpg");
            QFileInfo file("C:/TBD/data/SymbolDBJpg/"+Str1);
            pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/SYMB2LIB/"+Str,"C:/TBD/data/SymbolDBJpg/"+Str1,LabelWidth,LabelHeight);
            p=QPixmap("C:/TBD/data/SymbolDBJpg/"+Str1);
            labels[i]->setPixmap(p.scaled(LabelWidth,LabelHeight));
        }
    }
    p=QPixmap("");
    while(i<TotalLabelNum)
    {
        labels[i]->setPixmap(p);
        lbDwgName[i]->setText("");
        i++;
    }
}

int SearchIndex=0;
void DialogSymbols::on_BtnNext_clicked()
{
    int Index=0;
    for(int i=0;i<Model->rowCount();i++)//电气工程
    {qDebug()<<"i="<<i;
        if(Model->item(i,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
        {
            Index++;
            if(Index>SearchIndex)
            {
               ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)));
               SearchIndex++;
               return;
            }
        }
        for(int j=0;j<Model->item(i,0)->rowCount();j++)//功能大类
        {qDebug()<<"j="<<j;
            if(Model->item(i,0)->child(j,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
            {
                qDebug()<<"Index="<<Index<<",SearchIndex="<<SearchIndex;
                Index++;
                if(Index>SearchIndex)
                {
                   ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)));
                   ui->treeView->expand(Model->indexFromItem(Model->item(i,0)));
                   SearchIndex++;
                   return;
                }
            }
            for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)//功能小类
            {qDebug()<<"k="<<k;
                if(Model->item(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
                {
                    qDebug()<<"Index="<<Index<<",SearchIndex="<<SearchIndex;
                    Index++;
                    if(Index>SearchIndex)
                    {
                       ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)));
                       ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)));
                       SearchIndex++;
                       return;
                    }
                }
                for(int m=0;m<Model->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {qDebug()<<"m="<<m;
                   if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
                   {
                       qDebug()<<"Index="<<Index<<",SearchIndex="<<SearchIndex;
                        Index++;
                        if(Index>SearchIndex)
                        {
                           ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                           ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)));
                           SearchIndex++;
                           return;
                        }
                   }
                   for(int n=0;n<Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->rowCount();n++)
                   {qDebug()<<"n="<<n;
                       if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
                       {
     qDebug()<<"Index="<<Index<<",SearchIndex="<<SearchIndex;
                           Index++;
                           if(Index>SearchIndex)
                           {
     qDebug()<<"Index>SearchIndex,Index="<<Index<<",SearchIndex="<<SearchIndex;
     qDebug()<<"i="<<i<<",j="<<j<<",k="<<k<<",m="<<m<<",n="<<n;
                               ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)));
                               ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                               SearchIndex++;
                               return;
                           }
                       }
                   }
                }
            }
        }
    }
}

void DialogSymbols::on_BtnSearch_clicked()
{
    SearchIndex=0;
    for(int i=0;i<Model->rowCount();i++)//电气工程
    {
        if(Model->item(i,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
        {
            SearchIndex++;
            ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)));
            return;
        }
        for(int j=0;j<Model->item(i,0)->rowCount();j++)//功能大类
        {
            if(Model->item(i,0)->child(j,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
            {
                SearchIndex++;
                ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)));
                ui->treeView->expand(Model->indexFromItem(Model->item(i,0)));
                return;
            }
            for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)//功能小类
            {
                if(Model->item(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
                {
                    SearchIndex++;
                    ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)));
                    ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)));
                    return;
                }
                for(int m=0;m<Model->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
                    {
                        SearchIndex++;
                        ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                        ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)));
                        return;
                    }
                   for(int n=0;n<Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->rowCount();n++)
                   {
                       if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)->data(Qt::DisplayRole).toString().contains(ui->EdSearch->text()))
                       {
                           SearchIndex++;
                           ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)));
                           ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                           return;
                       }
                   }
                }
            }
        }
    }
}
