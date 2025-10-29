#include "dialogsymbolsort.h"
#include "ui_dialogsymbolsort.h"

DialogSymbolSort::DialogSymbolSort(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogSymbolSort)
{
    ui->setupUi(this);
    Canceled=true;
}

DialogSymbolSort::~DialogSymbolSort()
{
    delete ui;
}
void DialogSymbolSort::LoadData()
{
    ModelGroup = new QStandardItemModel(ListGroupName.count(), 1,this);
    for(int i=0;i<ListGroupName.count();i++)
    {
       ModelGroup->setItem(i,0,new QStandardItem(ListGroupName.at(i))) ;
    }
    ui->listViewGroup->setModel(ModelGroup);
    ui->listViewGroup->setContextMenuPolicy(Qt::CustomContextMenu);
    ui->listViewGroup->setEditTriggers(QAbstractItemView::DoubleClicked);
    connect(ui->listViewGroup,SIGNAL(customContextMenuRequested(const QPoint&)),this,SLOT(show_Menu(const QPoint&)));
    //ui->listViewGroup->setFixedSize(200,300);
    connect(ui->listViewGroup,SIGNAL(clicked(QModelIndex)),this,SLOT(showGroupMember(QModelIndex)));
    connect(ui->listViewGroupMember,SIGNAL(clicked(QModelIndex)),this,SLOT(GroupMemberView(QModelIndex)));


    QStandardItemModel *ModelAllSymbols = new QStandardItemModel(ListAllSymbols->count(), 1,this);
    for(int i=0;i<ListAllSymbols->count();i++)
    {
       ModelAllSymbols->setItem(i,0,new QStandardItem(ListAllSymbols->at(i))) ;
    }
    ui->listViewAllSymbol->setModel(ModelAllSymbols);
    connect(ui->listViewAllSymbol,SIGNAL(clicked(QModelIndex)),this,SLOT(AllSymbolsView(QModelIndex)));
    //ui->listViewAllSymbol->setFixedSize(200,300);
    SymbolType=0;
    UpdateGroupMembers();
}
void DialogSymbolSort::showGroupMember(QModelIndex index)
{
    SymbolType=index.row();
    UpdateGroupMembers();
    QPixmap p=QPixmap("");
    ui->Lb_GroupMemberView->setPixmap(p);
}
void DialogSymbolSort::GroupMemberView(QModelIndex index)
{
    QString SelectSymbol=index.data().toString()+".dwg";
    //qDebug()<<SelectSymbol;
    //如果不存在dwg对应的jpg文件，则创建jpg文件
    QString Str1=SelectSymbol;
    Str1.replace("dwg","jpg");
    QString path;
    if(Mode==0) path="C:/TBD/SymbolB/TempJpg/"+Str1;
    else if(Mode==1) path="C:/TBD/Part2lib/TempJpg/"+Str1;
    QFileInfo file(path);
    if(!file.exists())
    {
       //MxDrawApplication *App=new MxDrawApplication();
       //IMxDrawApplication *pApp=(IMxDrawApplication*)App;
       if(Mode==0)   pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/SYMB2LIB/"+SelectSymbol,"C:/TBD/data/SymbolJpg/"+Str1,100,50);
       else if(Mode==1)  pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/Part2lib/Dwg/"+SelectSymbol,"C:/TBD/Part2lib/TempJpg/"+Str1,100,50);
    }
    QPixmap p;
    if(Mode==0)  p=QPixmap("C:/TBD/data/SymbolJpg/"+Str1);
    else if(Mode==1)  p=QPixmap("C:/TBD/Part2lib/TempJpg/"+Str1);
    ui->Lb_GroupMemberView->setStyleSheet("background-color: rgb(0, 0, 0)");
    ui->Lb_GroupMemberView->setScaledContents(false);
    ui->Lb_GroupMemberView->setFrameShape(QFrame::Panel);
    ui->Lb_GroupMemberView->setFrameShadow(QFrame::Sunken);
    ui->Lb_GroupMemberView->setLineWidth(3);
    ui->Lb_GroupMemberView->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);
    ui->Lb_GroupMemberView->setPixmap(p.scaled(ui->Lb_AllSymbolsView->width()-8,ui->Lb_AllSymbolsView->height()-8));
}

void DialogSymbolSort::AllSymbolsView(QModelIndex index)
{
    QString SelectSymbol=index.data().toString()+".dwg";
    //如果不存在dwg对应的jpg文件，则创建jpg文件
    QString Str1=SelectSymbol;
    Str1.replace("dwg","jpg");
    QString path;
    if(Mode==0) path="C:/TBD/data/SymbolJpg/"+Str1;
    else if(Mode==1) path="C:/TBD/Part2lib/TempJpg/"+Str1;
    QFileInfo file(path);
    if(!file.exists())
    {
       //MxDrawApplication *App=new MxDrawApplication();
       //IMxDrawApplication *pApp=(IMxDrawApplication*)App;
       if(Mode==0)   pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/SYMB2LIB/"+SelectSymbol,"C:/TBD/data/SymbolJpg/"+Str1,100,50);
       else if(Mode==1)  pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/Part2lib/Dwg/"+SelectSymbol,"C:/TBD/Part2lib/TempJpg/"+Str1,100,50);
    }
    QPixmap p;
    if(Mode==0)  p=QPixmap("C:/TBD/data/SymbolJpg/"+Str1);
    else if(Mode==1)  p=QPixmap("C:/TBD/Part2lib/TempJpg/"+Str1);
    ui->Lb_AllSymbolsView->setStyleSheet("background-color: rgb(0, 0, 0)");
    ui->Lb_AllSymbolsView->setScaledContents(false);
    ui->Lb_AllSymbolsView->setFrameShape(QFrame::Panel);
    ui->Lb_AllSymbolsView->setFrameShadow(QFrame::Sunken);
    ui->Lb_AllSymbolsView->setLineWidth(3);
    ui->Lb_AllSymbolsView->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);
    ui->Lb_AllSymbolsView->setPixmap(p.scaled(ui->Lb_AllSymbolsView->width()-8,ui->Lb_AllSymbolsView->height()-8));
}
void DialogSymbolSort::show_Menu(const QPoint&)
{
    if(ui->listViewGroup->selectionModel()->selectedIndexes().empty()) return;
    QMenu *menu=new QMenu(ui->listViewGroup);
    QAction *ActionAddGroup = menu->addAction("增加类型");
    QAction *ActionModifyGroup = menu->addAction("修改类型");
    QAction *ActionRemoveGroup = menu->addAction("删除");
    connect(ActionAddGroup,SIGNAL(triggered(bool)),this,SLOT(DoAddGroup()));
    connect(ActionModifyGroup,SIGNAL(triggered(bool)),this,SLOT(DoModifyGroup()));
    connect(ActionRemoveGroup,SIGNAL(triggered(bool)),this,SLOT(DoRemoveGroup()));
    menu->exec(QCursor::pos());
    ui->listViewGroup->selectionModel()->clear();
}
void DialogSymbolSort::DoAddGroup()//增加类型
{
   ModelGroup->appendRow(new QStandardItem("新类型"));
   ListGroupName.append("新类型");
   QStringList list;
   list.clear();
   SymbolGroupList.append(list);
}
void DialogSymbolSort::DoModifyGroup()//修改类型
{
   emit SIGNAL(DoubleClicked(ui->listViewGroup->currentIndex()));
}
void DialogSymbolSort::DoRemoveGroup()//删除
{
    SymbolGroupList.removeAt(ui->listViewGroup->currentIndex().row());
    ModelGroup->removeRow(ui->listViewGroup->currentIndex().row());
    SymbolType=0;
    UpdateGroupMembers();
}
void DialogSymbolSort::UpdateGroupMembers()
{

    QStandardItemModel *ModelGroupMember = new QStandardItemModel(SymbolGroupList.at(SymbolType).count(), 1,this);
    for(int i=0;i<SymbolGroupList.at(SymbolType).count();i++)
    {
        ModelGroupMember->setItem(i,0,new QStandardItem(SymbolGroupList.at(SymbolType).at(i))) ;
    }
    ui->listViewGroupMember->setModel(ModelGroupMember);
    //ui->listViewGroupMember->setFixedSize(200,300);
}

void DialogSymbolSort::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}

void DialogSymbolSort::on_BtnAddToGroup_clicked()
{
    if(ui->listViewAllSymbol->currentIndex().row()<0) return;
    if(ui->listViewGroup->currentIndex().row()<0) return;
    //将符号添加进组
    QString SelectSymbol=ListAllSymbols->at(ui->listViewAllSymbol->currentIndex().row());
    if(SymbolGroupList.at(ui->listViewGroup->currentIndex().row()).contains(SelectSymbol)) return;
    //根据当前状态重新生成SymbolGroupList
    QList<QStringList> NewSymbolGroupList;
    NewSymbolGroupList.clear();
    for(int i=0;i<SymbolGroupList.count();i++)
    {
        if(i==ui->listViewGroup->currentIndex().row())
        {
            QStringList ListGroupMember;
            ListGroupMember.clear();
            for(int j=0;j<SymbolGroupList.at(i).count();j++)
            {
               ListGroupMember.append(SymbolGroupList.at(i).at(j));
            }
            ListGroupMember.append(SelectSymbol);
            NewSymbolGroupList.append(ListGroupMember);
        }
        else NewSymbolGroupList.append(SymbolGroupList.at(i));
    }
    SymbolGroupList=NewSymbolGroupList;
    SymbolType=ui->listViewGroup->currentIndex().row();
    UpdateGroupMembers();
    QModelIndex qindex = ui->listViewGroupMember->model()->index(ui->listViewGroupMember->model()->rowCount()-1,0);   //默认选中 index
    ui->listViewGroupMember->setCurrentIndex(qindex);
}

void DialogSymbolSort::on_BtnRemoveGroup_clicked()
{
    if(ui->listViewGroupMember->currentIndex().row()<0) return;
    if(ui->listViewGroup->currentIndex().row()<0) return;
    //将符号移出组
    QString SelectSymbol=ListAllSymbols->at(ui->listViewAllSymbol->currentIndex().row());
    //根据当前状态重新生成SymbolGroupList
    QList<QStringList> NewSymbolGroupList;
    NewSymbolGroupList.clear();
    for(int i=0;i<SymbolGroupList.count();i++)
    {
        if(i==ui->listViewGroup->currentIndex().row())
        {
            QStringList ListGroupMember;
            ListGroupMember.clear();
            for(int j=0;j<SymbolGroupList.at(i).count();j++)
            {
                if(j!=ui->listViewGroupMember->currentIndex().row())
                {
                    ListGroupMember.append(SymbolGroupList.at(i).at(j));
                }
            }
            NewSymbolGroupList.append(ListGroupMember);
        }
        else NewSymbolGroupList.append(SymbolGroupList.at(i));
    }
    SymbolGroupList=NewSymbolGroupList;
    SymbolType=ui->listViewGroup->currentIndex().row();
    UpdateGroupMembers();
    ui->listViewGroupMember->selectionModel()->clear();
}

void DialogSymbolSort::on_BtnOK_clicked()
{
    Canceled=false;
    //更新Groupname
    ListGroupName.clear();
    for(int i=0;i<ui->listViewGroup->model()->rowCount();i++)
    {
        ListGroupName.append(ui->listViewGroup->model()->index(i,0).data().toString());
    }
    this->close();
}


void DialogSymbolSort::on_BtnMemberSearch_clicked()
{
   for(int i=0;i<ui->listViewGroupMember->model()->rowCount();i++)
   {
       if(ui->listViewGroupMember->model()->index(i,0).data().toString().contains(ui->lineEdit_MemberSearch->text()))
       {
           QModelIndex qindex = ui->listViewGroupMember->model()->index(i,0);
           ui->listViewGroupMember->setCurrentIndex(qindex);
           break;
       }
   }
}

void DialogSymbolSort::on_BtnAllSymbolSearch_clicked()
{
    for(int i=0;i<ui->listViewAllSymbol->model()->rowCount();i++)
    {
        if(ui->listViewAllSymbol->model()->index(i,0).data().toString().contains(ui->lineEdit_AllSymbolSearch->text()))
        {
            QModelIndex qindex = ui->listViewAllSymbol->model()->index(i,0);
            ui->listViewAllSymbol->setCurrentIndex(qindex);
            break;
        }
    }
}
