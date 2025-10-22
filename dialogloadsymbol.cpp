#include "dialogloadsymbol.h"
#include <QStandardItemModel>
#include "ui_dialogloadsymbol.h"
#include <QDir>
#include <QMessageBox>

DialogLoadSymbol::DialogLoadSymbol(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogLoadSymbol)
{
    ui->setupUi(this);
    Canceled=true;
    Model = new QStandardItemModel(0, 0,this);

    ui->treeView->header()->setVisible(false);
    ui->treeView->setColumnWidth(0,50);
    ui->treeView->setModel(Model);
    LoadModelFromDB();
    for(int i=0;i<TotalLabelNum;i++)
    {
        labels[i]=new QXlabel(this);
        lbDwgName[i]=new QLabel(this);
        lbDwgName[i]->setVisible(false);
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
        lbDwgName[i]->setMinimumHeight(20);
        lbDwgName[i]->setAlignment(Qt::AlignHCenter);
        lbDwgName[i]->setAlignment(Qt::AlignVCenter);
        connect(labels[i], SIGNAL(doubleClicked(int)),this, SLOT(SymbolSel(int)));
        connect(labels[i], SIGNAL(Clicked(int)),this, SLOT(SymbolSelect(int)));
    }
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
    if(Model->rowCount()>0)
    {
        for(int i=0;i<Model->rowCount();i++)
          ui->treeView->expand(Model->item(i,0)->index());
        if(Model->item(0,0)->rowCount()>0)
        {
            ui->treeView->setCurrentIndex(Model->item(0,0)->child(0,0)->index());
            LoadSymbolList(ui->treeView->currentIndex());
        }
    }
}

void DialogLoadSymbol::LoadModelFromDB()
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
        temp = QString("SELECT * FROM Symb2Class WHERE Level = 1 AND Parent_ID = '"+QueryLevel0.value("Symb2Class_ID").toString()+"' ORDER BY _Order");
        QueryLevel1.exec(temp);
        while(QueryLevel1.next())
        {
            QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号大类.png"),QueryLevel1.value("Desc").toString());
            SubFatherItem->setData(QVariant(QueryLevel1.value("Symb2Class_ID").toString()),Qt::UserRole);
            SubFatherItem->setData(QVariant("1"),Qt::WhatsThisRole);
            fatherItem->appendRow(SubFatherItem);
            QSqlQuery QueryLevel2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            temp = QString("SELECT * FROM Symb2Class WHERE Level = 2 AND Parent_ID = '"+QueryLevel1.value("Symb2Class_ID").toString()+"' ORDER BY _Order");
            QueryLevel2.exec(temp);
            while(QueryLevel2.next())
            {
                QStandardItem *SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号小类.png"),QueryLevel2.value("Desc").toString());
                SubSubFatherItem->setData(QVariant(QueryLevel2.value("Symb2Class_ID").toString()),Qt::UserRole);
                SubSubFatherItem->setData(QVariant("2"),Qt::WhatsThisRole);
                SubFatherItem->appendRow(SubSubFatherItem);
                QSqlQuery QueryLevel3 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                temp = QString("SELECT * FROM Symb2Class WHERE Level = 3 AND Parent_ID = '"+QueryLevel2.value("Symb2Class_ID").toString()+"' ORDER BY _Order");
                QueryLevel3.exec(temp);
                while(QueryLevel3.next())
                {
                    QStandardItem *SubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号规格.png"),QueryLevel3.value("Desc").toString());
                    SubSubSubFatherItem->setData(QVariant(QueryLevel3.value("Symb2Class_ID").toString()),Qt::UserRole);
                    SubSubSubFatherItem->setData(QVariant("3"),Qt::WhatsThisRole);
                    SubSubFatherItem->appendRow(SubSubSubFatherItem);
                    QSqlQuery QueryLevel4 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                    temp = QString("SELECT * FROM Symb2Class WHERE Level = 4 AND Parent_ID = '"+QueryLevel3.value("Symb2Class_ID").toString()+"' ORDER BY _Order");
                    QueryLevel4.exec(temp);
                    while(QueryLevel4.next())
                    {
                        QStandardItem *SubSubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号规格.png"),QueryLevel4.value("Desc").toString());
                        SubSubSubSubFatherItem->setData(QVariant(QueryLevel4.value("Symb2Class_ID").toString()),Qt::UserRole);
                        SubSubSubSubFatherItem->setData(QVariant("4"),Qt::WhatsThisRole);
                        SubSubSubFatherItem->appendRow(SubSubSubSubFatherItem);
                    }
                }
            }
        }
    }
}

void DialogLoadSymbol::UpdateSymbols(QStringList listSymbolName,QStringList listSymbolID)
{
    QString Str;
    int i;
    QPixmap p;
    QStringList listSymbolload;
    //MxDrawApplication *App=new MxDrawApplication();
    //IMxDrawApplication *pApp=(IMxDrawApplication*)App;
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
            QFileInfo file("C:/TBD/data/SymbolLoadJpg/"+Str1);
            if(!file.exists())//如果不存在dwg对应的jpg文件，则创建jpg文件
              pApp->dynamicCall("DwgToJpg(QString,QString,int,int)","C:/TBD/SYMB2LIB/"+Str,"C:/TBD/data/SymbolLoadJpg/"+Str1,LabelWidth,LabelHeight);
            p=QPixmap("C:/TBD/data/SymbolLoadJpg/"+Str1);
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


void DialogLoadSymbol::SymbolSel(int id)
{
    SymbolSelect(id);
    Canceled=false;
    RetCode=3;
    close();
}

void DialogLoadSymbol::SymbolSelect(int id)
{
    QString FileName;
    BlockFileName=lbDwgName[id]->text()+".dwg";
    SymbolID=labels[id]->UsrData;

    if(LastSelectId>=0) labels[LastSelectId]->setStyleSheet("border:0px solid black;");
    labels[id]->setStyleSheet("border:2px solid red;");
    LastSelectId=id;
}

DialogLoadSymbol::~DialogLoadSymbol()
{
    delete ui;
    for(int i=0;i<TotalLabelNum;i++) { delete labels[i];delete lbDwgName[i];}
}

void DialogLoadSymbol::LoadSymbolList(const QModelIndex &index)
{
    QString temp;
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    //确定是哪一级
    if(index.data(Qt::WhatsThisRole).toString().toInt()<=3)
    {
        temp = QString("SELECT * FROM Symb2Lib WHERE Symb2Class_ID LIKE '"+index.data(Qt::UserRole).toString()+"%' AND _Order = 1");
        QueryVar.exec(temp);
        QStringList listSymbolName,listSymbolID;
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
        QStringList listSymbolName,listSymbolID;
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
}

void DialogLoadSymbol::on_treeView_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    BaseIndex=0;
    LoadSymbolList(index);
}

void DialogLoadSymbol::on_BtnPrePage_clicked()
{
    if(BaseIndex<TotalLabelNum) return;
    BaseIndex-=TotalLabelNum;
    LoadSymbolList(ui->treeView->currentIndex());
}

void DialogLoadSymbol::on_BtnNextPage_clicked()
{
    if(BaseIndex+TotalLabelNum<=AllSymbolCount)
    {
        BaseIndex+=TotalLabelNum;
        LoadSymbolList(ui->treeView->currentIndex());
    }

}

void DialogLoadSymbol::on_BtnFirstPage_clicked()
{
    if(BaseIndex==0) return;
    BaseIndex=0;
    LoadSymbolList(ui->treeView->currentIndex());
}

void DialogLoadSymbol::on_BtnLastPage_clicked()
{
    if((AllSymbolCount%TotalLabelNum)!=0)  BaseIndex=AllSymbolCount/TotalLabelNum*TotalLabelNum;
    else
    {
      if(AllSymbolCount>0) BaseIndex=AllSymbolCount/TotalLabelNum-1;
    }
    LoadSymbolList(ui->treeView->currentIndex());
}
void DialogLoadSymbol::closeEvent(QCloseEvent *event)
{
    emit(DialogIsClosed());
}

void DialogLoadSymbol::on_BtnOK_clicked()
{
    Canceled=false;
    RetCode=3;
    close();
}

void DialogLoadSymbol::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogLoadSymbol::SetCurStackedWidgetIndex(int Index)
{
    ui->stackedWidget_Btn->setCurrentIndex(Index);
}

void DialogLoadSymbol::on_BtnReLoad_clicked()
{
    LoadModelFromDB();
}
