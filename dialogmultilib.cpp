#include "dialogmultilib.h"
#include "ui_dialogmultilib.h"

DialogMultiLib::DialogMultiLib(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogMultiLib)
{
    ui->setupUi(this);
    Canceled=true;
    ModelFold = new QStandardItemModel(ui->treeViewFold);
    ui->treeViewFold->header()->setVisible(false);
    ui->treeViewFold->setColumnWidth(0,50);
    ui->treeViewFold->setModel(ModelFold);
    UpdateList();
    ui->treeViewFold->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeViewFold,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewFoldByUnitPopMenu(QPoint)));

}

DialogMultiLib::~DialogMultiLib()
{
    delete ui;
}

void DialogMultiLib::ShowtreeViewFoldByUnitPopMenu(const QPoint &pos)
{
    if(!ui->treeViewFold->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewFold->indexAt(pos).data(Qt::WhatsThisRole).toString()=="多端元件库")
    {
        QAction actNewFold("新建文件夹", this);
        tree_menu.addAction(&actNewFold);
        connect(&actNewFold,SIGNAL(triggered()),this,SLOT(NewFold()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewFold->indexAt(pos).data(Qt::WhatsThisRole).toString()=="文件夹")
    {
        QAction actNewFold("新建文件夹", this);
        tree_menu.addAction(&actNewFold);
        connect(&actNewFold,SIGNAL(triggered()),this,SLOT(NewFold()));
        QAction actRenameFold("重命名文件夹", this);
        tree_menu.addAction(&actRenameFold);
        connect(&actRenameFold,SIGNAL(triggered()),this,SLOT(RenameFold()));
        QAction actDeleteFold("删除文件夹", this);
        tree_menu.addAction(&actDeleteFold);
        connect(&actDeleteFold,SIGNAL(triggered()),this,SLOT(DeleteFold()));
        tree_menu.exec(QCursor::pos());
    }
}

void DialogMultiLib::NewFold()
{
    QDialog *dialogNameEdit =new QDialog();
    dialogNameEdit->setWindowTitle("输入文件夹名称");
    dialogNameEdit->setMinimumSize(QSize(600,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNameEdit);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNameEdit);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNameEdit);
    m_label1->setText("文件夹名称");
    QLineEdit *m_LineEdit = new QLineEdit(dialogNameEdit);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_LineEdit);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNameEdit,SLOT(accept()));
    if (dialogNameEdit->exec()==QDialog::Accepted)
    {
        //查看文件目录是否存在 不存在则创建目录
        QDir *newDir = new QDir;
        newDir->mkpath("C:/TBD/UserData/MultiLib/"+m_LineEdit->text()+"/");
        UpdateList();
    }
}

void DialogMultiLib::RenameFold()
{
    QDialog *dialogNameEdit =new QDialog();
    dialogNameEdit->setWindowTitle("重命名文件夹");
    dialogNameEdit->setMinimumSize(QSize(600,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNameEdit);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNameEdit);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNameEdit);
    m_label1->setText("文件夹名称");
    QLineEdit *m_LineEdit = new QLineEdit(dialogNameEdit);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_LineEdit);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNameEdit,SLOT(accept()));
    if (dialogNameEdit->exec()==QDialog::Accepted)
    {
        //查看文件目录是否存在 不存在则创建目录
        QDir *newDir = new QDir;
        if(newDir->exists("C:/TBD/UserData/MultiLib/"+m_LineEdit->text()+"/"))
        {
            QMessageBox::warning(nullptr, "提示", "该文件夹名称已存在！");
            return;
        }
        newDir->rename("C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/","C:/TBD/UserData/MultiLib/"+m_LineEdit->text()+"/");
        UpdateList();
    }
}

void DialogMultiLib::DeleteFold()
{
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("warn"),"是否删除文件夹及文件夹下所有文件?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result==QMessageBox::Yes)
    {
        QDir dirItem("C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/");
        dirItem.removeRecursively();
        UpdateList();
    }
}

void DialogMultiLib::UpdateList()
{
    //原来选中的文件夹
    QString OriginalFold;
    if(ui->treeViewFold->currentIndex().isValid()&&(ui->treeViewFold->currentIndex().data(Qt::WhatsThisRole).toString()=="文件夹"))
        OriginalFold=ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString();
    ModelFold->clear();
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/fold图标.png"),"多端元件库");
    fatherItem->setData(QVariant("多端元件库"),Qt::WhatsThisRole);
    ModelFold->appendRow(fatherItem);
    ui->treeViewFold->expand(fatherItem->index());

    QDir dir("C:/TBD/UserData/MultiLib/");
    QFileInfoList file_list = dir.entryInfoList(QDir::Files | QDir::Hidden | QDir::NoSymLinks);
    QFileInfoList folder_list = dir.entryInfoList(QDir::Dirs | QDir::NoDotAndDotDot);
    for(int i=0;i<folder_list.count();i++)
    {
        QStandardItem *SubItem= new QStandardItem(QIcon("C:/TBD/data/fold图标.png"),folder_list.at(i).fileName());
        SubItem->setData(QVariant("文件夹"),Qt::WhatsThisRole);
        fatherItem->appendRow(SubItem);
    }
    if(fatherItem->rowCount()>0)
    {
        if(OriginalFold!="")
        {
            for(int i=0;i<fatherItem->rowCount();i++)
            {
                if(fatherItem->child(i,0)->index().data(Qt::DisplayRole).toString()==OriginalFold)
                {
                    ui->treeViewFold->setCurrentIndex(fatherItem->child(i,0)->index());
                    on_treeViewFold_clicked(fatherItem->child(i,0)->index());
                    break;
                }
            }
        }
        else
        {
            ui->treeViewFold->setCurrentIndex(fatherItem->child(0,0)->index());
            on_treeViewFold_clicked(fatherItem->child(0,0)->index());
        }

    }
}

void DialogMultiLib::on_BtnAdd_clicked()
{
    //输入数据文件名称
    QDialog *dialogNameEdit =new QDialog();
    dialogNameEdit->setWindowTitle("输入库文件名称");
    dialogNameEdit->setMinimumSize(QSize(600,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNameEdit);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNameEdit);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNameEdit);
    m_label1->setText("库文件名称");
    QLineEdit *m_LineEdit = new QLineEdit(dialogNameEdit);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_LineEdit);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNameEdit,SLOT(accept()));
    if (dialogNameEdit->exec()==QDialog::Accepted)
    {
        QString SourceFileName="C:/TBD/data/MultiLibTemplate.dwg";
        QString DestinationFileName="C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"."+m_LineEdit->text()+".dwg";
        QFile::copy(SourceFileName,DestinationFileName);
        OpenFilePath=DestinationFileName;
        UpdateList();
    }
    else return;
}

void DialogMultiLib::on_treeViewFold_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="文件夹") return;
    ui->listWidget->clear();
    QFileInfoList ListFileInfo=GetFileList("C:/TBD/UserData/MultiLib/"+index.data(Qt::DisplayRole).toString());
    for(int i=0;i<ListFileInfo.count();i++)
    {
        if(ListFileInfo.at(i).fileName().contains(".dwg")) ui->listWidget->addItem(ListFileInfo.at(i).fileName());
    }
}

void DialogMultiLib::on_listWidget_clicked(const QModelIndex &index)
{
    if(!ui->treeViewFold->currentIndex().isValid()) return;
    if(!index.isValid()) return;
    qDebug()<<"C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/"+index.data(Qt::DisplayRole).toString()+".dwg";
    UnitSymbolsView("C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/"+index.data(Qt::DisplayRole).toString(),"C:/TBD/data/TempImage/"+index.data(Qt::DisplayRole).toString()+".jpg",ui->LbJpg,true);
}

void DialogMultiLib::on_BtnModify_clicked()
{
    if(!ui->treeViewFold->currentIndex().isValid()) return;
    if(ui->listWidget->currentRow()<0) return;
    OpenFilePath="C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/"+ui->listWidget->currentItem()->text();
    Canceled=false;
    RetCode=1;
    this->close();
}

void DialogMultiLib::on_BtnDelete_clicked()
{
    if(!ui->treeViewFold->currentIndex().isValid()) return;
    if(ui->listWidget->currentRow()<0) return;
    QString Path="C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/"+ui->listWidget->currentItem()->text();
    QFile file(Path);
    if(file.exists()) file.remove();
    UpdateList();
}

void DialogMultiLib::on_listWidget_doubleClicked(const QModelIndex &index)
{
    if(!ui->treeViewFold->currentIndex().isValid()) return;
    if(!index.isValid()) return;
    OpenFilePath="C:/TBD/UserData/MultiLib/"+ui->treeViewFold->currentIndex().data(Qt::DisplayRole).toString()+"/"+index.data(Qt::DisplayRole).toString();
    Canceled=false;
    RetCode=1;
    this->close();
}
