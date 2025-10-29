#include "dialogfuncdefine.h"
#include "ui_dialogfuncdefine.h"

DialogFuncDefine::DialogFuncDefine(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogFuncDefine)
{
    ui->setupUi(this);
    Canceled=true;
    Model = new QStandardItemModel(0, 0,this);
    ui->treeView->header()->setVisible(false);
    ui->treeView->setColumnWidth(0,50);
    ui->treeView->setModel(Model);
    LoadFunctionDefineClass();
    if(Model->rowCount()>0)
    {
        for(int i=0;i<Model->rowCount();i++)
          ui->treeView->expand(Model->item(i,0)->index());
        if(Model->item(0,0)->rowCount()>0)
        {
            ui->treeView->setCurrentIndex(Model->item(0,0)->child(0,0)->index());
        }
    }
    ui->BtnOk->setEnabled(false);
    //ui->CbFuncType->setEnabled(false);

    ui->treeView->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeView,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewPopMenu(QPoint)));
}

DialogFuncDefine::~DialogFuncDefine()
{
    delete ui;
}

void DialogFuncDefine::ShowtreeViewPopMenu(const QPoint &pos)
{
    if(!ui->treeView->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="0")
    {
        QAction actNewLevel0("新建功能总类别", this);
        tree_menu.addAction(&actNewLevel0);
        connect(&actNewLevel0,SIGNAL(triggered()),this,SLOT(NewLevel0()));
        QAction actNewLevel("新建子功能", this);
        tree_menu.addAction(&actNewLevel);
        connect(&actNewLevel,SIGNAL(triggered()),this,SLOT(NewLevel()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="1")
    {
        QAction actNewLevel("新建子功能", this);
        tree_menu.addAction(&actNewLevel);
        connect(&actNewLevel,SIGNAL(triggered()),this,SLOT(NewLevel()));
        QAction actDelete("删除", this);
        tree_menu.addAction(&actDelete);
        connect(&actDelete,SIGNAL(triggered()),this,SLOT(Delete()));
        QAction actRename("重命名", this);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actFuncEdit("编辑", this);
        tree_menu.addAction(&actFuncEdit);
        connect(&actFuncEdit,SIGNAL(triggered()),this,SLOT(FuncEdit()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="2")
    {
        QAction actNewLevel("新建子功能", this);
        tree_menu.addAction(&actNewLevel);
        connect(&actNewLevel,SIGNAL(triggered()),this,SLOT(NewLevel()));
        QAction actDelete("删除", this);
        tree_menu.addAction(&actDelete);
        connect(&actDelete,SIGNAL(triggered()),this,SLOT(Delete()));
        QAction actRename("重命名", this);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actFuncEdit("编辑", this);
        tree_menu.addAction(&actFuncEdit);
        connect(&actFuncEdit,SIGNAL(triggered()),this,SLOT(FuncEdit()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="3")
    {
        QAction actNewLevel("新建子功能", this);
        tree_menu.addAction(&actNewLevel);
        connect(&actNewLevel,SIGNAL(triggered()),this,SLOT(NewLevel()));
        QAction actDelete("删除", this);
        tree_menu.addAction(&actDelete);
        connect(&actDelete,SIGNAL(triggered()),this,SLOT(Delete()));
        QAction actRename("重命名", this);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actFuncEdit("编辑", this);
        tree_menu.addAction(&actFuncEdit);
        connect(&actFuncEdit,SIGNAL(triggered()),this,SLOT(FuncEdit()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeView->indexAt(pos).data(Qt::WhatsThisRole).toString()=="4")
    {
        QAction actDelete("删除", this);
        tree_menu.addAction(&actDelete);
        connect(&actDelete,SIGNAL(triggered()),this,SLOT(Delete()));
        QAction actRename("重命名", this);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actFuncEdit("编辑", this);
        tree_menu.addAction(&actFuncEdit);
        connect(&actFuncEdit,SIGNAL(triggered()),this,SLOT(FuncEdit()));
        tree_menu.exec(QCursor::pos());
    }
}

void DialogFuncDefine::FuncEdit()
{
    if(!ui->treeView->currentIndex().isValid()) return;
    DialogNewFunc *dlg = new DialogNewFunc(this);
    dlg->setWindowTitle("功能编辑");
    dlg->Mode=1;
    dlg->SetUIEnabled(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString());
    dlg->LoadInfo(ui->treeView->currentIndex().data(Qt::UserRole).toString());
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;

    this->FunctionDefineClass_ID=dlg->FunctionDefineClass_ID;
    delete dlg;
    LoadFunctionDefineClass();
    SetCurrentIndex(this->FunctionDefineClass_ID);
}

void DialogFuncDefine::Rename()
{
    if(!ui->treeView->currentIndex().isValid()) return;
    QDialog *dialogUnitTypeEdit =new QDialog();
    dialogUnitTypeEdit->setWindowTitle("输入功能名称");
    dialogUnitTypeEdit->setMinimumSize(QSize(300,70));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUnitTypeEdit);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogUnitTypeEdit);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogUnitTypeEdit);
    m_label1->setText("功能名称");
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
        QString NewUnitType=m_LineEdit->text();
        if(NewUnitType=="")
        {
            QMessageBox::warning(nullptr, "提示", "功能名称为空！");
            return;
        }
        QSqlQuery QueryUpdate = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr="UPDATE FunctionDefineClass SET FunctionDefineName=:FunctionDefineName WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryUpdate.prepare(SqlStr);
        QueryUpdate.bindValue(":FunctionDefineName",m_LineEdit->text());
        QueryUpdate.exec();
        this->FunctionDefineClass_ID=ui->treeView->currentIndex().data(Qt::UserRole).toString();
        LoadFunctionDefineClass();
        SetCurrentIndex(this->FunctionDefineClass_ID);
    }

}

void DialogFuncDefine::Delete()
{
    if(!ui->treeView->currentIndex().isValid()) return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除?",
                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="1")
    {
        QSqlQuery QueryDelete = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QSqlQuery QuerySearchLevel2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM FunctionDefineClass WHERE ParentNo= '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QuerySearchLevel2.exec(SqlStr);
        while(QuerySearchLevel2.next())//Level=2
        {
            QSqlQuery QuerySearchLevel3 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            SqlStr="SELECT * FROM FunctionDefineClass WHERE ParentNo= '"+QuerySearchLevel2.value("FunctionDefineClass_ID").toString()+"'";
            QuerySearchLevel3.exec(SqlStr);
            while(QuerySearchLevel3.next())//Level=3
            {
                SqlStr="DELETE FROM FunctionDefineClass WHERE ParentNo = '"+QuerySearchLevel3.value("FunctionDefineClass_ID").toString()+"'";
                QueryDelete.exec(SqlStr);
            }
            SqlStr = "DELETE FROM FunctionDefineClass WHERE ParentNo = '"+QuerySearchLevel2.value("FunctionDefineClass_ID").toString()+"'";
            QueryDelete.exec(SqlStr);
        }
        SqlStr = "DELETE FROM FunctionDefineClass WHERE ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
        SqlStr = "DELETE FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="2")
    {
        QSqlQuery QueryDelete = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QSqlQuery QuerySearchLevel3 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM FunctionDefineClass WHERE ParentNo= '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QuerySearchLevel3.exec(SqlStr);
        while(QuerySearchLevel3.next())//Level=3
        {
            SqlStr="DELETE FROM FunctionDefineClass WHERE ParentNo = '"+QuerySearchLevel3.value("FunctionDefineClass_ID").toString()+"'";
            QueryDelete.exec(SqlStr);
        }
        SqlStr = "DELETE FROM FunctionDefineClass WHERE ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
        SqlStr = "DELETE FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="3")
    {
        QSqlQuery QueryDelete = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr = "DELETE FROM FunctionDefineClass WHERE ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
        SqlStr = "DELETE FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="4")
    {
        QSqlQuery QueryDelete = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString SqlStr = "DELETE FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
        QueryDelete.exec(SqlStr);
    }
    if(ui->treeView->currentIndex().parent().isValid())
    {
        this->FunctionDefineClass_ID=ui->treeView->currentIndex().parent().data(Qt::UserRole).toString();
        LoadFunctionDefineClass();
        SetCurrentIndex(this->FunctionDefineClass_ID);
    }
    else LoadFunctionDefineClass();
}

void DialogFuncDefine::NewLevel0()
{
    if(!ui->treeView->currentIndex().isValid()) return;
    if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="0")
    {
        QDialog *dialogUnitTypeEdit =new QDialog();
        dialogUnitTypeEdit->setWindowTitle("输入总类别");
        dialogUnitTypeEdit->setMinimumSize(QSize(600,100));
        QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUnitTypeEdit);

        QVBoxLayout *layout = new QVBoxLayout(nullptr);
        QPushButton *pushbuttonOK = new QPushButton(dialogUnitTypeEdit);
        pushbuttonOK->setText("确认");

        QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
        QLabel *m_label1 = new QLabel(dialogUnitTypeEdit);
        m_label1->setText("总类别");
        QLineEdit *m_LineEdit = new QLineEdit(dialogUnitTypeEdit);
        linelayout1->addWidget(m_label1);
        linelayout1->addWidget(m_LineEdit);

        layout->addLayout(linelayout1);
        layout->addWidget(pushbuttonOK);
        formlayoutNameEdit->addRow(layout);

        QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogUnitTypeEdit,SLOT(accept()));
        if (dialogUnitTypeEdit->exec()==QDialog::Accepted)
        {
            QString NewUnitType=m_LineEdit->text();
            if(NewUnitType=="")
            {
                QMessageBox::warning(this,"提示","总类别为空！");
                return;
            }
            int MaxFunctionDefineClass_ID=(ui->treeView->currentIndex().data(Qt::UserRole).toString()).toInt();
            QSqlQuery QueryID = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempQueryID = "SELECT FunctionDefineClass_ID FROM FunctionDefineClass WHERE Level = 0 AND ParentNo = '0'";
            QueryID.exec(tempQueryID);
            while(QueryID.next())
            {
                if(QueryID.value(0).toInt()>=MaxFunctionDefineClass_ID) MaxFunctionDefineClass_ID=QueryID.value(0).toInt()+1;
            }
            //更新T_ProjectDatabase数据库的Equipment表
            QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempSQL = "INSERT INTO FunctionDefineClass (FunctionDefineClass_ID,ParentNo,Level,Desc,_Order,FunctionDefineName,FunctionDefineCode,DefaultSymbol)"
                              "VALUES (:FunctionDefineClass_ID,:ParentNo,:Level,:Desc,:_Order,:FunctionDefineName,:FunctionDefineCode,:DefaultSymbol)";
            QueryVar.prepare(tempSQL);
            QueryVar.bindValue(":FunctionDefineClass_ID",QString::number(MaxFunctionDefineClass_ID));
            QueryVar.bindValue(":ParentNo","0");
            QueryVar.bindValue(":Level",0);
            QueryVar.bindValue(":Desc","");
            QSqlQuery Query_Order = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            tempSQL = "SELECT * FROM FunctionDefineClass WHERE Level = 0 AND ParentNo = '0' ORDER BY _Order DESC";
            Query_Order.exec(tempSQL);
            if(Query_Order.next()) QueryVar.bindValue(":_Order",Query_Order.value("_Order").toInt()+1);
            else  QueryVar.bindValue(":_Order",1);
            QueryVar.bindValue(":FunctionDefineName",NewUnitType);
            QueryVar.bindValue(":FunctionDefineCode","");
            QueryVar.bindValue(":DefaultSymbol","");
            QueryVar.exec();
            this->FunctionDefineClass_ID=QString::number(MaxFunctionDefineClass_ID);
            LoadFunctionDefineClass();
            SetCurrentIndex(this->FunctionDefineClass_ID);
        }
        else return;
    }
}

void DialogFuncDefine::NewLevel()
{
    if(!ui->treeView->currentIndex().isValid()) return;
    if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="0")//新建功能
    {
        QDialog *dialogUnitTypeEdit =new QDialog();
        dialogUnitTypeEdit->setWindowTitle("输入功能名称");
        dialogUnitTypeEdit->setMinimumSize(QSize(300,70));
        QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUnitTypeEdit);

        QVBoxLayout *layout = new QVBoxLayout(nullptr);
        QPushButton *pushbuttonOK = new QPushButton(dialogUnitTypeEdit);
        pushbuttonOK->setText("确认");

        QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
        QLabel *m_label1 = new QLabel(dialogUnitTypeEdit);
        m_label1->setText("功能名称");
        QLineEdit *m_LineEdit = new QLineEdit(dialogUnitTypeEdit);
        linelayout1->addWidget(m_label1);
        linelayout1->addWidget(m_LineEdit);

        layout->addLayout(linelayout1);
        layout->addWidget(pushbuttonOK);
        formlayoutNameEdit->addRow(layout);

        QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogUnitTypeEdit,SLOT(accept()));
        if (dialogUnitTypeEdit->exec()==QDialog::Accepted)
        {
            QString NewUnitType=m_LineEdit->text();
            if(NewUnitType=="")
            {
                QMessageBox::warning(nullptr, "提示", "功能名称为空！");
                return;
            }
            int MaxFunctionDefineClass_ID=(ui->treeView->currentIndex().data(Qt::UserRole).toString()+"00").toInt();
            QSqlQuery QueryID = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempQueryID = "SELECT FunctionDefineClass_ID FROM FunctionDefineClass WHERE Level = 1 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
            QueryID.exec(tempQueryID);
            while(QueryID.next())
            {
                if(QueryID.value(0).toInt()>=MaxFunctionDefineClass_ID) MaxFunctionDefineClass_ID=QueryID.value(0).toInt()+1;
            }

            //更新T_ProjectDatabase数据库的Equipment表
            QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempSQL = "INSERT INTO FunctionDefineClass (FunctionDefineClass_ID,ParentNo,Level,Desc,_Order,FunctionDefineName,FunctionDefineCode,DefaultSymbol)"
                              "VALUES (:FunctionDefineClass_ID,:ParentNo,:Level,:Desc,:_Order,:FunctionDefineName,:FunctionDefineCode,:DefaultSymbol)";
            QueryVar.prepare(tempSQL);
            QueryVar.bindValue(":FunctionDefineClass_ID",QString::number(MaxFunctionDefineClass_ID));
            QueryVar.bindValue(":ParentNo",ui->treeView->currentIndex().data(Qt::UserRole).toString());
            QueryVar.bindValue(":Level",1);
            QueryVar.bindValue(":Desc","");
            QSqlQuery Query_Order = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            tempSQL = QString("SELECT * FROM FunctionDefineClass WHERE Level = 1 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"' ORDER BY _Order DESC");
            Query_Order.exec(tempSQL);
            if(Query_Order.next()) QueryVar.bindValue(":_Order",Query_Order.value("_Order").toInt()+1);
            else  QueryVar.bindValue(":_Order",1);
            QueryVar.bindValue(":FunctionDefineName",NewUnitType);
            QueryVar.bindValue(":FunctionDefineCode","");
            QueryVar.bindValue(":DefaultSymbol","");
            QueryVar.exec();
            this->FunctionDefineClass_ID=QString::number(MaxFunctionDefineClass_ID);
            LoadFunctionDefineClass();
            SetCurrentIndex(this->FunctionDefineClass_ID);
        }
        else return;       
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="1")//新建子功能类
    {
        QDialog *dialogUnitTypeEdit =new QDialog();
        dialogUnitTypeEdit->setWindowTitle("输入子功能名称");
        dialogUnitTypeEdit->setMinimumSize(QSize(300,70));
        QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUnitTypeEdit);

        QVBoxLayout *layout = new QVBoxLayout(nullptr);
        QPushButton *pushbuttonOK = new QPushButton(dialogUnitTypeEdit);
        pushbuttonOK->setText("确认");

        QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
        QLabel *m_label1 = new QLabel(dialogUnitTypeEdit);
        m_label1->setText("子功能名称：");
        QLineEdit *m_LineEdit = new QLineEdit(dialogUnitTypeEdit);
        linelayout1->addWidget(m_label1);
        linelayout1->addWidget(m_LineEdit);

        layout->addLayout(linelayout1);
        layout->addWidget(pushbuttonOK);
        formlayoutNameEdit->addRow(layout);

        QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogUnitTypeEdit,SLOT(accept()));
        if (dialogUnitTypeEdit->exec()==QDialog::Accepted)
        {
            QString NewUnitType=m_LineEdit->text();
            if(NewUnitType=="")
            {
                QMessageBox::warning(nullptr, "提示", "功能名称为空！");
                return;
            }
            int MaxFunctionDefineClass_ID=(ui->treeView->currentIndex().data(Qt::UserRole).toString()+"00").toInt();
            QSqlQuery QueryID = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempQueryID = "SELECT FunctionDefineClass_ID FROM FunctionDefineClass WHERE Level = 2 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
            QueryID.exec(tempQueryID);
            while(QueryID.next())
            {
                if(QueryID.value(0).toInt()>=MaxFunctionDefineClass_ID) MaxFunctionDefineClass_ID=QueryID.value(0).toInt()+1;
            }
            //更新T_ProjectDatabase数据库的Equipment表
            QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempSQL = "INSERT INTO FunctionDefineClass (FunctionDefineClass_ID,ParentNo,Level,Desc,_Order,FunctionDefineName,FunctionDefineCode,DefaultSymbol)"
                              "VALUES (:FunctionDefineClass_ID,:ParentNo,:Level,:Desc,:_Order,:FunctionDefineName,:FunctionDefineCode,:DefaultSymbol)";
            QueryVar.prepare(tempSQL);
            QueryVar.bindValue(":FunctionDefineClass_ID",QString::number(MaxFunctionDefineClass_ID));
            QueryVar.bindValue(":ParentNo",ui->treeView->currentIndex().data(Qt::UserRole).toString());
            QueryVar.bindValue(":Level",2);
            QueryVar.bindValue(":Desc","");
            QSqlQuery Query_Order = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            tempSQL = QString("SELECT * FROM FunctionDefineClass WHERE Level = 2 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"' ORDER BY _Order DESC");
            Query_Order.exec(tempSQL);
            if(Query_Order.next()) QueryVar.bindValue(":_Order",Query_Order.value("_Order").toInt()+1);
            else  QueryVar.bindValue(":_Order",1);
            QueryVar.bindValue(":FunctionDefineName",NewUnitType);
            //自动生成功能码
            int MaxCode=1;
            QSqlQuery QueryFunctionDefineCode = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM FunctionDefineClass WHERE Level = 2";
            QueryFunctionDefineCode.exec(SqlStr);
            while(QueryFunctionDefineCode.next())
            {
               QString FunctionDefineCode=QueryFunctionDefineCode.value("FunctionDefineCode").toString();
               if(FunctionDefineCode.toInt()>=MaxCode)
                   MaxCode=FunctionDefineCode.toInt()+1;
            }
            QueryVar.bindValue(":FunctionDefineCode",QString::number(MaxCode));

            QueryVar.bindValue(":DefaultSymbol","");
            QueryVar.exec();
            this->FunctionDefineClass_ID=QString::number(MaxFunctionDefineClass_ID);
            LoadFunctionDefineClass();
            SetCurrentIndex(this->FunctionDefineClass_ID);
        }
        else return;
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="2")//新建子功能类
    {
        QDialog *dialogUnitTypeEdit =new QDialog();
        dialogUnitTypeEdit->setWindowTitle("输入子功能名称");
        dialogUnitTypeEdit->setMinimumSize(QSize(300,70));
        QFormLayout *formlayoutNameEdit = new QFormLayout(dialogUnitTypeEdit);

        QVBoxLayout *layout = new QVBoxLayout(nullptr);
        QPushButton *pushbuttonOK = new QPushButton(dialogUnitTypeEdit);
        pushbuttonOK->setText("确认");

        QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
        QLabel *m_label1 = new QLabel(dialogUnitTypeEdit);
        m_label1->setText("子功能名称：");
        QLineEdit *m_LineEdit = new QLineEdit(dialogUnitTypeEdit);
        linelayout1->addWidget(m_label1);
        linelayout1->addWidget(m_LineEdit);

        layout->addLayout(linelayout1);
        layout->addWidget(pushbuttonOK);
        formlayoutNameEdit->addRow(layout);

        QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogUnitTypeEdit,SLOT(accept()));
        if (dialogUnitTypeEdit->exec()==QDialog::Accepted)
        {
            QString NewUnitType=m_LineEdit->text();
            if(NewUnitType=="")
            {
                QMessageBox::warning(nullptr, "提示", "功能名称为空！");
                return;
            }
            int MaxFunctionDefineClass_ID=(ui->treeView->currentIndex().data(Qt::UserRole).toString()+"00").toInt();
            QSqlQuery QueryID = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempQueryID = "SELECT FunctionDefineClass_ID FROM FunctionDefineClass WHERE Level = 3 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
            QueryID.exec(tempQueryID);
            while(QueryID.next())
            {
                if(QueryID.value(0).toInt()>=MaxFunctionDefineClass_ID) MaxFunctionDefineClass_ID=QueryID.value(0).toInt()+1;
            }
            QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString tempSQL = "INSERT INTO FunctionDefineClass (FunctionDefineClass_ID,ParentNo,Level,Desc,_Order,FunctionDefineName,FunctionDefineCode,DefaultSymbol)"
                              "VALUES (:FunctionDefineClass_ID,:ParentNo,:Level,:Desc,:_Order,:FunctionDefineName,:FunctionDefineCode,:DefaultSymbol)";
            QueryVar.prepare(tempSQL);
            QueryVar.bindValue(":FunctionDefineClass_ID",QString::number(MaxFunctionDefineClass_ID));
            QueryVar.bindValue(":ParentNo",ui->treeView->currentIndex().data(Qt::UserRole).toString());
            QueryVar.bindValue(":Level",3);
            QueryVar.bindValue(":Desc","");
            QSqlQuery Query_Order = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            tempSQL = QString("SELECT * FROM FunctionDefineClass WHERE Level = 3 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"' ORDER BY _Order DESC");
            Query_Order.exec(tempSQL);
            if(Query_Order.next()) QueryVar.bindValue(":_Order",Query_Order.value("_Order").toInt()+1);
            else  QueryVar.bindValue(":_Order",1);
            QueryVar.bindValue(":FunctionDefineName",NewUnitType);
            //自动生成功能码
            int MaxCode=1;
            QSqlQuery QueryFunctionDefineCode = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM FunctionDefineClass WHERE Level = 3 AND ParentNo = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
            QueryFunctionDefineCode.exec(SqlStr);
            while(QueryFunctionDefineCode.next())
            {
               QString FunctionDefineCode=QueryFunctionDefineCode.value("FunctionDefineCode").toString();
               if(FunctionDefineCode.mid(FunctionDefineCode.lastIndexOf(".")+1,FunctionDefineCode.count()-FunctionDefineCode.lastIndexOf(".")-1).toInt()>=MaxCode)
                   MaxCode=FunctionDefineCode.mid(FunctionDefineCode.lastIndexOf(".")+1,FunctionDefineCode.count()-FunctionDefineCode.lastIndexOf(".")-1).toInt()+1;
            }
            SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'";
            QueryFunctionDefineCode.exec(SqlStr);
            if(QueryFunctionDefineCode.next()) QueryVar.bindValue(":FunctionDefineCode",QueryFunctionDefineCode.value("FunctionDefineCode").toString()+"."+QString::number(MaxCode));
            else QueryVar.bindValue(":FunctionDefineCode","");

            QueryVar.bindValue(":DefaultSymbol","");
            QueryVar.exec();
            this->FunctionDefineClass_ID=QString::number(MaxFunctionDefineClass_ID);
            LoadFunctionDefineClass();
            SetCurrentIndex(this->FunctionDefineClass_ID);
        }
        else return;
    }
    else if(ui->treeView->currentIndex().data(Qt::WhatsThisRole).toString()=="3")//新建子功能
    {
        DialogNewFunc *dlg = new DialogNewFunc(this);
        dlg->setWindowTitle("新建功能");
        dlg->Mode=0;
        dlg->ParentNo=ui->treeView->currentIndex().data(Qt::UserRole).toString();
        dlg->setModal(true);
        dlg->show();
        dlg->exec();
        if(dlg->Canceled) return;

        this->FunctionDefineClass_ID=dlg->FunctionDefineClass_ID;
        delete dlg;
        LoadFunctionDefineClass();
        SetCurrentIndex(this->FunctionDefineClass_ID);
    }
}
void DialogFuncDefine::SetCurStackedWidgetIndex(int Index)
{
    ui->stackedWidget->setCurrentIndex(Index);
}

void DialogFuncDefine::LoadFunctionDefineClass()
{
    Model->clear();
    QSqlQuery QueryLevel0 = QSqlQuery(T_LibDatabase);//设置数据库选择模型

    QString temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 0 ORDER BY _Order");
    QueryLevel0.exec(temp);
    while(QueryLevel0.next())
    {
        QStandardItem *fatherItem;
        fatherItem= new QStandardItem(QIcon("C:/TBD/data/电气符号.png"),QueryLevel0.value("FunctionDefineName").toString());
        fatherItem->setData(QVariant(QueryLevel0.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
        fatherItem->setData(QVariant("0"),Qt::WhatsThisRole);
        Model->appendRow(fatherItem);
        QSqlQuery QueryLevel1 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 1 AND ParentNo = '"+QueryLevel0.value("FunctionDefineClass_ID").toString()+"' ORDER BY _Order");
        QueryLevel1.exec(temp);
        while(QueryLevel1.next())
        {
            QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号大类.png"),QueryLevel1.value("FunctionDefineName").toString());
            SubFatherItem->setData(QVariant(QueryLevel1.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
            SubFatherItem->setData(QVariant("1"),Qt::WhatsThisRole);
            fatherItem->appendRow(SubFatherItem);
            QSqlQuery QueryLevel2 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
            temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 2 AND ParentNo = '"+QueryLevel1.value("FunctionDefineClass_ID").toString()+"' ORDER BY _Order");
            QueryLevel2.exec(temp);
            while(QueryLevel2.next())
            {
                QStandardItem *SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号小类.png"),QueryLevel2.value("FunctionDefineName").toString());
                SubSubFatherItem->setData(QVariant(QueryLevel2.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                SubSubFatherItem->setData(QVariant("2"),Qt::WhatsThisRole);
                SubFatherItem->appendRow(SubSubFatherItem);
                QSqlQuery QueryLevel3 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 3 AND ParentNo = '"+QueryLevel2.value("FunctionDefineClass_ID").toString()+"' ORDER BY _Order");
                QueryLevel3.exec(temp);
                while(QueryLevel3.next())
                {
                    QStandardItem *SubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/符号规格.png"),QueryLevel3.value("FunctionDefineName").toString());
                    SubSubSubFatherItem->setData(QVariant(QueryLevel3.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                    SubSubSubFatherItem->setData(QVariant("3"),Qt::WhatsThisRole);
                    SubSubFatherItem->appendRow(SubSubSubFatherItem);
                    QSqlQuery QueryLevel4 = QSqlQuery(T_LibDatabase);//设置数据库选择模型
                    temp = QString("SELECT * FROM FunctionDefineClass WHERE Level = 4 AND ParentNo = '"+QueryLevel3.value("FunctionDefineClass_ID").toString()+"' ORDER BY _Order");
                    QueryLevel4.exec(temp);
                    while(QueryLevel4.next())
                    {
                        QStandardItem *SubSubSubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/功能定义节点图标.png"),QueryLevel4.value("FunctionDefineName").toString());
                        SubSubSubSubFatherItem->setData(QVariant(QueryLevel4.value("FunctionDefineClass_ID").toString()),Qt::UserRole);
                        SubSubSubSubFatherItem->setData(QVariant("4"),Qt::WhatsThisRole);
                        SubSubSubFatherItem->appendRow(SubSubSubSubFatherItem);
                    }//while(QueryLevel4.next())
                }//while(QueryLevel3.next())
            }//while(QueryLevel2.next())
        }//while(QueryLevel1.next())
    }//while(QueryLevel0.next())
}

void DialogFuncDefine::SetVirtualPort(QString FuncType,QString FunctionDefineName)
{
    this->FuncType=FuncType;
    this->FunctionDefineName=FunctionDefineName;
    ui->RbVirtualPort->setChecked(true);
    ui->EdFuncName->setText(FunctionDefineName);
    ui->CbFuncType->setCurrentText(FuncType);
}

void DialogFuncDefine::SetCurrentIndex(QString FunctionDefineClass_ID)//如1302.1.1
{
    for(int i=0;i<Model->rowCount();i++)//电气工程
    {
        if(Model->item(i,0)->data(Qt::UserRole).toString()==FunctionDefineClass_ID)
        {
            ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)));
            ui->treeView->expand(Model->indexFromItem(Model->item(i,0)));
            return;
        }
        for(int j=0;j<Model->item(i,0)->rowCount();j++)//功能大类
        {
            if(Model->item(i,0)->child(j,0)->data(Qt::UserRole).toString()==FunctionDefineClass_ID)
            {
                ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)));
                ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)));
                return;
            }
            for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)//功能小类
            {
                if(Model->item(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toString()==FunctionDefineClass_ID)
                {
                    ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)));
                    ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)));
                    return;
                }
                for(int m=0;m<Model->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                   if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString()==FunctionDefineClass_ID)
                   {
                        ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                        ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                        return;
                   }
                   for(int n=0;n<Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->rowCount();n++)
                   {
                       if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)->data(Qt::UserRole).toString()==FunctionDefineClass_ID)
                       {
                           //Index=Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0));
                           ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)));
                           ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                           on_treeView_clicked(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)));
                           return;
                       }
                   }
                }
            }
        }
    }
}

void DialogFuncDefine::SetCurrentIndexByFunctionDefineName(QString DefaultFunctionDefineName)
{
qDebug()<<"SetCurrentIndex="<<DefaultFunctionDefineName;
    for(int i=0;i<Model->rowCount();i++)//电气工程
    {
        for(int j=0;j<Model->item(i,0)->rowCount();j++)//功能大类
            for(int k=0;k<Model->item(i,0)->child(j,0)->rowCount();k++)//功能小类
            {
                for(int m=0;m<Model->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                   for(int n=0;n<Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->rowCount();n++)
                   {
                       if(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)->data(Qt::DisplayRole).toString()==DefaultFunctionDefineName)
                       {
                           ui->treeView->setCurrentIndex(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)->child(n,0)));
                           ui->treeView->expand(Model->indexFromItem(Model->item(i,0)->child(j,0)->child(k,0)->child(m,0)));
                           return;
                       }
                   }
                }
            }
    }
}

void DialogFuncDefine::on_BtnOk_clicked()
{
    if(ui->RbVirtualPort->isChecked())
    {
        Canceled=false;
        FunctionDefineName=ui->EdFuncName->text();
        FuncType=ui->CbFuncType->currentText();
        close();
        return;
    }

    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'");
    QueryVar.exec(temp);
    if(QueryVar.next())
    {
        Canceled=false;
        FunctionDefineName=QueryVar.value("FunctionDefineName").toString();
        FunctionDefineCode=QueryVar.value("FunctionDefineCode").toString();
        FunctionDefineClass_ID=QueryVar.value("FunctionDefineClass_ID").toString();
        FuncType=ui->CbFuncType->currentText();
        if(ui->treeView->currentIndex().parent().parent().isValid())
           FunctionType=ui->treeView->currentIndex().parent().parent().data(Qt::DisplayRole).toString();
        close();
    }
    else
    {
        Canceled=true;
        close();
    }

}

void DialogFuncDefine::on_treeView_clicked(const QModelIndex &index)
{
qDebug()<<"ValidLevel="<<ValidLevel<<",WhatsThisRole="<<index.data(Qt::WhatsThisRole).toString();

    if(index.data(Qt::WhatsThisRole).toString()==QString::number(ValidLevel)) ui->BtnOk->setEnabled(true);
    else ui->BtnOk->setEnabled(false);

    if(index.data(Qt::WhatsThisRole).toString()=="4")
    {
        qDebug()<<"data(Qt::UserRole)"<<ui->treeView->currentIndex().data(Qt::UserRole).toString();

        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString temp = QString("SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'");
        QueryVar.exec(temp);
        if(QueryVar.next())
        {
            qDebug()<<"DefaultSymbol:"<<QueryVar.value("DefaultSymbol").toString();
            if(QueryVar.value("DefaultSymbol").toString().contains("SPS_M_")) ui->RbMultiTerm->setChecked(true);
            else ui->RbSingleTerm->setChecked(true);//单端 RadioButton
            ui->EdFuncName->setText(QueryVar.value("FunctionDefineName").toString());//功能名称
            ui->EbLibFileName->setText(QueryVar.value("DefaultSymbol").toString());//库文件名
            if(QueryVar.value("DefaultSymbol").toString()!="")
            {
                QString FilePath="C:/TBD/SPS/"+QueryVar.value("DefaultSymbol").toString()+".dwg";
                QPixmap p=QPixmap(FilePath);
                QFileInfo file(FilePath);
                QString JpgName=file.fileName();
                JpgName.replace("dwg","jpg");
                UnitSymbolsView(FilePath,"C:/TBD/data/TempImage/"+JpgName,ui->LbSPSPic,true);
                ui->EdSPSName->setText(FilePath);//默认符号
            }
            else ui->EdSPSName->setText("");//默认符号
            ui->CbFuncType->setCurrentText(QueryVar.value("FuncType").toString());//功能类型
            ui->EdTClassName->setText(QueryVar.value("TClassName").toString());//T类型名
        }
    }
    else
    {
        ui->EdFuncName->setText("");
        ui->EbLibFileName->setText("");
        QPixmap p=QPixmap("");
        ui->LbSPSPic->setPixmap(p);
        ui->EdSPSName->setText("");

        QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
        QString temp = QString("SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+ui->treeView->currentIndex().data(Qt::UserRole).toString()+"'");
        QueryVar.exec(temp);
        if(QueryVar.next())
        {
           ui->EdTClassName->setText(QueryVar.value("TClassName").toString());
        }
    }
}

void DialogFuncDefine::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogFuncDefine::on_BtnOk_Manage_clicked()
{
    this->close();
}

void DialogFuncDefine::on_RbVirtualPort_clicked()
{
    ui->BtnOk->setEnabled(true);
    ui->EbLibFileName->setText("");
    ui->EdSPSName->setText("");
    QPixmap p=QPixmap("");
    ui->LbSPSPic->setPixmap(p);
}
