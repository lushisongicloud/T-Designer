#include "mainwindow.h"
#include "ui_mainwindow.h"
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

namespace {
QStandardItem *findChildItem(QStandardItem *parent, const QString &roleTag, const QString &label)
{
    if (!parent) return nullptr;
    for (int row = 0; row < parent->rowCount(); ++row) {
        QStandardItem *child = parent->child(row, 0);
        if (!child) continue;
        if (child->data(Qt::WhatsThisRole).toString() == roleTag &&
            child->data(Qt::DisplayRole).toString() == label)
            return child;
    }
    return nullptr;
}

QStandardItem *ensurePageHierarchyItem(QStandardItem *root,
                                       const QString &gaoceng,
                                       const QString &pos,
                                       const QString &pageCode,
                                       int projectStructureId)
{
    if (!root) return nullptr;

    QStandardItem *gaocengParent = root;
    if (!gaoceng.isEmpty()) {
        QStandardItem *gaocengItem = findChildItem(root, QString("高层"), gaoceng);
        if (!gaocengItem) {
            gaocengItem = new QStandardItem(QIcon("C:/TBD/data/高层图标.png"), gaoceng);
            gaocengItem->setData(QString("高层"), Qt::WhatsThisRole);
            root->appendRow(gaocengItem);
        }
        gaocengParent = gaocengItem;
    }

    QStandardItem *posParent = gaocengParent;
    if (!pos.isEmpty()) {
        QStandardItem *posItem = findChildItem(gaocengParent, QString("位置"), pos);
        if (!posItem) {
            posItem = new QStandardItem(QIcon("C:/TBD/data/位置图标.png"), pos);
            posItem->setData(QString("位置"), Qt::WhatsThisRole);
            gaocengParent->appendRow(posItem);
        }
        posParent = posItem;
    }

    if (pageCode.isEmpty()) {
        return posParent;
    }

    // QString listLabel = pageCode;
    // if (listLabel.isEmpty())
    //     listLabel = QString("未分组");

    QStandardItem *listItem = findChildItem(posParent, QString("分组"), pageCode);
    if (!listItem) {
        listItem = new QStandardItem(QIcon("C:/TBD/data/列表图标.png"), pageCode);
        listItem->setData(QString("分组"), Qt::WhatsThisRole);
        if (projectStructureId > 0)
            listItem->setData(projectStructureId, Qt::UserRole);
        posParent->appendRow(listItem);
    } else if (projectStructureId > 0 && listItem->data(Qt::UserRole).toInt() == 0) {
        listItem->setData(projectStructureId, Qt::UserRole);
    }
    return listItem;
}
} // namespace

void MainWindow::ShowtreeViewPagePopMenu(const QPoint &pos)
{
    if(!ui->treeViewPages->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="项目")
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actProjectAttr("项目属性", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>1) actProjectAttr.setEnabled(false);
        tree_menu.addAction(&actProjectAttr);
        connect(&actProjectAttr,SIGNAL(triggered()),this,SLOT(ProjectAttr()));
        QAction actAddExistPage("添加现有图纸", this);
        tree_menu.addAction(&actAddExistPage);
        connect(&actAddExistPage,SIGNAL(triggered()),this,SLOT(AddExistPage()));
        tree_menu.exec(QCursor::pos());
    }
    else if((ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="高层")||(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="位置"))
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actRename("重命名", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>1) actRename.setEnabled(false);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actDelDwgPage("删除", this);
        tree_menu.addAction(&actDelDwgPage);
        connect(&actDelDwgPage,SIGNAL(triggered()),this,SLOT(actSlotDelete()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="图纸")
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actDwgPageAttr("页属性", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>1) actDwgPageAttr.setEnabled(false);
        tree_menu.addAction(&actDwgPageAttr);
        connect(&actDwgPageAttr,SIGNAL(triggered()),this,SLOT(DwgPageAttr()));
        QAction actDelDwgPage("删除", this);
        tree_menu.addAction(&actDelDwgPage);
        connect(&actDelDwgPage,SIGNAL(triggered()),this,SLOT(actSlotDelete()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="分组")
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actLBRename("重命名", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>1) actLBRename.setEnabled(false);
        tree_menu.addAction(&actLBRename);
        connect(&actLBRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actDelLB("删除", this);
        tree_menu.addAction(&actDelLB);
        connect(&actDelLB,SIGNAL(triggered()),this,SLOT(actSlotDelete()));
        tree_menu.exec(QCursor::pos());
    }
}
void MainWindow::Rename()
{
    if(!ui->treeViewPages->currentIndex().isValid()) return;
    QDialog *dialogNameEdit =new QDialog();
    dialogNameEdit->setWindowTitle("重命名");
    dialogNameEdit->setMinimumSize(QSize(300,60));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNameEdit);
    QLineEdit *m_LineEdit = new QLineEdit(dialogNameEdit);
    m_LineEdit->setText(ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString());
    QHBoxLayout *layoutBtn = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNameEdit);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogNameEdit);
    pushbuttonCancel->setText("取消");
    layoutBtn->addWidget(pushbuttonOK);
    layoutBtn->addWidget(pushbuttonCancel);
    formlayoutNameEdit->addRow(m_LineEdit);
    formlayoutNameEdit->addRow(layoutBtn);
    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNameEdit,SLOT(accept()));

    if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        if (dialogNameEdit->exec()==QDialog::Accepted)
        {
            QSqlQuery query(T_ProjectDatabase);
            QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE Structure_ID= '3' AND Structure_INT= '"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString()+"'");
            query.prepare(tempSQL);
            query.bindValue(":Structure_INT",m_LineEdit->text());
            query.exec();
        }
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        if (dialogNameEdit->exec()==QDialog::Accepted)
        {
            if(ui->treeViewPages->currentIndex().parent().data(Qt::WhatsThisRole).toString()=="高层")
            {
                QSqlQuery query(T_ProjectDatabase);
                QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString()+"'");
                query.exec(sqlstr);
                while(query.next())
                {
                    QSqlQuery query2(T_ProjectDatabase);
                    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+query.value("Parent_ID").toString());
                    query2.exec(sqlstr);
                    if(!query2.next()) continue;
                    if(query2.value("Structure_INT").toString()==ui->treeViewPages->currentIndex().parent().data(Qt::DisplayRole).toString())
                    {
                        QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE ProjectStructure_ID = "+query.value("ProjectStructure_ID").toString());
                        query.prepare(tempSQL);
                        query.bindValue(":Structure_INT",m_LineEdit->text());
                        query.exec();
                        break;
                    }
                }
            }
            else
            {
                QSqlQuery query(T_ProjectDatabase);
                QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE Structure_ID = '5' AND Structure_INT = '"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString()+"'");
                query.prepare(tempSQL);
                query.bindValue(":Structure_INT",m_LineEdit->text());
                query.exec();
            }
        }
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="分组")
    {
        if (dialogNameEdit->exec()==QDialog::Accepted)
        {
            QSqlQuery query(T_ProjectDatabase);
            QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE ProjectStructure_ID = "+QString::number(ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt()));
            query.prepare(tempSQL);
            query.bindValue(":Structure_INT",m_LineEdit->text());
            query.exec();
        }
    }
    LoadProjectPages();
}
void MainWindow::actSlotDelete()
{
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewPages->selectionModel()->selectedIndexes().count();i++)
    {
        if(!ui->treeViewPages->selectionModel()->selectedIndexes().at(i).isValid()) continue;
        if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="图纸")
        {
            int Page_ID=ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
            SelectPage_ID=0;
            //删除对应的文件
            QString dwgfilename=GetPageNameByPageID(Page_ID);
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            //查看是否已经打开改图纸
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                }
            }
            QFile dwgfile(dwgfilepath);
            dwgfile.remove();

            // 获取该图纸所属的ProjectStructure_ID,用于后续清理空节点
            int pageStructureId = 0;
            QSqlQuery queryStructureId(T_ProjectDatabase);
            queryStructureId.prepare("SELECT ProjectStructure_ID FROM Page WHERE Page_ID = :pid");
            queryStructureId.bindValue(":pid", Page_ID);
            if (queryStructureId.exec() && queryStructureId.next()) {
                pageStructureId = queryStructureId.value("ProjectStructure_ID").toInt();
            }
            
            QSqlQuery query=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM Page WHERE Page_ID="+QString::number(Page_ID));
            query.exec(temp);
            //同时更新图纸下所有的子块、端子、Connect、Wire、Link、Cable信息
            temp =  "DELETE FROM Connector WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            temp =  "DELETE FROM Link WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            temp =  "DELETE FROM Wires WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);

            temp="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            while(query.next())
            {
                QSqlQuery queryUpdate=QSqlQuery(T_ProjectDatabase);
                temp="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID = "+query.value("Symbol_ID").toString();
                queryUpdate.prepare(temp);
                queryUpdate.bindValue(":Page_ID","");
                queryUpdate.bindValue(":Symbol_Handle","");
                queryUpdate.bindValue(":InsertionPoint","");
                queryUpdate.exec();
                temp="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate WHERE Symbol_ID = '"+query.value("Symbol_ID").toString()+"'";
                queryUpdate.prepare(temp);
                queryUpdate.bindValue(":Conn_Coordinate","");
                queryUpdate.exec();
            }
            temp="DELETE FROM TerminalInstance WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            
            // 删除图纸后,清理空的结构节点
            if (pageStructureId > 0) {
                RemoveEmptyStructureNodes(pageStructureId);
            }
        }
        else if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="分组")
        {
            QSqlQuery query=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM Page WHERE ProjectStructure_ID='"+QString::number(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt())+"'");
            query.exec(temp);
            temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt()));
            query.exec(temp);
        }
        else if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="位置")
        {
            QSqlQuery query(T_ProjectDatabase);
            if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).parent().data(Qt::WhatsThisRole).toString()=="高层")
            {
                QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::DisplayRole).toString()+"'");
                query.exec(sqlstr);
                while(query.next())
                {
                    QSqlQuery queryGaoceng(T_ProjectDatabase);
                    sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3' AND ProjectStructure_ID = "+query.value("Parent_ID").toString());
                    queryGaoceng.exec(sqlstr);
                    if(!queryGaoceng.next()) continue;
                    if(queryGaoceng.value("Structure_INT").toString()==ui->treeViewPages->selectionModel()->selectedIndexes().at(i).parent().data(Qt::DisplayRole).toString())
                    {
                        int ProjectStructure_ID=ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
                        QSqlQuery querydel(T_ProjectDatabase);
                        QString temp =  QString("DELETE FROM Page WHERE ProjectStructure_ID='"+QString::number(ProjectStructure_ID)+"'");
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(ProjectStructure_ID));//page
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(query.value("ProjectStructure_ID").toInt()));//位置
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryGaoceng.value("ProjectStructure_ID").toInt()));//高层
                        querydel.exec(temp);
                    }
                }
            }

        }
        else if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="高层")
        {
            QSqlQuery queryGaoceng(T_ProjectDatabase);
            QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3' AND Structure_INT = '"+ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::DisplayRole).toString()+"'");
            queryGaoceng.exec(sqlstr);
            while(queryGaoceng.next())
            {
                QSqlQuery queryPos(T_ProjectDatabase);
                sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Parent_ID = '"+queryGaoceng.value("ProjectStructure_ID").toString()+"'");
                queryPos.exec(sqlstr);
                while(queryPos.next())
                {
                    QSqlQuery queryPage(T_ProjectDatabase);
                    sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6' AND Parent_ID = '"+queryPos.value("ProjectStructure_ID").toString()+"'");
                    queryPage.exec(sqlstr);
                    while(queryPage.next())
                    {
                        QSqlQuery querydel(T_ProjectDatabase);
                        QString temp =  QString("DELETE FROM Page WHERE ProjectStructure_ID='"+QString::number(queryPage.value("ProjectStructure_ID").toInt())+"'");
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryPage.value("ProjectStructure_ID").toInt()));//page
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryPos.value("ProjectStructure_ID").toInt()));//位置
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryGaoceng.value("ProjectStructure_ID").toInt()));//高层
                        querydel.exec(temp);
                    }
                }
            }
        }
    }
    LoadProjectPages();
}
void MainWindow::DwgPageAttr()
{
    if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()!="图纸") return;
    DialogPageAttr *dlg=new DialogPageAttr(this);
    dlg->Mode=2;//modify page


    dlg->Page_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
    QString OriginalPageName=GetPageNameByPageID(dlg->Page_ID);
    dlg->LoadPageInfo();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        SelectPage_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        //更新treeview
        LoadProjectPages();
        if(OriginalPageName!=dlg->PageInitName)//重命名dwg文件
        {
            //查看是否已经打开改图纸，如打开则先关闭
            QString dwgfilename=OriginalPageName;
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            bool DwgOpened=false;
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    DwgOpened=true;
                    break;
                }
            }
            QFile File(dwgfilepath);
            File.rename(CurProjectPath+"/"+dlg->PageInitName+".dwg");
            if(DwgOpened) OpenDwgPageByPageID(dlg->Page_ID);//打开对应的图纸
        }
    }
    delete dlg;
}
QString MainWindow::CreateUnusedFileName(QString CurSelectPageName,QString ProjectStructure_ID)
{
    //在当前选中文件名的基础上加1，如果该文件存在，则新文件名为数字.a,.b,以此类推
    QString NumStr="";
    CurSelectPageName=CurSelectPageName.split(" ").at(0);
    for(int i=0;i<CurSelectPageName.count();i++)
    {
        if((CurSelectPageName.at(i)>='0')&&(CurSelectPageName.at(i)<='9')) NumStr+=CurSelectPageName.at(i);
    }
    int NewStr;
    if(NumStr!="")  NewStr=NumStr.toInt()+1;
    else
    {
        NewStr=1;
    }
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Page WHERE ProjectStructure_ID = '"+ProjectStructure_ID+"'");
    QueryVar.exec(temp);
    bool Existed=false;
    while(QueryVar.next())
    {qDebug()<<"get value PageName";
        if(QueryVar.value("PageName").toString()==QString::number(NewStr))
        {
            Existed=true;
            break;
        }
    }
    if(Existed)
    {
        QueryVar.first();
        QueryVar.previous();
        Existed=false;
        while(QueryVar.next())
        {
            if(QueryVar.value("PageName").toString()==(QString::number(NewStr)+".a"))
            {
                Existed=true;break;
            }
        }
        if(!Existed) return  QString::number(NewStr)+".a";
        else
        {
            QueryVar.first();
            QueryVar.previous();
            Existed=false;
            while(QueryVar.next())
            {
                if(QueryVar.value("PageName").toString()==(QString::number(NewStr)+".b"))
                {
                    Existed=true;break;
                }
            }
            if(!Existed) return  QString::number(NewStr)+".b";
            else
            {
                QueryVar.first();
                QueryVar.previous();
                Existed=false;
                while(QueryVar.next())
                {
                    if(QueryVar.value("PageName").toString()==(QString::number(NewStr)+".c"))
                    {
                        Existed=true;break;
                    }
                }
                if(!Existed) return  QString::number(NewStr)+".c";
            }
        }
    }
    else
    {
        return  QString::number(NewStr);
    }
    return CurSelectPageName+".abc";
}

void MainWindow::AddExistPage()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("添加现有文件"));
    fileDialog.setDirectory(LocalProjectDefaultPath);
    fileDialog.setNameFilter(tr("dwg(*.dwg)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    QFileInfo SelectedFileInfo(fileNames.at(0));

    QString fileStem = SelectedFileInfo.completeBaseName();
    QString baseName = ExtractPageBaseName(fileStem);
    if (baseName.isEmpty())
        baseName = fileStem;
    QString prefix = GetCurIndexProTag(1);
    if (prefix.isEmpty())
        prefix = ExtractPagePrefix(fileStem);
    QString PageName = BuildCanonicalPageName(prefix, baseName, baseName);
    DialogPageAttr *dlg=new DialogPageAttr(this);
    dlg->Mode=1;//add page
    //根据节点确定dwg文件初始名称
    dlg->PageInitName=PageName;
    dlg->SetPageName();
    dlg->LoadPageInfo();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        QFile::copy(fileNames.at(0),CurProjectPath+"/"+dlg->PageInitName+".dwg");
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this,CurProjectPath+"/"+dlg->PageInitName+".dwg",dlg->Page_ID);
        formMxdraw->setWindowTitle(dlg->PageInitName);
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        //formMxdraw->InsertNodes();
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
        connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
        connect(formMxdraw,SIGNAL(SigalShowSpurAttr(int)),this,SLOT(ShowSpurAttr(int)));
        connect(formMxdraw,SIGNAL(SigalShowTerminalAttr(int,int)),this,SLOT(ShowTerminalAttr(int,int)));
        connect(formMxdraw,SIGNAL(UpdateCounterLink(int,QString)),this,SLOT(updateCounterLink(int,QString)));
        connect(formMxdraw,SIGNAL(SignalUpdateSpur(int)),this,SLOT(UpdateSpurBySymbol_ID(int)));
        connect(formMxdraw,SIGNAL(SignalUpdateTerminal(int)),this,SLOT(UpdateTerminalByTerminal_ID(int)));
        connect(formMxdraw,SIGNAL(ConnectLinesChanged(int)),this,SLOT(handleConnectLinesChanged(int)));
        connect(formMxdraw,SIGNAL(SignalUpdateDwgBlkTagByPage_ID(int,QString,QString,QString)),this,SLOT(UpdateDwgBlkTagByPage_ID(int,QString,QString,QString)));
        SelectPage_ID=dlg->Page_ID;
        //更新treeview
        LoadProjectPages();
    }
    delete dlg;
}

//Mode=0:Add new  Mode=1:Add exist
QString MainWindow::GetCurIndexProTag(int Mode)
{
    qDebug()<<"GetCurIndexProTag,Mode="<<Mode;
    QString ProTag="";
    QString nodeType = ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString();
    
    if(nodeType == "图纸")
    {
        //如果选择的节点是图纸，则查看节点data中的Page_ID，检索数据库得到对应的page名称和ProjectStructure_ID，根据ProjectStructure_ID在ProjectStructure中检索对应的高层和位置信息
        int Page_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString temp = QString("SELECT * FROM Page WHERE Page_ID = "+QString::number(Page_ID));
        QueryVar.exec(temp);
        if(!QueryVar.next()) return "";
        QString ProjectStructure_ID=QueryVar.value("ProjectStructure_ID").toString();
        QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+ProjectStructure_ID);
        QueryPage.exec(temp);
        if(!QueryPage.next()) return "";

        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString());
        QueryPos.exec(temp);
        if(!QueryPos.next()) return "";
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) return "";
        if(QueryGaoceng.value("Structure_INT").toString()!="") ProTag+="="+QueryGaoceng.value("Structure_INT").toString();
        if(QueryPos.value("Structure_INT").toString()!="") ProTag+="+"+QueryPos.value("Structure_INT").toString();
        if(Mode==0)
        {
            if(QueryPage.value("Structure_INT").toString()!="") ProTag+="&"+QueryPage.value("Structure_INT").toString();
        }
    }
    else if(nodeType == "分组" || nodeType == "位置" || nodeType == "高层")
    {
        // 对于结构节点，查找该节点下的第一张图纸
        int structureId = ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        int firstPageId = FindFirstPageIDUnderStructure(structureId);
        
        if(firstPageId > 0)
        {
            // 找到第一张图纸，获取其完整结构信息
            QSqlQuery queryPage(T_ProjectDatabase);
            queryPage.prepare("SELECT * FROM Page WHERE Page_ID = :pid");
            queryPage.bindValue(":pid", firstPageId);
            if(queryPage.exec() && queryPage.next())
            {
                QString pageStructureId = queryPage.value("ProjectStructure_ID").toString();
                QSqlQuery QueryPage(T_ProjectDatabase);
                QString temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+pageStructureId);
                QueryPage.exec(temp);
                if(QueryPage.next())
                {
                    QSqlQuery QueryPos(T_ProjectDatabase);
                    temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString());
                    QueryPos.exec(temp);
                    if(QueryPos.next())
                    {
                        QSqlQuery QueryGaoceng(T_ProjectDatabase);
                        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
                        QueryGaoceng.exec(temp);
                        if(QueryGaoceng.next())
                        {
                            if(QueryGaoceng.value("Structure_INT").toString()!="") 
                                ProTag+="="+QueryGaoceng.value("Structure_INT").toString();
                            if(QueryPos.value("Structure_INT").toString()!="") 
                                ProTag+="+"+QueryPos.value("Structure_INT").toString();
                            if(Mode==0 && QueryPage.value("Structure_INT").toString()!="")
                                ProTag+="&"+QueryPage.value("Structure_INT").toString();
                        }
                    }
                }
            }
        }
        else
        {
            // 没有找到图纸，退回到原逻辑（至少获取当前结构信息）
            if(nodeType == "分组")
            {
                QSqlQuery QueryLB = QSqlQuery(T_ProjectDatabase);
                QString temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QString::number(structureId));
                QueryLB.exec(temp);
                if(QueryLB.next())
                {
                    QSqlQuery QueryPos(T_ProjectDatabase);
                    temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryLB.value("Parent_ID").toString());
                    QueryPos.exec(temp);
                    if(QueryPos.next())
                    {
                        QSqlQuery QueryGaoceng(T_ProjectDatabase);
                        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
                        QueryGaoceng.exec(temp);
                        if(QueryGaoceng.next())
                        {
                            if(QueryGaoceng.value("Structure_INT").toString()!="") ProTag+="="+QueryGaoceng.value("Structure_INT").toString();
                            if(QueryPos.value("Structure_INT").toString()!="") ProTag+="+"+QueryPos.value("Structure_INT").toString();
                            if(Mode==0 && QueryLB.value("Structure_INT").toString()!="") ProTag+="&"+QueryLB.value("Structure_INT").toString();
                        }
                    }
                }
            }
            else if(nodeType == "位置")
            {
                if(ui->treeViewPages->currentIndex().parent().data(Qt::WhatsThisRole).toString()=="高层")
                {
                    ProTag+="="+ui->treeViewPages->currentIndex().parent().data(Qt::DisplayRole).toString();
                }
                ProTag+="+"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString();
            }
            else if(nodeType == "高层")
            {
                ProTag+="="+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString();
                if(ModelPages->itemFromIndex(ui->treeViewPages->currentIndex())->rowCount()>0)
                {
                    if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="位置")
                    {
                        ProTag+="+"+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
                    }
                }
            }
        }
    }
    else if(nodeType == "项目")
    {
        // 项目节点：查找第一张图纸
        if(ModelPages->itemFromIndex(ui->treeViewPages->currentIndex())->rowCount()>0)
        {
            // 尝试从第一个子节点获取
            QString childType = ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString();
            if(childType == "高层")
            {
                int structureId = ui->treeViewPages->currentIndex().child(0,0).data(Qt::UserRole).toInt();
                int firstPageId = FindFirstPageIDUnderStructure(structureId);
                if(firstPageId > 0)
                {
                    QSqlQuery queryPage(T_ProjectDatabase);
                    queryPage.prepare("SELECT * FROM Page WHERE Page_ID = :pid");
                    queryPage.bindValue(":pid", firstPageId);
                    if(queryPage.exec() && queryPage.next())
                    {
                        QString pageStructureId = queryPage.value("ProjectStructure_ID").toString();
                        QSqlQuery QueryPage(T_ProjectDatabase);
                        QString temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+pageStructureId);
                        QueryPage.exec(temp);
                        if(QueryPage.next())
                        {
                            QSqlQuery QueryPos(T_ProjectDatabase);
                            temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString());
                            QueryPos.exec(temp);
                            if(QueryPos.next())
                            {
                                QSqlQuery QueryGaoceng(T_ProjectDatabase);
                                temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
                                QueryGaoceng.exec(temp);
                                if(QueryGaoceng.next())
                                {
                                    if(QueryGaoceng.value("Structure_INT").toString()!="") 
                                        ProTag+="="+QueryGaoceng.value("Structure_INT").toString();
                                    if(QueryPos.value("Structure_INT").toString()!="") 
                                        ProTag+="+"+QueryPos.value("Structure_INT").toString();
                                    if(Mode==0 && QueryPage.value("Structure_INT").toString()!="")
                                        ProTag+="&"+QueryPage.value("Structure_INT").toString();
                                }
                            }
                        }
                    }
                }
                else
                {
                    // 退回原逻辑
                    ProTag+="="+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
                    if(ModelPages->itemFromIndex(ui->treeViewPages->currentIndex().child(0,0))->rowCount()>0)
                    {
                        if(ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::WhatsThisRole).toString()=="位置")
                        {
                            ProTag+="+"+ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::DisplayRole).toString();
                        }
                    }
                }
            }
            else if(childType == "位置")
            {
                ProTag+="+"+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
            }
        }
    }
    return ProTag;
}

void MainWindow::NewDwgPage()
{
    //根据选择节点的位置确定新建图纸的名称
    QString PageName="";
    QString ProTag=GetCurIndexProTag(0);
    qDebug()<<"ProTag="<<ProTag;
    QString StrGaoceng,StrPos,StrPage;
    SplitPagePrefix(ProTag,&StrGaoceng,&StrPos,&StrPage);
    
    // 如果有分组描述，转换为Structure_INT
    if(StrPage != "")
    {
        QSqlQuery queryInt = QSqlQuery(T_ProjectDatabase);
        QString sqlstrInt=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6' AND Struct_Desc = '"+StrPage+"'");
        queryInt.exec(sqlstrInt);
        if(queryInt.next()) StrPage = queryInt.value("Structure_INT").toString();
    }
    
    QString ProjectStructure_ID=GetPageProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos,StrPage);
    QString baseCode;
    QString nodeType = ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString();
    
    if(nodeType == "图纸")
    {
        // 选中图纸节点：继承该图纸的页名并递增
        int Page_ID = ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        QSqlQuery queryPage(T_ProjectDatabase);
        queryPage.prepare("SELECT PageName FROM Page WHERE Page_ID = :pid");
        queryPage.bindValue(":pid", Page_ID);
        if(queryPage.exec() && queryPage.next())
        {
            QString currentPageName = queryPage.value("PageName").toString();
            baseCode = IncrementPageBaseName(currentPageName);
        }
        else
        {
            baseCode = "1";
        }
    }
    else
    {
        // 选中结构节点：找该节点下第一张图纸的页名并递增
        int structureId = ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        int firstPageId = FindFirstPageIDUnderStructure(structureId);
        
        if(firstPageId > 0)
        {
            QSqlQuery queryPage(T_ProjectDatabase);
            queryPage.prepare("SELECT PageName FROM Page WHERE Page_ID = :pid");
            queryPage.bindValue(":pid", firstPageId);
            if(queryPage.exec() && queryPage.next())
            {
                QString firstPageName = queryPage.value("PageName").toString();
                baseCode = IncrementPageBaseName(firstPageName);
            }
            else
            {
                baseCode = "1";
            }
        }
        else
        {
            // 该结构下没有图纸，使用默认值
            baseCode = "1";
        }
    }
    
    PageName=BuildCanonicalPageName(ProTag, StrPage, baseCode);

    DialogPageAttr *dlg=new DialogPageAttr(this);
    dlg->Mode=1;//add page

    //根据节点确定dwg文件初始名称
    dlg->PageInitName=PageName;
    dlg->SetPageName();
    dlg->LoadPageInfo();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this,CurProjectPath+"/"+dlg->PageInitName+".dwg",dlg->Page_ID);
        connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
        connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
        formMxdraw->setWindowTitle(dlg->PageInitName);
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        //formMxdraw->InsertNodes();
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
        connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
        connect(formMxdraw,SIGNAL(SigalShowSpurAttr(int)),this,SLOT(ShowSpurAttr(int)));
        connect(formMxdraw,SIGNAL(SigalShowTerminalAttr(int,int)),this,SLOT(ShowTerminalAttr(int,int)));
        connect(formMxdraw,SIGNAL(UpdateCounterLink(int,QString)),this,SLOT(updateCounterLink(int,QString)));
        connect(formMxdraw,SIGNAL(SignalUpdateSpur(int)),this,SLOT(UpdateSpurBySymbol_ID(int)));
        connect(formMxdraw,SIGNAL(SignalUpdateTerminal(int)),this,SLOT(UpdateTerminalByTerminal_ID(int)));
        connect(formMxdraw,SIGNAL(ConnectLinesChanged(int)),this,SLOT(handleConnectLinesChanged(int)));


        SelectPage_ID=dlg->Page_ID;
        //更新treeview
        LoadProjectPages();
    }
    delete dlg;
}

void MainWindow::InitNavigatorTree()
{
    ModelPages = new QStandardItemModel(ui->treeViewPages);
    ui->treeViewPages->header()->setVisible(false);
    ui->treeViewPages->setColumnWidth(0,50);
    ui->treeViewPages->setModel(ModelPages);

    ModelUnits = new QStandardItemModel(ui->treeViewUnits);
    ui->treeViewUnits->header()->setVisible(false);
    ui->treeViewUnits->setColumnWidth(0,50);
    ui->treeViewUnits->setModel(ModelUnits);

    ModelTerminals=new QStandardItemModel(ui->treeViewTerminal);
    ui->treeViewTerminal->header()->setVisible(false);
    ui->treeViewTerminal->setColumnWidth(0,50);
    ui->treeViewTerminal->setModel(ModelTerminals);

    ModelLineDT=new QStandardItemModel(ui->treeViewLineDT);
    ui->treeViewLineDT->header()->setVisible(false);
    ui->treeViewLineDT->setColumnWidth(0,50);
    ui->treeViewLineDT->setModel(ModelLineDT);

    ModelLineByUnits=new QStandardItemModel(ui->treeViewLineByUnit);
    ui->treeViewLineByUnit->header()->setVisible(false);
    ui->treeViewLineByUnit->setColumnWidth(0,50);
    ui->treeViewLineByUnit->setModel(ModelLineByUnits);
}

QString MainWindow::GetTerminalTermStrByTermID(QString TermID)
{
    QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+TermID.mid(0,TermID.indexOf("."));
    QueryTerminalTerm.exec(temp);
    if(QueryTerminalTerm.next())
    {
        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = "SELECT * FROM Terminal WHERE Terminal_ID = "+QueryTerminalTerm.value("Terminal_ID").toString();
        QueryTerminal.exec(temp);
        if(QueryTerminal.next())
        {
            QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            temp = "SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+QueryTerminal.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(temp);
            if(QueryTerminalStrip.next())
            {
                return QueryTerminalStrip.value("DT").toString()+":"+QueryTerminal.value("Designation").toString()+TermID.mid(TermID.indexOf("."),TermID.count()-TermID.indexOf("."));
            }
        }
    }
    return "";
}

QString MainWindow::GetUnitTermStrByTermID(QString TermID)
{
    QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+TermID;
    QuerySymb2TermInfo.exec(temp);
    if(QuerySymb2TermInfo.next())
    {
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySymb2TermInfo.value("Symbol_ID").toString();
        QuerySymbol.exec(temp);
        if(QuerySymbol.next())
        {
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            temp = "SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
            QueryEquipment.exec(temp);
            if(QueryEquipment.next())
            {
                return GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString()+":"+QuerySymb2TermInfo.value("ConnNum").toString();
            }
        }
    }
    return "";
}
void MainWindow::ProduceDBJXB()
{
    //删除原JXB表
    QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
    QString SqlStr =  "DELETE FROM JXB ";
    QueryJXB.exec(SqlStr);
    //在ConnectLine表中检索连线
    QSqlQuery QueryConnectLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM ConnectLine WHERE Page_ID <> '' ORDER BY ConnectionNumber";
    QueryConnectLine.exec(SqlStr);
    while(QueryConnectLine.next())
    {
        QString Symb1_ID=QueryConnectLine.value("Symb1_ID").toString();
        QString Symb2_ID=QueryConnectLine.value("Symb2_ID").toString();
        if((Symb1_ID=="")||(Symb2_ID=="")) continue;
        if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) continue;
        if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) continue;
        //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表
        QString ConnectionNumber=QueryConnectLine.value("ConnectionNumber").toString();
        QString Symb1_Category=QueryConnectLine.value("Symb1_Category").toString();
        QString Symb2_Category=QueryConnectLine.value("Symb2_Category").toString();
        if((Symb1_Category=="1")&&(Symb2_Category=="1"))//同一个端子排的短接片要排除
        {
            QString TerminalStrip_ID1,TerminalStrip_ID2,Terminal_ID1,Terminal_ID2,ShortJumper1,ShortJumper2;
            QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb1_ID;
            QueryTerminalInstance.exec(SqlStr);
            if(QueryTerminalInstance.next())
            {
                TerminalStrip_ID1=QueryTerminalInstance.value("TerminalStrip_ID").toString();
                Terminal_ID1=QueryTerminalInstance.value("Terminal_ID").toString();
                QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+Terminal_ID1;
                QueryTerminal.exec(SqlStr);
                if(QueryTerminal.next()) ShortJumper1=QueryTerminal.value("ShortJumper").toString();
            }
            SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb2_ID;
            QueryTerminalInstance.exec(SqlStr);
            if(QueryTerminalInstance.next())
            {
                TerminalStrip_ID2=QueryTerminalInstance.value("TerminalStrip_ID").toString();
                Terminal_ID2=QueryTerminalInstance.value("Terminal_ID").toString();
                QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+Terminal_ID2;
                QueryTerminal.exec(SqlStr);
                if(QueryTerminal.next()) ShortJumper2=QueryTerminal.value("ShortJumper").toString();
            }
            if((TerminalStrip_ID1==TerminalStrip_ID2)&&(ShortJumper1==ShortJumper2)) continue;//同一个端子排的短接片要排除
        }
        QString ProjectStructure_ID=GetProjectStructureIDByPageID(QueryConnectLine.value("Page_ID").toInt());
        bool CurLineIsUnValid=false;
        if(ConnectionNumber!="")//如果线号不为空则查看列表中是否已存在相同线号的导线，如果存在，则为无效导线
        {
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+ConnectionNumber+"' AND ProjectStructure_ID = '"+ProjectStructure_ID+"'";
            QuerySearch.exec(SqlStr);
            if(QuerySearch.next()) CurLineIsUnValid=true;
        }
        else//线号为空则查看列表中线号为空的连线，如果列表中导线两端连接点对象与当前连线的相同（Symb1_ID和Symb2_ID可互换），则当前导线为无效导线，反之则添加到列表
        {
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '' AND ProjectStructure_ID = '"+ProjectStructure_ID+"'";
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                QString SearchSymb1_ID=QuerySearch.value("Symb1_ID").toString();
                QString SearchSymb2_ID=QuerySearch.value("Symb2_ID").toString();
                QString SearchSymb1_Category=QuerySearch.value("Symb1_Category").toString();
                QString SearchSymb2_Category=QuerySearch.value("Symb2_Category").toString();
                if((SearchSymb1_ID==Symb1_ID)&&(SearchSymb2_ID==Symb2_ID)&&(SearchSymb1_Category==Symb1_Category)&&(SearchSymb2_Category==Symb2_Category))  CurLineIsUnValid=true;
                if((SearchSymb2_ID==Symb1_ID)&&(SearchSymb1_ID==Symb2_ID)&&(SearchSymb2_Category==Symb1_Category)&&(SearchSymb1_Category==Symb2_Category))  CurLineIsUnValid=true;
                if(CurLineIsUnValid) break;
            }
        }
        if(!CurLineIsUnValid)
        {
            SqlStr =  "INSERT INTO JXB (JXB_ID,ProjectStructure_ID,Page_ID,Cable_ID,ConnectionNumber,ConnectionNumber_Handle,Symb1_ID,Symb2_ID,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category,Symb1_Category,Symb2_Category)"
                      "VALUES (:JXB_ID,:ProjectStructure_ID,:Page_ID,:Cable_ID,:ConnectionNumber,:ConnectionNumber_Handle,:Symb1_ID,:Symb2_ID,:Wires_Type,:Wires_Color,:Wires_Diameter,:Wires_Category,:Symb1_Category,:Symb2_Category)";
            QueryJXB.prepare(SqlStr);
            QueryJXB.bindValue(":JXB_ID",GetMaxIDOfDB(T_ProjectDatabase,"JXB","JXB_ID"));
            QueryJXB.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
            QueryJXB.bindValue(":Page_ID",QueryConnectLine.value("Page_ID").toString());
            QueryJXB.bindValue(":Cable_ID",QueryConnectLine.value("Cable_ID").toString());
            QueryJXB.bindValue(":ConnectionNumber",QueryConnectLine.value("ConnectionNumber").toString());
            QueryJXB.bindValue(":ConnectionNumber_Handle",QueryConnectLine.value("ConnectionNumber_Handle").toString());
            QueryJXB.bindValue(":Symb1_ID",QueryConnectLine.value("Symb1_ID").toString());
            QueryJXB.bindValue(":Symb2_ID",QueryConnectLine.value("Symb2_ID").toString());
            QueryJXB.bindValue(":Wires_Type",QueryConnectLine.value("Wires_Type").toString());
            QueryJXB.bindValue(":Wires_Color",QueryConnectLine.value("Wires_Color").toString());
            QueryJXB.bindValue(":Wires_Diameter",QueryConnectLine.value("Wires_Diameter").toString());
            QueryJXB.bindValue(":Wires_Category",QueryConnectLine.value("Wires_Category").toString());
            QueryJXB.bindValue(":Symb1_Category",QueryConnectLine.value("Symb1_Category").toString());
            QueryJXB.bindValue(":Symb2_Category",QueryConnectLine.value("Symb2_Category").toString());
            QueryJXB.exec();
        }
    }
}

void MainWindow::InsertTermToUnitStrip(QStandardItem *Item,QSqlQuery QueryJXBLine,QString Symb_ID,QString Symb_Category,int index)
{
    QString TermStr,StrSql;
    QString ConnectionNumber=QueryJXBLine.value("ConnectionNumber").toString();
    QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category;
    if(index==0) {Symb1_ID=Symb_ID;Symb1_Category=Symb_Category;}
    else {Symb2_ID=Symb_ID;Symb2_Category=Symb_Category;}
    if(Symb_Category=="0")
    {
        QSqlQuery QuerySearchTerm(T_ProjectDatabase);
        StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb_ID;
        QuerySearchTerm.exec(StrSql);
        if(QuerySearchTerm.next()) TermStr=QuerySearchTerm.value("ConnNum").toString();
    }
    else if(Symb_Category=="1")
    {
        QSqlQuery QuerySearchTerm(T_ProjectDatabase);
        StrSql="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+Symb_ID;
        QuerySearchTerm.exec(StrSql);
        if(QuerySearchTerm.next())
        {
            QSqlQuery QuerySearchTerminal(T_ProjectDatabase);
            StrSql="SELECT * FROM Terminal WHERE Terminal_ID= "+QuerySearchTerm.value("Terminal_ID").toString();
            QuerySearchTerminal.exec(StrSql);
            if(QuerySearchTerminal.next())
            {
                TermStr=QuerySearchTerminal.value("Designation").toString();
            }
        }
    }
    TermStr+="("+ConnectionNumber+")<->";
    if(index==0)//查找另一端的器件
    {
        Symb2_ID=QueryJXBLine.value("Symb2_ID").toString();
        Symb2_Category=QueryJXBLine.value("Symb2_Category").toString();
        if(Symb2_Category=="0") TermStr+=GetUnitTermStrByTermID(Symb2_ID);
        else if(Symb2_Category=="1") TermStr+=GetTerminalTermStrByTermID(Symb2_ID);
    }
    else if(index==1)//查找另一端的器件
    {
        Symb1_ID=QueryJXBLine.value("Symb1_ID").toString();
        Symb1_Category=QueryJXBLine.value("Symb1_Category").toString();
        if(Symb1_Category=="0") TermStr+=GetUnitTermStrByTermID(Symb1_ID);
        else if(Symb1_Category=="1") TermStr+=GetTerminalTermStrByTermID(Symb1_ID);
    }
    //判断Symb1_ID、Symb2_ID、Symb1_Category、Symb2_Category是否已存在
    for(int i=0;i<Item->rowCount();i++)
    {
        QStringList ListLineItemData=Item->data(Qt::UserRole).toStringList();
        if(ListLineItemData.count()==5)
        {
            if((ListLineItemData.at(1)==Symb1_ID)&&(ListLineItemData.at(2)==Symb1_Category)&&(ListLineItemData.at(3)==Symb2_ID)&&(ListLineItemData.at(4)==Symb2_Category))
                return;
        }
    }
    QStandardItem *TermItem=new QStandardItem(QIcon("C:/TBD/data/功能子块图标_已插入.png"),TermStr);
    TermItem->setData(QVariant("功能子块"),Qt::WhatsThisRole);

    QStringList ListLineItemData;
    ListLineItemData.clear();
    ListLineItemData.append(QueryJXBLine.value("JXB_ID").toString());
    if(index==0)
    {
        ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
    }
    else if(index==1)
    {
        ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
    }

    TermItem->setData(QVariant(ListLineItemData),Qt::UserRole);
    Item->appendRow(TermItem);
}
/*
QString MainWindow::GetLinkRoadBySymbol(int Symbol_ID)//获取信号链路(针对功能子块)
{
    QString FinalLinkRoad="";
    //获取功能子块下的端口ID提取信号链路
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QuerySymb2TermInfo.exec(StrSql);
    while(QuerySymb2TermInfo.next())
    {
       QList<QStringList> listFinalLinkRoad=GetLinkRoadByUnitStripID(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toInt());
       for(QStringList ListLinkRoad:listFinalLinkRoad)
       {
           FinalLinkRoad+="[";
           for(QString StrLinkRoad:ListLinkRoad)
             FinalLinkRoad+=StrLinkRoad+";";
           FinalLinkRoad.remove(FinalLinkRoad.count()-1,1);
           FinalLinkRoad+="]";
       }
    }
    //存储到数据库中
    QString SqlStr =  "UPDATE Symbol SET LinkRoad=:LinkRoad WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QSqlQuery querySymbol(T_ProjectDatabase);
    querySymbol.prepare(SqlStr);
    querySymbol.bindValue(":LinkRoad",FinalLinkRoad);
    querySymbol.exec();
    return FinalLinkRoad;
}


//KnownLineValidRoadCnt定义：器件ID，器件类型（0：元件，1：端子排，2：导线），子块数
QList<QStringList> MainWindow::GetLinkRoadByUnitStripID(int Symb2TermInfo_ID)//获取端口信号链路
{
    QList<QStringList> listFinalLinkRoad;
    QStringList listLinkRoad={QString::number(GetSymbolIDByTermID(0,Symb2TermInfo_ID))+",0,"+QString::number(GetLinesBySymb2TermInfo_ID(Symb2TermInfo_ID,0,"").count())};
    QStringList KnownLineValidRoadCnt=listLinkRoad;
    QString DT;
    int initSymb2TermInfo_ID=Symb2TermInfo_ID;
    int Category=0;
    while(1)
    {
        bool FindTerm=false;
        bool FindExecConn=false;
        bool FindSourceConn=false;
        int NodeSpurCount=0;
        QString StrLinkRoad="";//ID+类型 类型元件为0 端子排为1 导线为2
        //根据Symb2TermInfo_ID找到下一个端口，可以是连线的另一头，也可以是功能子块的另一头，优先找连线的另一头
        //====找连线的另一头====
        //查找端口对应的元件ID
        int UnitStripID=GetUnitStripIDByTermID(Category,Symb2TermInfo_ID,DT);
        if(ModelLineByUnits->rowCount()>0)
        {
            for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
            {
                for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
                {
                  for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                  {
                      if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toInt()!=0) continue;//必须是元件而不是端子排
                      if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt()!=UnitStripID) continue;
                      QStringList ListLineItemData;
                      //检索元件下的各个引脚连线，并且需要通过功能子块或T语言确定引脚之间的逻辑关系,暂时由功能子块确定引脚之间的逻辑关系
                      for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//元件引脚连线
                      {
                         QStandardItem *TermItem=ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0);
                         ListLineItemData=TermItem->data(Qt::UserRole).toStringList();
                         if(ListLineItemData.count()!=5) continue;
                         if(ListLineItemData.at(1).toInt()!=Symb2TermInfo_ID) continue;
                         //不能往回检索
                         bool LinkRepeated=false;
                         for(int n=0;n<listLinkRoad.count();n++)
                         {
                             if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(ListLineItemData.at(0)+",2")) {LinkRepeated=true;break;}
                         }
                         if(LinkRepeated) continue;

                         //判断是否是错误的路径
                         if(!CheckLinkRoad(ListLineItemData.at(0)+",2",KnownLineValidRoadCnt)) continue;
                         Symb2TermInfo_ID=ListLineItemData.at(3).toInt();
                         Category=ListLineItemData.at(4).toInt();
                         StrLinkRoad=ListLineItemData.at(0)+",2";
                         //如果是源端口则停止搜索
                         if(IsSourceConn(Symb2TermInfo_ID,Category))
                         {
                             FindSourceConn=true;
                             break;
                         }
                         FindTerm=true;
                         break;
                      }//for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//元件引脚连线
                      if(FindTerm||FindSourceConn) break;
                  }//for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                  if(FindTerm||FindSourceConn) break;
                }//for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
                if(FindTerm||FindSourceConn) break;
            }//for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层

        }//if(ModelLineByUnits->rowCount()>0)
        //====找连线的另一头END====
        //====找功能子块另一头=====
        if(!FindTerm)
        {
            QString SymbolID=QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID));
            //不能往回检索
            bool LinkRepeated=false;
            for(int n=0;n<listLinkRoad.count();n++)
            {
                if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(SymbolID+","+QString::number(Category))) {LinkRepeated=true;break;}
            }
            if(!LinkRepeated)
            {
                //查找功能子块另一端的端口之前必须检查功能子块
                if(CheckLinkRoad(SymbolID+","+QString::number(Category),KnownLineValidRoadCnt))
                {
                    if(GetUnitStripOtherSideTerm(Symb2TermInfo_ID,Category)>=0)
                    {
                        StrLinkRoad=QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID))+","+QString::number(Category);
                        if(IsExecConn(Symb2TermInfo_ID,Category)) FindExecConn=true;
                        else FindTerm=true;
                    }
                }
            }
        }
        //====找功能子块另一头END=====
        if(FindTerm||FindSourceConn||FindExecConn)
        {
            //更新KnownLineValidRoadCnt，listLinkRoad和ListNodeSpurCount
            //查看ListLineItemData.at(3)节点有几条子块,优先采用KnownLineValidRoadCnt中的结果
            bool FindedInKnownLineValidRoadCnt=false;
            for(QString StrKnownLine:KnownLineValidRoadCnt)
            {
                if(StrKnownLine.mid(0,StrKnownLine.lastIndexOf(","))==StrLinkRoad)
                {
                    //NodeSpurCount=StrKnownLine.split(",").at(2).toInt();
                    StrLinkRoad=StrKnownLine;
                    FindedInKnownLineValidRoadCnt=true;
                    break;
                }
            }
            if(!FindedInKnownLineValidRoadCnt)
            {
                NodeSpurCount=GetLinesBySymb2TermInfo_ID(Symb2TermInfo_ID,Category,"").count();
                StrLinkRoad+=","+QString::number(NodeSpurCount);
                KnownLineValidRoadCnt.append(StrLinkRoad);
            }
            listLinkRoad.append(StrLinkRoad);
            if(FindSourceConn) listLinkRoad.append(QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID))+","+QString::number(Category)+",0");
        }
        if(FindExecConn||FindSourceConn)
        {
            //当前的链路不是目标链路，因为没有找到源端口或检索到了终端端口，重新搜索
            Symb2TermInfo_ID=initSymb2TermInfo_ID;
            Category=0;
            UpdateKnownLineValidRoadCnt(listLinkRoad,KnownLineValidRoadCnt);
            if(FindSourceConn) listFinalLinkRoad.append(listLinkRoad);
            //else qDebug()<<"错误，找到终端端口";
//qDebug()<<"listLinkRoad="<<listLinkRoad<<",KnownLineValidRoadCnt="<<KnownLineValidRoadCnt;
            listLinkRoad.clear();
            listLinkRoad.append(QString::number(GetSymbolIDByTermID(0,initSymb2TermInfo_ID))+",0,"+QString::number(GetLinesBySymb2TermInfo_ID(initSymb2TermInfo_ID,0,"").count()));
        }
        else if(!FindTerm)
        {
            break;
        }
    }//end of while(1)
    //qDebug()<<"执行器链路检索完成："<<listFinalLinkRoad;
    return listFinalLinkRoad;
}*/



void MainWindow::InsertUnitTerminalToItem(QStandardItem *Item,QSqlQuery QueryJXBLine,int index)
{
    QString Symb_ID;
    if(index==0) Symb_ID=QueryJXBLine.value("Symb1_ID").toString();
    else if(index==1) Symb_ID=QueryJXBLine.value("Symb2_ID").toString();
    if(Symb_ID.contains(":C")||Symb_ID.contains(":G")||Symb_ID.contains(":1")||Symb_ID.contains(":2")||Symb_ID.contains(":3")) return;
    QString Symb_Category;
    if(index==0) Symb_Category=QueryJXBLine.value("Symb1_Category").toString();
    else if(index==1) Symb_Category=QueryJXBLine.value("Symb2_Category").toString();
    //qDebug()<<"ConnectLine_ID="<<QueryConnectLine.value("ConnectLine_ID").toInt();
    //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表

    //找到Symb_ID对应的器件
    QString DT;
    int UnitStripID=GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
    //查看当前的器件是否在列表中已经存在
    bool UnitStripExisted=false;
    for(int i=0;i<Item->rowCount();i++)
    {
        if((Item->child(i,0)->data(Qt::UserRole).toInt()==UnitStripID)&&(Item->child(i,0)->data(Qt::WhatsThisRole).toString()==Symb_Category))//已存在，添加Term到Item->child(i,0)
        {
            UnitStripExisted=true;
            /*
            //查看当前端口在Item->child(i,0)是否存在
            bool TermExisted=false;
            for(int j=0;j<Item->child(i,0)->rowCount();j++)
            {
                QStringList ListData=Item->child(i,0)->child(j,0)->data(Qt::UserRole).toStringList();
                if(ListData.count()==5)
                {
                    if(ListData.at(1)==Symb_ID)
                    {
                        TermExisted=true;
                        break;
                    }
                }
            }*/
            //if(!TermExisted)//添加Term到Item->child(i,0)
            {
                InsertTermToUnitStrip(Item->child(i,0),QueryJXBLine,Symb_ID,Symb_Category,index);
            }
            break;
        }//if(Item->child(i,0)->data(Qt::UserRole).toInt()==UnitStripID)
    }//for(int i=0;i<Item->rowCount();i++)
    if(!UnitStripExisted)//元件不存在，添加元件和端口
    {
        QStandardItem *UnitStripItem=new QStandardItem(QIcon("C:/TBD/data/端子排图标.png"),DT);
        UnitStripItem->setData(QVariant(Symb_Category),Qt::WhatsThisRole);
        UnitStripItem->setData(QVariant(UnitStripID),Qt::UserRole);
        Item->appendRow(UnitStripItem);
        InsertTermToUnitStrip(UnitStripItem,QueryJXBLine,Symb_ID,Symb_Category,index);
    }
}

void MainWindow::InsertLineToItem(QStandardItem *Item,QSqlQuery QueryJXBLine)
{
    QString Symb1_ID=QueryJXBLine.value("Symb1_ID").toString();
    QString Symb2_ID=QueryJXBLine.value("Symb2_ID").toString();
    if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) return;
    if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) return;
    QString Symb1_Category=QueryJXBLine.value("Symb1_Category").toString();
    QString Symb2_Category=QueryJXBLine.value("Symb2_Category").toString();
    //qDebug()<<"ConnectLine_ID="<<QueryConnectLine.value("ConnectLine_ID").toInt();
    //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表
    QString ConnectionNumber=QueryJXBLine.value("ConnectionNumber").toString();
    QStandardItem *ConnectionNumberNodeItem;
    bool AddConnectionNumberNode=true;
    if(ConnectionNumber=="")
    {
        for(int i=0;i<Item->rowCount();i++)
        {
            if(Item->child(i,0)->data(Qt::DisplayRole).toString()=="")
            {
                ConnectionNumberNodeItem=Item->child(i,0);
                AddConnectionNumberNode=false;
                break;
            }
        }
    }
    if(AddConnectionNumberNode)
    {
        ConnectionNumberNodeItem=new QStandardItem(QIcon("C:/TBD/data/线号图标.png"),ConnectionNumber);
        ConnectionNumberNodeItem->setData(QVariant("线号"),Qt::WhatsThisRole);
        ConnectionNumberNodeItem->setData(QVariant(QueryJXBLine.value("JXB_ID").toInt()),Qt::UserRole);
        Item->appendRow(ConnectionNumberNodeItem);
    }
    //在列表中添加导线
    //根据连接点对象是元件还是端子排分类
    QString Symb1Str,Symb2Str;
    if(Symb1_Category=="0")//元件
    {
        Symb1Str=GetUnitTermStrByTermID(Symb1_ID);
    }
    else if(Symb1_Category=="1")//端子排
    {
        Symb1Str=GetTerminalTermStrByTermID(Symb1_ID);
    }
    if(Symb2_Category=="0")//元件
    {
        Symb2Str=GetUnitTermStrByTermID(Symb2_ID);
    }
    else if(Symb2_Category=="1")//端子排
    {
        Symb2Str=GetTerminalTermStrByTermID(Symb2_ID);
    }
    QString LineStr=Symb1Str+"<->"+Symb2Str;
    if(ConnectionNumberNodeItem!=nullptr)
    {
        QStandardItem *LineItem=new QStandardItem(QIcon("C:/TBD/data/连线图标.png"),LineStr);
        LineItem->setData(QVariant("连线"),Qt::WhatsThisRole);
        QStringList ListLineItemData;
        ListLineItemData.clear();
        ListLineItemData.append(QueryJXBLine.value("JXB_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
        LineItem->setData(QVariant(ListLineItemData),Qt::UserRole);
        ConnectionNumberNodeItem->appendRow(LineItem);
    }
}

void MainWindow::LoadModelLineDT()
{
    //根据线号================
    ModelLineDT->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelLineDT->appendRow(fatherItem);

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    while(QueryJXB.next())
    {
        QString ProjectStructure_ID=QueryJXB.value("ProjectStructure_ID").toString();

        QString StrGaoceng,StrPos;
        QSqlQuery queryPos=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+ProjectStructure_ID;
        queryPos.exec(SqlStr);
        if(queryPos.next()) StrPos=queryPos.value("Structure_INT").toString();
        QSqlQuery queryGaoceng=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPos.value("Parent_ID").toString();
        queryGaoceng.exec(SqlStr);
        if(queryGaoceng.next()) StrGaoceng=queryGaoceng.value("Structure_INT").toString();

        //查看ModelLineDT是否有该高层节点
        bool GaoCengExisted=false;
        QStandardItem *GaoCengNodeItem;
        for(int i=0;i<fatherItem->rowCount();i++)
        {
            if((fatherItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")&&(fatherItem->child(i,0)->data(Qt::DisplayRole).toString()==StrGaoceng))
            {
                GaoCengExisted=true;
                GaoCengNodeItem=fatherItem->child(i,0);
                break;
            }
        }
        if(!GaoCengExisted)
        {
            GaoCengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),StrGaoceng);
            GaoCengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
            fatherItem->appendRow(GaoCengNodeItem);
        }
        if(GaoCengNodeItem==nullptr) continue;
        bool PosExisted=false;
        QStandardItem *PosNodeItem;
        for(int i=0;i<GaoCengNodeItem->rowCount();i++)
        {
            if((GaoCengNodeItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")&&(GaoCengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==StrPos))
            {
                PosExisted=true;
                PosNodeItem=GaoCengNodeItem->child(i,0);
                break;
            }
        }
        if(!PosExisted)
        {
            PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),StrPos);
            PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
            GaoCengNodeItem->appendRow(PosNodeItem);
        }
        if(PosNodeItem==nullptr) continue;
        //在PosNodeItem下插入连线
        InsertLineToItem(PosNodeItem,QueryJXB);
    }
    if(ModelLineDT->rowCount()>0) ui->treeViewLineDT->expand(fatherItem->index());
}

void MainWindow::LoadModelLineByUnits()
{
    //根据元件=================
    ModelLineByUnits->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelLineByUnits->appendRow(fatherItem);

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    while(QueryJXB.next())
    {
        QString StrGaoceng,StrPos;
        for(int index=0;index<2;index++)
        {
            if(index==0)
            {
                if(QueryJXB.value("Symb1_ID").toString()!="")
                {
                    GetUnitTermimalGaocengAndPos(QueryJXB.value("Symb1_Category").toInt(),QueryJXB.value("Symb1_ID").toInt(),StrGaoceng,StrPos);
                }
                else continue;
            }
            else if(index==1)
            {
                if(QueryJXB.value("Symb2_ID").toString()!="")
                {
                    GetUnitTermimalGaocengAndPos(QueryJXB.value("Symb2_Category").toInt(),QueryJXB.value("Symb2_ID").toInt(),StrGaoceng,StrPos);
                }
                else continue;
            }
            //qDebug()<<"StrGaoceng="<<StrGaoceng<<",StrPos="<<StrPos<<",index="<<index<<",ConnectionNumber="<<QueryJXB.value("ConnectionNumber").toString();
            //查看ModelLineByUnits是否有该高层节点
            bool GaoCengExisted=false;
            QStandardItem *GaoCengNodeItem;
            for(int i=0;i<fatherItem->rowCount();i++)
            {
                if((fatherItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")&&(fatherItem->child(i,0)->data(Qt::DisplayRole).toString()==StrGaoceng))
                {
                    GaoCengExisted=true;
                    GaoCengNodeItem=fatherItem->child(i,0);
                    break;
                }
            }
            if(!GaoCengExisted)
            {
                GaoCengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),StrGaoceng);
                GaoCengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
                fatherItem->appendRow(GaoCengNodeItem);
            }
            if(GaoCengNodeItem==nullptr) continue;
            bool PosExisted=false;
            QStandardItem *PosNodeItem;
            for(int i=0;i<GaoCengNodeItem->rowCount();i++)
            {
                if((GaoCengNodeItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")&&(GaoCengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==StrPos))
                {
                    PosExisted=true;
                    PosNodeItem=GaoCengNodeItem->child(i,0);
                    break;
                }
            }
            if(!PosExisted)
            {
                PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),StrPos);
                PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                GaoCengNodeItem->appendRow(PosNodeItem);
            }
            if(PosNodeItem==nullptr) continue;
            //在PosNodeItem下插入器件
            InsertUnitTerminalToItem(PosNodeItem,QueryJXB,index);
        }//for(int index=0;index<2;index++)
    }
    if(ModelLineByUnits->rowCount()>0) ui->treeViewLineByUnit->expand(fatherItem->index());

    QString OriginalLineGaoceng=ui->CbLineGaoceng->currentText();
    QString OriginalLinePos=ui->CbLinePos->currentText();
    ui->CbLineGaoceng->clear();
    ui->CbLineGaoceng->addItem("高层");
    ui->CbLinePos->clear();
    ui->CbLinePos->addItem("位置");
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)
    {
        ui->CbLineGaoceng->addItem(ModelLineByUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            bool Existed=false;
            for(int k=0;k<ui->CbLinePos->count();k++)
            {
                if(ui->CbLinePos->itemText(k)==ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbLinePos->addItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
            }
        }
    }
    ui->CbLineGaoceng->setCurrentText(OriginalLineGaoceng);
    ui->CbLinePos->setCurrentText(OriginalLinePos);

    //载入页
    QString OriginalPageName=ui->CbLinePage->currentText();
    ui->CbLinePage->clear();
    ui->CbLinePage->addItem("页");
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Page WHERE PageType = '原理图' ORDER BY ProjectStructure_ID";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        ui->CbLinePage->addItem(GetPageNameByPageID(QueryPage.value("Page_ID").toInt()));
    }
    ui->CbLinePage->setCurrentText(OriginalPageName);
    FilterLines();
}

void MainWindow::LoadProjectLines()
{
    LoadModelLineDT();
    LoadModelLineByUnits();
}

void MainWindow::handleConnectLinesChanged(int pageId)
{
    Q_UNUSED(pageId);
    on_Btn_RemakeConnectLine_clicked();
}

void MainWindow::LoadProjectTerminals()
{
    //记录当前展开的index
    QList<int> listGaocengExpendID,listPosExpendID,listTerminalStripExpendID;
    if(ModelTerminals->rowCount()>0)
    {
        for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//位置
        {
            if(ui->treeViewTerminal->isExpanded(ModelTerminals->item(0,0)->child(i,0)->index()))//高层
                listGaocengExpendID.append(ModelTerminals->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
            for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)//位置
            {
                if(ui->treeViewTerminal->isExpanded(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->index()))
                    listPosExpendID.append(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
                for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                {
                    if(ui->treeViewTerminal->isExpanded(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->index()))
                        listTerminalStripExpendID.append(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());
                }
            }
        }
    }

    ModelTerminals->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelTerminals->appendRow(fatherItem);
    ui->treeViewTerminal->expand(fatherItem->index());
    //在TerminalStrip表中检索元件
    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM TerminalStrip ORDER BY DT");
    QueryTerminalStrip.exec(temp);
    while(QueryTerminalStrip.next())
    {
        QString ProjectStructure_ID=QueryTerminalStrip.value("ProjectStructure_ID").toString();
        int TerminalStrip_ID=QueryTerminalStrip.value("TerminalStrip_ID").toInt();
        QString TerminalTag=QueryTerminalStrip.value("DT").toString();
        //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+ProjectStructure_ID);
        QueryPos.exec(temp);
        if(!QueryPos.next()) continue;
        QString PosStr=QueryPos.value("Structure_INT").toString();
        //查找对应的高层
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) continue;
        QString GaocengStr=QueryGaoceng.value("Structure_INT").toString();
        QString TerminalNodeStr;
        //UnitNodeStr+="="+GaocengStr;
        TerminalNodeStr=TerminalTag;
        //在treeViewUnits中查看位置是否存在，不存在则新增位置节点
        bool GaocengNodeExist=false;
        bool PosNodeExist=false;
        QStandardItem *PosNodeItem,*GaocengNodeItem;
        for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)
        {
            if(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==GaocengStr)
            {
                GaocengNodeExist=true;
                GaocengNodeItem=ModelTerminals->item(0,0)->child(i,0);
                break;
            }
        }
        if(!GaocengNodeExist) //新增高层节点
        {
            GaocengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),GaocengStr);
            GaocengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
            GaocengNodeItem->setData(QVariant(QueryGaoceng.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            fatherItem->appendRow(GaocengNodeItem);
        }
        if(GaocengNodeItem==nullptr) continue;
        for(int i=0;i<listGaocengExpendID.count();i++)
        {
            if(listGaocengExpendID.at(i)==QueryGaoceng.value("ProjectStructure_ID").toInt()) {ui->treeViewTerminal->expand(GaocengNodeItem->index());break;}
        }
        for(int i=0;i<GaocengNodeItem->rowCount();i++)//在高层节点下查找位置节点，不存在则新增位置节点
        {
            if(GaocengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==PosStr)
            {
                PosNodeExist=true;
                PosNodeItem=GaocengNodeItem->child(i,0);
                break;
            }
        }
        if(!PosNodeExist) //新增位置节点
        {
            PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),PosStr);
            PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
            PosNodeItem->setData(QVariant(QueryPos.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            GaocengNodeItem->appendRow(PosNodeItem);
        }
        if(PosNodeItem==nullptr) continue;
        for(int i=0;i<listPosExpendID.count();i++)
        {
            if(listPosExpendID.at(i)==QueryPos.value("ProjectStructure_ID").toInt()) {ui->treeViewTerminal->expand(PosNodeItem->index());break;}
        }
        //在位置节点下插入端子排
        QStandardItem *TerminalItem=new QStandardItem(QIcon("C:/TBD/data/端子排图标.png"),TerminalNodeStr);
        TerminalItem->setData(QVariant("端子排"),Qt::WhatsThisRole);
        TerminalItem->setData(QVariant(TerminalStrip_ID),Qt::UserRole);
        PosNodeItem->appendRow(TerminalItem);
        //在节点下插入所有的端子,在Symbol表中检索与元件关联的所有子块
        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QString::number(TerminalStrip_ID)+"' ORDER BY Terminal_ID");
        QueryTerminal.exec(temp);
        while(QueryTerminal.next())
        {
            QStandardItem *TerminalSpurItem;
            QString TerminalSpurStr=QueryTerminal.value("ShortJumper").toString()+QueryTerminal.value("Designation").toString();
            QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            temp = "SELECT * FROM TerminalInstance WHERE Terminal_ID = '"+QueryTerminal.value("Terminal_ID").toString()+"'";
            QueryTerminalInstance.exec(temp);
            if(QueryTerminalInstance.next())
            {
                //TerminalSpurStr+="("+GetPageNameByPageID(QueryTerminal.value("Page_ID").toString().toInt())+")";
                TerminalSpurStr+="("+QueryTerminal.value("FunDefine").toString()+")";
                TerminalSpurItem=new QStandardItem(QIcon("C:/TBD/data/端子图标_已插入.png"),TerminalSpurStr);
            }
            else
            {
                TerminalSpurStr+="("+QueryTerminal.value("FunDefine").toString()+")";
                TerminalSpurItem=new QStandardItem(QIcon("C:/TBD/data/端子图标_未插入.png"),TerminalSpurStr);
            }
            TerminalSpurItem->setData(QVariant("端子"),Qt::WhatsThisRole);
            TerminalSpurItem->setData(QVariant(QueryTerminal.value("Terminal_ID").toInt()),Qt::UserRole);
            TerminalItem->appendRow(TerminalSpurItem);
            if(SelectTerminal_ID==QueryTerminal.value("Terminal_ID").toInt())
            {
                ui->treeViewTerminal->expand(TerminalItem->index());
                ui->treeViewTerminal->setCurrentIndex(TerminalSpurItem->index());
            }
        }
        if(SelectTerminalStrip_ID==TerminalStrip_ID)
        {
            ui->treeViewTerminal->expand(TerminalItem->index());
            ui->treeViewTerminal->setCurrentIndex(TerminalItem->index());
        }
        else
        {
            for(int i=0;i<listTerminalStripExpendID.count();i++)
            {
                if(listTerminalStripExpendID.at(i)==TerminalStrip_ID) {ui->treeViewTerminal->expand(TerminalItem->index());break;}
            }
        }
    }

    QString OriginalTerminalGaoceng=ui->CbTermGaoceng->currentText();
    QString OriginalTerminalPos=ui->CbTermPos->currentText();
    ui->CbTermGaoceng->clear();
    ui->CbTermGaoceng->addItem("高层");
    ui->CbTermPos->clear();
    ui->CbTermPos->addItem("位置");
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)
    {
        ui->CbTermGaoceng->addItem(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)
        {
            bool Existed=false;
            for(int k=0;k<ui->CbTermPos->count();k++)
            {
                if(ui->CbTermPos->itemText(k)==ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbTermPos->addItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
            }
        }
    }
    ui->CbTermGaoceng->setCurrentText(OriginalTerminalGaoceng);
    ui->CbTermPos->setCurrentText(OriginalTerminalPos);

    //载入页
    QString OriginalPageName=ui->CbUnitPage->currentText();
    ui->CbTermPage->clear();
    ui->CbTermPage->addItem("页");
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Page WHERE PageType = '原理图' ORDER BY ProjectStructure_ID";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        ui->CbTermPage->addItem(GetPageNameByPageID(QueryPage.value("Page_ID").toInt()));
    }
    ui->CbTermPage->setCurrentText(OriginalPageName);
    FilterTerminal();
}

void MainWindow::LoadProjectUnits()
{
    //记录当前展开的index
    QList<int> listGaocengExpendID,listPosExpendID,listEquipmentExpendID;
    if(ModelUnits->rowCount()>0)
    {
        for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//位置
        {
            if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->index()))//高层
                listGaocengExpendID.append(ModelUnits->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
            for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
            {
                if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->child(j,0)->index()))
                    listPosExpendID.append(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
                for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                {
                    if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->index()))
                        listEquipmentExpendID.append(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());
                }
            }
        }
    }

    ModelUnits->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelUnits->appendRow(fatherItem);
    ui->treeViewUnits->expand(fatherItem->index());
    //在Equipment表中检索元件
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM Equipment ORDER BY DT");
    QueryEquipment.exec(temp);
    while(QueryEquipment.next())
    {
        QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
        int Equipment_ID=QueryEquipment.value("Equipment_ID").toInt();
        QString UnitTag=QueryEquipment.value("DT").toString();
        QString UnitType=QueryEquipment.value("Type").toString();
        QString UnitName=QueryEquipment.value("Name").toString();
        //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+ProjectStructure_ID);
        QueryPos.exec(temp);
        if(!QueryPos.next()) continue;
        QString PosStr=QueryPos.value("Structure_INT").toString();
        //查找对应的高层
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) continue;
        QString GaocengStr=QueryGaoceng.value("Structure_INT").toString();
        QString UnitNodeStr;
        //UnitNodeStr+="="+GaocengStr;
        UnitNodeStr=UnitTag;
        if((UnitType!="")||(UnitName!="")) UnitNodeStr+="(";
        UnitNodeStr+=UnitType;
        if(UnitType!="") UnitNodeStr+=",";
        UnitNodeStr+=UnitName;
        if((UnitType!="")||(UnitName!="")) UnitNodeStr+=")";
        //在treeViewUnits中查看位置是否存在，不存在则新增位置节点
        bool GaocengNodeExist=false;
        bool PosNodeExist=false;
        QStandardItem *PosNodeItem,*GaocengNodeItem;
        for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
        {
            if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==GaocengStr)
            {
                GaocengNodeExist=true;
                GaocengNodeItem=ModelUnits->item(0,0)->child(i,0);
                break;
            }
        }
        if(!GaocengNodeExist) //新增高层节点
        {
            GaocengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),GaocengStr);
            GaocengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
            GaocengNodeItem->setData(QVariant(QueryGaoceng.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            fatherItem->appendRow(GaocengNodeItem);
        }
        if(GaocengNodeItem==nullptr) continue;
        for(int i=0;i<listGaocengExpendID.count();i++)
        {
            if(listGaocengExpendID.at(i)==QueryGaoceng.value("ProjectStructure_ID").toInt()) {ui->treeViewUnits->expand(GaocengNodeItem->index());break;}
        }
        for(int i=0;i<GaocengNodeItem->rowCount();i++)//在高层节点下查找位置节点，不存在则新增位置节点
        {
            if(GaocengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==PosStr)
            {
                PosNodeExist=true;
                PosNodeItem=GaocengNodeItem->child(i,0);
                break;
            }
        }
        if(!PosNodeExist) //新增位置节点
        {
            PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),PosStr);
            PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
            PosNodeItem->setData(QVariant(QueryPos.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            GaocengNodeItem->appendRow(PosNodeItem);
        }
        if(PosNodeItem==nullptr) continue;
        for(int i=0;i<listPosExpendID.count();i++)
        {
            if(listPosExpendID.at(i)==QueryPos.value("ProjectStructure_ID").toInt()) {ui->treeViewUnits->expand(PosNodeItem->index());break;}
        }
        //在位置节点下插入元件
        QStandardItem *UnitItem=new QStandardItem(QIcon("C:/TBD/data/元件图标.png"),UnitNodeStr);
        UnitItem->setData(QVariant("元件"),Qt::WhatsThisRole);
        UnitItem->setData(QVariant(Equipment_ID),Qt::UserRole);
        PosNodeItem->appendRow(UnitItem);
        //在元件节点下插入所有的功能子块,在Symbol表中检索与元件关联的所有子块
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"'");
        QuerySymbol.exec(temp);
        //qDebug()<<"LoadProjectUnits Equipment_ID:"<<Equipment_ID;
        while(QuerySymbol.next())
        {
            QStandardItem *UnitSpurItem;
            QString UnitSpurStr;
            UnitSpurStr=GetUnitSpurStrBySymbol_ID(QuerySymbol);
            //根据Symbol_Handle是否存在确定功能子块图标和文字
            //qDebug()<<"Symbol:"<<QuerySymbol.value("Symbol").toString()<<"  Symbol_Handle:"<<QuerySymbol.value("Symbol_Handle").toString();
            if(QuerySymbol.value("Symbol").toString()==""&&(QuerySymbol.value("FunDefine").toString()!="黑盒")&&(QuerySymbol.value("FunDefine").toString()!="PLC 盒子"))
            {
                UnitSpurStr+="-"+QuerySymbol.value("FunDefine").toString();
                UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_不可插入.png"),UnitSpurStr);
            }
            else
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")//
                {
                    //根据实际子块插入的位置
                    //得到子块实际放置的图纸位置名称
                    UnitSpurStr+="("+GetPageNameByPageID(QuerySymbol.value("Page_ID").toString().toInt())+")";
                    UnitSpurStr+=QuerySymbol.value("FunDefine").toString();
                    UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_已插入.png"),UnitSpurStr);
                }
                else
                {
                    UnitSpurStr+="-"+QuerySymbol.value("FunDefine").toString();
                    UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_未插入.png"),UnitSpurStr);
                }
            }
            UnitSpurItem->setData(QVariant("功能子块"),Qt::WhatsThisRole);
            UnitSpurItem->setData(QVariant(QuerySymbol.value("Symbol_ID").toInt()),Qt::UserRole);
            UnitSpurItem->setFlags(UnitSpurItem->flags()|Qt::ItemIsDragEnabled);
            UnitItem->appendRow(UnitSpurItem);
            if(SelectSymbol_ID==QuerySymbol.value("Symbol_ID").toInt())
            {
                ui->treeViewUnits->expand(UnitItem->index());
                ui->treeViewUnits->setCurrentIndex(UnitSpurItem->index());
            }
        }
        if(SelectEquipment_ID==Equipment_ID)
        {
            ui->treeViewUnits->expand(UnitItem->index());
            ui->treeViewUnits->setCurrentIndex(UnitItem->index());
        }
        else
        {
            for(int i=0;i<listEquipmentExpendID.count();i++)
            {
                if(listEquipmentExpendID.at(i)==Equipment_ID) {ui->treeViewUnits->expand(UnitItem->index());break;}
            }
        }
    }

    LoadUnitTable();

    QString OriginalUnitGaoceng=ui->CbUnitGaoceng->currentText();
    QString OriginalUnitPos=ui->CbUnitPos->currentText();
    ui->CbUnitGaoceng->clear();
    ui->CbUnitGaoceng->addItem("高层");
    ui->CbUnitPos->clear();
    ui->CbUnitPos->addItem("位置");
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
    {
        ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            bool Existed=false;
            for(int k=0;k<ui->CbUnitPos->count();k++)
            {
                if(ui->CbUnitPos->itemText(k)==ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbUnitPos->addItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
            }
        }
    }
    ui->CbUnitGaoceng->setCurrentText(OriginalUnitGaoceng);
    ui->CbUnitPos->setCurrentText(OriginalUnitPos);

    //载入页
    QString OriginalPageName=ui->CbUnitPage->currentText();
    ui->CbUnitPage->clear();
    ui->CbUnitPage->addItem("页");
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Page WHERE PageType = '原理图' ORDER BY ProjectStructure_ID";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        ui->CbUnitPage->addItem(GetPageNameByPageID(QueryPage.value("Page_ID").toInt()));
    }
    ui->CbUnitPage->setCurrentText(OriginalPageName);
    FilterUnit();
    LoadProjectSystemDescription();
}

void MainWindow::LoadUnitTable()
{
    ui->tableWidgetUnit->setRowCount(0);
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    //载入table
    if(!ui->CbUnitTogether->isChecked())//不汇总
    {
        for(int i=0;i<ModelUnits->rowCount();i++)
        {
            for(int j=0;j<ModelUnits->item(i,0)->rowCount();j++)
            {
                for(int k=0;k<ModelUnits->item(i,0)->child(j,0)->rowCount();k++)
                {
                    for(int m=0;m<ModelUnits->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                    {
                        int Equipment_ID = ModelUnits->item(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toInt();
                        QString SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(Equipment_ID);
                        QueryEquipment.exec(SqlStr);
                        if(QueryEquipment.next())
                        {
                            ui->tableWidgetUnit->setRowCount(ui->tableWidgetUnit->rowCount()+1);
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidgetUnit->rowCount())));//序号
                            ui->tableWidgetUnit->item(ui->tableWidgetUnit->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipment.value("Equipment_ID").toInt());
                            QString UnitTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,1,new QTableWidgetItem(UnitTag));//项目代号
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,2,new QTableWidgetItem(QueryEquipment.value("Type").toString()));//型号
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,3,new QTableWidgetItem(QueryEquipment.value("Name").toString()));//名称
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,4,new QTableWidgetItem("1"));//数量
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,5,new QTableWidgetItem(QueryEquipment.value("Factory").toString()));//厂家
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,6,new QTableWidgetItem(QueryEquipment.value("PartCode").toString()));//部件编号
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,7,new QTableWidgetItem(QueryEquipment.value("Remark").toString()));//元件备注
                        }
                    }
                }

            }
        }
    }
    else//汇总
    {
        QString StrSql;
        QStringList ListedPart;
        ListedPart.clear();
        StrSql="SELECT * FROM Equipment ORDER BY ProjectStructure_ID";
        QueryEquipment.exec(StrSql);
        while(QueryEquipment.next())
        {
            if(QueryEquipment.value("PartCode").toString()=="") continue;
            bool PartExisted=false;
            for(int i=0;i<ListedPart.count();i++)
            {
                if(ListedPart.at(i)==QueryEquipment.value("PartCode").toString())
                {
                    PartExisted=true;
                    break;
                }
            }
            if(PartExisted) continue;
            ListedPart.append(QueryEquipment.value("PartCode").toString());
            ui->tableWidgetUnit->setRowCount(ui->tableWidgetUnit->rowCount()+1);
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidgetUnit->rowCount())));//序号
            ui->tableWidgetUnit->item(ui->tableWidgetUnit->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipment.value("Equipment_ID").toInt());
            QString UnitTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,1,new QTableWidgetItem(UnitTag));//项目代号
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,2,new QTableWidgetItem(QueryEquipment.value("Type").toString()));//型号
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,3,new QTableWidgetItem(QueryEquipment.value("Name").toString()));//名称
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            StrSql="SELECT * FROM Equipment WHERE PartCode = '"+QueryEquipment.value("PartCode").toString()+"'";
            QuerySearch.exec(StrSql);
            if(QuerySearch.last())
                ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,4,new QTableWidgetItem(QString::number(QuerySearch.at()+1)));//数量
            else
                ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,4,new QTableWidgetItem("0"));//数量
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,5,new QTableWidgetItem(QueryEquipment.value("Factory").toString()));//厂家
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,6,new QTableWidgetItem(QueryEquipment.value("PartCode").toString()));//部件编号
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,7,new QTableWidgetItem(QueryEquipment.value("Remark").toString()));//元件备注
        }
    }
}

void MainWindow::LoadProjectPages()
{
    //记录当前展开的index
    QList<int> listPagesExpend;
    if(ModelPages->rowCount()>0)
    {
        for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
        {
            if(ui->treeViewPages->isExpanded(ModelPages->item(0,0)->child(i,0)->index()))
            {
                if(StrIsNumber(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toString()))
                    listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
            }
            for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
            {
                if(ui->treeViewPages->isExpanded(ModelPages->item(0,0)->child(i,0)->child(j,0)->index()))
                {
                    if(StrIsNumber(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toString()))
                        listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
                }
                for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
                {
                    if(ui->treeViewPages->isExpanded(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->index()))
                    {
                        if(StrIsNumber(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toString()))
                            listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());
                    }
                }
            }
        }
    }

    ModelPages->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelPages->appendRow(fatherItem);
    ui->treeViewPages->expand(fatherItem->index());
    QSqlQuery QueryVarPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6'");
    QueryVarPage.exec(temp);
    while(QueryVarPage.next())
    {
        //if(QueryVarPage.value("Structure_INT").toString()!="") continue;
        QString PosRecordID=QueryVarPage.value("Parent_ID").toString();
        QSqlQuery QueryVar2 = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+PosRecordID);
        QueryVar2.exec(temp);
        if(!QueryVar2.next()) return;
        QString GaoCengRecordID=QueryVar2.value("Parent_ID").toString();
        QSqlQuery QueryVar3 = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+GaoCengRecordID);
        QueryVar3.exec(temp);
        if(!QueryVar3.next()) return;

        //查看高层节点是否存在，若不存在则新建,若存在则添加位置信息
        bool GaocengExist=false;
        //如果高层代号非空，则先检索高层代号节点是否存在；如果高层代号为空，则检索位置代号节点是否存在
        if(QueryVar3.value("Structure_INT").toString()!="")//高层代号非空，则先检索高层代号节点是否存在
        {
            for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==QueryVar3.value("Structure_INT").toString())//高层存在，添加位置信息
                {
                    bool PosExist=false;
                    //在高层代号非空的前提下，如果位置代号非空，则检索位置代号是否存在；
                    if(QueryVar2.value("Structure_INT").toString()!="")//位置信息非空
                    {
                        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
                        {
                            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()==QueryVar2.value("Structure_INT").toString())//位置信息存在
                            {
                                if(QueryVarPage.value("Structure_INT").toString()!="")
                                {
                                    AddIndexToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0),QueryVarPage,true,"分组");
                                }
                                else
                                    ModelPages->item(0,0)->child(i,0)->child(j,0)->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);

                                PosExist=true;
                                break;
                            }
                        }
                        if(!PosExist)//位置信息不存在
                        {
                            QStandardItem *SubSubFatherItem;
                            SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),QueryVar2.value("Structure_INT").toString());
                            SubSubFatherItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                            // 设置位置节点的 tooltip
                            QString posDesc = QueryVar2.value("Struct_Desc").toString().trimmed();
                            if(!posDesc.isEmpty()) {
                                SubSubFatherItem->setToolTip(posDesc);
                            }
                            if(QueryVarPage.value("Structure_INT").toString()=="")
                            {
                                SubSubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                            }
                            else
                            {
                                AddIndexToIndex(SubSubFatherItem,QueryVarPage,true,"分组");
                            }
                            ModelPages->item(0,0)->child(i,0)->appendRow(SubSubFatherItem);

                        }
                    }
                    else//位置信息为空，直接添加列表图标
                    {
                        if(QueryVarPage.value("Structure_INT").toString()!="")
                        {
                            AddIndexToIndex(ModelPages->item(0,0)->child(i,0),QueryVarPage,true,"分组");
                        }
                        else
                        {
                            ModelPages->item(0,0)->child(i,0)->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                        }
                    }
                    GaocengExist=true;
                    break;
                }
            }
            if(!GaocengExist)//高层不存在,添加高层信息和位置信息
            {
                QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),QueryVar3.value("Structure_INT").toString());
                SubFatherItem->setData(QVariant("高层"),Qt::WhatsThisRole);
                // 设置高层节点的 tooltip
                QString gaocengDesc = QueryVar3.value("Struct_Desc").toString().trimmed();
                if(!gaocengDesc.isEmpty()) {
                    SubFatherItem->setToolTip(gaocengDesc);
                }
                ModelPages->item(0,0)->appendRow(SubFatherItem);
                if(QueryVar2.value("Structure_INT").toString()!="")//位置信息非空
                {
                    QStandardItem *SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),QueryVar2.value("Structure_INT").toString());
                    SubSubFatherItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                    // 设置位置节点的 tooltip
                    QString posDesc = QueryVar2.value("Struct_Desc").toString().trimmed();
                    if(!posDesc.isEmpty()) {
                        SubSubFatherItem->setToolTip(posDesc);
                    }
                    if(QueryVarPage.value("Structure_INT").toString()=="")//非表报
                    {
                        SubSubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                    }
                    else
                    {
                        AddIndexToIndex(SubSubFatherItem,QueryVarPage,true,"分组");
                    }
                    SubFatherItem->appendRow(SubSubFatherItem);
                }
                else//位置信息为空，直接添加列表节点
                {
                    if(QueryVarPage.value("Structure_INT").toString()=="")//非表报
                    {
                        SubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                    }
                    else
                    {
                        AddIndexToIndex(SubFatherItem,QueryVarPage,true,"分组");
                    }

                }
            }
        }
        else//高层代号为空，直接添加位置节点
        {
            bool PosExist=false;
            //在高层代号非空的前提下，如果位置代号非空，则检索位置代号是否存在；
            if(QueryVar2.value("Structure_INT").toString()!="")//位置信息非空
            {
                for(int j=0;j<ModelPages->item(0,0)->rowCount();j++)
                {
                    if(ModelPages->item(0,0)->child(j,0)->data(Qt::DisplayRole).toString()==QueryVar2.value("Structure_INT").toString())//位置信息存在
                    {
                        if(QueryVarPage.value("Structure_INT").toString()!="")
                        {
                            AddIndexToIndex(ModelPages->item(0,0)->child(j,0),QueryVarPage,true,"分组");
                        }
                        PosExist=true;
                        break;
                    }
                }
                if(!PosExist)//位置信息不存在
                {
                    QStandardItem *SubFatherItem;
                    SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),QueryVar2.value("Structure_INT").toString());
                    SubFatherItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                    // 设置位置节点的 tooltip
                    QString posDesc = QueryVar2.value("Struct_Desc").toString().trimmed();
                    if(!posDesc.isEmpty()) {
                        SubFatherItem->setToolTip(posDesc);
                    }
                    if(QueryVarPage.value("Structure_INT").toString()=="")
                    {
                        SubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                    }
                    else
                    {
                        AddIndexToIndex(SubFatherItem,QueryVarPage,true,"分组");
                    }
                    ModelPages->item(0,0)->appendRow(SubFatherItem);
                }
            }
            else//位置信息为空，直接添加列表图标
            {
                if(QueryVarPage.value("Structure_INT").toString()!="")
                {
                    AddIndexToIndex(ModelPages->item(0,0),QueryVarPage,true,"分组");
                }
                else
                {
                    fatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                }
            }
        }
    }


    //从table Page载入Pages
    temp = QString("SELECT * FROM Page ORDER BY Page_ID ASC");
    QueryVar.exec(temp);
    while(QueryVar.next())
    {
        //在树节点中查找对应的位置节点
        bool Find=false;
        if(ModelPages->item(0,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
        {
            AddDwgFileToIndex(ModelPages->item(0,0),QueryVar,listPagesExpend);
            continue;
        }
        for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
        {
            //确认当前节点是是高层还是位置还是列表
            if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                {
                    AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0),QueryVar,listPagesExpend);
                    break;
                }
                for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
                {
                    //确认当前节点是位置还是列表
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="位置")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                        {
                            AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0),QueryVar,listPagesExpend);
                            Find=true;
                            break;
                        }
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount()<=0) continue;
                        for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
                        {
                            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()!="列表") continue;
                            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                            {
                                AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0),QueryVar,listPagesExpend);
                                Find=true;
                                break;
                            }
                        }
                    }
                    else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表")//当前节点是列表
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                        {
                            AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0),QueryVar,listPagesExpend);
                            Find=true;
                            break;
                        }
                    }
                }
            }
            else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                {
                    AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0),QueryVar,listPagesExpend);
                    Find=true;
                    break;
                }
                if(ModelPages->item(0,0)->child(i,0)->rowCount()<=0) continue;
                for(int k=0;k<ModelPages->item(0,0)->child(i,0)->rowCount();k++)
                {
                    if(ModelPages->item(0,0)->child(i,0)->child(k,0)->data(Qt::WhatsThisRole).toString()!="分组") continue;
                    if(ModelPages->item(0,0)->child(i,0)->child(k,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                    {
                        AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(k,0),QueryVar,listPagesExpend);
                        Find=true;
                        break;
                    }
                }
            }
            else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="分组")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                {
                    AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0),QueryVar,listPagesExpend);
                    Find=true;
                    break;
                }
            }
            if(Find) break;
        }
        if(!Find)
        {
            QString gaocengStr, posStr, pageCodeStr;
            const QString prefix = ExtractPagePrefix(GetPageNameByPageID(QueryVar.value("Page_ID").toInt()));
            SplitPagePrefix(prefix, &gaocengStr, &posStr, &pageCodeStr);
            QStandardItem *fallbackParent = ensurePageHierarchyItem(ModelPages->item(0,0),
                                                                     gaocengStr,
                                                                     posStr,
                                                                     pageCodeStr,
                                                                     QueryVar.value("ProjectStructure_ID").toInt());
            if(fallbackParent)
                AddDwgFileToIndex(fallbackParent,QueryVar,listPagesExpend);
        }
    }
    //删除没有图纸的报表节点
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//列表
            {
                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()=="分组")
                {
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()<=0)
                    {
                        ModelPages->item(0,0)->child(i,0)->child(j,0)->removeRow(k);
                        k=k-1;
                        continue;
                    }
                }
            }
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount()<=0)
            {
                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()!="图纸")
                {
                    ModelPages->item(0,0)->child(i,0)->removeRow(j);
                    j=j-1;
                    continue;
                }
            }
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        if(ModelPages->item(0,0)->child(i,0)->rowCount()<=0)
        {
            if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()!="图纸")
            {
                ModelPages->item(0,0)->removeRow(i);i=i-1;continue;
            }
        }
    }
    ui->treeViewPages->expand(ModelPages->indexFromItem(fatherItem));
    QString OriginalPageGaoceng=ui->CbPageGaocengFilter->currentText();
    QString OriginalPagePos=ui->CbPagePosFilter->currentText();
    ui->CbPageGaocengFilter->clear();
    ui->CbPageGaocengFilter->addItem("高层");
    ui->CbPagePosFilter->clear();
    ui->CbPagePosFilter->addItem("位置");
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")
            ui->CbPageGaocengFilter->addItem(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")
        {
            //存在高层为空的图纸
            bool Existed=false;
            for(int k=0;k<ui->CbPageGaocengFilter->count();k++)
            {
                if(ui->CbPageGaocengFilter->itemText(k)=="")
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed) ui->CbPageGaocengFilter->addItem("");
            Existed=false;
            for(int k=0;k<ui->CbPagePosFilter->count();k++)
            {
                if(ui->CbPagePosFilter->itemText(k)==ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbPagePosFilter->addItem(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
            }
        }
        else if((ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="图纸")||(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="分组"))
        {
            //存在高层和位置为空的图纸
            bool Existed=false;
            for(int k=0;k<ui->CbPageGaocengFilter->count();k++)
            {
                if(ui->CbPageGaocengFilter->itemText(k)=="")
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed) ui->CbPageGaocengFilter->addItem("");

            Existed=false;
            for(int k=0;k<ui->CbPagePosFilter->count();k++)
            {
                if(ui->CbPagePosFilter->itemText(k)=="")
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed) ui->CbPagePosFilter->addItem("");
        }
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="位置")
            {
                bool Existed=false;
                for(int k=0;k<ui->CbPagePosFilter->count();k++)
                {
                    if(ui->CbPagePosFilter->itemText(k)==ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed)
                {
                    ui->CbPagePosFilter->addItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
                }
            }
            else if((ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="图纸")||(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="分组"))
            {
                //存在高层和位置为空的图纸
                bool Existed=false;
                for(int k=0;k<ui->CbPageGaocengFilter->count();k++)
                {
                    if(ui->CbPageGaocengFilter->itemText(k)=="")
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed) ui->CbPageGaocengFilter->addItem("");

                Existed=false;
                for(int k=0;k<ui->CbPagePosFilter->count();k++)
                {
                    if(ui->CbPagePosFilter->itemText(k)=="")
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed) ui->CbPagePosFilter->addItem("");
            }
        }
    }
    ui->CbPageGaocengFilter->setCurrentText(OriginalPageGaoceng);
    ui->CbPagePosFilter->setCurrentText(OriginalPagePos);
    FilterPage();
}

void MainWindow::FilterTerminal()
{
    if(ModelTerminals->rowCount()<=0) return;

    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)
    {
        if(ui->CbTermGaoceng->currentText()!="高层")
        {
            if(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbTermGaoceng->currentText())
                ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),true);
            else
                ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),false);
        }
        else
            ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),false);

        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ui->CbTermPos->currentText()!="位置")
            {
                if(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbTermPos->currentText())
                    ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),true);
                else
                    ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),false);
            }
            else
                ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),false);

            for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                //元件
                if(ui->EdTermTagFilter->text()!="")
                {
                    if(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdTermTagFilter->text()))
                        ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),false);
                    else
                        ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),true);
                }
                else
                {
                    ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),false);
                }


                for(int m=0;m<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//功能子块
                {
                    if(ui->CbTermPage->currentText()!="页")
                    {
                        //查看当前功能子块是否在所筛选页面上
                        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString();
                        QueryTerminal.exec(SqlStr);
                        if(QueryTerminal.next())
                        {
                            if(QueryTerminal.value("Page_ID").toString()!="")
                            {
                                if(GetPageNameByPageID(QueryTerminal.value("Page_ID").toInt())==ui->CbTermPage->currentText())
                                    ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                else
                                    ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                            }
                            else
                                ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                        }
                        else
                            ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                    }
                    else
                    {
                        ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                    }
                }
            }
        }
    }

    //隐藏没有功能子块的节点
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
            {
                bool AllHide=true;
                for(int m=0;m<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewTerminal->isRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewTerminal->isRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//高层
    {
        bool AllHide=true;
        for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->rowCount();k++)//位置
        {
            if(!ui->treeViewTerminal->isRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelTerminals->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),true);
    }
}

void MainWindow::FilterLines()
{
    if(ModelLineByUnits->rowCount()<=0) return;

    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)
    {
        if(ui->CbLineGaoceng->currentText()!="高层")
        {
            if(ModelLineByUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbLineGaoceng->currentText())
                ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),true);
            else
                ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),false);
        }
        else
            ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),false);

        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ui->CbLinePos->currentText()!="位置")
            {
                if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbLinePos->currentText())
                    ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),true);
                else
                    ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),false);
            }
            else
                ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),false);

            for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                //元件
                if(ui->EdLineTagFilter->text()!="")
                {
                    if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdLineTagFilter->text()))
                        ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),false);
                    else
                        ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),true);
                }
                else
                {
                    ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),false);
                }


                for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//功能子块
                {
                    if(ui->CbLinePage->currentText()!="页")
                    {
                        //查看当前功能子块是否在所筛选页面上

                        //可能是元件或端子
                        QStringList ListData=ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toStringList();
                        if(ListData.count()==5)
                        {
                            if(ListData.at(2)=="0")
                            {
                                QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+ListData.at(1);
                                QuerySymb2TermInfo.exec(SqlStr);
                                if(QuerySymb2TermInfo.next())
                                {
                                    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                    SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySymb2TermInfo.value("Symbol_ID").toString();
                                    QuerySymbol.exec(SqlStr);
                                    if(QuerySymbol.next())
                                    {
                                        if(QuerySymbol.value("Page_ID").toString()!="")
                                        {
                                            if(GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt())==ui->CbLinePage->currentText())
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                            else
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                        }
                                        else
                                            ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                    }
                                    else
                                        ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                }
                            }
                            else if(ListData.at(2)=="1")
                            {
                                QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID = "+ListData.at(1);
                                QueryTerminalTerm.exec(SqlStr);
                                if(QueryTerminalTerm.next())
                                {
                                    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                    SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+QueryTerminalTerm.value("Terminal_ID").toString();
                                    QueryTerminal.exec(SqlStr);
                                    if(QueryTerminal.next())
                                    {
                                        if(QueryTerminal.value("Page_ID").toString()!="")
                                        {
                                            if(GetPageNameByPageID(QueryTerminal.value("Page_ID").toInt())==ui->CbLinePage->currentText())
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                            else
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                        }
                                        else
                                            ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                    }
                                    else
                                        ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                }
                            }
                        }
                    }
                    else
                    {
                        ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                    }
                }
            }
        }
    }

    //隐藏没有功能子块的节点
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
            {
                bool AllHide=true;
                for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewLineByUnit->isRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewLineByUnit->isRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
    {
        bool AllHide=true;
        for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();k++)//位置
        {
            if(!ui->treeViewLineByUnit->isRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelLineByUnits->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),true);
    }
}

void MainWindow::FilterUnit()
{
    if(ModelUnits->rowCount()<=0) return;

    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
    {
        if(ui->CbUnitGaoceng->currentText()!="高层")
        {
            if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbUnitGaoceng->currentText())
                ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),true);
            else
                ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),false);
        }
        else
            ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),false);

        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ui->CbUnitPos->currentText()!="位置")
            {
                if(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbUnitPos->currentText())
                    ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),true);
                else
                    ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),false);
            }
            else
                ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),false);

            for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                //元件
                if(ui->EdUnitTagSearch->text()!="")
                {
                    if(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdUnitTagSearch->text()))
                        ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),false);
                    else
                        ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),true);
                }
                else
                {
                    ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),false);
                }


                for(int m=0;m<ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//功能子块
                {
                    if(ui->CbUnitPage->currentText()!="页")
                    {
                        //查看当前功能子块是否在所筛选页面上
                        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString();
                        QuerySymbol.exec(SqlStr);
                        if(QuerySymbol.next())
                        {
                            if(QuerySymbol.value("Page_ID").toString()!="")
                            {
                                if(GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt())==ui->CbUnitPage->currentText())
                                    ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                else
                                    ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                            }
                            else
                                ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                        }
                        else
                            ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                    }
                    else
                    {
                        ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                    }
                }
            }
        }
    }

    //隐藏没有功能子块的节点
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
            {
                bool AllHide=true;
                for(int m=0;m<ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewUnits->isRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewUnits->isRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//高层
    {
        bool AllHide=true;
        for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->rowCount();k++)//位置
        {
            if(!ui->treeViewUnits->isRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelUnits->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),true);
    }
}

void MainWindow::FilterPage()
{
    if(ModelPages->rowCount()<=0) return;

    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")
        {
            if(ui->CbPageGaocengFilter->currentText()!="高层")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbPageGaocengFilter->currentText())
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                else
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
            }
            else
                ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
        }
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")
        {
            if(ui->CbPagePosFilter->currentText()!="位置")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbPagePosFilter->currentText())
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                else
                {
                    if((ui->CbPageGaocengFilter->currentText()=="高层")||(ui->CbPageGaocengFilter->currentText()==""))
                        ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                    else
                        ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                }
            }
            else
            {
                if((ui->CbPageGaocengFilter->currentText()=="高层")||(ui->CbPageGaocengFilter->currentText()==""))
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                else
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
        }
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="图纸")
        {
            bool TypeNotSame=false;
            if(ModelPages->item(0,0)->data(Qt::WhatsThisRole).toString()=="列表")
            {
                if(ModelPages->item(0,0)->data(Qt::DisplayRole).toString()==ui->CbPageTypeFilter->currentText()) TypeNotSame=false;
                else TypeNotSame=true;
            }
            else
            {
                if(ui->CbPageTypeFilter->currentText()=="原理图") TypeNotSame=false;
                else TypeNotSame=true;
            }
            if(ui->CbPageTypeFilter->currentText()!="类型"&&TypeNotSame)
            {
                ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
            else//需要显示出来
            {
                bool ShouldHide=false;
                if((ui->CbPageGaocengFilter->currentText()!="高层")&&(ui->CbPageGaocengFilter->currentText()!="")) ShouldHide=true;
                if((ui->CbPagePosFilter->currentText()!="位置")&&(ui->CbPagePosFilter->currentText()!="")) ShouldHide=true;
                if(!ShouldHide)
                {
                    if(ui->EdPageFilter->text()!="")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                            ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                    }
                    else
                        ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                }
                else ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
        }
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="列表")
        {
            if((ui->CbPageTypeFilter->currentText()!="类型")&&(ui->CbPageTypeFilter->currentText()!=ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()))
                ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            else
            {
                bool ShouldHide=false;
                if((ui->CbPageGaocengFilter->currentText()!="高层")&&(ui->CbPageGaocengFilter->currentText()!="")) ShouldHide=true;
                if((ui->CbPagePosFilter->currentText()!="位置")&&(ui->CbPagePosFilter->currentText()!="")) ShouldHide=true;
                if(!ShouldHide) ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                else ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
        }

        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="位置")
            {
                if(ui->CbPagePosFilter->currentText()!="位置")
                {
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbPagePosFilter->currentText())
                        ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    else
                        ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                }
                else
                    ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
            }
            else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="图纸")
            {
                //必须满足高层为空或者位置为空，非空的已经经过筛选
                bool TypeNotSame=false;
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="列表")
                {
                    if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==ui->CbPageTypeFilter->currentText()) TypeNotSame=false;
                    else TypeNotSame=true;
                }
                else
                {
                    if(ui->CbPageTypeFilter->currentText()=="原理图") TypeNotSame=false;
                    else TypeNotSame=true;
                }

                if((ui->CbPageTypeFilter->currentText()!="类型")&&TypeNotSame)
                    ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                else
                {
                    bool DwgNameOk=true;
                    if(ui->EdPageFilter->text()!="")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                            DwgNameOk=true;
                        else
                            DwgNameOk=false;
                    }
                    else DwgNameOk=true;

                    if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")//高层不为空，位置为空
                    {
                        if((ui->CbPagePosFilter->currentText()=="位置")||(ui->CbPagePosFilter->currentText()==""))
                        {
                            if(DwgNameOk)
                                ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                            else
                                ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                        }
                        else
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    }
                    else
                    {
                        if(DwgNameOk)
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    }
                }
            }
            else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表")
            {
                if((ui->CbPageTypeFilter->currentText()!="类型")&&(ui->CbPageTypeFilter->currentText()!=ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()))
                    ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                else
                {
                    if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")//高层不为空，位置为空
                    {
                        if((ui->CbPagePosFilter->currentText()=="位置")||(ui->CbPagePosFilter->currentText()==""))
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    }
                    else
                        ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                }
            }

            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()=="图纸")
                {
                    bool TypeNotSame=false;
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()==ui->CbPageTypeFilter->currentText()) TypeNotSame=false;
                        else TypeNotSame=true;
                    }
                    else
                    {
                        if(ui->CbPageTypeFilter->currentText()=="原理图") TypeNotSame=false;
                        else TypeNotSame=true;
                    }

                    bool DwgNameOk=true;
                    if(ui->EdPageFilter->text()!="")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                            DwgNameOk=true;
                        else
                            DwgNameOk=false;
                    }
                    else DwgNameOk=true;

                    if((ui->CbPageTypeFilter->currentText()!="类型")&&TypeNotSame)
                        ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
                    else
                    {
                        if(DwgNameOk)
                            ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
                    }
                }
                else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()=="列表")
                {
                    if((ui->CbPageTypeFilter->currentText()!="类型")&&(ui->CbPageTypeFilter->currentText()!=ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString()))
                        ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
                    else
                        ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),false);
                    for(int m=0;m<ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::WhatsThisRole).toString()=="图纸")
                        {
                            bool DwgNameOk=true;
                            if(ui->EdPageFilter->text()!="")
                            {
                                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                                    DwgNameOk=true;
                                else
                                    DwgNameOk=false;
                            }
                            else DwgNameOk=true;

                            if(DwgNameOk) ui->treeViewPages->setRowHidden(m,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                            else ui->treeViewPages->setRowHidden(m,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                        }
                    }
                }
            }
        }
    }

    //隐藏没有图纸的节点
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//列表
            {
                bool AllHide=true;
                for(int m=0;m<ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewPages->isRowHidden(m,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewPages->isRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        bool AllHide=true;
        for(int k=0;k<ModelPages->item(0,0)->child(i,0)->rowCount();k++)
        {
            if(!ui->treeViewPages->isRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelPages->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
    }
}

void MainWindow::AddIndexToIndex(QStandardItem *FatherItem,QSqlQuery query,bool AddProjectStructure_ID,QString Type)
{
    QStandardItem *SubItem;
    if(Type=="分组") SubItem=new QStandardItem(QIcon("C:/TBD/data/列表图标.png"),query.value("Structure_INT").toString());
    else if(Type=="位置") SubItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),query.value("Structure_INT").toString());
    else if(Type=="高层") SubItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),query.value("Structure_INT").toString());
    else if(Type=="项目") SubItem=new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),query.value("Structure_INT").toString());

    if(AddProjectStructure_ID)  SubItem->setData(QVariant(query.value("ProjectStructure_ID").toInt()),Qt::UserRole);
    SubItem->setData(QVariant(Type),Qt::WhatsThisRole);
    
    // 为结构节点设置 tooltip，显示描述信息
    QString desc = query.value("Struct_Desc").toString().trimmed();
    if(!desc.isEmpty()) {
        SubItem->setToolTip(desc);
    }
    
    FatherItem->appendRow(SubItem);
}
void MainWindow::AddDwgFileToIndex(QStandardItem *item,QSqlQuery query,QList<int> listPagesExpend)
{
    QString pageName = query.value("PageName").toString();
    QString pageDesc = query.value("Page_Desc").toString();
    QStandardItem *SubFatherItem = new QStandardItem(QIcon("C:/TBD/data/dwg图标.png"), pageName);
    // 把页描述作为项的悬停提示（ToolTip）显示，同时也设置ToolTipRole以便其它地方访问
    SubFatherItem->setToolTip(pageDesc);
    SubFatherItem->setData(QVariant(pageDesc), Qt::ToolTipRole);
    //图纸名称：PageName.dwg
    SubFatherItem->setData(QVariant("图纸"),Qt::WhatsThisRole);
    SubFatherItem->setData(QVariant(query.value("Page_ID").toInt()),Qt::UserRole);
    //添加到报表前面去
    int InsertRowIndex=-1;
    for(int k=0;k<item->rowCount();k++)
    {
        if(item->child(k,0)->data(Qt::WhatsThisRole).toString()=="列表")
        {
            InsertRowIndex=k;
            break;
        }
    }
    if(InsertRowIndex>=0) item->insertRow(InsertRowIndex,SubFatherItem);
    else item->appendRow(SubFatherItem);

    for(int i=0;i<listPagesExpend.count();i++)
    {
        if(listPagesExpend.at(i)==query.value("ProjectStructure_ID").toInt())
        {
            ui->treeViewPages->expand(item->index());
            break;
        }
    }
    if(SelectPage_ID==query.value("Page_ID").toInt()) ui->treeViewPages->setCurrentIndex(SubFatherItem->index());
}
void MainWindow::on_BtnNavigatorShow_clicked()
{
    ui->widgetNavigator->setVisible(true);
}

void MainWindow::on_BtnCloseNavigator_clicked()
{
    ui->widgetNavigator->setVisible(false);
}

void MainWindow::on_BtnNewProject_clicked()
{
    //建立后缀名为.swPro的文本文件
    DialogNewProject *dlgNewProject=new DialogNewProject(this);
    dlgNewProject->move(QApplication::desktop()->screenGeometry().width()/2-dlgNewProject->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgNewProject->height()/2);
    dlgNewProject->setModal(true);
    dlgNewProject->show();
    dlgNewProject->exec();
    if(dlgNewProject->Canceled) return;
    //dlgNewProject->ProjectPath,ProjectName
    CurProjectName=dlgNewProject->ProjectName;
    CurProjectPath=dlgNewProject->ProjectPath;
    LoadProject();
    delete dlgNewProject;
}

QStringList MainWindow::selectSystemUnitStripLineInfo()
{
    QStringList ListUnitStrip;
    QStringList ListUnitStripLineInfo;
    //得到器件清单 和 连接列表
    QSqlQuery QueryJXB(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(SqlStr);
    while(QueryJXB.next())
    {
        for(int index=0;index<2;index++)
        {
            QString Symb_ID;
            if(index==0) Symb_ID=QueryJXB.value("Symb1_ID").toString();
            else if(index==1) Symb_ID=QueryJXB.value("Symb2_ID").toString();
            if(Symb_ID=="") continue;
            if(Symb_ID.contains(":C")||Symb_ID.contains(":G")||Symb_ID.contains(":1")||Symb_ID.contains(":2")||Symb_ID.contains(":3")) continue;
            QString Symb_Category;
            if(index==0) Symb_Category=QueryJXB.value("Symb1_Category").toString();
            else if(index==1) Symb_Category=QueryJXB.value("Symb2_Category").toString();
            //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表

            //找到Symb_ID对应的器件
            QString DT;
            int UnitStripID=GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
            bool UnitStripExisted=false;
            for(int i=0;i<ListUnitStrip.count();i++)//这里可能存在器件与端子排ID的重复
            {
                QString id=ListUnitStrip.at(i).split(",").at(0);
                QString category=ListUnitStrip.at(i).split(",").at(1);
                if((id==QString::number(UnitStripID))&&(category==Symb_Category)) UnitStripExisted=true;
            }
            if(!UnitStripExisted)
            {
                ListUnitStrip.append(QString::number(UnitStripID)+","+Symb_Category);
                QString UnitStripLineInfo;
                QSqlQuery QuerySearch(T_ProjectDatabase);
                if(Symb_Category=="0")
                {
                    SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(UnitStripID);
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        UnitStripLineInfo=QuerySearch.value("Name").toString()+" "+DT;
                        SqlStr="SELECT * FROM EquipmentDiagnosePara WHERE Equipment_ID= '"+QString::number(UnitStripID)+"'";
                        QuerySearch.exec(SqlStr);
                        QString StrParameter;
                        while(QuerySearch.next())
                        {
                            if(StrParameter!="") StrParameter+=",";
                            StrParameter+=QuerySearch.value("Name").toString()+"="+QuerySearch.value("CurValue").toString()+QuerySearch.value("Unit").toString();
                        }
                        UnitStripLineInfo+="("+StrParameter+")";
                    }
                }
                else if(Symb_Category=="1")
                {
                    UnitStripLineInfo="端子排 "+DT;
                    SqlStr="SELECT * FROM TerminalStripDiagnosePara WHERE TerminalStrip_ID= '"+QString::number(UnitStripID)+"'";
                    QuerySearch.exec(SqlStr);
                    QString StrParameter;
                    while(QuerySearch.next())
                    {
                        if(StrParameter!="") StrParameter+=",";
                        StrParameter+=QuerySearch.value("Name").toString()+"="+QuerySearch.value("CurValue").toString()+QuerySearch.value("Unit").toString();
                    }
                    UnitStripLineInfo+="("+StrParameter+")";
                }
                ListUnitStripLineInfo.append(UnitStripLineInfo);
            }
        }//for(int index=0;index<2;index++)
        ListUnitStrip.append(QueryJXB.value("JXB_ID").toString()+",2");//添加导线
        ListUnitStripLineInfo.append("导线 "+QueryJXB.value("ConnectionNumber").toString()+"(MaxCurrent=20A,Resistance=0)");
    }
    return ListUnitStripLineInfo;
}

QStringList MainWindow::selectSystemConnections()
{
    QStringList ListConnections;
    QSqlQuery QueryJXB(T_ProjectDatabase);//设置数据库选择模型
    QSqlQuery QuerySearch(T_ProjectDatabase);
    QString SqlStr = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(SqlStr);
    while(QueryJXB.next())
    {
        for(int index=0;index<2;index++)
        {
            QString ConnectionStr="";
            QString Symb_ID;
            if(index==0) Symb_ID=QueryJXB.value("Symb1_ID").toString();
            else if(index==1) Symb_ID=QueryJXB.value("Symb2_ID").toString();
            if(Symb_ID.contains(":C")||Symb_ID.contains(":G")||Symb_ID.contains(":1")||Symb_ID.contains(":2")||Symb_ID.contains(":3")) continue;
            QString Symb_Category;
            if(index==0) Symb_Category=QueryJXB.value("Symb1_Category").toString();
            else if(index==1) Symb_Category=QueryJXB.value("Symb2_Category").toString();
            //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表

            //找到Symb_ID对应的器件
            QString DT;
            GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
            QString TermStr;
            if(Symb_Category=="0")
            {
                QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb_ID;
                QuerySearch.exec(StrSql);
                if(QuerySearch.next()) TermStr=QuerySearch.value("ConnNum").toString();
            }
            else if(Symb_Category=="1")
            {
                QString StrSql="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+Symb_ID;
                QuerySearch.exec(StrSql);
                if(QuerySearch.next()) TermStr=QuerySearch.value("ConnNum").toString();
            }
            ConnectionStr=QueryJXB.value("ConnectionNumber").toString()+"."+QString::number(index+1)+","+DT+"."+TermStr;
            //查找有没有其他连接到同一个节点的端口
            SqlStr="SELECT * FROM JXB WHERE Symb1_ID = '"+Symb_ID+"' AND Symb1_Category = '"+Symb_Category+"' AND JXB_ID <> "+QueryJXB.value("JXB_ID").toString();
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                ConnectionStr+=","+QuerySearch.value("ConnectionNumber").toString()+".1";
            }
            SqlStr="SELECT * FROM JXB WHERE Symb2_ID = '"+Symb_ID+"' AND Symb2_Category = '"+Symb_Category+"' AND JXB_ID <> "+QueryJXB.value("JXB_ID").toString();
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                ConnectionStr+=","+QuerySearch.value("ConnectionNumber").toString()+".2";
            }
            ListConnections.append("connect"+QString::number(ConnectionStr.split(",").count())+"e("+ConnectionStr+")");
        }//for(int index=0;index<2;index++)
    }
    return ListConnections;
}

void MainWindow::LoadProjectSystemDescription()
{
    ui->textEditSystemDiscription->clear();
    QStringList ListEquipmentsInfo=selectSystemUnitStripLineInfo();
    QStringList ListSystemConnections=selectSystemConnections();
    QString SystemDescription="DEF BEGIN\n";
    for(QString EquipmentsInfo:ListEquipmentsInfo) SystemDescription+=EquipmentsInfo+"\n";
    SystemDescription+="DEF END\n\n";
    for(QString SystemConnections:ListSystemConnections) SystemDescription+=SystemConnections+"\n";
    ui->textEditSystemDiscription->setText(SystemDescription);
}

void MainWindow::LoadModel()
{
    //移除功能管理Tab中的QTreeWidget
    QLayout *layout = ui->widget_func->layout();
    if (layout != nullptr) {
        QLayoutItem *item;
        while ((item = layout->takeAt(0)) != nullptr) {
            delete item->widget(); // 删除控件
            delete item;           // 删除布局项
        }
    }
    const QString projectDbPath = CurProjectPath + "/" + CurProjectName + ".db";
    //连接统一项目数据库
    database = new SQliteDatabase(projectDbPath);
    if(!database->connect()){
        QMessageBox::information(nullptr, "Tips", "数据库连接失败！",QMessageBox::Yes);
    }

    systemEntity = new SystemEntity(database);
    systemEntity->setMainWindow(this);
    systemEntity->setCurrentModel(&currentModel);

    //=========================open model============
    currentModelName = "QBT";
    currentModel = database->selectModelByName(currentModelName);
    QString systemDescription = currentModel.getSystemDescription();
    ui->textEditSystemDiscription->setText(systemDescription);
    //qDebug()<<"systemDescription="<<systemDescription;
    functionDescription = currentModel.getFunctionDiscription();
    //qDebug()<<"functionDescription="<<functionDescription;
    systemEntity->updateObsVarsMap(systemEntity->prepareModel(systemDescription));
    //QString savedObsCode= currentModel.getTestDiscription();
    //ui->textEditTestDiscription->setText(savedObsCode);

    pDlgSelectFunctionDialog = new SelectFunctionDialog(systemEntity, systemDescription,functionDescription,this);
    pDlgSelectFunctionDialog->hide();
    UpdateFuncTree();
}

void MainWindow::UpdateFuncTree()
{
    QLayout *layout = ui->widget_func->layout();
    if (layout == nullptr) {
        layout = new QVBoxLayout;
        ui->widget_func->setLayout(layout);
    }
    layout->addWidget(pDlgSelectFunctionDialog->GetTreeWidget());
}

void MainWindow::initializeMxModules()
{
    static bool initialized = false;
    if (initialized) {
        return;
    }

    QAxObject object("{4FF8F5E1-8D85-45CC-B58E-BE1CF4A5C3EC}");
    object.dynamicCall("InitMxDrawOcx(const QString&,const QString&,const QString&,const QString&,const QString&)", "",
                       QString::fromLocal8Bit("中国船舶重工集团公司第704研究所"),
                       QString::fromLocal8Bit("电液系统"), "0510-83078024",
                       "010ADE5E0DA2A305784A00001F22E8014E9A9FCF5957272AA51F7EA69E974AA5D173220AB9865714670FA0B2ED850000060A177AE70EC20BB6BE0000242ABDE1218C1C87E1F84B3CFA9D1A5FB7E0B8C0A8702F347CEEE340D84B85CBAB639EADA5C7717953A30000262A75D1DCB40BDD2D638097969BF91CB4EFC96862F3DB91F7D7292C97D270AD6EBC8EC0EFB13063444100001A22E98792BAD32A4231E8E85A70D588C1B7B782224023E9D27CD844ED721BC9F99D00000D120712AC0F10BFC62E976BEF515415B18F0000080AB8CA9D8405892A7C0000");

    const QStringList iniOptions = {
        "EnableUndo=Y",
        "DisplayPrecision=500",
        "EnablePropertyWindow=N",
        "NOSHOWBOORDER=Y",
        "DrawGridLine=Y",
        "EnableClipboard=Y",
        "EnableSingleSelection=Y",
        "EnableDeleteKey=N",
        "IsHighQualityTTf=Y",
        "ObjectModifyEvent=Y",
        "DynamicHighlight=Y",
        "ISDISABLEEDITTEXT=Y"
    };
    object.dynamicCall("IniSet(const QString&)", iniOptions.join(","));

    if (!GlobalBackAxWidget) {
        GlobalBackAxWidget = new QAxWidget("{74A777F8-7A8F-4E7C-AF47-7074828086E2}");
    }

    if (!pApp) {
        auto *mxApp = new MxDrawApplication();
        pApp = reinterpret_cast<IMxDrawApplication *>(mxApp);
    }

    if (!dlgLoadSymbol) {
        dlgLoadSymbol = new DialogLoadSymbol(this);
    }
    if (!dlgDialogSymbols) {
        dlgDialogSymbols = new DialogSymbols(this);
    }

    const QString dwgPath = "C:/TBD/SPS/SPS_CDP.dwg";
    const QString jpgPath = "C:/TBD/data/TempImage/SPS_CDP.jpg";
    const QFileInfo dwgInfo(dwgPath);
    const QFileInfo jpgInfo(jpgPath);
    if (dwgInfo.exists()) {
        if (!jpgInfo.exists() || dwgInfo.lastModified() > jpgInfo.lastModified()) {
            pApp->dynamicCall("DwgToJpg(QString,QString,int,int)", dwgPath, jpgPath, 150, 85);
        }
    } else {
        qWarning() << "DWG file not found:" << dwgPath;
    }

    initialized = true;
}

void MainWindow::initAfterShow()
{
    initializeMxModules();
    LoadLastOpenedProject();
}

void MainWindow::LoadProject()
{
    qDebug()<<"CurProjectPath="<<CurProjectPath;
    qDebug()<<"CurProjectName="<<CurProjectName;
    if(T_ProjectDatabase.isOpen()) T_ProjectDatabase.close();
    T_ProjectDatabase = QSqlDatabase::addDatabase("QSQLITE",CurProjectName);
    QFile  File(CurProjectPath+"/"+CurProjectName+".db");
    if(!File.exists()){
        QMessageBox::warning(nullptr, "错误", "数据库文件不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return ;
    }
    else
        T_ProjectDatabase.setDatabaseName(CurProjectPath+"/"+CurProjectName+".db");
    if (!T_ProjectDatabase.open()){
        QMessageBox::warning(nullptr, "错误", "打开数据库失败",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return ;
    }
    ui->LbProjectName->setText("项目导航器（"+CurProjectName+"）");
    LoadProjectPages();
    LoadProjectUnits();
    LoadProjectTerminals();
    LoadProjectLines();

    //更新历史工程记录
    QString StrDir=LocalDataBasePath;
    QFile HisProFilePath(StrDir+"/历史工程记录.dat");
    if(!HisProFilePath.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    QStringList ListHisFile;
    ListHisFile.append(CurProjectPath+"/"+CurProjectName+".swPro");
    QTextStream txtInput(&HisProFilePath);
    txtInput.setCodec("UTF-8");
    while(!txtInput.atEnd())
    {
        QString CurLineText=txtInput.readLine();
        if(CurLineText==(CurProjectPath+"/"+CurProjectName+".swPro")) continue;
        if(CurLineText=="") continue;
        ListHisFile.append(CurLineText);
    }
    HisProFilePath.close();
    qDebug()<<"ListHisFile="<<ListHisFile;
    if(!HisProFilePath.open(QIODevice::WriteOnly | QIODevice::Text| QIODevice::Truncate)) return;
    QTextStream txtOutput(&HisProFilePath);
    txtOutput.setCodec("UTF-8");
    txtOutput.setGenerateByteOrderMark(true);
    for(int i=0;i<ListHisFile.count();i++)
    {
        if(i==10) break;
        txtOutput<<ListHisFile.at(i)<<"\n";
    }
    txtOutput.flush();
    HisProFilePath.close();

    LoadModel();
}

void MainWindow::createDemoProject()
{
    const QString projectName = QString("DemoWorkflow");
    const QString projectDir = QString("%1/%2").arg(QString(LocalProjectDefaultPath), projectName);

    QString error;
    if (!DemoProjectBuilder::buildDemoProject(projectDir, projectName, &error)) {
        QMessageBox::warning(this, tr("演示项目生成失败"), error);
        qDebug()<<"演示项目生成失败:"<<error;
        return;
    }

    if (T_ProjectDatabase.isOpen()) {
        const QString connName = T_ProjectDatabase.connectionName();
        T_ProjectDatabase.close();
        QSqlDatabase::removeDatabase(connName);
    }

    QDir dataDir(QString(LocalDataBasePath));
    if (!dataDir.exists())
        dataDir.mkpath(QString("."));
    QFile historyFile(dataDir.filePath(QString("历史工程记录.dat")));
    if (!historyFile.exists()) {
        if (historyFile.open(QIODevice::WriteOnly | QIODevice::Text | QIODevice::Truncate)) {
            QTextStream historyStream(&historyFile);
            historyStream.setCodec("UTF-8");
            historyStream.setGenerateByteOrderMark(true);
            historyStream.flush();
            historyFile.close();
        }
    }

    CurProjectPath = projectDir;
    CurProjectName = projectName;

    LoadProject();

    QMessageBox::information(this,
                             tr("演示项目已创建"),
                             tr("已在 %1 创建并加载演示项目，您可以按照 workflow_demo.md 的步骤体验完整流程。")
                                 .arg(projectDir));
}

void MainWindow::LoadLastOpenedProject()
{
    QString StrDir=LocalDataBasePath;
    QFile HisProFilePath(StrDir+"/历史工程记录.dat");
    if(!HisProFilePath.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    QTextStream txtInput(&HisProFilePath);
    txtInput.setCodec("UTF-8");
    CurProjectName=txtInput.readLine();//读取第一行
    HisProFilePath.close();

    //CurProjectName:C:/TBD/MyProjects/测试系统5/测试系统5.swPro
    QFile LastProFilePath(CurProjectName);
    if(!LastProFilePath.exists()) return;
    int Index=CurProjectName.lastIndexOf("/");
    CurProjectPath=CurProjectName.mid(0,Index);
    CurProjectName=CurProjectName.mid(Index+1,CurProjectName.lastIndexOf(".swPro")-Index-1);
    LoadProject();
}

void MainWindow::on_BtnOpenProject_clicked()
{
    /*
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
       ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->dwgFileName);
    }*/
    if(ui->mdiArea->subWindowList().count()>0)
    {
        QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否关闭所有打开的图纸?",
                                                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

        if(result==QMessageBox::Yes)
        {
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                ui->mdiArea->subWindowList().at(i)->close();
            }
        }
    }
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("打开文件"));
    fileDialog.setDirectory(LocalProjectDefaultPath);
    fileDialog.setNameFilter(tr("swPro(*.swPro)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    QString swProPath = fileNames.at(0);
    int Index = swProPath.lastIndexOf("/");
    CurProjectPath = swProPath.mid(0, Index);
    int dotIndex = swProPath.lastIndexOf(".swPro");
    CurProjectName = swProPath.mid(Index + 1, dotIndex - Index - 1);
    LoadProject();
}
void MainWindow::CloseMdiWnd(int Mode)
{
    qDebug()<<"CloseMdiWnd,Mode="<<Mode;
    formaxwidget *dlg=(formaxwidget *)sender();

    dlg->mdisubwindow->close();
    //如果Mode=1,删除dwg文件，打开符号库
    if(Mode==1)
    {
        qDebug()<<"Mode=1,删除dwg文件，打开符号库,SymbolName="<<dlg->SymbolName;
        QString DwgFileName="C:/TBD/SYMB2LIB/"+dlg->SymbolName;
        qDebug()<<"delete file";
        QFile file(DwgFileName);
        if(file.exists()) file.remove();
    }
    //if(Mode==0||Mode==1) on_BtnSymbolBaseManage_clicked();
}

QString MainWindow::resolvePageFilePath(const QString &displayName) const
{
    const QStringList candidates = PageNameCandidates(displayName);
    for (const QString &candidate : candidates) {
        QFileInfo info(CurProjectPath + "/" + candidate + ".dwg");
        if (info.exists())
            return info.absoluteFilePath();
    }

    const QString baseName = ExtractPageBaseName(displayName);
    if (!baseName.isEmpty()) {
        QFileInfo baseInfo(CurProjectPath + "/" + baseName + ".dwg");
        if (baseInfo.exists())
            return baseInfo.absoluteFilePath();
    }

    QDir dir(CurProjectPath);
    const QStringList files = dir.entryList(QStringList() << "*.dwg", QDir::Files);
    for (const QString &fileName : files) {
        QFileInfo info(dir.absoluteFilePath(fileName));
        const QString stem = info.completeBaseName();
        if (stem == displayName || (!baseName.isEmpty() && stem == baseName))
            return info.absoluteFilePath();

        const QStringList stemCandidates = PageNameCandidates(stem);
        if (stemCandidates.contains(displayName) || (!baseName.isEmpty() && stemCandidates.contains(baseName)))
            return info.absoluteFilePath();
    }

    return QString();
}

void MainWindow::OpenDwgPageByPageID(int PageID)
{
    const QString dwgDisplayName = GetPageNameByPageID(PageID);
    const QString dwgfilepath = resolvePageFilePath(dwgDisplayName);
    if (dwgfilepath.isEmpty()) return;
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgDisplayName)
        {
            ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
            return;
        }
    }
    //创建新的mdi
    formaxwidget *formMxdraw=new formaxwidget(this,dwgfilepath,PageID);
    formMxdraw->setWindowTitle(dwgDisplayName);
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
    connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
    connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
    connect(formMxdraw,SIGNAL(SigalShowSpurAttr(int)),this,SLOT(ShowSpurAttr(int)));
    connect(formMxdraw,SIGNAL(SigalShowTerminalAttr(int,int)),this,SLOT(ShowTerminalAttr(int,int)));
    connect(formMxdraw,SIGNAL(UpdateCounterLink(int,QString)),this,SLOT(updateCounterLink(int,QString)));
    connect(formMxdraw,SIGNAL(SignalUpdateSpur(int)),this,SLOT(UpdateSpurBySymbol_ID(int)));
    connect(formMxdraw,SIGNAL(SignalUpdateTerminal(int)),this,SLOT(UpdateTerminalByTerminal_ID(int)));
    connect(formMxdraw,SIGNAL(ConnectLinesChanged(int)),this,SLOT(handleConnectLinesChanged(int)));
}

//单击鼠标左键预览图纸，双击鼠标左键打开图纸
void MainWindow::on_treeViewPages_doubleClicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    qDebug()<<index.data(Qt::WhatsThisRole).toString();
    qDebug()<<"UserRole="<<index.data(Qt::UserRole).toInt();
    if(index.data(Qt::WhatsThisRole).toString()!="图纸") return;
    int Page_ID=index.data(Qt::UserRole).toInt();
    OpenDwgPageByPageID(Page_ID);
}

void MainWindow::on_treeViewPages_clicked(const QModelIndex &index)
{
    if(!ui->widgetPreView->isVisible()) return;
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="图纸") return;
    int Page_ID=index.data(Qt::UserRole).toInt();
    QString dwgfilename=GetPageNameByPageID(Page_ID);

    const QString path=resolvePageFilePath(dwgfilename);
    qDebug()<<"path="<<path;
    if(path.isEmpty()) return;
    QFileInfo file(path);
    if(!file.exists()) return;
    ui->axWidgetPreview->dynamicCall("OpenDwgFile(QString)",path);
    ui->axWidgetPreview->dynamicCall("ZoomAll()");
}

void MainWindow::on_Btn_SymbolLoad_clicked()
{
    dlgLoadSymbol->Canceled=true;
    dlgLoadSymbol->move(this->width()-dlgLoadSymbol->width()-20,50);
    dlgLoadSymbol->show();
    //QApplication::processEvents();
    dlgLoadSymbol->exec();
    if(dlgLoadSymbol->Canceled) return;
    if(dlgLoadSymbol->RetCode!=3)  return;//载入当前符号

    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->SymbolLoad(dlgLoadSymbol->BlockFileName,dlgLoadSymbol->SymbolID);
    }
}

void MainWindow::UpdateSymbolLib(QString CurSelectSymb2Class_ID)
{
    dlgDialogSymbols->LoadModelFromDB(CurSelectSymb2Class_ID);
}

void MainWindow::SlotSetCurMdiActive()
{
    formaxwidget *formMxdraw=(formaxwidget *)sender();
    ui->mdiArea->setActiveSubWindow(formMxdraw->mdisubwindow);
}

void MainWindow::SlotNewSymbol(int Mode)//0:取消 1：选择有效
{
    //创建新的mdi
    if(Mode==0)
    {
        on_BtnSymbolBaseManage_clicked();
        return;
    }
    qDebug()<<"SlotNewSymbol";
    formaxwidget *formMxdraw=new formaxwidget(this);
    formMxdraw->setWindowTitle(dlgDialogSymbols->Symb2_Name);
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
    connect(formMxdraw,SIGNAL(SignalUpdateSymbolLib(QString)),this,SLOT(UpdateSymbolLib(QString)));
    connect(formMxdraw,SIGNAL(SignalSetCurMdiActive()),this,SLOT(SlotSetCurMdiActive()));
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    qDebug()<<"SymbolName="<<dlgDialogSymbols->Symb2_Name+".dwg";
    formMxdraw->SymbolName=dlgDialogSymbols->Symb2_Name+".dwg";
    formMxdraw->DataBaseSymbolID="";
    formMxdraw->SymbolType=dlgDialogSymbols->SymbolType;
    formMxdraw->FunctionDefineClass_ID=dlgDialogSymbols->FunctionDefineClass_ID;
    formMxdraw->EditSymbol();

    qDebug()<<"end SlotNewSymbol";
}

void MainWindow::on_BtnSymbolBaseManage_clicked()
{
    //connect(&dlgDialogSymbols,SIGNAL(SignalUpdateLib()),this,SLOT(UpdateSymbolLib()));
    dlgDialogSymbols->setModal(true);
    dlgDialogSymbols->Canceled=true;
    dlgDialogSymbols->RetCode=2;
    dlgDialogSymbols->show();
    dlgDialogSymbols->exec();
    if(dlgDialogSymbols->Canceled) return;
    qDebug()<<"dlgDialogSymbols->RetCode="<<dlgDialogSymbols->RetCode;
    if(dlgDialogSymbols->RetCode==1) //修改符号
    {
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this);
        formMxdraw->setWindowTitle(dlgDialogSymbols->BlockFileName);
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        formMxdraw->SymbolName=dlgDialogSymbols->BlockFileName;
        formMxdraw->DataBaseSymbolID=dlgDialogSymbols->SymbolID;
        qDebug()<<"DataBaseSymbolID="<<formMxdraw->DataBaseSymbolID;
        formMxdraw->SymbolType=dlgDialogSymbols->SymbolType;
        formMxdraw->EditSymbol();
    }
    else if(dlgDialogSymbols->RetCode==3) //增加库文件
    {
        //在现有的窗口中选择图形
        if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
        {
            formaxwidget *formMdi;
            formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
            if(formMdi!=nullptr)
            {
                connect(formMdi,SIGNAL(SignalSelectDone(int)),this,SLOT(SlotNewSymbol(int)));
                formMdi->NewSymbolDwgName=dlgDialogSymbols->Symb2_Name+".dwg";
                formMdi->SelectEntitys();
            }
        }
        else//没有打开的主窗口，直接新建
        {
            qDebug()<<"没有打开的主窗口，直接新建";
            QString SourceFileName="C:/TBD/data/SymbolTemplate.dwg";
            QString DestinationFileName="C:/TBD/SYMB2LIB/"+dlgDialogSymbols->Symb2_Name+".dwg";
            QFile::copy(SourceFileName,DestinationFileName);
            SlotNewSymbol(1);
        }
    }
}

void MainWindow::on_BtnLocalDB_clicked()
{

    dlgUnitManage->show();
    //dlgUnitManage->showMaximized();
    QApplication::processEvents();
}

void MainWindow::on_BtnShowHidePreViewWidget_clicked()
{
    if(ui->tabWidget_Navigator->currentIndex()==3) return;
    if(ShowPreViewWidget)
    {
        ShowPreViewWidget=false;
        ui->BtnShowHidePreViewWidget->setText("图形预览▲");
        ui->widgetPreView->setVisible(false);
    }
    else
    {
        ShowPreViewWidget=true;
        ui->BtnShowHidePreViewWidget->setText("图形预览▼");
        ui->widgetPreView->setVisible(true);
    }
}

void MainWindow::on_Btn_GeneratePageList_clicked()
{
    dlgGenerate.setWindowTitle("生成图纸目录");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(0);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        qDebug()<<"GetPageProjectStructure_IDByGaocengAndPos,"<<GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"图纸目录");
        StrSql= "SELECT * FROM Page WHERE PageType = '图纸目录' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"图纸目录")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '图纸目录'  AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"图纸目录")+"'";
        QueryPage.exec(StrSql);
    }
    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(0,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Page WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建图纸目录清单dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"TZML");
                SetCurLayer(GlobalBackAxWidget,"TZML");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"目录",10,0,0,2);//目录
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",59,264,"页名",7,0,1,2);//页名
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,271,99,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",174,264,"页描述",7,0,1,2);//页描述
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",249,271,249,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",282,264,"页类型",7,0,1,2);//页类型
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",315,271,315,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",349,264,"备注",7,0,1,2);//备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线6
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","图纸目录");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,GetPageNameByPageID(QueryPage.value("Page_ID").toInt()),3.5,0,0,2);//页名
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,Lasty,99,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",101,Lasty-3.5,QueryPage.value("Page_Desc").toString(),3.5,0,0,2);//页描述
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",249,Lasty,249,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",251,Lasty-3.5,QueryPage.value("PageType").toString(),3.5,0,0,2);//页类型
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",315,Lasty,315,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",317,Lasty-3.5,"",3.5,0,0,2);//备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    LoadProjectPages();
}

void MainWindow::on_Btn_GenerateUnitList_clicked()//元件列表
{
    dlgGenerate.setWindowTitle("生成元件列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(1);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '元件列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"元件列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '元件列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"元件列表")+"'";
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Equipment WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryEquipment.exec(StrSql);
        while(QueryEquipment.next())
        {
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"MXB");
                SetCurLayer(GlobalBackAxWidget,"MXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"元件列表",10,0,0,2);//元件列表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",44,264,"项目代号",7,0,1,2);//项目代号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",69,271,69,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",104,264,"型号",7,0,1,2);//型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",139,271,139,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",169,264,"名称",7,0,1,2);//名称
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,271,199,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",205,264,"数量",7,0,1,2);//数量
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",211,257,211,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",236,264,"厂家",7,0,1,2);//厂家
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",261,257,261,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",296,264,"部件编号",7,0,1,2);//部件编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,257,331,271);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",357,264,"元件备注",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线9
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","元件列表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
            QString UnitTag=QueryEquipment.value("DT").toString();
            QString UnitType=QueryEquipment.value("Type").toString();
            QString UnitName=QueryEquipment.value("Name").toString();
            //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
            QString UnitNameStr=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+UnitTag;

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,UnitNameStr,3.5,0,0,2);//项目代号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",69,Lasty,69,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",71,Lasty-3.5,UnitType,3.5,0,0,2);//型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",139,Lasty,139,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",141,Lasty-3.5,UnitName,3.5,0,0,2);//名称
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,Lasty,199,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",201,Lasty-3.5,"1",3.5,0,0,2);//数量
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",211,Lasty,211,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",213,Lasty-3.5,QueryEquipment.value("Factory").toString(),3.5,0,0,2);//厂家
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",261,Lasty,261,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",263,Lasty-3.5,QueryEquipment.value("PartCode").toString(),3.5,0,0,2);//部件编号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,Lasty,331,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",333,Lasty-3.5,QueryEquipment.value("Remark").toString(),3.5,0,0,2);//元件备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线9
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

//Mode=0:Page  Mode=1:连线、元件、端子等
QStringList MainWindow::GetAllIDFromProjectStructure(int Mode,QString StrGaoceng,QString StrPos,bool AllGaoceng,bool AllPos)
{
    //这里要区分是不是所有的高层或位置
    QStringList ListProjectStructure_ID;
    QString StrSql;
    QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    if(Mode==0)
    {
        StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '6'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            if(AllGaoceng)
            {
                if(AllPos)
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                }
                else
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE Structure_INT = '"+StrPos+"' AND ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                }
            }
            else
            {
                if(AllPos)
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next())
                    {
                        QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                        QuerySearchGaoceng.exec(StrSql);
                        if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                    }
                }
                else
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE Structure_INT = '"+StrPos+"' AND ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next())
                    {
                        QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                        QuerySearchGaoceng.exec(StrSql);
                        if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                    }
                }
            }
        }
    }
    else
    {
        if(AllGaoceng)
        {
            if(AllPos)
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5'";
                QueryPos.exec(StrSql);
                while(QueryPos.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
            }
            else
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+StrPos+"'";
                QueryPos.exec(StrSql);
                while(QueryPos.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
            }
        }
        else
        {
            if(AllPos)
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5'";
                QueryPos.exec(StrSql);
                while(QueryPos.next())
                {
                    QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                    QuerySearchGaoceng.exec(StrSql);
                    if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
                }
            }
            else
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+StrPos+"'";
                QueryPos.exec(StrSql);
                while(QueryPos.next())
                {
                    QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                    QuerySearchGaoceng.exec(StrSql);
                    if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
                }
            }
        }
    }
    return ListProjectStructure_ID;
}
void MainWindow::on_Btn_GenerateConnectList_clicked()//连接列表
{
    dlgGenerate.setWindowTitle("生成连接列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(4);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '连接列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"连接列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '连接列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"连接列表")+"'";
        QueryPage.exec(StrSql);
    }
    qDebug()<<"SELECT * FROM JXB";
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM JXB WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        qDebug()<<"StrSql="<<StrSql;
        QueryJXB.exec(StrSql);
        while(QueryJXB.next())
        {
            if(CurRecordIndex>CurPageNum*32)
            {
                if(CurPageNum>0) GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                qDebug()<<"PageName="<<PageName;
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                CreateLayer(GlobalBackAxWidget,"JXB");
                SetCurLayer(GlobalBackAxWidget,"JXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"连接列表",10,0,0,2);//元件列表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",16,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",26,271,26,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",41,264,"连接代号",7,0,1,2);//项目代号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",56,271,56,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",81,264,"源",7,0,1,2);//型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",106,271,106,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",131,264,"目标",7,0,1,2);//名称
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",156,271,156,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",177,264,"型号",7,0,1,2);//数量
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",198,257,198,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",214,264,"颜色",7,0,1,2);//厂家
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",230,257,230,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",246,264,"截面积/直径",7,0,1,2);//部件编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",262,257,262,271);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",287,264,"源区图号",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",312,257,312,271);//竖线9
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",337,264,"目标区图号",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",362,257,362,271);//竖线10
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",372,264,"备注",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",382,257,382,271);//竖线11
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","连接列表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString StrDT=QueryJXB.value("ConnectionNumber").toString();

            QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
            QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
            if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) continue;
            if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) continue;
            QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
            QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
            QString Symb1Str,Symb2Str;
            if(Symb1_Category=="0")//元件
                Symb1Str=GetUnitTermStrByTermID(Symb1_ID);
            else if(Symb1_Category=="1")//端子排
                Symb1Str=GetTerminalTermStrByTermID(Symb1_ID);
            if(Symb2_Category=="0")//元件
                Symb2Str=GetUnitTermStrByTermID(Symb2_ID);
            else if(Symb2_Category=="1")//端子排
                Symb2Str=GetTerminalTermStrByTermID(Symb2_ID);

            //根据源符号类型和目标符号类型进行检索确定区号
            QString SourcePageArea;
            QString DestinationPageArea;
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            if(Symb1_Category=="0")//符号
            {
                StrSql = QString("SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+Symb1_ID);//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                SourcePageArea=QuerySearch.value("PageArea").toString();
            }
            else if(Symb1_Category=="1")//端子
            {
                StrSql = QString("SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb1_ID);//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Terminal WHERE Terminal_ID = "+QuerySearch.value("Terminal_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                SourcePageArea=QuerySearch.value("PageArea").toString();
            }
            if(Symb2_Category=="0")//符号
            {
                StrSql = QString("SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+Symb2_ID);//目标符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                DestinationPageArea=QuerySearch.value("PageArea").toString();
            }
            else if(Symb2_Category=="1")//端子
            {
                StrSql = QString("SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb2_ID);//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Terminal WHERE Terminal_ID = "+QuerySearch.value("Terminal_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                DestinationPageArea=QuerySearch.value("PageArea").toString();
            }
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",26,Lasty,26,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",28,Lasty-3.5,StrDT,3.5,0,0,2);//连接代号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",56,Lasty,56,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",58,Lasty-3.5,Symb1Str,3.5,0,0,2);//源
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",106,Lasty,106,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",108,Lasty-3.5,Symb2Str,3.5,0,0,2);//目标
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",156,Lasty,156,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",158,Lasty-3.5,QueryJXB.value("Wires_Type").toString(),3.5,0,0,2);//型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",198,Lasty,198,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",200,Lasty-3.5,QueryJXB.value("Wires_Color").toString(),3.5,0,0,2);//颜色
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",230,Lasty,230,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",232,Lasty-3.5,QueryJXB.value("Wires_Diameter").toString(),3.5,0,0,2);//截面积/直径
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",262,Lasty,262,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",264,Lasty-3.5,SourcePageArea,3.5,0,0,2);//源区图号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",312,Lasty,312,Lasty-7);//竖线9
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",314,Lasty-3.5,DestinationPageArea,3.5,0,0,2);//目标区图号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",362,Lasty,362,Lasty-7);//竖线10
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",364,Lasty-3.5,"",3.5,0,0,2);//备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",382,Lasty,382,Lasty-7);//竖线11
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }

    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_Btn_GenerateTerminalList_clicked()//端子列表
{
    dlgGenerate.setWindowTitle("生成端子列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(3);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '端子列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"端子列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '端子列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"端子列表")+"'";
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM TerminalStrip WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryTerminalStrip.exec(StrSql);
        while(QueryTerminalStrip.next())
        {
            CurRecordIndex=1;
            QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            StrSql="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryTerminalStrip.value("TerminalStrip_ID").toString()+"'";
            QueryTerminal.exec(StrSql);
            int InitCurPageNum=CurPageNum;
            QStringList AddedTerminalID;
            AddedTerminalID.clear();
            while(QueryTerminal.next())
            {
                if(CurRecordIndex>(CurPageNum-InitCurPageNum)*32)
                {
                    PageName="";
                    if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                    if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                    if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                    PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                    //创建dwg文件
                    QFileInfo fileinfo(PageName);
                    if(fileinfo.exists())
                    {
                        QFile file(PageName);
                        file.remove();
                    }
                    QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                    QFile::copy(SourceFileName,PageName);
                    bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                    qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                    CreateLayer(GlobalBackAxWidget,"MXB");
                    SetCurLayer(GlobalBackAxWidget,"MXB");
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"端子列表",10,0,0,2);//端子列表
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,253,383,253);//横线2
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,253);//竖线1
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,271,383,253);//竖线2
                    QString TerminalStripTag=GetProjectStructureStrByProjectStructureID(QueryTerminalStrip.value("ProjectStructure_ID").toInt())+"-"+QueryTerminalStrip.value("DT").toString();
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",195,262,TerminalStripTag,7,0,1,2);//端子排项目代号
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,239,383,239);//横线3
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,253,7,239);//竖线1
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",22,246,"功能文本",7,0,1,2);//功能文本
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",37,253,37,239);//竖线2
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",60,246,"电缆编号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",83,253,83,239);//竖线3
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",108,246,"目标代号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",133,253,133,239);//竖线4
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",143,246,"连接点",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",153,253,153,239);//竖线5
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",164,246,"端子",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175,253,175,239);//竖线6
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",191,246,"短连接",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",207,253,207,239);//竖线7
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",232,246,"目标代号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",257,253,257,239);//竖线8
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",267,246,"连接点",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",277,253,277,239);//竖线9
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",300,246,"电缆编号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",323,253,323,239);//竖线10
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",353,246,"页/列",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,253,383,239);//竖线11
                    //GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                    int Page_ID=1;
                    QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                    QueryNewPage.exec(StrSql);
                    if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                    StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                      "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                    QueryNewPage.prepare(StrSql);
                    QueryNewPage.bindValue(":Page_ID",Page_ID);
                    QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                    QueryNewPage.bindValue(":Page_Desc","端子列表:"+TerminalStripTag);
                    QueryNewPage.bindValue(":PageType","端子列表");
                    QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                    QueryNewPage.bindValue(":Scale","1:1");
                    QueryNewPage.bindValue(":Border","A3:420x297");
                    QueryNewPage.bindValue(":Title","A3-zju.dwg");
                    QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                    QueryNewPage.exec();
                    Lasty=239;
                    CurPageNum++;
                }
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",22,Lasty-3.5,QueryTerminal.value("FunctionText").toString(),3.5,0,0,2);//功能文本

                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",37,Lasty,37,Lasty-7);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",83,Lasty,83,Lasty-7);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",133,Lasty,133,Lasty-7);//竖线4

                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",153,Lasty,153,Lasty-7);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",155,Lasty-3.5,QueryTerminal.value("Designation").toString(),3.5,0,0,2);//端子
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175,Lasty,175,Lasty-7);//竖线6
                //查看当前端子是否与上面的端子存在短接，存在则绘制短接线
                if(QueryTerminal.value("ShortJumper").toString()!="")
                {
                    qlonglong lID=GlobalBackAxWidget->dynamicCall("DrawCircle(double,double,double)",175+8*QueryTerminal.value("ShortJumper").toString().count(),Lasty-3.5,0.75).toLongLong();
                    IMxDrawCircle *LineCircle= (IMxDrawCircle*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
                    LineCircle->dynamicCall("setColorIndex(int)",McColor::mcYellow);
                    QSqlQuery QueryShortJump = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    double Internal=0;
                    for(int i=AddedTerminalID.count()-1;i>=0;i--)
                    {
                        Internal+=7;
                        StrSql = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryTerminalStrip.value("TerminalStrip_ID").toString()+"' AND ShortJumper = '"+QueryTerminal.value("ShortJumper").toString()+"' AND Terminal_ID = "+AddedTerminalID.at(i);
                        QueryShortJump.exec(StrSql);
                        if(QueryShortJump.next())
                        {
                            //绘制短接线
                            qlonglong lID=GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175+8*QueryTerminal.value("ShortJumper").toString().count(),Lasty-3.5+0.75,175+8*QueryTerminal.value("ShortJumper").toString().count(),Lasty-3.5+Internal-0.75).toLongLong();
                            IMxDrawLine *LineEnty= (IMxDrawLine*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
                            LineEnty->dynamicCall("setColorIndex(int)",McColor::mcYellow);
                            break;
                        }
                    }
                }
                AddedTerminalID.append(QueryTerminal.value("Terminal_ID").toString());
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",185,Lasty-3.5,QueryTerminal.value("FunctionText").toString(),3.5,0,0,2);//短连接
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",207,Lasty,207,Lasty-7);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",257,Lasty,257,Lasty-7);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",277,Lasty,277,Lasty-7);//竖线9
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",323,Lasty,323,Lasty-7);//竖线10
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线11
                //从JXB中获取端子两端的连线，注意可能存在多根线接到同一个端子的情形
                int CurTerminalTermIndex=0;
                QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql="SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+QueryTerminal.value("Terminal_ID").toString()+"'";
                //qDebug()<<"StrSql="<<StrSql;
                QueryTerminalTerm.exec(StrSql);
                while(QueryTerminalTerm.next())
                {
                    // qDebug()<<"TerminalTerm_ID="<<QueryTerminalTerm.value("TerminalTerm_ID").toString();
                    CurTerminalTermIndex++;
                    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql="SELECT * FROM JXB WHERE (Symb1_ID = '"+QueryTerminalTerm.value("TerminalTerm_ID").toString()+"' AND Symb1_Category = '1') OR (Symb2_ID = '"+QueryTerminalTerm.value("TerminalTerm_ID").toString()+"' AND Symb2_Category = '1')";
                    QueryJXB.exec(StrSql);
                    QString ConnectionNumber,SymbDT,ConnectTermNum;
                    while(QueryJXB.next())
                    {
                        if(QueryJXB.value("Symb1_ID").toString()==QueryTerminalTerm.value("TerminalTerm_ID").toString())
                        {
                            ConnectionNumber=QueryJXB.value("ConnectionNumber").toString();
                            QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
                            if(QueryJXB.value("Symb2_Category").toString()=="0")//元件
                            {
                                QString UnitTermStr=GetUnitTermStrByTermID(Symb2_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                            else if(QueryJXB.value("Symb2_Category").toString()=="1")//端子
                            {
                                QString UnitTermStr=GetTerminalTermStrByTermID(Symb2_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                        }
                        else if(QueryJXB.value("Symb2_ID").toString()==QueryTerminalTerm.value("TerminalTerm_ID").toString())
                        {
                            ConnectionNumber=QueryJXB.value("ConnectionNumber").toString();
                            QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
                            if(QueryJXB.value("Symb1_Category").toString()=="0")//元件
                            {
                                QString UnitTermStr=GetUnitTermStrByTermID(Symb1_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                            else if(QueryJXB.value("Symb1_Category").toString()=="1")//端子
                            {
                                QString UnitTermStr=GetTerminalTermStrByTermID(Symb1_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                        }
                        if((CurTerminalTermIndex>2)&&((CurTerminalTermIndex%2)==1))
                        {
                            Lasty=Lasty-7;
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",37,Lasty,37,Lasty-7);//竖线2
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",83,Lasty,83,Lasty-7);//竖线3
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",133,Lasty,133,Lasty-7);//竖线4
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",153,Lasty,153,Lasty-7);//竖线5
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",155,Lasty-3.5,QueryTerminal.value("Designation").toString(),3.5,0,0,2);//端子
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175,Lasty,175,Lasty-7);//竖线6
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",207,Lasty,207,Lasty-7);//竖线7
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",257,Lasty,257,Lasty-7);//竖线8
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",277,Lasty,277,Lasty-7);//竖线9
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",323,Lasty,323,Lasty-7);//竖线10
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线11
                        }
                        if((CurTerminalTermIndex%2)==1)//表格左侧
                        {
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",39,Lasty-3.5,ConnectionNumber,3.5,0,0,2);//电缆编号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",85,Lasty-3.5,SymbDT,3.5,0,0,2);//目标代号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",135,Lasty-3.5,ConnectTermNum,3.5,0,0,2);//连接点
                        }
                        else
                        {
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",279,Lasty-3.5,ConnectionNumber,3.5,0,0,2);//电缆编号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",209,Lasty-3.5,SymbDT,3.5,0,0,2);//目标代号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",259,Lasty-3.5,ConnectTermNum,3.5,0,0,2);//连接点
                        }
                    }
                }
                Lasty=Lasty-7;
                CurRecordIndex++;
            }//while(QueryTerminal.next())
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            //CurPageNum++;
        }//while(QueryTerminalStrip.next())
    }//for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_BtnLineConnect_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->LineConnect();
    }
}

void MainWindow::on_Btn_MultiLine_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->MultiLine();
    }
}

//重新生成连接
void MainWindow::on_Btn_RemakeConnectLine_clicked()
{
    //删除原连接Line表和ConnectLine表
    QSqlQuery QueryLine=QSqlQuery(T_ProjectDatabase);
    QString SqlStr =  "DELETE FROM Line ";
    QueryLine.exec(SqlStr);

    QSqlQuery QueryConnectLine=QSqlQuery(T_ProjectDatabase);
    SqlStr =  "DELETE FROM ConnectLine ";
    QueryConnectLine.exec(SqlStr);

    //先生成Line表，Line表中的Symb1_Category和Symb2_Category的0代表元件，1代表端子，2代表节点，3代表链接点
    //检索工程下所有dwg图纸的连线
    QSqlQuery QueryPage=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Page ORDER BY Page_ID ASC";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        QFile dwgfile(dwgfilepath);
        qDebug()<<"dwgfilepath="<<dwgfilepath;
        if(!dwgfile.exists()) continue;
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath);
        IMxDrawSelectionSet *ssLINE= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filterLINE=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
        filterLINE->AddStringEx("LINE",5020);
        filterLINE->AddStringEx("CONNECT", 8);
        ssLINE->dynamicCall("AllSelect(QVariant)",filterLINE->asVariant());
        int Cnt=ssLINE->dynamicCall("Count()").toInt();
        qDebug()<<"Cnt="<<Cnt;
        for(int LineIndex=0;LineIndex<Cnt;LineIndex++)
        {
            QString Symb1_ID="",Symb2_ID="",Symb1_Category="",Symb2_Category="",ConnectionNumber="",ConnectionNumber_Handle="",Wires_Handle="";
            QString Wires_Type="",Wires_Color="",Wires_Diameter="",Wires_Category="";

            IMxDrawLine *mLine= (IMxDrawLine *)ssLINE->querySubObject("Item(int)",LineIndex);
            if(EntyIsErased(GlobalBackAxWidget,(IMxDrawEntity *)mLine)) continue;//去除erase的实体
            //查看line的端点与Symb2TermInfo表、TerminalTerm表、Connector表、Link表是否有连接关系
            IMxDrawPoint *StartPt = (IMxDrawPoint *)mLine->querySubObject("StartPoint()");
            IMxDrawPoint *EndPt = (IMxDrawPoint *)mLine->querySubObject("EndPoint()");
            if((fabs(StartPt->x()-EndPt->x())<0.1)&&(fabs(StartPt->y()-EndPt->y())<0.1)) continue;
            for(int j=0;j<2;j++)
            {
                IMxDrawPoint *PtCross;
                if(j==0) PtCross=StartPt;
                else PtCross=EndPt;
                qDebug()<<"PtCrossx="<<PtCross->x()<<" PtCrossy="<<PtCross->y();
                QString Coordinate=QString::number(PtCross->x(),'f',0)+".000000,"+QString::number(PtCross->y(),'f',0)+".000000,0.000000";
                //Range&0x01:Symbol  Range&0x02:Terminal  Range&0x04:Connector  Range&0x08:Link
                QString StrTermConnect;
                if(GetLineDir(mLine)=="垂直")
                {
                    if((StartPt->y()>EndPt->y())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                    else if((StartPt->y()>EndPt->y())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                    else if((StartPt->y()<EndPt->y())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                    else if((StartPt->y()<EndPt->y())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                }
                else//水平
                {
                    if((StartPt->x()>EndPt->x())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                    else if((StartPt->x()>EndPt->x())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                    else if((StartPt->x()<EndPt->x())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                    else if((StartPt->x()<EndPt->x())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                }

                qDebug()<<"Coordinate="<<Coordinate<<",StrTermConnect="<<StrTermConnect;
                if(StrTermConnect!="")
                {
                    QStringList ListStrTermConnect=StrTermConnect.split(",");
                    if(j==0)
                    {
                        Symb1_ID=ListStrTermConnect.at(0);//QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString();
                        Symb1_Category=ListStrTermConnect.at(1);
                    }
                    else
                    {
                        Symb2_ID=ListStrTermConnect.at(0);
                        Symb2_Category=ListStrTermConnect.at(1);
                    }
                }
            }//for(int j=0;j<2;j++)
            //insert记录到Line表
            QString StrSql =  "INSERT INTO Line (Line_ID,Page_ID,ConnectionNumber,ConnectionNumber_Handle,Wires_Handle,Symb1_ID,Symb2_ID,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category,Symb1_Category,Symb2_Category)"
                              "VALUES (:Line_ID,:Page_ID,:ConnectionNumber,:ConnectionNumber_Handle,:Wires_Handle,:Symb1_ID,:Symb2_ID,:Wires_Type,:Wires_Color,:Wires_Diameter,:Wires_Category,:Symb1_Category,:Symb2_Category)";
            QueryLine.prepare(StrSql);
            QueryLine.bindValue(":Line_ID",GetMaxIDOfDB(T_ProjectDatabase,"Line","Line_ID"));
            QueryLine.bindValue(":Page_ID",QueryPage.value("Page_ID").toString());

            //查看该连线是否有Wire定义（是否相交）
            //bool HasWireDefine=false;
            int Wires_ID=CheckLineCDPCross(mLine,QueryPage.value("Page_ID").toString());
            qDebug()<<"Wires_ID="<<Wires_ID;
            if(Wires_ID>0)
            {
                QSqlQuery QueryWires = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM Wires WHERE Wires_ID = "+QString::number(Wires_ID);
                QueryWires.exec(SqlStr);
                if(QueryWires.next())
                {
                    ConnectionNumber=QueryWires.value("ConnectionNumber").toString();
                    ConnectionNumber_Handle=QueryWires.value("Handle").toString();
                    Wires_Type=QueryWires.value("Type").toString();
                    Wires_Color=QueryWires.value("Color").toString();
                    Wires_Diameter=QueryWires.value("Diameters").toString();
                }
            }

            /*
           //创建选择集对象
           IMxDrawSelectionSet *ssWire= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
           //创建过滤对象
           //MxDrawResbuf* filterWire =new MxDrawResbuf();
           IMxDrawResbuf *filterWire=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
           filterWire->AddStringEx("INSERT",5020);
           filterWire->AddStringEx("LY_CDP",8);
           //McSelect::mcSelectionSetCrossing
           ssWire->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetFence, ((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->asVariant(), ((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->asVariant(),filterWire->asVariant());
           qDebug()<<" LY_CDP ss.Count()="<<ssWire->Count();
           for (int WireIndex = 0; WireIndex < ssWire->Count(); WireIndex++)
           {
               IMxDrawEntity* entCross = (IMxDrawEntity *)ssWire->querySubObject("Item(int)",WireIndex);
               if(EntyIsErased(GlobalBackAxWidget,entCross)) return;
               if(entCross->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
               {
                   IMxDrawBlockReference *BlkWire=(IMxDrawBlockReference *)entCross;
                   if(BlkWire->dynamicCall("GetBlockName()").toString()=="SPS_CDP")
                   {
                       QSqlQuery QueryWires(T_ProjectDatabase);
                       QString StrSql="SELECT * FROM Wires WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"' AND Handle = '"+BlkWire->dynamicCall("handle()").toString()+"'";
                       QueryWires.exec(StrSql);
                       if(QueryWires.next())
                       {
                           HasWireDefine=true;
                           ConnectionNumber=QueryWires.value("ConnectionNumber").toString();
                           ConnectionNumber_Handle=QueryWires.value("Handle").toString();
                           Wires_Type=QueryWires.value("Type").toString();
                           Wires_Color=QueryWires.value("Color").toString();
                           Wires_Diameter=QueryWires.value("Diameters").toString();
                           break;
                       }
                   }
               }
           }
           */
            QueryLine.bindValue(":ConnectionNumber",ConnectionNumber);
            QueryLine.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
            QueryLine.bindValue(":Wires_Handle",mLine->dynamicCall("handle()").toString());
            QueryLine.bindValue(":Symb1_ID",Symb1_ID);
            QueryLine.bindValue(":Symb2_ID",Symb2_ID);
            QueryLine.bindValue(":Wires_Type",Wires_Type);
            QueryLine.bindValue(":Wires_Color",Wires_Color);
            QueryLine.bindValue(":Wires_Diameter",Wires_Diameter);
            QueryLine.bindValue(":Wires_Category",Wires_Category);
            QueryLine.bindValue(":Symb1_Category",Symb1_Category);
            QueryLine.bindValue(":Symb2_Category",Symb2_Category);
            QueryLine.exec();
        }//for(int i=0;i<Cnt;i++)
    }//while(QueryPage.next())

    //根据Line表生成ConnectLine表，将节点的"1"、"2"、"3"、"G"替换成"C"另一端的连接对象
    SqlStr =  "SELECT * FROM Line";
    QueryLine.exec(SqlStr);
    while(QueryLine.next())
    {
        QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category,Page_ID;;
        QString ConnectionNumber,ConnectionNumber_Handle,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category;
        Symb1_ID=QueryLine.value("Symb1_ID").toString();
        Symb2_ID=QueryLine.value("Symb2_ID").toString();
        Symb1_Category=QueryLine.value("Symb1_Category").toString();
        Symb2_Category=QueryLine.value("Symb2_Category").toString();
        ConnectionNumber=QueryLine.value("ConnectionNumber").toString();
        ConnectionNumber_Handle=QueryLine.value("ConnectionNumber_Handle").toString();
        Wires_Type=QueryLine.value("Wires_Type").toString();
        Wires_Color=QueryLine.value("Wires_Color").toString();
        Wires_Diameter=QueryLine.value("Wires_Diameter").toString();
        Wires_Category=QueryLine.value("Wires_Category").toString();
        Page_ID=QueryLine.value("Page_ID").toString();
        while(1)
        {
            bool LoopEnd=true;
            bool ShouldBreak=true;
            //如果是链接点则进行配对连接
            if((Symb1_Category=="3")||(Symb2_Category=="3"))
            {
                ShouldBreak=false;
                if(Symb1_Category=="3")
                {
                    QString Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Link WHERE Link_ID = "+Symb_ID+" AND CounterLink_ID <> ''";
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        QString CounterLink_ID=QuerySearch.value("CounterLink_ID").toString();

                        SqlStr = "SELECT * FROM Line WHERE Symb1_ID LIKE '"+CounterLink_ID+":%' AND Symb1_Category = '3'";
                        QuerySearch.exec(SqlStr);
                        bool FindedInLine=false;
                        if(QuerySearch.next())
                        {
                            FindedInLine=true;
                            Symb1_ID=QuerySearch.value("Symb2_ID").toString();
                            Symb1_Category=QuerySearch.value("Symb2_Category").toString();
                            if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                            {
                                ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                Wires_Type=QuerySearch.value("Wires_Type").toString();
                                Wires_Color=QuerySearch.value("Wires_Color").toString();
                                Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                Wires_Category=QuerySearch.value("Wires_Category").toString();
                                Page_ID=QueryLine.value("Page_ID").toString();
                            }
                            LoopEnd=false;
                        }

                        if(!FindedInLine)
                        {
                            SqlStr = "SELECT * FROM Line WHERE Symb2_ID LIKE '"+CounterLink_ID+":%' AND Symb2_Category = '3'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                FindedInLine=true;
                                Symb1_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb1_Category=QuerySearch.value("Symb1_Category").toString();
                                if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                                {
                                    ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                    ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                    Wires_Type=QuerySearch.value("Wires_Type").toString();
                                    Wires_Color=QuerySearch.value("Wires_Color").toString();
                                    Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                    Wires_Category=QuerySearch.value("Wires_Category").toString();
                                    Page_ID=QueryLine.value("Page_ID").toString();
                                }
                                LoopEnd=false;
                            }
                        }//end of if(!FindedInLine)


                        if(!FindedInLine)
                        {
                            //可能CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索
                            SqlStr = "SELECT * FROM Link WHERE Link_ID = "+CounterLink_ID;
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Coordinate_1=QuerySearch.value("Coordinate_1").toString();
                                QString LinkPage_ID=QuerySearch.value("Page_ID").toString();
                                SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                    QuerySearch.exec(SqlStr);
                                    if(QuerySearch.next())
                                    {
                                        if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                        {
                                            Symb1_ID=Symb2TermInfo_ID;
                                            Symb1_Category="0";
                                        }
                                    }
                                }
                                SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                    {
                                        Symb1_ID=TerminalInstanceID;
                                        Symb1_Category="1";
                                    }
                                }
                            }
                        }//end of if(!FindedInLine)
                    }
                }//end of if(Symb1_Category=="3")
                else if(Symb2_Category=="3")
                {
                    QString Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Link WHERE Link_ID = "+Symb_ID+" AND CounterLink_ID <> ''";
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        QString CounterLink_ID=QuerySearch.value("CounterLink_ID").toString();
                        SqlStr = "SELECT * FROM Line WHERE Symb1_ID LIKE '"+CounterLink_ID+":%' AND Symb1_Category = '3'";
                        QuerySearch.exec(SqlStr);
                        bool FindedInLine=false;
                        if(QuerySearch.next())
                        {
                            FindedInLine=true;
                            Symb2_ID=QuerySearch.value("Symb2_ID").toString();
                            Symb2_Category=QuerySearch.value("Symb2_Category").toString();
                            if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                            {
                                ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                Wires_Type=QuerySearch.value("Wires_Type").toString();
                                Wires_Color=QuerySearch.value("Wires_Color").toString();
                                Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                Wires_Category=QuerySearch.value("Wires_Category").toString();
                                Page_ID=QueryLine.value("Page_ID").toString();
                            }
                            LoopEnd=false;
                        }

                        if(!FindedInLine)
                        {
                            SqlStr = "SELECT * FROM Line WHERE Symb2_ID LIKE '"+CounterLink_ID+":%' AND Symb2_Category = '3'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                FindedInLine=true;
                                Symb2_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb2_Category=QuerySearch.value("Symb1_Category").toString();
                                if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                                {
                                    ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                    ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                    Wires_Type=QuerySearch.value("Wires_Type").toString();
                                    Wires_Color=QuerySearch.value("Wires_Color").toString();
                                    Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                    Wires_Category=QuerySearch.value("Wires_Category").toString();
                                    Page_ID=QueryLine.value("Page_ID").toString();
                                }
                                LoopEnd=false;
                            }
                        }//end of if(!FindedInLine)

                        if(!FindedInLine)
                        {
                            //可能CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索
                            SqlStr = "SELECT * FROM Link WHERE Link_ID = "+CounterLink_ID;
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Coordinate_1=QuerySearch.value("Coordinate_1").toString();
                                QString LinkPage_ID=QuerySearch.value("Page_ID").toString();
                                SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                    QuerySearch.exec(SqlStr);
                                    if(QuerySearch.next())
                                    {
                                        if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                        {
                                            Symb2_ID=Symb2TermInfo_ID;
                                            Symb2_Category="0";
                                        }
                                    }
                                }
                                SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                    {
                                        Symb2_ID=TerminalInstanceID;
                                        Symb2_Category="1";
                                    }
                                }
                            }
                        }//end of if(!FindedInLine)
                    }
                }//end of else if(Symb1_Category=="3")
            }//end of if((Symb1_Category=="3")||(Symb2_Category=="3"))
            else if((Symb1_Category=="2")||(Symb2_Category=="2"))
            {
                if(((Symb1_ID.contains(":1"))||(Symb1_ID.contains(":2"))||(Symb1_ID.contains(":3"))||(Symb1_ID.contains(":G")))&&(Symb1_Category=="2")) ShouldBreak=false;
                if(((Symb2_ID.contains(":1"))||(Symb2_ID.contains(":2"))||(Symb2_ID.contains(":3"))||(Symb2_ID.contains(":G")))&&(Symb2_Category=="2")) ShouldBreak=false;
                if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C")) ShouldBreak=false;
                if(ShouldBreak) break;
                int CaseID=0;
                if(((Symb1_ID.contains(":1"))||(Symb1_ID.contains(":2"))||(Symb1_ID.contains(":3"))||(Symb1_ID.contains(":G")))&&(Symb1_Category=="2")) CaseID=1;
                if(((Symb2_ID.contains(":1"))||(Symb2_ID.contains(":2"))||(Symb2_ID.contains(":3"))||(Symb2_ID.contains(":G")))&&(Symb2_Category=="2")) CaseID=2;
                if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C")) CaseID=3;
                if((CaseID==1)||(CaseID==2))
                {
                    QString Symb_ID;
                    if(CaseID==1) Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
                    else if(CaseID==2) Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Line WHERE (Symb1_ID = '"+Symb_ID+":C' AND Symb1_Category = '2') OR (Symb2_ID = '"+Symb_ID+":C' AND Symb2_Category = '2')";
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        if(QuerySearch.value("Symb1_ID").toString()==(Symb_ID+":C"))
                        {
                            if(CaseID==1)
                            {
                                Symb1_ID=QuerySearch.value("Symb2_ID").toString();
                                Symb1_Category=QuerySearch.value("Symb2_Category").toString();
                            }
                            else
                            {
                                Symb2_ID=QuerySearch.value("Symb2_ID").toString();
                                Symb2_Category=QuerySearch.value("Symb2_Category").toString();
                            }
                        }
                        else
                        {
                            if(CaseID==1)
                            {
                                Symb1_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb1_Category=QuerySearch.value("Symb1_Category").toString();
                            }
                            else
                            {
                                Symb2_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb2_Category=QuerySearch.value("Symb1_Category").toString();
                            }
                        }
                        if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                        {
                            ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                            ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                            Wires_Type=QuerySearch.value("Wires_Type").toString();
                            Wires_Color=QuerySearch.value("Wires_Color").toString();
                            Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                            Wires_Category=QuerySearch.value("Wires_Category").toString();
                            Page_ID=QueryLine.value("Page_ID").toString();
                        }
                        LoopEnd=false;
                    }
                    else
                    {
                        qDebug()<<"CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索";
                        //可能CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索
                        SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
                        qDebug()<<"SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
                        QuerySearch.exec(SqlStr);
                        if(QuerySearch.next())
                        {
                            QString C_Coordinate=QuerySearch.value("C_Coordinate").toString();
                            QString ConnectorPage_ID=QuerySearch.value("Page_ID").toString();
                            QString Connector_Name=QuerySearch.value("Connector_Name").toString();
                            SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+C_Coordinate+"'";
                            qDebug()<<"SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+C_Coordinate+"'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                qDebug()<<"SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    qDebug()<<"QuerySearch.value(Page_ID).toString()="<<QuerySearch.value("Page_ID").toString()<<",ConnectorPage_ID="<<ConnectorPage_ID;
                                    if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                    {
                                        if(CaseID==1)
                                        {
                                            Symb1_ID=Symb2TermInfo_ID;
                                            Symb1_Category="0";
                                        }
                                        else
                                        {
                                            Symb2_ID=Symb2TermInfo_ID;
                                            Symb2_Category="0";
                                        }
                                        LoopEnd=false;
                                    }
                                }
                            }
                            SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+C_Coordinate+"'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                {
                                    if(CaseID==1)
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb1_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb1_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb1_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb1_ID=TerminalInstanceID+".1";
                                        //Symb1_ID=TerminalInstanceID;
                                        Symb1_Category="1";
                                    }
                                    else
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb2_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb2_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb2_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb2_ID=TerminalInstanceID+".1";
                                        //Symb2_ID=TerminalInstanceID;
                                        Symb2_Category="1";
                                    }
                                    LoopEnd=false;
                                }
                            }
                        }
                    }//end of else
                }//end of if(CaseID>0)

                if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))//如果是CO节点则找CO节点1端口连线另一侧的连接
                {
                    QString Symb_ID;
                    if(Symb1_ID.contains(":C")) Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
                    else Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        if(QuerySearch.value("Connector_Name").toString().contains("SYMB2_M_PWF_CO"))
                        {
                            QString Coordinate_1=QuerySearch.value("Coordinate_1").toString();
                            QString ConnectorPage_ID=QuerySearch.value("Page_ID").toString();
                            QString Connector_Name=QuerySearch.value("Connector_Name").toString();
                            qDebug()<<"Coordinate_1="<<Coordinate_1<<",ConnectorPage_ID="<<ConnectorPage_ID<<",Connector_Name="<<Connector_Name;
                            SqlStr = "SELECT * FROM Line WHERE (Symb1_ID = '"+Symb_ID+":1' AND Symb1_Category = '2') OR (Symb2_ID = '"+Symb_ID+":1' AND Symb2_Category = '2')";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                if(QuerySearch.value("Symb1_ID").toString()==(Symb_ID+":1"))
                                {
                                    if(Symb1_ID.contains(":C"))
                                    {
                                        Symb1_ID=QuerySearch.value("Symb2_ID").toString();
                                        Symb1_Category=QuerySearch.value("Symb2_Category").toString();
                                    }
                                    else
                                    {
                                        Symb2_ID=QuerySearch.value("Symb2_ID").toString();
                                        Symb2_Category=QuerySearch.value("Symb2_Category").toString();
                                    }
                                }
                                else
                                {
                                    if(Symb1_ID.contains(":C"))
                                    {
                                        Symb1_ID=QuerySearch.value("Symb1_ID").toString();
                                        Symb1_Category=QuerySearch.value("Symb1_Category").toString();
                                    }
                                    else
                                    {
                                        Symb2_ID=QuerySearch.value("Symb1_ID").toString();
                                        Symb2_Category=QuerySearch.value("Symb1_Category").toString();
                                    }

                                }
                                if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                                {
                                    ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                    ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                    Wires_Type=QuerySearch.value("Wires_Type").toString();
                                    Wires_Color=QuerySearch.value("Wires_Color").toString();
                                    Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                    Wires_Category=QuerySearch.value("Wires_Category").toString();
                                    Page_ID=QueryLine.value("Page_ID").toString();
                                }
                                LoopEnd=false;
                            }
                            //如果Symb1_ID或Symb2_ID包含:C且另一端与端口或端子直连，则更新Symb1_ID

                            SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+Coordinate_1+"'";
                            qDebug()<<"SqlStr="<<SqlStr;
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                    {
                                        if(Symb1_ID.contains(":C"))
                                        {
                                            Symb1_ID=Symb2TermInfo_ID;
                                            Symb1_Category="0";
                                        }
                                        else
                                        {
                                            Symb2_ID=Symb2TermInfo_ID;
                                            Symb2_Category="0";
                                        }
                                        LoopEnd=false;
                                    }
                                }
                            }
                            SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+Coordinate_1+"'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                {
                                    if(Symb1_ID.contains(":C"))
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb1_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb1_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb1_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb1_ID=TerminalInstanceID+".2";
                                        Symb1_Category="1";
                                    }
                                    else
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb2_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb2_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb2_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb2_ID=TerminalInstanceID+".2";
                                        Symb2_Category="1";
                                    }
                                    LoopEnd=false;
                                }
                            }
                        }
                    }
                }//end of if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))//如果是CO节点则找CO节点1端口连线另一侧的连接
            }//end of else if((Symb1_Category=="2")||(Symb2_Category=="2"))
            if(LoopEnd) break;
        }//while(1)

        QString StrSql =  "INSERT INTO ConnectLine (ConnectLine_ID,Page_ID,Cable_ID,Equipotential_Num,ConnectionNumber,ConnectionNumber_Handle,Symb1_ID,Symb2_ID,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category,Symb1_Category,Symb2_Category)"
                          "VALUES (:ConnectLine_ID,:Page_ID,:Cable_ID,:Equipotential_Num,:ConnectionNumber,:ConnectionNumber_Handle,:Symb1_ID,:Symb2_ID,:Wires_Type,:Wires_Color,:Wires_Diameter,:Wires_Category,:Symb1_Category,:Symb2_Category)";
        QueryConnectLine.prepare(StrSql);
        QueryConnectLine.bindValue(":ConnectLine_ID",GetMaxIDOfDB(T_ProjectDatabase,"ConnectLine","ConnectLine_ID"));
        QueryConnectLine.bindValue(":Page_ID",QueryLine.value("Page_ID").toString());
        QSqlQuery QuerySearchWire=QSqlQuery(T_ProjectDatabase);
        SqlStr = "SELECT * FROM Wires WHERE Handle = '"+ConnectionNumber_Handle+"' AND Page_ID = '"+Page_ID+"'";
        QuerySearchWire.exec(SqlStr);
        if(QuerySearchWire.next())  QueryConnectLine.bindValue(":Cable_ID",QuerySearchWire.value("Cable_ID").toString());
        else QueryConnectLine.bindValue(":Cable_ID","");
        QueryConnectLine.bindValue(":Equipotential_Num",QueryLine.value("Equipotential_Num").toString());
        QueryConnectLine.bindValue(":ConnectionNumber",ConnectionNumber);
        QueryConnectLine.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
        QueryConnectLine.bindValue(":Symb1_ID",Symb1_ID);
        QueryConnectLine.bindValue(":Symb2_ID",Symb2_ID);
        QueryConnectLine.bindValue(":Wires_Type",Wires_Type);
        QueryConnectLine.bindValue(":Wires_Color",Wires_Color);
        QueryConnectLine.bindValue(":Wires_Diameter",Wires_Diameter);
        QueryConnectLine.bindValue(":Wires_Category",Wires_Category);
        QueryConnectLine.bindValue(":Symb1_Category",Symb1_Category);
        QueryConnectLine.bindValue(":Symb2_Category",Symb2_Category);
        QueryConnectLine.exec();
    }//while(QueryLine.next())

    //如果某一个ConnectLine的两端都是"C"节点，则将他们连起来
    SqlStr="SELECT * FROM ConnectLine WHERE Symb1_ID LIKE '%:C' AND Symb2_ID LIKE '%:C'";
    QueryConnectLine.exec(SqlStr);
    while(QueryConnectLine.next())
    {
        qDebug()<<"Find 某一个ConnectLine的两端都是C节点，ConnectLine_ID="<<QueryConnectLine.value("ConnectLine_ID").toString();
        QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category,Page_ID;
        QString ConnectionNumber,ConnectionNumber_Handle,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category;
        QString ConnectLineSymb1_ID=QueryConnectLine.value("Symb1_ID").toString();
        QString ConnectLineSymb2_ID=QueryConnectLine.value("Symb2_ID").toString();
        Symb1_Category=QueryConnectLine.value("Symb1_Category").toString();
        Symb2_Category=QueryConnectLine.value("Symb2_Category").toString();
        ConnectionNumber=QueryConnectLine.value("ConnectionNumber").toString();
        ConnectionNumber_Handle=QueryConnectLine.value("ConnectionNumber_Handle").toString();
        Wires_Type=QueryConnectLine.value("Wires_Type").toString();
        Wires_Color=QueryConnectLine.value("Wires_Color").toString();
        Wires_Diameter=QueryConnectLine.value("Wires_Diameter").toString();
        Wires_Category=QueryConnectLine.value("Wires_Category").toString();
        Page_ID=QueryConnectLine.value("Page_ID").toString();

        QSqlQuery QuerySearch1=QSqlQuery(T_ProjectDatabase);
        QSqlQuery QuerySearch2=QSqlQuery(T_ProjectDatabase);
        SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+ConnectLineSymb1_ID+"' AND Symb1_Category = '2' AND Symb2_ID NOT LIKE '%:C') OR (Symb2_ID = '"+ConnectLineSymb1_ID+"' AND Symb2_Category = '2' AND Symb1_ID NOT LIKE '%:C')";
        QuerySearch1.exec(SqlStr);
        while(QuerySearch1.next())
        {
            SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+ConnectLineSymb2_ID+"' AND Symb1_Category = '2' AND Symb2_ID NOT LIKE '%:C') OR (Symb2_ID = '"+ConnectLineSymb2_ID+"' AND Symb2_Category = '2' AND Symb1_ID NOT LIKE '%:C')";
            QuerySearch2.exec(SqlStr);
            while(QuerySearch2.next())
            {
                if(ConnectLineSymb1_ID==QuerySearch1.value("Symb1_ID").toString())
                {
                    if(ConnectLineSymb2_ID==QuerySearch2.value("Symb1_ID").toString())
                    {
                        Symb1_ID=QuerySearch2.value("Symb2_ID").toString();
                        Symb1_Category=QuerySearch2.value("Symb2_Category").toString();
                        Symb2_ID=QuerySearch1.value("Symb2_ID").toString();
                        Symb2_Category=QuerySearch1.value("Symb2_Category").toString();
                    }
                    else if(ConnectLineSymb2_ID==QuerySearch2.value("Symb2_ID").toString())
                    {
                        Symb1_ID=QuerySearch2.value("Symb1_ID").toString();
                        Symb1_Category=QuerySearch2.value("Symb1_Category").toString();
                        Symb2_ID=QuerySearch1.value("Symb2_ID").toString();
                        Symb2_Category=QuerySearch1.value("Symb2_Category").toString();
                    }
                }
                else if(ConnectLineSymb1_ID==QuerySearch1.value("Symb2_ID").toString())
                {
                    if(ConnectLineSymb2_ID==QuerySearch2.value("Symb1_ID").toString())
                    {
                        Symb1_ID=QuerySearch1.value("Symb1_ID").toString();
                        Symb1_Category=QuerySearch1.value("Symb1_Category").toString();
                        Symb2_ID=QuerySearch2.value("Symb2_ID").toString();
                        Symb2_Category=QuerySearch2.value("Symb2_Category").toString();
                    }
                    else if(ConnectLineSymb2_ID==QuerySearch2.value("Symb2_ID").toString())
                    {
                        Symb1_ID=QuerySearch1.value("Symb1_ID").toString();
                        Symb1_Category=QuerySearch1.value("Symb1_Category").toString();
                        Symb2_ID=QuerySearch2.value("Symb1_ID").toString();
                        Symb2_Category=QuerySearch2.value("Symb1_Category").toString();
                    }
                }
                if(QuerySearch1.value("ConnectionNumber_Handle").toString()!="")
                {
                    ConnectionNumber=QuerySearch1.value("ConnectionNumber").toString();
                    ConnectionNumber_Handle=QuerySearch1.value("ConnectionNumber_Handle").toString();
                    Wires_Type=QuerySearch1.value("Wires_Type").toString();
                    Wires_Color=QuerySearch1.value("Wires_Color").toString();
                    Wires_Diameter=QuerySearch1.value("Wires_Diameter").toString();
                    Wires_Category=QuerySearch1.value("Wires_Category").toString();
                    Page_ID=QuerySearch1.value("Page_ID").toString();
                }
                else if(QuerySearch2.value("ConnectionNumber_Handle").toString()!="")
                {
                    ConnectionNumber=QuerySearch2.value("ConnectionNumber").toString();
                    ConnectionNumber_Handle=QuerySearch2.value("ConnectionNumber_Handle").toString();
                    Wires_Type=QuerySearch2.value("Wires_Type").toString();
                    Wires_Color=QuerySearch2.value("Wires_Color").toString();
                    Wires_Diameter=QuerySearch2.value("Wires_Diameter").toString();
                    Wires_Category=QuerySearch2.value("Wires_Category").toString();
                    Page_ID=QuerySearch2.value("Page_ID").toString();
                }
                //更新QuerySearch1
                QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                SqlStr="UPDATE ConnectLine SET Cable_ID=:Cable_ID,ConnectionNumber=:ConnectionNumber,ConnectionNumber_Handle=:ConnectionNumber_Handle,Symb1_ID=:Symb1_ID,"
                       "Symb2_ID=:Symb2_ID,Wires_Type=:Wires_Type,Wires_Color=:Wires_Color,Wires_Diameter=:Wires_Diameter,Wires_Category=:Wires_Category,"
                       "Symb1_Category=:Symb1_Category,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QuerySearch1.value("ConnectLine_ID").toString();
                QueryUpdate.prepare(SqlStr);
                QSqlQuery QuerySearchWire=QSqlQuery(T_ProjectDatabase);
                SqlStr = "SELECT * FROM Wires WHERE Handle = '"+ConnectionNumber_Handle+"' AND Page_ID = '"+Page_ID+"'";
                QuerySearchWire.exec(SqlStr);
                if(QuerySearchWire.next())  QueryUpdate.bindValue(":Cable_ID",QuerySearchWire.value("Cable_ID").toString());
                else QueryUpdate.bindValue(":Cable_ID","");
                QueryUpdate.bindValue(":ConnectionNumber",ConnectionNumber);
                QueryUpdate.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
                QueryUpdate.bindValue(":Symb1_ID",Symb1_ID);
                QueryUpdate.bindValue(":Symb2_ID",Symb2_ID);
                QueryUpdate.bindValue(":Wires_Type",Wires_Type);
                QueryUpdate.bindValue(":Wires_Color",Wires_Color);
                QueryUpdate.bindValue(":Wires_Diameter",Wires_Diameter);
                QueryUpdate.bindValue(":Wires_Category",Wires_Category);
                QueryUpdate.bindValue(":Symb1_Category",Symb1_Category);
                QueryUpdate.bindValue(":Symb2_Category",Symb2_Category);
                QueryUpdate.exec();
            }
        }
    }//while(QueryLine.next())

    //如果有2个CO节点直连，则将他们连起来
    QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%'";
    QueryConnector.exec(SqlStr);
    while(QueryConnector.next())
    {
        QString Connector_ID1,Connector_ID2;
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND C_Coordinate = '"+QueryConnector.value("C_Coordinate").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":1";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":1";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND C_Coordinate = '"+QueryConnector.value("Coordinate_1").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":C";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":1";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND Coordinate_1 = '"+QueryConnector.value("Coordinate_1").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":C";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":C";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND Coordinate_1 = '"+QueryConnector.value("C_Coordinate").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":1";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":C";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
    }

    /*
   //如果某一个ConnectLine有一端是节点，且该处端点与元件端点或端子直连，则将他们连起来
   SqlStr="SELECT * FROM ConnectLine WHERE Symb1_Category = '2'";
   QueryConnectLine.exec(SqlStr);
   while(QueryConnectLine.next())
   {
       QString Symb1_ID=QueryConnectLine.value("Symb1_ID").toString();
       QString Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
       QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
       SqlStr="SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
       QuerySearch.exec(SqlStr);
       if(QuerySearch.next())
       {
           QString TermConnectC,TermConnectG,TermConnect1,TermConnect2,TermConnect3;
           if(Symb1_ID.contains(":C"))
           {
               QStringList ListColumnName;
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":G' OR Symb2_ID = '"+Symb_ID+":G'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"G_Coordinate";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":1' OR Symb2_ID = '"+Symb_ID+":1'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_1";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":2' OR Symb2_ID = '"+Symb_ID+":2'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_2";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":3' OR Symb2_ID = '"+Symb_ID+":3'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_3";

               for(int i=0;i<ListColumnName.count();i++)
               {
qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value(ListColumnName.at(i)).toString();
                   //Range&0x01:Symbol  Range&0x02:Terminal  Range&0x04:Connector  Range&0x08:Link
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value(ListColumnName.at(i)).toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb1_ID=:Symb1_ID,Symb1_Category=:Symb1_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb1_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb1_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
           else
           {
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":C' OR Symb2_ID = '"+Symb_ID+":C'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next())
               {
qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value("C_Coordinate").toString();
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value("C_Coordinate").toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb1_ID=:Symb1_ID,Symb1_Category=:Symb1_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb1_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb1_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
       }
   }

   SqlStr="SELECT * FROM ConnectLine WHERE Symb2_Category = '2'";
   QueryConnectLine.exec(SqlStr);
   while(QueryConnectLine.next())
   {
       QString Symb2_ID=QueryConnectLine.value("Symb2_ID").toString();
       QString Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
       QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
       SqlStr="SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
       QuerySearch.exec(SqlStr);
       if(QuerySearch.next())
       {
           QString TermConnectC,TermConnectG,TermConnect1,TermConnect2,TermConnect3;
           if(Symb2_ID.contains(":C"))
           {
               QStringList ListColumnName;
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":G' OR Symb2_ID = '"+Symb_ID+":G'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"G_Coordinate";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":1' OR Symb2_ID = '"+Symb_ID+":1'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_1";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":2' OR Symb2_ID = '"+Symb_ID+":2'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_2";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":3' OR Symb2_ID = '"+Symb_ID+":3'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_3";

               for(int i=0;i<ListColumnName.count();i++)
               {
 qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value(ListColumnName.at(i)).toString();
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value(ListColumnName.at(i)).toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb2_ID=:Symb2_ID,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb2_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb2_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
           else
           {
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":C' OR Symb2_ID = '"+Symb_ID+":C'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next())
               {
 qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value("C_Coordinate").toString();
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value("C_Coordinate").toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb2_ID=:Symb2_ID,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb2_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb2_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
       }
   }*/
    ProduceDBJXB();
    LoadProjectLines();
    LoadProjectSystemDescription();
}

//如果有2个CO节点直连，则将他们连起来
void MainWindow::UpdateConnectLine_CO_Connection(QString Connector_ID1,QString Connector_ID2)
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+Connector_ID1+"' AND Symb1_Category = '2') OR (Symb2_ID = '"+Connector_ID1+"' AND Symb2_Category = '2')";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        QSqlQuery QuerySearch2=QSqlQuery(T_ProjectDatabase);
        SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+Connector_ID2+"' AND Symb1_Category = '2') OR (Symb2_ID = '"+Connector_ID2+"' AND Symb2_Category = '2')";
        QuerySearch2.exec(SqlStr);
        while(QuerySearch2.next())
        {
            QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category,Page_ID;
            QString ConnectionNumber,ConnectionNumber_Handle,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category;
            Symb1_ID=QuerySearch.value("Symb1_ID").toString();
            Symb2_ID=QuerySearch.value("Symb2_ID").toString();
            Symb1_Category=QuerySearch.value("Symb1_Category").toString();
            Symb2_Category=QuerySearch.value("Symb2_Category").toString();
            ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
            ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
            Wires_Type=QuerySearch.value("Wires_Type").toString();
            Wires_Color=QuerySearch.value("Wires_Color").toString();
            Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
            Wires_Category=QuerySearch.value("Wires_Category").toString();
            if((QuerySearch.value("Symb1_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb1_ID").toString()==Connector_ID2))
            {
                Symb1_ID=QuerySearch2.value("Symb2_ID").toString();
                Symb1_Category=QuerySearch2.value("Symb2_Category").toString();
            }
            if((QuerySearch.value("Symb1_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb2_ID").toString()==Connector_ID2))
            {
                Symb1_ID=QuerySearch2.value("Symb1_ID").toString();
                Symb1_Category=QuerySearch2.value("Symb1_Category").toString();
            }
            if((QuerySearch.value("Symb2_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb1_ID").toString()==Connector_ID2))
            {
                Symb2_ID=QuerySearch2.value("Symb2_ID").toString();
                Symb2_Category=QuerySearch2.value("Symb2_Category").toString();
            }
            if((QuerySearch.value("Symb2_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb2_ID").toString()==Connector_ID2))
            {
                Symb2_ID=QuerySearch2.value("Symb1_ID").toString();
                Symb2_Category=QuerySearch2.value("Symb1_Category").toString();
            }
            if(QuerySearch2.value("ConnectionNumber_Handle").toString()!="")
            {
                ConnectionNumber=QuerySearch2.value("ConnectionNumber").toString();
                ConnectionNumber_Handle=QuerySearch2.value("ConnectionNumber_Handle").toString();
                Wires_Type=QuerySearch2.value("Wires_Type").toString();
                Wires_Color=QuerySearch2.value("Wires_Color").toString();
                Wires_Diameter=QuerySearch2.value("Wires_Diameter").toString();
                Wires_Category=QuerySearch2.value("Wires_Category").toString();
            }
            //更新QuerySearch1
            QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
            SqlStr="UPDATE ConnectLine SET ConnectionNumber=:ConnectionNumber,ConnectionNumber_Handle=:ConnectionNumber_Handle,Symb1_ID=:Symb1_ID,"
                   "Symb2_ID=:Symb2_ID,Wires_Type=:Wires_Type,Wires_Color=:Wires_Color,Wires_Diameter=:Wires_Diameter,Wires_Category=:Wires_Category,"
                   "Symb1_Category=:Symb1_Category,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QuerySearch.value("ConnectLine_ID").toString();
            QueryUpdate.prepare(SqlStr);
            QueryUpdate.bindValue(":ConnectionNumber",ConnectionNumber);
            QueryUpdate.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
            QueryUpdate.bindValue(":Symb1_ID",Symb1_ID);
            QueryUpdate.bindValue(":Symb2_ID",Symb2_ID);
            QueryUpdate.bindValue(":Wires_Type",Wires_Type);
            QueryUpdate.bindValue(":Wires_Color",Wires_Color);
            QueryUpdate.bindValue(":Wires_Diameter",Wires_Diameter);
            QueryUpdate.bindValue(":Wires_Category",Wires_Category);
            QueryUpdate.bindValue(":Symb1_Category",Symb1_Category);
            QueryUpdate.bindValue(":Symb2_Category",Symb2_Category);
            QueryUpdate.exec();
        }
    }
}

//Range&0x01:Symbol  Range&0x02:Terminal  Range&0x04:Connector  Range&0x08:Link
QString MainWindow::FindTermConnectInDB(QString Page_ID,QString Coordinate,unsigned char Range,QString LineDir)
{
    if(Coordinate=="") return "";
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    if(Range&0x01)//Symbol
    {
        SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+Page_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QuerySearch.value("Symbol_ID").toString()+"' AND Conn_Coordinate = '"+Coordinate+"'";
            QuerySymb2TermInfo.exec(SqlStr);
            if(QuerySymb2TermInfo.next())
            {
                return QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()+",0";
            }
        }
    }
    if(Range&0x02)//Terminal
    {
        SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+Page_ID+"' AND Coordinate = '"+Coordinate+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            if(LineDir=="左")   return QuerySearch.value("TerminalInstanceID").toString()+"."+QuerySearch.value("LeftTerm").toString()+",1";
            else if(LineDir=="右")   return QuerySearch.value("TerminalInstanceID").toString()+"."+QuerySearch.value("RightTerm").toString()+",1";
        }
    }
    if(Range&0x04)//Connector
    {
        SqlStr="SELECT * FROM Connector WHERE Page_ID = '"+Page_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QStringList ListConnName={"C_Coordinate","G_Coordinate","Coordinate_1","Coordinate_2","Coordinate_3"};
            QStringList ListTermStr={":C",":G",":1",":2",":3"};
            for(int i=0;i<ListConnName.count();i++)
            {
                if(QuerySearch.value(ListConnName.at(i))==Coordinate) return QuerySearch.value("Connector_ID").toString()+ListTermStr.at(i)+",2";
            }
        }
    }
    if(Range&0x08)//Link
    {
        SqlStr="SELECT * FROM Link WHERE Page_ID = '"+Page_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QStringList ListConnName={"C_Coordinate","Coordinate_1"};
            QStringList ListTermStr={":C",":1"};
            for(int i=0;i<ListConnName.count();i++)
            {
                if(QuerySearch.value(ListConnName.at(i))==Coordinate) return QuerySearch.value("Link_ID").toString()+ListTermStr.at(i)+",3";
            }
        }
    }
    return "";
}

void MainWindow::on_Btn_LineDefine_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->LineDefine();
    }
}

void MainWindow::on_Btn_CableDefine_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->CableDefine();
    }
}

void MainWindow::on_BtnNodeRightDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO1");
    }
}

void MainWindow::on_BtnNodeLeftDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO2");
    }
}

void MainWindow::on_BtnNodeRightUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO3");
    }
}

void MainWindow::on_BtnNodeLeftUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO4");
    }
}

void MainWindow::on_BtnTNodeDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TLRU1");
    }
}

void MainWindow::on_BtnTNodeUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TLRO1");
    }
}

void MainWindow::on_BtnTNodeRight_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TOUR1");
    }
}

void MainWindow::on_BtnTNodeLeft_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TOUL1");
    }
}

void MainWindow::on_BtnTNodeTX_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_BR1");
    }
}

void MainWindow::on_BtnTNodeCross_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CR1");
    }
}

void MainWindow::on_BtnLinkRight_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点1");
    }
}

void MainWindow::on_BtnLinkUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点2");
    }
}

void MainWindow::on_BtnLinkLeft_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点3");
    }
}

void MainWindow::on_BtnLinkDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点4");
    }
}

//Mode=1:全部向上 Mode=2:全部向下 Mode=3：奇数向上，偶数向下 Mode=4：奇数向下，偶数向上  mode=5:前半部分向上，后面向下  Mode=6：前半部分向下，后面向上
void MainWindow::LoadWholeUnit(int Mode)
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                qDebug()<<"LoadUnit,ID="<<ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
                formMdi->LoadWholeUnit(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt(),Mode);
            }
        }
    }
}

//整体放置，接线图章
void MainWindow::LoadUnitStamp()
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+ui->treeViewUnits->currentIndex().data(Qt::UserRole).toString();
    QuerySearch.exec(SqlStr);
    if(QuerySearch.next())
    {
        QSqlQuery QuerySearchLib=QSqlQuery(T_LibDatabase);
        SqlStr="SELECT * FROM Equipment WHERE PartCode= '"+QuerySearch.value("PartCode").toString()+"'";
        QuerySearchLib.exec(SqlStr);
        if(QuerySearchLib.next())
        {
            if(QuerySearchLib.value("MultiLib").toString()!="")
            {
                if(!ui->treeViewUnits->currentIndex().isValid()) return;
                if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
                if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
                {
                    formaxwidget *formMdi;
                    formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
                    if(formMdi!=nullptr)
                    {
                        //确定当前活动窗口的图纸是否为本项目图纸
                        QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
                        QFileInfo file(PageName);
                        if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
                        else
                        {
                            qDebug()<<"LoadUnitStamp,ID="<<ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
                            formMdi->UnitIdInDB=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
                            formMdi->LoadUnitStamp(QuerySearchLib.value("MultiLib").toString());
                        }
                    }
                }
            }
        }
    }
}

//整体放置,全部向上
void MainWindow::LoadWholeUnitAllTermsUp()
{
    LoadWholeUnit(1);
}
//整体放置,全部向下
void MainWindow::LoadWholeUnitAllTermsDown()
{
    LoadWholeUnit(2);
}
//整体放置,奇数向上，偶数向下
void MainWindow::LoadWholeUnitOddTermsUp()
{
    LoadWholeUnit(3);
}
//整体放置,奇数向下，偶数向上
void MainWindow::LoadWholeUnitEvenTermsUp()
{
    LoadWholeUnit(4);
}
//整体放置,前半部分向上，后面向下
void MainWindow::LoadWholeUnitFirstHalfUp()
{
    LoadWholeUnit(5);
}
//整体放置,前半部分向下，后面向上
void MainWindow::LoadWholeUnitLastHalfUp()
{
    LoadWholeUnit(6);
}

void MainWindow::SlotLoadSpur()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListSymbol_ID;
                for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
                    ListSymbol_ID.append(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadSymbolSpur(ListSymbol_ID);//ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
            }
        }
    }
}

void MainWindow::DrawSpurEqualDistance()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListSymbol_ID;
                for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
                    ListSymbol_ID.append(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadEqualDistance(ListSymbol_ID,0);
            }
        }
    }
}

void MainWindow::DrawTerminalEqualDistance()//等距绘制端子
{
    if(!ui->treeViewTerminal->currentIndex().isValid()) return;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListTerminal_ID;
                for(int i=0;i<ui->treeViewTerminal->selectionModel()->selectedIndexes().count();i++)
                    ListTerminal_ID.append(ui->treeViewTerminal->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadEqualDistance(ListTerminal_ID,1);
            }
        }
    }
}

void MainWindow::SlotLoadTerminal()
{
    if(!ui->treeViewTerminal->currentIndex().isValid()) return;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListSymbol_ID;
                for(int i=0;i<ui->treeViewTerminal->selectionModel()->selectedIndexes().count();i++)
                    ListSymbol_ID.append(ui->treeViewTerminal->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadTerminal(ListSymbol_ID);
            }
        }
    }
}


void MainWindow::on_Btn_BlackBox_clicked()
{
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            if(!formMdi->IsDrawingMultiLib)
            {
                //确定当前活动窗口的图纸是否为本项目图纸
                QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
                QFileInfo file(PageName);
                if(!file.exists())
                {
                    QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
                    return;
                }
            }
            formMdi->DrawBlackBox();
        }
    }
}

void MainWindow::on_Btn_StructBox_clicked()
{
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                formMdi->DrawStructBox();
            }
        }
    }
}

void MainWindow::on_BtnFuncManage_clicked()
{
    dlgFuncDefine->setModal(true);
    dlgFuncDefine->SetCurStackedWidgetIndex(1);
    dlgFuncDefine->show();
    dlgFuncDefine->exec();
}



void MainWindow::on_treeViewUnits_clicked(const QModelIndex &index)
{
    if(!ui->widgetPreView->isVisible()) return;
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="功能子块") return;
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+index.data(Qt::UserRole).toString();
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return;
    QString Path;
    if(QuerySymbol.value("Symbol").toString().contains("SPS_"))
        Path="C:/TBD/SPS/"+QuerySymbol.value("Symbol").toString()+".dwg";
    else
        Path="C:/TBD/SYMB2LIB/"+QuerySymbol.value("Symbol").toString()+".dwg";
    ui->axWidgetPreview->dynamicCall("OpenDwgFile(QString)",Path);
    ui->axWidgetPreview->dynamicCall("ZoomAll()");
}

void MainWindow::on_treeViewTerminal_clicked(const QModelIndex &index)
{
    if(!ui->widgetPreView->isVisible()) return;
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="端子") return;
    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+index.data(Qt::UserRole).toString();
    QueryTerminal.exec(SqlStr);
    if(!QueryTerminal.next()) return;
    QString Path;
    if(QueryTerminal.value("Symbol").toString().contains("SPS_"))
        Path="C:/TBD/SPS/"+QueryTerminal.value("Symbol").toString()+".dwg";
    else
        Path="C:/TBD/SYMB2LIB/"+QueryTerminal.value("Symbol").toString()+".dwg";
    ui->axWidgetPreview->dynamicCall("OpenDwgFile(QString)",Path);
    ui->axWidgetPreview->dynamicCall("ZoomAll()");
}

void MainWindow::on_tabWidget_Navigator_currentChanged(int index)
{
    if(index==3)
    {
        ShowPreViewWidget=false;
        ui->BtnShowHidePreViewWidget->setText("图形预览▲");
        ui->widgetPreView->setVisible(false);
    }
}

void MainWindow::on_Btn_GeneratePartList_clicked()
{
    dlgGenerate.setWindowTitle("生成部件汇总表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(2);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '部件汇总表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"部件汇总表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '部件汇总表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"部件汇总表")+"'";
        qDebug()<<"StrSql="<<StrSql;
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    QStringList ListedPart;
    ListedPart.clear();
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Equipment WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryEquipment.exec(StrSql);
        while(QueryEquipment.next())
        {
            if(QueryEquipment.value("PartCode").toString()=="") continue;
            bool PartExisted=false;
            for(int i=0;i<ListedPart.count();i++)
            {
                if(ListedPart.at(i)==QueryEquipment.value("PartCode").toString())
                {
                    PartExisted=true;
                    break;
                }
            }
            if(PartExisted) continue;
            ListedPart.append(QueryEquipment.value("PartCode").toString());
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"MXB");
                SetCurLayer(GlobalBackAxWidget,"MXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"部件汇总表",10,0,0,2);//部件汇总表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",59,264,"部件编号",7,0,1,2);//部件编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,271,99,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",149,264,"型号",7,0,1,2);//型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,271,199,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",234,264,"名称",7,0,1,2);//名称
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",269,271,269,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",275,264,"数量",7,0,1,2);//数量
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",281,257,281,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",306,264,"厂家",7,0,1,2);//厂家
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,257,331,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",357,264,"部件备注",7,0,1,2);//部件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线8
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","部件汇总表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
            QString UnitTag=QueryEquipment.value("DT").toString();
            QString UnitType=QueryEquipment.value("Type").toString();
            QString UnitName=QueryEquipment.value("Name").toString();
            //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
            QString UnitNameStr=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+UnitTag;

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,QueryEquipment.value("PartCode").toString(),3.5,0,0,2);//部件编号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,Lasty,99,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",101,Lasty-3.5,UnitType,3.5,0,0,2);//型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,Lasty,199,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",201,Lasty-3.5,UnitName,3.5,0,0,2);//名称
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",269,Lasty,269,Lasty-7);//竖线5

            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            StrSql="SELECT * FROM Equipment WHERE PartCode = '"+QueryEquipment.value("PartCode").toString()+"'";
            QuerySearch.exec(StrSql);
            if(QuerySearch.last())
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",271,Lasty-3.5,QString::number(QuerySearch.at()+1),3.5,0,0,2);//数量
            else
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",271,Lasty-3.5,"0",3.5,0,0,2);//数量
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",281,Lasty,281,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",283,Lasty-3.5,QueryEquipment.value("Factory").toString(),3.5,0,0,2);//厂家
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,Lasty,331,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",333,Lasty-3.5,QueryEquipment.value("Remark").toString(),3.5,0,0,2);//部件备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_Btn_GenerateCableList_clicked()
{
    dlgGenerate.setWindowTitle("生成电缆列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(5);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '电缆列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"电缆列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '电缆列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"电缆列表")+"'";
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryWires = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Wires WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' AND Cable_ID <> '' ORDER BY ProjectStructure_ID";
        QueryWires.exec(StrSql);
        while(QueryWires.next())
        {
            if(QueryWires.value("Cable_ID").toString()=="") continue;
            if(QueryWires.value("TextHandle").toString()!="") continue;
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"MXB");
                SetCurLayer(GlobalBackAxWidget,"MXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"电缆列表",10,0,0,2);//电缆列表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",56,264,"电缆编号",7,0,1,2);//电缆编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",86,271,86,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",107,264,"电缆型号",7,0,1,2);//电缆型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",128,271,128,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",150,264,"线芯结构",7,0,1,2);//线芯结构
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",172,271,172,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",202,264,"源",7,0,1,2);//源
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",232,257,232,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",262,264,"目标",7,0,1,2);//目标
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",292,257,292,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",317,264,"页号",7,0,1,2);//页号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",342,257,342,271);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",362,264,"功能描述",7,0,1,2);//功能描述
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线9
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","电缆列表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString BHTag="";
            QSqlQuery QueryCable = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr="SELECT * FROM Cable WHERE Cable_ID = '"+QueryWires.value("Cable_ID").toString()+"'";
            QueryCable.exec(SqlStr);
            if(QueryCable.next())
            {
                BHTag= GetProjectStructureStrByProjectStructureID(QueryCable.value("ProjectStructure_ID").toInt())+"-"+QueryCable.value("CableNum").toString();
                if(QueryWires.value("Color").toString()!="") BHTag+="("+QueryWires.value("Color").toString()+")";
            }
            QString StrType=QueryCable.value("Type").toString();
            QString StrStructure=QueryCable.value("Structure").toString();

            QString StrSource,StrTarget;
            QSqlQuery QueryLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr="SELECT * FROM Line WHERE Wires_Handle = '"+QueryWires.value("Handle").toString()+"'";
            QueryLine.exec(SqlStr);
            if(QueryLine.next())
            {
                int Line_ID=QueryLine.value("Line_ID").toInt();
                QSqlQuery QueryConnectLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM ConnectLine WHERE ConnectLine_ID = "+QString::number(Line_ID);
                QueryConnectLine.exec(SqlStr);
                if(QueryConnectLine.next())
                {
                    if(QueryConnectLine.value("Symb1_Category").toString()=="0") StrSource=GetUnitTermStrByTermID(QueryConnectLine.value("Symb1_ID").toString());
                    if(QueryConnectLine.value("Symb1_Category").toString()=="1") StrSource=GetTerminalTermStrByTermID(QueryConnectLine.value("Symb1_ID").toString());
                    if(QueryConnectLine.value("Symb2_Category").toString()=="0") StrTarget=GetUnitTermStrByTermID(QueryConnectLine.value("Symb2_ID").toString());
                    if(QueryConnectLine.value("Symb2_Category").toString()=="1") StrTarget=GetTerminalTermStrByTermID(QueryConnectLine.value("Symb2_ID").toString());
                }
            }
            //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2

            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,BHTag,3.5,0,0,2);//电缆编号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",86,Lasty,86,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",88,Lasty-3.5,StrType,3.5,0,0,2);//电缆型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",128,Lasty,128,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",130,Lasty-3.5,StrStructure,3.5,0,0,2);//线芯结构
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",172,Lasty,172,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",174,Lasty-3.5,StrSource,3.5,0,0,2);//源
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",232,Lasty,232,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",234,Lasty-3.5,StrTarget,3.5,0,0,2);//目标
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",292,Lasty,292,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",294,Lasty-3.5,GetPageNameByPageID(QueryWires.value("Page_ID").toInt()),3.5,0,0,2);//页号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",342,Lasty,342,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",344,Lasty-3.5,QueryCable.value("Desc").toString(),3.5,0,0,2);//功能描述
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线9
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_CbUnitTogether_clicked()
{
    LoadUnitTable();
}

void MainWindow::on_TabUnit_currentChanged(int index)
{
    if(index==0) ui->CbUnitTogether->setVisible(false);
    else ui->CbUnitTogether->setVisible(true);
}

void MainWindow::on_tableWidgetUnit_doubleClicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    int Equipment_ID=ui->tableWidgetUnit->item(index.row(),0)->data(Qt::UserRole).toInt();
    qDebug()<<"Equipment_ID="<<Equipment_ID;
    ShowUnitAttrByEquipment_ID(Equipment_ID);
}

void MainWindow::on_BtnPageFilter_clicked()
{
    FilterPage();
}

void MainWindow::on_CbPageGaocengFilter_currentIndexChanged(const QString &arg1)
{
    FilterPage();
}

void MainWindow::on_CbPagePosFilter_currentIndexChanged(const QString &arg1)
{
    FilterPage();
}

void MainWindow::on_CbPageTypeFilter_currentIndexChanged(const QString &arg1)
{
    FilterPage();
}

void MainWindow::on_EdPageFilter_editingFinished()
{
    FilterPage();
}

void MainWindow::on_BtnUnitFilter_clicked()
{
    FilterUnit();
}

void MainWindow::on_CbUnitGaoceng_currentIndexChanged(const QString &arg1)
{
    FilterUnit();
}

void MainWindow::on_CbUnitPos_currentIndexChanged(const QString &arg1)
{
    FilterUnit();
}

void MainWindow::on_CbUnitPage_currentIndexChanged(const QString &arg1)
{
    FilterUnit();
}

void MainWindow::on_EdUnitTagSearch_editingFinished()
{
    FilterUnit();
}

void MainWindow::on_BtnTermFilter_clicked()
{
    FilterTerminal();
}

void MainWindow::on_CbTermGaoceng_currentIndexChanged(const QString &arg1)
{
    FilterTerminal();
}

void MainWindow::on_CbTermPos_currentIndexChanged(const QString &arg1)
{
    FilterTerminal();
}

void MainWindow::on_CbTermPage_currentIndexChanged(const QString &arg1)
{
    FilterTerminal();
}

void MainWindow::on_EdTermTagFilter_editingFinished()
{
    FilterTerminal();
}

void MainWindow::on_tabWidgetLine_currentChanged(int index)
{
    ui->stackedWidgetLine->setCurrentIndex(index);
}

void MainWindow::on_BtnLineFilter_clicked()
{
    FilterLines();
}

void MainWindow::on_CbLineGaoceng_currentIndexChanged(const QString &arg1)
{
    FilterLines();
}

void MainWindow::on_CbLinePos_currentIndexChanged(const QString &arg1)
{
    FilterLines();
}

void MainWindow::on_CbLinePage_currentIndexChanged(const QString &arg1)
{
    FilterLines();
}

void MainWindow::on_EdLineTagFilter_editingFinished()
{
    FilterLines();
}

QString RecentPath="";
void MainWindow::on_BtnOpenPage_clicked()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("打开图纸"));
    if(RecentPath!="") fileDialog.setDirectory(RecentPath);
    else fileDialog.setDirectory(LocalProjectDefaultPath);
    fileDialog.setNameFilter(tr("dwg(*.dwg)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();

    QFileInfo fileinfo(fileNames.at(0));
    if(!fileinfo.exists()) return;
    QString dwgfilename=fileinfo.fileName();
    dwgfilename=dwgfilename.mid(0,dwgfilename.lastIndexOf(".dwg"));
    QString dwgfilepath=fileinfo.filePath();
    RecentPath=dwgfilepath;
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
            return;
        }
    }
    //创建新的mdi
    formaxwidget *formMxdraw=new formaxwidget(this,dwgfilepath);
    formMxdraw->setWindowTitle(dwgfilename);
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
}

//刷新终端功能子块链路
