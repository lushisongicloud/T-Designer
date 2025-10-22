#include "dialognewproject.h"
#include "ui_dialognewproject.h"

DialogNewProject::DialogNewProject(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogNewProject)
{
    ui->setupUi(this);
    ui->LbProjectPath->setText(LocalProjectDefaultPath);
    Canceled=true;
}

DialogNewProject::~DialogNewProject()
{
    delete ui;
}

void DialogNewProject::on_BtnBrowse_clicked()
{
    QString directory = QFileDialog::getExistingDirectory(
                        this,
                        tr("选择文件夹"),
                        LocalProjectDefaultPath,
                        QFileDialog::ShowDirsOnly);
    if (!directory.isEmpty())
    {
          ui->LbProjectPath->setText(directory);
    }
}

void DialogNewProject::on_BtnOK_clicked()
{
    Canceled=false;

    QFile file(ui->LbProjectPath->text()+"/"+ui->EdProjectName->text()+".swPro");
    if(!file.open(QIODevice::WriteOnly))//以写的方式打开文件，如果文件不存在则创建，
       return;

    file.write(ui->EdProjectName->text().toLocal8Bit().data());//写入文件，支持QByteArray和 char * 类型数据写入
    file.close();//关闭文件
    //创建数据库
    QString SourceFileName,DestFileName;
    /* 为方便调试，暂时修改SourceFile到项目目录./templete/project.db
    SourceFileName=LocalDataBasePath;
    SourceFileName.append("/project.db");
    */
    SourceFileName = "./templete/project.db";
    DestFileName=ui->LbProjectPath->text()+"/"+ui->EdProjectName->text()+".db";
    QFile::copy(SourceFileName,DestFileName);
    //建立ProjectStructure中的工程记录
    QSqlDatabase T_ProjectDatabase = QSqlDatabase::addDatabase("QSQLITE",ui->EdProjectName->text());
    QFile  File(ui->LbProjectPath->text()+"/"+ui->EdProjectName->text()+".db");
    if(!File.exists()){
            QMessageBox::warning(nullptr, "错误", "数据库文件不存在",
                                 QMessageBox::Ok,QMessageBox::NoButton);
            return ;
    }
    else
        T_ProjectDatabase.setDatabaseName(ui->LbProjectPath->text()+"/"+ui->EdProjectName->text()+".db");
    if (!T_ProjectDatabase.open()){
        QMessageBox::warning(nullptr, "错误", "打开数据库失败",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return ;
    }
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString tempSQL = QString("INSERT INTO ProjectStructure (ProjectStructure_ID,Structure_ID,Structure_INT,Parent_ID,Struct_Desc)"
                                   "VALUES (:ProjectStructure_ID,:Structure_ID,:Structure_INT,:Parent_ID,:Struct_Desc)");
    QueryVar.prepare(tempSQL);
    QueryVar.bindValue(":ProjectStructure_ID",1001);
    QueryVar.bindValue(":Structure_ID","1");
    QueryVar.bindValue(":Structure_INT",ui->EdProjectName->text());
    QueryVar.bindValue(":Parent_ID","0");
    QueryVar.bindValue(":Struct_Desc","V1.0");
    QueryVar.exec();
    T_ProjectDatabase.close();

    SourceFileName=LocalDataBasePath;
    SourceFileName.append("/LdMainData_T.db");
    DestFileName=ui->LbProjectPath->text()+"/LdMainData_T.db";
    QFile::copy(SourceFileName,DestFileName);

    SourceFileName=LocalDataBasePath;
    SourceFileName.append("/test.params");
    DestFileName=ui->LbProjectPath->text()+"/test.params";
    QFile::copy(SourceFileName,DestFileName);

    ProjectPath=ui->LbProjectPath->text()+"/";
    ProjectName=ui->EdProjectName->text();
    close();
}

void DialogNewProject::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}
