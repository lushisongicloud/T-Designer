#include "dialogfactoryedit.h"
#include "ui_dialogfactoryedit.h"

DialogFactoryEdit::DialogFactoryEdit(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogFactoryEdit)
{
    ui->setupUi(this);
}

DialogFactoryEdit::~DialogFactoryEdit()
{
    delete ui;
}

void DialogFactoryEdit::on_BtnOK_clicked()
{
    if(ui->EdFactory->text()=="")
    {
        QMessageBox::warning(this,"提示","生产厂家名称为空！");
        return;
    }
    Canceled=false;
    QSqlQuery QueryVar(T_LibDatabase);
    QString tempSQL;
    if(Mode==0)
    {
        tempSQL="UPDATE Factory SET Factory=:Factory,ForShort=:ForShort,Logo=:Logo,WebSite=:WebSite,Remark=:Remark WHERE Factory_ID = '"+Factory_ID+"'";
        QueryVar.prepare(tempSQL);
        QueryVar.bindValue(":Factory",ui->EdFactory->text());
        QueryVar.bindValue(":ForShort",ui->EdForShort->text());
        QueryVar.bindValue(":Logo",ui->EdLogo->text());
        QueryVar.bindValue(":WebSite",ui->EdWebSite->text());
        QueryVar.bindValue(":Remark",ui->EdRemark->text());
        QueryVar.exec();
    }
    else
    {
        tempSQL = QString("INSERT INTO Factory (Factory_ID,Factory,ForShort,Logo,WebSite,Remark,_Order)"
                                       "VALUES (:Factory_ID,:Factory,:ForShort,:Logo,:WebSite,:Remark,:_Order)");
        QueryVar.prepare(tempSQL);
        Factory_ID=QString::number(GetMaxIDOfLibDatabase(T_LibDatabase,"Factory","Factory_ID"));
        QueryVar.bindValue(":Factory_ID",Factory_ID);
        QueryVar.bindValue(":Factory",ui->EdFactory->text());
        QueryVar.bindValue(":ForShort",ui->EdForShort->text());
        QueryVar.bindValue(":Logo",ui->EdLogo->text());
        QueryVar.bindValue(":WebSite",ui->EdWebSite->text());
        QueryVar.bindValue(":Remark",ui->EdRemark->text());
        QueryVar.bindValue(":_Order",_Order);
        QueryVar.exec();
    }
    this->close();
}

void DialogFactoryEdit::LoadInfo(QString Factory_ID)
{
    this->Factory_ID=Factory_ID;
    QSqlQuery QueryVar = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM Factory WHERE Factory_ID = '"+Factory_ID+"'";
    QueryVar.exec(temp);
    if(QueryVar.next())
    {
        ui->EdFactory->setText(QueryVar.value("Factory").toString());
        ui->EdForShort->setText(QueryVar.value("ForShort").toString());
        ui->EdLogo->setText(QueryVar.value("Logo").toString());
        ui->EdRemark->setText(QueryVar.value("Remark").toString());
        ui->EdWebSite->setText(QueryVar.value("WebSite").toString());
        QPixmap p=QPixmap("C:/TBD/LOGO/"+QueryVar.value("Logo").toString());
        ui->LbPic->setStyleSheet("background-color: rgb(255, 255, 255)");
        ui->LbPic->setScaledContents(false);
        ui->LbPic->setFrameShape(QFrame::Panel);
        ui->LbPic->setFrameShadow(QFrame::Sunken);
        ui->LbPic->setLineWidth(3);
        ui->LbPic->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);
        ui->LbPic->setPixmap(p.scaled(ui->LbPic->width(),ui->LbPic->height()));
    }
}

void DialogFactoryEdit::on_BtnCancel_clicked()
{
    Canceled=true;
    this->close();
}

void DialogFactoryEdit::on_BtnSetLogo_clicked()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("选择文件"));
    fileDialog.setDirectory("C:/TBD/LOGO/");
    QStringList filter;
    //filter << "*.jpg" << "*.png" << "*.bmp" << "*.gif";
    //fileDialog.setNameFilters(filter);
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    QPixmap p=QPixmap(fileNames.at(0));
    ui->LbPic->setPixmap(p.scaled(ui->LbPic->width(),ui->LbPic->height()));
    QFileInfo file_info(fileNames.at(0));
    QFile::copy(fileNames.at(0),"C:/TBD/LOGO/"+file_info.fileName());
    ui->EdLogo->setText(file_info.fileName());
}
