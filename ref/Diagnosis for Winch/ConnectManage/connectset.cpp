#include "connectset.h"
#include "ui_connectset.h"
#include <QMessageBox>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

ConnectSet::ConnectSet(QWidget *parent,myQSqlDatabase *TMATE_Database) :
    QWidget(parent),ui(new Ui::ConnectSet),m_Database(TMATE_Database)

{
    ui->setupUi(this);

    //设置遮罩窗口
    mpShadeWindow = new QWidget(this);
    QString str("QWidget{background-color:rgba(0,0,0,0.6);}");
    mpShadeWindow->setStyleSheet(str);
    mpShadeWindow->setGeometry(0, 0, 1, 1);
    mpShadeWindow->hide();

    InitSystemConfigUI();
}

ConnectSet::~ConnectSet()
{
    delete ui;
    delete mpShadeWindow;
}

void ConnectSet::SetConfigurationEnabled(bool enable)
{
    ui->lineEdit_MK2CPU_IP->setEnabled(enable);
    ui->pushButton_MK2CPU_IP_SET->setEnabled(enable);

    ui->lineEdit_MK2CPU_PORT->setEnabled(enable);
    ui->pushButton_MK2CPU_PORT_SET->setEnabled(enable);

    ui->lineEdit_MK5CPU_IP->setEnabled(enable);
    ui->pushButton_MK5CPU_IP_SET->setEnabled(enable);

    ui->lineEdit_MK5CPU_PORT->setEnabled(enable);
    ui->pushButton_MK5CPU_PORT_SET->setEnabled(enable);

    ui->lineEdit_Detector1_IP->setEnabled(enable);
    ui->pushButton_Detector1_IP_SET->setEnabled(enable);

    ui->lineEdit_Detector1_PORT->setEnabled(enable);
    ui->pushButton_Detector1_PORT_SET->setEnabled(enable);

    ui->lineEdit_Detector2_IP->setEnabled(enable);
    ui->pushButton_Detector2_IP_SET->setEnabled(enable);

    ui->lineEdit_Detector2_PORT->setEnabled(enable);
    ui->pushButton_Detector2_PORT_SET->setEnabled(enable);

    ui->lineEdit_Detector3_IP->setEnabled(enable);
    ui->pushButton_Detector3_IP_SET->setEnabled(enable);

    ui->lineEdit_Detector3_PORT->setEnabled(enable);
    ui->pushButton_Detector3_PORT_SET->setEnabled(enable);
}

void ConnectSet::InitSystemConfigUI()
{//初始化系统IP设置UI
    DataBase::Str_communication communication;

    //查询MK2通信配置
    communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable("MK2CPU");
    if(communication.Name!="MK2CPU"){
        QMessageBox::warning(nullptr, "错误", "MK2CPU通信配置信息不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    ui->lineEdit_MK2CPU_IP->setText(communication.IP);
    ui->lineEdit_MK2CPU_PORT->setText(communication.Port);

    //查询MK5通信配置
    communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable("MK5CPU");
    if(communication.Name!="MK5CPU"){
        QMessageBox::warning(nullptr, "错误", "MK5CPU通信配置信息不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    ui->lineEdit_MK5CPU_IP->setText(communication.IP);
    ui->lineEdit_MK5CPU_PORT->setText(communication.Port);

    //查询Detector1通信配置
    communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable("Detector1");
    if(communication.Name!="Detector1"){
        QMessageBox::warning(nullptr, "错误", "Detector1通信配置信息不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    ui->lineEdit_Detector1_IP->setText(communication.IP);
    ui->lineEdit_Detector1_PORT->setText(communication.Port);

    //查询Detector2通信配置
    communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable("Detector2");
    if(communication.Name!="Detector2"){
        QMessageBox::warning(nullptr, "错误", "Detector2通信配置信息不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    ui->lineEdit_Detector2_IP->setText(communication.IP);
    ui->lineEdit_Detector2_PORT->setText(communication.Port);

    //查询Detector3通信配置
    communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable("Detector3");
    if(communication.Name!="Detector3"){
        QMessageBox::warning(nullptr, "错误", "Detector3通信配置信息不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }
    ui->lineEdit_Detector3_IP->setText(communication.IP);
    ui->lineEdit_Detector3_PORT->setText(communication.Port);
}

void ConnectSet::on_pushButton_MK2CPU_IP_SET_clicked()
{//系统配置 MK2CPU 通信配置
    DataBase::Str_communication communication;
    communication.Name = "MK2CPU";
    communication.IP = ui->lineEdit_MK2CPU_IP->text();
    communication.Port = ui->lineEdit_MK2CPU_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "MK2CPU通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "MK2CPU通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_MK2CPU_PORT_SET_clicked()
{//系统配置 MK2CPU 通信配置
    DataBase::Str_communication communication;
    communication.Name = "MK2CPU";
    communication.IP = ui->lineEdit_MK2CPU_IP->text();
    communication.Port = ui->lineEdit_MK2CPU_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "MK2CPU通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "MK2CPU通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_MK5CPU_IP_SET_clicked()
{//系统配置 MK5CPU 通信配置
    DataBase::Str_communication communication;
    communication.Name = "MK5CPU";
    communication.IP = ui->lineEdit_MK5CPU_IP->text();
    communication.Port = ui->lineEdit_MK5CPU_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "MK5CPU通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "MK5CPU通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_MK5CPU_PORT_SET_clicked()
{//系统配置 MK5CPU 通信配置
    DataBase::Str_communication communication;
    communication.Name = "MK5CPU";
    communication.IP = ui->lineEdit_MK5CPU_IP->text();
    communication.Port = ui->lineEdit_MK5CPU_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "MK5CPU通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "MK5CPU通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_Detector1_IP_SET_clicked()
{//系统配置 Detector1 通信配置
    DataBase::Str_communication communication;
    communication.Name = "Detector1";
    communication.IP = ui->lineEdit_Detector1_IP->text();
    communication.Port = ui->lineEdit_Detector1_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "Detector1通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "Detector1通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_Detector1_PORT_SET_clicked()
{//系统配置 Detector1 通信配置
    DataBase::Str_communication communication;
    communication.Name = "Detector1";
    communication.IP = ui->lineEdit_Detector1_IP->text();
    communication.Port = ui->lineEdit_Detector1_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "Detector1通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "Detector1通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_Detector2_IP_SET_clicked()
{//系统配置 Detector2 通信配置
    DataBase::Str_communication communication;
    communication.Name = "Detector2";
    communication.IP = ui->lineEdit_Detector2_IP->text();
    communication.Port = ui->lineEdit_Detector2_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "Detector2通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "Detector2通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_Detector2_PORT_SET_clicked()
{//系统配置 Detector2 通信配置
    DataBase::Str_communication communication;
    communication.Name = "Detector2";
    communication.IP = ui->lineEdit_Detector2_IP->text();
    communication.Port = ui->lineEdit_Detector2_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "Detector2通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "Detector2通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_Detector3_IP_SET_clicked()
{//系统配置 Detector3 通信配置
    DataBase::Str_communication communication;
    communication.Name = "Detector3";
    communication.IP = ui->lineEdit_Detector3_IP->text();
    communication.Port = ui->lineEdit_Detector3_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "Detector3通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "Detector3通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}

void ConnectSet::on_pushButton_Detector3_PORT_SET_clicked()
{//系统配置 Detector3 通信配置
    DataBase::Str_communication communication;
    communication.Name = "Detector3";
    communication.IP = ui->lineEdit_Detector3_IP->text();
    communication.Port = ui->lineEdit_Detector3_PORT->text();

    //更新数据库系统中的通信配置信息
    if(m_Database->UpdateCommunicationInforToCommunicationConfigTable(communication)){
        QMessageBox::warning(nullptr, "提示", "Detector3通信配置信息完成",QMessageBox::Ok);
        InitSystemConfigUI();
    }
    else{

        QMessageBox::warning(nullptr, "错误", "Detector3通信配置信息配置失败",QMessageBox::Ok);
        InitSystemConfigUI();
    }
}
