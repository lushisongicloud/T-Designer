#include "formrealtimedata.h"
#include "ui_formrealtimedata.h"
#include <QDebug>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif
extern int NetSt[5];
FormRealTimeData::FormRealTimeData(QWidget *parent) :
    QWidget(parent),
    ui(new Ui::FormRealTimeData)
{
    ui->setupUi(this);

    ui->stackedWidgetRealTimeData->setCurrentIndex(0);
    ui->label_RealTimeDataCurrentPageNum->setText(QString::number(1));
    ui->label_RealTimeDataSumageNum->setText(QString::number(ui->stackedWidgetRealTimeData->count()));
}

FormRealTimeData::~FormRealTimeData()
{
    delete ui;
}

void FormRealTimeData::UpDate(QMap<QString,DataBase::Signal> signal)
{
    // 更新 INT 类型的信号
    if(signal.contains("WCC_PLC_HeartBeat")) ui->WCC_PLC_HeartBeat->setText(QString::number(signal["WCC_PLC_HeartBeat"].value.INT));
    if(signal.contains("WCC_VFD1_HeartBeat")) ui->WCC_VFD1_HeartBeat->setText(QString::number(signal["WCC_VFD1_HeartBeat"].value.INT));
    if(signal.contains("WCC_VFD2_HeartBeat")) ui->WCC_VFD2_HeartBeat->setText(QString::number(signal["WCC_VFD2_HeartBeat"].value.INT));
    if(signal.contains("WCC_VFD3_HeartBeat")) ui->WCC_VFD3_HeartBeat->setText(QString::number(signal["WCC_VFD3_HeartBeat"].value.INT));
    if(signal.contains("WCC_IAU_HeartBeat")) ui->WCC_IAU_HeartBeat->setText(QString::number(signal["WCC_IAU_HeartBeat"].value.INT));
    if(signal.contains("WCC_PLC_WorkMode")) ui->WCC_PLC_WorkMode->setText(QString::number(signal["WCC_PLC_WorkMode"].value.INT));
    if(signal.contains("WCC_PLC_CNT0")) ui->WCC_PLC_CNT0->setText(QString::number(signal["WCC_PLC_CNT0"].value.INT));
    if(signal.contains("WCC_PLC_CNT1")) ui->WCC_PLC_CNT1->setText(QString::number(signal["WCC_PLC_CNT1"].value.INT));
    if(signal.contains("JB_IAU_IW1000")) ui->JB_IAU_IW1000->setText(QString::number(signal["JB_IAU_IW1000"].value.INT));
    if(signal.contains("JB_IAU_IW1004")) ui->JB_IAU_IW1004->setText(QString::number(signal["JB_IAU_IW1004"].value.INT));
    if(signal.contains("JB_IAU_IW1008")) ui->JB_IAU_IW1008->setText(QString::number(signal["JB_IAU_IW1008"].value.INT));

    // 更新 DOUBLE 类型的信号
    if(signal.contains("WCC_PLC_Para_CableLength")) ui->WCC_PLC_Para_CableLength->setText(QString::number(signal["WCC_PLC_Para_CableLength"].value.DOUBLE,'f',2));
    if(signal.contains("WCC_PLC_Para_ArrayLength")) ui->WCC_PLC_Para_ArrayLength->setText(QString::number(signal["WCC_PLC_Para_ArrayLength"].value.DOUBLE,'f',2));
    if(signal.contains("WCC_PLC_Para_ArrayDepth")) ui->WCC_PLC_Para_ArrayDepth->setText(QString::number(signal["WCC_PLC_Para_ArrayDepth"].value.DOUBLE,'f',2));
    if(signal.contains("WCC_PLC_Para_SeaDepth")) ui->WCC_PLC_Para_SeaDepth->setText(QString::number(signal["WCC_PLC_Para_SeaDepth"].value.DOUBLE,'f',2));
    if(signal.contains("WCC_PLC_Para_Tension")) ui->WCC_PLC_Para_Tension->setText(QString::number(signal["WCC_PLC_Para_Tension"].value.DOUBLE,'f',0));
    if(signal.contains("WCC_PLC_IW96")) ui->WCC_PLC_IW96->setText(QString::number(signal["WCC_PLC_IW96"].value.DOUBLE,'f',1));
    if(signal.contains("WCC_PLC_QW112")) ui->WCC_PLC_QW112->setText(QString::number(signal["WCC_PLC_QW112"].value.DOUBLE,'f',3));
    if(signal.contains("WCC_PLC_QW114")) ui->WCC_PLC_QW114->setText(QString::number(signal["WCC_PLC_QW114"].value.DOUBLE,'f',3));
    if(signal.contains("WCC_PLC_QW48")) ui->WCC_PLC_QW48->setText(QString::number(signal["WCC_PLC_QW48"].value.DOUBLE,'f',3));
    if(signal.contains("WCC_VFD1_AI1")) ui->WCC_VFD1_AI1->setText(QString::number(signal["WCC_VFD1_AI1"].value.DOUBLE,'f',3));
    if(signal.contains("WCC_VFD2_AI1")) ui->WCC_VFD2_AI1->setText(QString::number(signal["WCC_VFD2_AI1"].value.DOUBLE,'f',3));
    if(signal.contains("WCC_VFD3_AI2")) ui->WCC_VFD3_AI2->setText(QString::number(signal["WCC_VFD3_AI2"].value.DOUBLE,'f',3));
    if(signal.contains("JB_IAU_IW64")) ui->JB_IAU_IW64->setText(QString::number(signal["JB_IAU_IW64"].value.DOUBLE,'f',1));

    // 更新 BOOL 类型的信号
    if(signal.contains("WCC_PLC_Alarm1")) ui->WCC_PLC_Alarm1->setText(QString::number(signal["WCC_PLC_Alarm1"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm2")) ui->WCC_PLC_Alarm2->setText(QString::number(signal["WCC_PLC_Alarm2"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm3")) ui->WCC_PLC_Alarm3->setText(QString::number(signal["WCC_PLC_Alarm3"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm4")) ui->WCC_PLC_Alarm4->setText(QString::number(signal["WCC_PLC_Alarm4"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm5")) ui->WCC_PLC_Alarm5->setText(QString::number(signal["WCC_PLC_Alarm5"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm6")) ui->WCC_PLC_Alarm6->setText(QString::number(signal["WCC_PLC_Alarm6"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm7")) ui->WCC_PLC_Alarm7->setText(QString::number(signal["WCC_PLC_Alarm7"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm8")) ui->WCC_PLC_Alarm8->setText(QString::number(signal["WCC_PLC_Alarm8"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm9")) ui->WCC_PLC_Alarm9->setText(QString::number(signal["WCC_PLC_Alarm9"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm10")) ui->WCC_PLC_Alarm10->setText(QString::number(signal["WCC_PLC_Alarm10"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm11")) ui->WCC_PLC_Alarm11->setText(QString::number(signal["WCC_PLC_Alarm11"].value.BOOL));
    if(signal.contains("WCC_PLC_Alarm12")) ui->WCC_PLC_Alarm12->setText(QString::number(signal["WCC_PLC_Alarm12"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_0")) ui->WCC_PLC_I0_0->setText(QString::number(signal["WCC_PLC_I0_0"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_1")) ui->WCC_PLC_I0_1->setText(QString::number(signal["WCC_PLC_I0_1"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_2")) ui->WCC_PLC_I0_2->setText(QString::number(signal["WCC_PLC_I0_2"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_3")) ui->WCC_PLC_I0_3->setText(QString::number(signal["WCC_PLC_I0_3"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_4")) ui->WCC_PLC_I0_4->setText(QString::number(signal["WCC_PLC_I0_4"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_5")) ui->WCC_PLC_I0_5->setText(QString::number(signal["WCC_PLC_I0_5"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_6")) ui->WCC_PLC_I0_6->setText(QString::number(signal["WCC_PLC_I0_6"].value.BOOL));
    if(signal.contains("WCC_PLC_I0_7")) ui->WCC_PLC_I0_7->setText(QString::number(signal["WCC_PLC_I0_7"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_0")) ui->WCC_PLC_I1_0->setText(QString::number(signal["WCC_PLC_I1_0"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_1")) ui->WCC_PLC_I1_1->setText(QString::number(signal["WCC_PLC_I1_1"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_2")) ui->WCC_PLC_I1_2->setText(QString::number(signal["WCC_PLC_I1_2"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_3")) ui->WCC_PLC_I1_3->setText(QString::number(signal["WCC_PLC_I1_3"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_4")) ui->WCC_PLC_I1_4->setText(QString::number(signal["WCC_PLC_I1_4"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_5")) ui->WCC_PLC_I1_5->setText(QString::number(signal["WCC_PLC_I1_5"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_6")) ui->WCC_PLC_I1_6->setText(QString::number(signal["WCC_PLC_I1_6"].value.BOOL));
    if(signal.contains("WCC_PLC_I1_7")) ui->WCC_PLC_I1_7->setText(QString::number(signal["WCC_PLC_I1_7"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_0")) ui->WCC_PLC_I2_0->setText(QString::number(signal["WCC_PLC_I2_0"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_1")) ui->WCC_PLC_I2_1->setText(QString::number(signal["WCC_PLC_I2_1"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_2")) ui->WCC_PLC_I2_2->setText(QString::number(signal["WCC_PLC_I2_2"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_3")) ui->WCC_PLC_I2_3->setText(QString::number(signal["WCC_PLC_I2_3"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_4")) ui->WCC_PLC_I2_4->setText(QString::number(signal["WCC_PLC_I2_4"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_5")) ui->WCC_PLC_I2_5->setText(QString::number(signal["WCC_PLC_I2_5"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_6")) ui->WCC_PLC_I2_6->setText(QString::number(signal["WCC_PLC_I2_6"].value.BOOL));
    if(signal.contains("WCC_PLC_I2_7")) ui->WCC_PLC_I2_7->setText(QString::number(signal["WCC_PLC_I2_7"].value.BOOL));
    if(signal.contains("WCC_PLC_I80_0")) ui->WCC_PLC_I80_0->setText(QString::number(signal["WCC_PLC_I80_0"].value.BOOL));
    if(signal.contains("WCC_PLC_I80_1")) ui->WCC_PLC_I80_1->setText(QString::number(signal["WCC_PLC_I80_1"].value.BOOL));
    if(signal.contains("WCC_PLC_I80_2")) ui->WCC_PLC_I80_2->setText(QString::number(signal["WCC_PLC_I80_2"].value.BOOL));
    if(signal.contains("WCC_PLC_I80_3")) ui->WCC_PLC_I80_3->setText(QString::number(signal["WCC_PLC_I80_3"].value.BOOL));
    if(signal.contains("WCC_PLC_I80_4")) ui->WCC_PLC_I80_4->setText(QString::number(signal["WCC_PLC_I80_4"].value.BOOL));
    if(signal.contains("WCC_PLC_I80_5")) ui->WCC_PLC_I80_5->setText(QString::number(signal["WCC_PLC_I80_5"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_0")) ui->WCC_PLC_Q0_0->setText(QString::number(signal["WCC_PLC_Q0_0"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_1")) ui->WCC_PLC_Q0_1->setText(QString::number(signal["WCC_PLC_Q0_1"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_2")) ui->WCC_PLC_Q0_2->setText(QString::number(signal["WCC_PLC_Q0_2"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_3")) ui->WCC_PLC_Q0_3->setText(QString::number(signal["WCC_PLC_Q0_3"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_4")) ui->WCC_PLC_Q0_4->setText(QString::number(signal["WCC_PLC_Q0_4"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_5")) ui->WCC_PLC_Q0_5->setText(QString::number(signal["WCC_PLC_Q0_5"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_6")) ui->WCC_PLC_Q0_6->setText(QString::number(signal["WCC_PLC_Q0_6"].value.BOOL));
    if(signal.contains("WCC_PLC_Q0_7")) ui->WCC_PLC_Q0_7->setText(QString::number(signal["WCC_PLC_Q0_7"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_0")) ui->WCC_PLC_Q1_0->setText(QString::number(signal["WCC_PLC_Q1_0"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_1")) ui->WCC_PLC_Q1_1->setText(QString::number(signal["WCC_PLC_Q1_1"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_2")) ui->WCC_PLC_Q1_2->setText(QString::number(signal["WCC_PLC_Q1_2"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_3")) ui->WCC_PLC_Q1_3->setText(QString::number(signal["WCC_PLC_Q1_3"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_4")) ui->WCC_PLC_Q1_4->setText(QString::number(signal["WCC_PLC_Q1_4"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_5")) ui->WCC_PLC_Q1_5->setText(QString::number(signal["WCC_PLC_Q1_5"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_6")) ui->WCC_PLC_Q1_6->setText(QString::number(signal["WCC_PLC_Q1_6"].value.BOOL));
    if(signal.contains("WCC_PLC_Q1_7")) ui->WCC_PLC_Q1_7->setText(QString::number(signal["WCC_PLC_Q1_7"].value.BOOL));
    if(signal.contains("WCC_PLC_Q64_4")) ui->WCC_PLC_Q64_4->setText(QString::number(signal["WCC_PLC_Q64_4"].value.BOOL));
    if(signal.contains("WCC_PLC_Q64_5")) ui->WCC_PLC_Q64_5->setText(QString::number(signal["WCC_PLC_Q64_5"].value.BOOL));
    if(signal.contains("WCC_PLC_Q64_6")) ui->WCC_PLC_Q64_6->setText(QString::number(signal["WCC_PLC_Q64_6"].value.BOOL));
    if(signal.contains("WCC_PLC_Q64_7")) ui->WCC_PLC_Q64_7->setText(QString::number(signal["WCC_PLC_Q64_7"].value.BOOL));
    if(signal.contains("WCC_VFD1_DI1")) ui->WCC_VFD1_DI1->setText(QString::number(signal["WCC_VFD1_DI1"].value.BOOL));
    if(signal.contains("WCC_VFD1_DI2")) ui->WCC_VFD1_DI2->setText(QString::number(signal["WCC_VFD1_DI2"].value.BOOL));
    if(signal.contains("WCC_VFD1_DI4")) ui->WCC_VFD1_DI4->setText(QString::number(signal["WCC_VFD1_DI4"].value.BOOL));
    if(signal.contains("WCC_VFD1_DI6")) ui->WCC_VFD1_DI6->setText(QString::number(signal["WCC_VFD1_DI6"].value.BOOL));
    if(signal.contains("WCC_VFD1_DO1")) ui->WCC_VFD1_DO1->setText(QString::number(signal["WCC_VFD1_DO1"].value.BOOL));
    if(signal.contains("WCC_VFD1_DO2")) ui->WCC_VFD1_DO2->setText(QString::number(signal["WCC_VFD1_DO2"].value.BOOL));
    if(signal.contains("WCC_VFD1_DO3")) ui->WCC_VFD1_DO3->setText(QString::number(signal["WCC_VFD1_DO3"].value.BOOL));
    if(signal.contains("WCC_VFD2_DI1")) ui->WCC_VFD2_DI1->setText(QString::number(signal["WCC_VFD2_DI1"].value.BOOL));
    if(signal.contains("WCC_VFD2_DI2")) ui->WCC_VFD2_DI2->setText(QString::number(signal["WCC_VFD2_DI2"].value.BOOL));
    if(signal.contains("WCC_VFD2_DI4")) ui->WCC_VFD2_DI4->setText(QString::number(signal["WCC_VFD2_DI4"].value.BOOL));
    if(signal.contains("WCC_VFD2_DI6")) ui->WCC_VFD2_DI6->setText(QString::number(signal["WCC_VFD2_DI6"].value.BOOL));
    if(signal.contains("WCC_VFD2_DO1")) ui->WCC_VFD2_DO1->setText(QString::number(signal["WCC_VFD2_DO1"].value.BOOL));
    if(signal.contains("WCC_VFD2_DO2")) ui->WCC_VFD2_DO2->setText(QString::number(signal["WCC_VFD2_DO2"].value.BOOL));
    if(signal.contains("WCC_VFD2_DO3")) ui->WCC_VFD2_DO3->setText(QString::number(signal["WCC_VFD2_DO3"].value.BOOL));
    if(signal.contains("WCC_VFD3_DI1")) ui->WCC_VFD3_DI1->setText(QString::number(signal["WCC_VFD3_DI1"].value.BOOL));
    if(signal.contains("WCC_VFD3_DI2")) ui->WCC_VFD3_DI2->setText(QString::number(signal["WCC_VFD3_DI2"].value.BOOL));
    if(signal.contains("WCC_VFD3_DI5")) ui->WCC_VFD3_DI5->setText(QString::number(signal["WCC_VFD3_DI5"].value.BOOL));
    if(signal.contains("WCC_VFD3_DO5")) ui->WCC_VFD3_DO5->setText(QString::number(signal["WCC_VFD3_DO5"].value.BOOL));
    if(signal.contains("JB_IAU_I0_0")) ui->JB_IAU_I0_0->setText(QString::number(signal["JB_IAU_I0_0"].value.BOOL));
    if(signal.contains("JB_IAU_I0_1")) ui->JB_IAU_I0_1->setText(QString::number(signal["JB_IAU_I0_1"].value.BOOL));
    if(signal.contains("JB_IAU_I0_2")) ui->JB_IAU_I0_2->setText(QString::number(signal["JB_IAU_I0_2"].value.BOOL));
    if(signal.contains("JB_IAU_I0_3")) ui->JB_IAU_I0_3->setText(QString::number(signal["JB_IAU_I0_3"].value.BOOL));
    if(signal.contains("JB_IAU_I0_4")) ui->JB_IAU_I0_4->setText(QString::number(signal["JB_IAU_I0_4"].value.BOOL));
    if(signal.contains("JB_IAU_I0_5")) ui->JB_IAU_I0_5->setText(QString::number(signal["JB_IAU_I0_5"].value.BOOL));
    if(signal.contains("JB_IAU_I0_6")) ui->JB_IAU_I0_6->setText(QString::number(signal["JB_IAU_I0_6"].value.BOOL));
    if(signal.contains("JB_IAU_I0_7")) ui->JB_IAU_I0_7->setText(QString::number(signal["JB_IAU_I0_7"].value.BOOL));
    if(signal.contains("JB_IAU_I1_0")) ui->JB_IAU_I1_0->setText(QString::number(signal["JB_IAU_I1_0"].value.BOOL));
    if(signal.contains("JB_IAU_I1_1")) ui->JB_IAU_I1_1->setText(QString::number(signal["JB_IAU_I1_1"].value.BOOL));
    if(signal.contains("JB_IAU_I1_2")) ui->JB_IAU_I1_2->setText(QString::number(signal["JB_IAU_I1_2"].value.BOOL));
    if(signal.contains("JB_IAU_I1_3")) ui->JB_IAU_I1_3->setText(QString::number(signal["JB_IAU_I1_3"].value.BOOL));
    if(signal.contains("JB_IAU_I1_4")) ui->JB_IAU_I1_4->setText(QString::number(signal["JB_IAU_I1_4"].value.BOOL));
    if(signal.contains("JB_IAU_I1_5")) ui->JB_IAU_I1_5->setText(QString::number(signal["JB_IAU_I1_5"].value.BOOL));
    if(signal.contains("JB_IAU_I2_0")) ui->JB_IAU_I2_0->setText(QString::number(signal["JB_IAU_I2_0"].value.BOOL));
    if(signal.contains("JB_IAU_I2_1")) ui->JB_IAU_I2_1->setText(QString::number(signal["JB_IAU_I2_1"].value.BOOL));
    if(signal.contains("JB_IAU_I2_2")) ui->JB_IAU_I2_2->setText(QString::number(signal["JB_IAU_I2_2"].value.BOOL));
    if(signal.contains("JB_IAU_I2_3")) ui->JB_IAU_I2_3->setText(QString::number(signal["JB_IAU_I2_3"].value.BOOL));
    if(signal.contains("JB_IAU_I2_4")) ui->JB_IAU_I2_4->setText(QString::number(signal["JB_IAU_I2_4"].value.BOOL));


    //if(signal.contains("Detector1")) ui->lineEdit_Detector1->setText(QString::number(signal["Detector1"].value.DOUBLE));
    //if(signal.contains("Detector2")) ui->lineEdit_Detector2->setText(QString::number(signal["Detector2"].value.DOUBLE));
    //if(signal.contains("Detector3")) ui->lineEdit_Detector3->setText(QString::number(signal["Detector3"].value.DOUBLE));
    //if(signal.contains("MK2CPU")) ui->lineEdit_MK2CPU->setText(QString::number(signal["MK2CPU"].value.INT));
    //if(signal.contains("MK5CPU")) ui->lineEdit_MK5CPU->setText(signal["MK5CPU"].value.BOOL?"TREU":"FALSE");
//    if(signal.contains("CentreBox_U01")) ui->lineEdit_CentreBoxVal1->setText(QString::number(signal["CentreBox_U01"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U02")) ui->lineEdit_CentreBoxVal2->setText(QString::number(signal["CentreBox_U02"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U03")) ui->lineEdit_CentreBoxVal3->setText(QString::number(signal["CentreBox_U03"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U04")) ui->lineEdit_CentreBoxVal4->setText(QString::number(signal["CentreBox_U04"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U05")) ui->lineEdit_CentreBoxVal5->setText(QString::number(signal["CentreBox_U05"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U06")) ui->lineEdit_CentreBoxVal6->setText(QString::number(signal["CentreBox_U06"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U07")) ui->lineEdit_CentreBoxVal7->setText(QString::number(signal["CentreBox_U07"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U08")) ui->lineEdit_CentreBoxVal8->setText(QString::number(signal["CentreBox_U08"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U09")) ui->lineEdit_CentreBoxVal9->setText(QString::number(signal["CentreBox_U09"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_U10")) ui->lineEdit_CentreBoxVal10->setText(QString::number(signal["CentreBox_U10"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_I01")) ui->lineEdit_CentreBoxVal11->setText(QString::number(signal["CentreBox_I01"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_I02")) ui->lineEdit_CentreBoxVal12->setText(QString::number(signal["CentreBox_I02"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_I03")) ui->lineEdit_CentreBoxVal13->setText(QString::number(signal["CentreBox_I03"].value.DOUBLE/10,'f',2));

//    if(signal.contains("MechCtrolBox_U01")) ui->lineEdit_MechCtrolBoxVal1->setText(QString::number(signal["MechCtrolBox_U01"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U02")) ui->lineEdit_MechCtrolBoxVal2->setText(QString::number(signal["MechCtrolBox_U02"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U03")) ui->lineEdit_MechCtrolBoxVal3->setText(QString::number(signal["MechCtrolBox_U03"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U04")) ui->lineEdit_MechCtrolBoxVal4->setText(QString::number(signal["MechCtrolBox_U04"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U05")) ui->lineEdit_MechCtrolBoxVal5->setText(QString::number(signal["MechCtrolBox_U05"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U06")) ui->lineEdit_MechCtrolBoxVal6->setText(QString::number(signal["MechCtrolBox_U06"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U07")) ui->lineEdit_MechCtrolBoxVal7->setText(QString::number(signal["MechCtrolBox_U07"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U08")) ui->lineEdit_MechCtrolBoxVal8->setText(QString::number(signal["MechCtrolBox_U08"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U09")) ui->lineEdit_MechCtrolBoxVal9->setText(QString::number(signal["MechCtrolBox_U09"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U10")) ui->lineEdit_MechCtrolBoxVal10->setText(QString::number(signal["MechCtrolBox_U10"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U11")) ui->lineEdit_MechCtrolBoxVal11->setText(QString::number(signal["MechCtrolBox_U11"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U12")) ui->lineEdit_MechCtrolBoxVal12->setText(QString::number(signal["MechCtrolBox_U12"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U13")) ui->lineEdit_MechCtrolBoxVal13->setText(QString::number(signal["MechCtrolBox_U13"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U14")) ui->lineEdit_MechCtrolBoxVal14->setText(QString::number(signal["MechCtrolBox_U14"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U15")) ui->lineEdit_MechCtrolBoxVal15->setText(QString::number(signal["MechCtrolBox_U15"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U16")) ui->lineEdit_MechCtrolBoxVal16->setText(QString::number(signal["MechCtrolBox_U16"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U17")) ui->lineEdit_MechCtrolBoxVal17->setText(QString::number(signal["MechCtrolBox_U17"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U18")) ui->lineEdit_MechCtrolBoxVal18->setText(QString::number(signal["MechCtrolBox_U18"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U19")) ui->lineEdit_MechCtrolBoxVal19->setText(QString::number(signal["MechCtrolBox_U19"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U20")) ui->lineEdit_MechCtrolBoxVal20->setText(QString::number(signal["MechCtrolBox_U20"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U21")) ui->lineEdit_MechCtrolBoxVal21->setText(QString::number(signal["MechCtrolBox_U21"].value.DOUBLE/10,'f',1));
//    if(signal.contains("MechCtrolBox_U22")) ui->lineEdit_MechCtrolBoxVal22->setText(QString::number(signal["MechCtrolBox_U22"].value.DOUBLE/10,'f',1));

//    if(signal.contains("BackPump_U01")) ui->lineEdit_BackPumpVal1->setText(QString::number(signal["BackPump_U01"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U02")) ui->lineEdit_BackPumpVal2->setText(QString::number(signal["BackPump_U02"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U03")) ui->lineEdit_BackPumpVal3->setText(QString::number(signal["BackPump_U03"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U04")) ui->lineEdit_BackPumpVal4->setText(QString::number(signal["BackPump_U04"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U05")) ui->lineEdit_BackPumpVal5->setText(QString::number(signal["BackPump_U05"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U06")) ui->lineEdit_BackPumpVal6->setText(QString::number(signal["BackPump_U06"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U07")) ui->lineEdit_BackPumpVal7->setText(QString::number(signal["BackPump_U07"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U08")) ui->lineEdit_BackPumpVal8->setText(QString::number(signal["BackPump_U08"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U09")) ui->lineEdit_BackPumpVal9->setText(QString::number(signal["BackPump_U09"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U10")) ui->lineEdit_BackPumpVal10->setText(QString::number(signal["BackPump_U10"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U11")) ui->lineEdit_BackPumpVal11->setText(QString::number(signal["BackPump_U11"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U12")) ui->lineEdit_BackPumpVal12->setText(QString::number(signal["BackPump_U12"].value.DOUBLE/10,'f',1));
//    if(signal.contains("BackPump_U13")) ui->lineEdit_BackPumpVal13->setText(QString::number(signal["BackPump_U13"].value.DOUBLE/10,'f',1));

//    if(signal.contains("ImprovePump_U01")) ui->lineEdit_ImprovePumpVal1->setText(QString::number(signal["ImprovePump_U01"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U02")) ui->lineEdit_ImprovePumpVal2->setText(QString::number(signal["ImprovePump_U02"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U03")) ui->lineEdit_ImprovePumpVal3->setText(QString::number(signal["ImprovePump_U03"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U04")) ui->lineEdit_ImprovePumpVal4->setText(QString::number(signal["ImprovePump_U04"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U05")) ui->lineEdit_ImprovePumpVal5->setText(QString::number(signal["ImprovePump_U05"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U06")) ui->lineEdit_ImprovePumpVal6->setText(QString::number(signal["ImprovePump_U06"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U07")) ui->lineEdit_ImprovePumpVal7->setText(QString::number(signal["ImprovePump_U07"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U08")) ui->lineEdit_ImprovePumpVal8->setText(QString::number(signal["ImprovePump_U08"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U09")) ui->lineEdit_ImprovePumpVal9->setText(QString::number(signal["ImprovePump_U09"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U10")) ui->lineEdit_ImprovePumpVal10->setText(QString::number(signal["ImprovePump_U10"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U11")) ui->lineEdit_ImprovePumpVal11->setText(QString::number(signal["ImprovePump_U11"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U12")) ui->lineEdit_ImprovePumpVal12->setText(QString::number(signal["ImprovePump_U12"].value.DOUBLE/10,'f',1));
//    if(signal.contains("ImprovePump_U13")) ui->lineEdit_ImprovePumpVal13->setText(QString::number(signal["ImprovePump_U13"].value.DOUBLE/10,'f',1));

//    if(signal.contains("CentreBox_PARA1")) ui->lineEdit_CentreBox_PLC1->setText(QString::number(signal["CentreBox_PARA1"].value.BOOL));
//    if(signal.contains("CentreBox_PARA2")) ui->lineEdit_CentreBox_PLC2->setText(QString::number(signal["CentreBox_PARA2"].value.BOOL));
//    if(signal.contains("CentreBox_PARA3")) ui->lineEdit_CentreBox_PLC3->setText(QString::number(signal["CentreBox_PARA3"].value.BOOL));
//    if(signal.contains("CentreBox_PARA4")) ui->lineEdit_CentreBox_PLC4->setText(QString::number(signal["CentreBox_PARA4"].value.BOOL));
//    if(signal.contains("CentreBox_PARA5")) ui->lineEdit_CentreBox_PLC5->setText(QString::number(signal["CentreBox_PARA5"].value.BOOL));
//    if(signal.contains("CentreBox_PARA6")) ui->lineEdit_CentreBox_PLC6->setText(QString::number(signal["CentreBox_PARA6"].value.BOOL));
//    if(signal.contains("CentreBox_PARA7")) ui->lineEdit_CentreBox_PLC7->setText(QString::number(signal["CentreBox_PARA7"].value.BOOL));
//    if(signal.contains("CentreBox_PARA8")) ui->lineEdit_CentreBox_PLC8->setText(QString::number(signal["CentreBox_PARA8"].value.BOOL));
//    if(signal.contains("CentreBox_PARA9")) ui->lineEdit_CentreBox_PLC9->setText(QString::number(signal["CentreBox_PARA9"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_PARA10")) ui->lineEdit_CentreBox_PLC10->setText(QString::number(signal["CentreBox_PARA10"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_PARA11")) ui->lineEdit_CentreBox_PLC11->setText(QString::number(signal["CentreBox_PARA11"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_PARA12")) ui->lineEdit_CentreBox_PLC12->setText(QString::number(signal["CentreBox_PARA12"].value.DOUBLE/10,'f',2));
//    if(signal.contains("CentreBox_PARA13")) ui->lineEdit_CentreBox_PLC13->setText(QString::number(signal["CentreBox_PARA13"].value.DOUBLE/10,'f',2));

//    if(signal.contains("MechCtrolBox_PARA1")) ui->lineEdit_MechCtrolBox_PLC2_1->setText(QString::number(signal["MechCtrolBox_PARA1"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA2")) ui->lineEdit_MechCtrolBox_PLC2_2->setText(QString::number(signal["MechCtrolBox_PARA2"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA3")) ui->lineEdit_MechCtrolBox_PLC2_3->setText(QString::number(signal["MechCtrolBox_PARA3"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA4")) ui->lineEdit_MechCtrolBox_PLC2_4->setText(QString::number(signal["MechCtrolBox_PARA4"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA5")) ui->lineEdit_MechCtrolBox_PLC2_5->setText(QString::number(signal["MechCtrolBox_PARA5"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA6")) ui->lineEdit_MechCtrolBox_PLC2_6->setText(QString::number(signal["MechCtrolBox_PARA6"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA7")) ui->lineEdit_MechCtrolBox_PLC2_7->setText(QString::number(signal["MechCtrolBox_PARA7"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA8")) ui->lineEdit_MechCtrolBox_PLC2_8->setText(QString::number(signal["MechCtrolBox_PARA8"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA9")) ui->lineEdit_MechCtrolBox_PLC2_9->setText(QString::number(signal["MechCtrolBox_PARA9"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA10")) ui->lineEdit_MechCtrolBox_PLC2_10->setText(QString::number(signal["MechCtrolBox_PARA10"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA11")) ui->lineEdit_MechCtrolBox_PLC2_11->setText(QString::number(signal["MechCtrolBox_PARA11"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA12")) ui->lineEdit_MechCtrolBox_PLC2_12->setText(QString::number(signal["MechCtrolBox_PARA12"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA13")) ui->lineEdit_MechCtrolBox_PLC2_13->setText(QString::number(signal["MechCtrolBox_PARA13"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA14")) ui->lineEdit_MechCtrolBox_PLC2_14->setText(QString::number(signal["MechCtrolBox_PARA14"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA15")) ui->lineEdit_MechCtrolBox_PLC2_15->setText(QString::number(signal["MechCtrolBox_PARA15"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA16")) ui->lineEdit_MechCtrolBox_PLC2_16->setText(QString::number(signal["MechCtrolBox_PARA16"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA17")) ui->lineEdit_MechCtrolBox_PLC2_17->setText(QString::number(signal["MechCtrolBox_PARA17"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA18")) ui->lineEdit_MechCtrolBox_PLC2_18->setText(QString::number(signal["MechCtrolBox_PARA18"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA19")) ui->lineEdit_MechCtrolBox_PLC2_19->setText(QString::number(signal["MechCtrolBox_PARA19"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA20")) ui->lineEdit_MechCtrolBox_PLC2_20->setText(QString::number(signal["MechCtrolBox_PARA20"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA21")) ui->lineEdit_MechCtrolBox_PLC2_21->setText(QString::number(signal["MechCtrolBox_PARA21"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA22")) ui->lineEdit_MechCtrolBox_PLC2_22->setText(QString::number(signal["MechCtrolBox_PARA22"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA23")) ui->lineEdit_MechCtrolBox_PLC2_23->setText(QString::number(signal["MechCtrolBox_PARA23"].value.BOOL));
//    if(signal.contains("MechCtrolBox_PARA24")) ui->lineEdit_MechCtrolBox_PLC2_24->setText(QString::number(signal["MechCtrolBox_PARA24"].value.DOUBLE,'f',1));//系统油压传感器信号
//    if(signal.contains("MechCtrolBox_PARA25")) ui->lineEdit_MechCtrolBox_PLC2_25->setText(QString::number(signal["MechCtrolBox_PARA25"].value.DOUBLE,'f',1));//A口油压传感器信号
//    if(signal.contains("MechCtrolBox_PARA26")) ui->lineEdit_MechCtrolBox_PLC2_26->setText(QString::number(signal["MechCtrolBox_PARA26"].value.DOUBLE,'f',1));//B口油压传感器信号
//    if(signal.contains("MechCtrolBox_PARA27")) ui->lineEdit_MechCtrolBox_PLC2_27->setText(QString::number(signal["MechCtrolBox_PARA27"].value.DOUBLE,'f',1));//静压腔油压传感器信号
//    if(signal.contains("MechCtrolBox_PARA28")) ui->lineEdit_MechCtrolBox_PLC2_28->setText(QString::number(signal["MechCtrolBox_PARA28"].value.DOUBLE,'f',1));//主油箱液位传感器信号
//    if(signal.contains("MechCtrolBox_PARA29")) ui->lineEdit_MechCtrolBox_PLC2_29->setText(QString::number(signal["MechCtrolBox_PARA29"].value.DOUBLE/10,'f',1));//比例阀阀芯位移信号
//    if(signal.contains("MechCtrolBox_PARA30")) ui->lineEdit_MechCtrolBox_PLC2_30->setText(QString::number(signal["MechCtrolBox_PARA30"].value.DOUBLE,'f',1));//系统油温信号
//    if(signal.contains("MechCtrolBox_PARA31")) ui->lineEdit_MechCtrolBox_PLC2_31->setText(QString::number(signal["MechCtrolBox_PARA31"].value.DOUBLE/10,'f',1));//初始螺距指示 mA
//    if(signal.contains("MechCtrolBox_PARA32")) ui->lineEdit_MechCtrolBox_PLC2_32->setText(QString::number(signal["MechCtrolBox_PARA32"].value.BOOL));//备用泵运行

//    if(signal.contains("BackPump_PARA1")) ui->lineEdit_BackPump_Para1->setText(QString::number(signal["BackPump_PARA1"].value.BOOL));
//    if(signal.contains("BackPump_PARA2")) ui->lineEdit_BackPump_Para2->setText(QString::number(signal["BackPump_PARA2"].value.BOOL));
//    if(signal.contains("BackPump_PARA3")) ui->lineEdit_BackPump_Para3->setText(QString::number(signal["BackPump_PARA3"].value.DOUBLE,'f',1));
//    if(signal.contains("BackPump_PARA4")) ui->lineEdit_BackPump_Para4->setText(QString::number(signal["BackPump_PARA4"].value.BOOL));
//    if(signal.contains("BackPump_PARA5")) ui->lineEdit_BackPump_Para5->setText(QString::number(signal["BackPump_PARA5"].value.BOOL));
//    if(signal.contains("BackPump_PARA6")) ui->lineEdit_BackPump_Para6->setText(QString::number(signal["BackPump_PARA6"].value.BOOL));

//    if(signal.contains("ImprovePump_PARA1")) ui->lineEdit_ImprovePump_Para1->setText(QString::number(signal["ImprovePump_PARA1"].value.BOOL));
//    if(signal.contains("ImprovePump_PARA2")) ui->lineEdit_ImprovePump_Para2->setText(QString::number(signal["ImprovePump_PARA2"].value.BOOL));
//    if(signal.contains("ImprovePump_PARA3")) ui->lineEdit_ImprovePump_Para3->setText(QString::number(signal["ImprovePump_PARA3"].value.DOUBLE,'f',1));
//    if(signal.contains("ImprovePump_PARA4")) ui->lineEdit_ImprovePump_Para4->setText(QString::number(signal["ImprovePump_PARA4"].value.BOOL));
//    if(signal.contains("ImprovePump_PARA5")) ui->lineEdit_ImprovePump_Para5->setText(QString::number(signal["ImprovePump_PARA5"].value.BOOL));
//    if(signal.contains("ImprovePump_PARA6")) ui->lineEdit_ImprovePump_Para6->setText(QString::number(signal["ImprovePump_PARA6"].value.BOOL));

//    if(signal.contains("Hydro_PARA1")) ui->lineEdit_Hydro_Para1->setText(QString::number(signal["Hydro_PARA1"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA2")) ui->lineEdit_Hydro_Para2->setText(QString::number(signal["Hydro_PARA2"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA3")) ui->lineEdit_Hydro_Para3->setText(QString::number(signal["Hydro_PARA3"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA4")) ui->lineEdit_Hydro_Para4->setText(QString::number(signal["Hydro_PARA4"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA5")) ui->lineEdit_Hydro_Para5->setText(QString::number(signal["Hydro_PARA5"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA6")) ui->lineEdit_Hydro_Para6->setText(QString::number(signal["Hydro_PARA6"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA7")) ui->lineEdit_Hydro_Para7->setText(QString::number(signal["Hydro_PARA7"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA8")) ui->lineEdit_Hydro_Para8->setText(QString::number(signal["Hydro_PARA8"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA9")) ui->lineEdit_Hydro_Para9->setText(QString::number(signal["Hydro_PARA9"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA10")) ui->lineEdit_Hydro_Para10->setText(QString::number(signal["Hydro_PARA10"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA11")) ui->lineEdit_Hydro_Para11->setText(QString::number(signal["Hydro_PARA11"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA12")) ui->lineEdit_Hydro_Para12->setText(QString::number(signal["Hydro_PARA12"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA13")) ui->lineEdit_Hydro_Para13->setText(QString::number(signal["Hydro_PARA13"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA14")) ui->lineEdit_Hydro_Para14->setText(QString::number(signal["Hydro_PARA14"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA15")) ui->lineEdit_Hydro_Para15->setText(QString::number(signal["Hydro_PARA15"].value.DOUBLE,'f',2));
//    if(signal.contains("Hydro_PARA16")) ui->lineEdit_Hydro_Para16->setText(QString::number(signal["Hydro_PARA16"].value.DOUBLE,'f',2));

    //qDebug()<<"void FormRealTimeData::UpDate(QVector<DataBase::Signal> signal) 待完善";

//lu 在线/离线信息显示
//    if(NetSt[0]<50) ui->label_StCentreBox->setText("中心控制箱在线诊断模块(在线)");
//    else ui->label_StCentreBox->setText("中心控制箱在线诊断模块(离线)");

//    if(NetSt[1]<50) ui->label_StMechBox->setText("机旁控制箱在线诊断模块(在线)");
//    else ui->label_StMechBox->setText("机旁控制箱在线诊断模块(离线)");

//    if(NetSt[2]<50) ui->label_StBackPump->setText("备用泵电机启动箱在线诊断模块(在线)");
//    else ui->label_StBackPump->setText("备用泵电机启动箱在线诊断模块(离线)");

//    if(NetSt[2]<50) ui->label_StImprovePump->setText("提升泵电机启动箱在线诊断模块(在线)");
//    else ui->label_StImprovePump->setText("提升泵电机启动箱在线诊断模块(离线)");

//    if(NetSt[3]<50)
//    {
//        ui->label_StCentreBoxPLC->setText("中心控制箱PLC(在线)");
//        ui->label_StMechBoxPLC->setText("机旁控制箱PLC(在线)");
//        ui->label_StBackPumpPLC->setText("备用泵电机启动箱电机检测输出信号(在线)");
//        ui->label_StImprovePumpPLC->setText("提升泵电机启动箱电机检测输出信号(在线)");
//        ui->label_StHydro->setText("液压系统输出信号(在线)");
//    }
//    else
//    {
//        ui->label_StCentreBoxPLC->setText("中心控制箱PLC(离线)");
//        ui->label_StMechBoxPLC->setText("机旁控制箱PLC(离线)");
//        ui->label_StImprovePumpPLC->setText("备用泵电机启动箱电机检测输出信号(离线)");
//        ui->label_StImprovePumpPLC->setText("提升泵电机启动箱电机检测输出信号(离线)");
//        ui->label_StHydro->setText("液压系统输出信号(离线)");
//    }

}

void FormRealTimeData::on_Btn_RealTimeDataPreviousPage_clicked()
{//实时数据显示上一页
    if(ui->stackedWidgetRealTimeData->currentIndex()==0){
        return;
    }
    else{
        ui->stackedWidgetRealTimeData->setCurrentIndex(ui->stackedWidgetRealTimeData->currentIndex()-1);
        ui->label_RealTimeDataCurrentPageNum->setText(QString::number(ui->stackedWidgetRealTimeData->currentIndex()+1));
    }
}

void FormRealTimeData::on_Btn_RealTimeDataNextPage_clicked()
{//实时数据显示下一页
    if(ui->stackedWidgetRealTimeData->currentIndex()==(ui->stackedWidgetRealTimeData->count()-1)){
        return;
    }
    else{
        ui->stackedWidgetRealTimeData->setCurrentIndex(ui->stackedWidgetRealTimeData->currentIndex()+1);
        ui->label_RealTimeDataCurrentPageNum->setText(QString::number(ui->stackedWidgetRealTimeData->currentIndex()+1));
    }
}
