#include "detector1_datatransthread.h"
#include <QDebug>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern RuleVariablePool m_RuleVariablePool;//当前规则库变量池
extern QMutex mutex;
int NetSt[5]={0,0,0,0,0};
Detector1_DataTrans::Detector1_DataTrans(myQSqlDatabase *TMATE_Database,int DetectorID):
    m_Database(TMATE_Database),m_DetectorID(DetectorID)
{
    udpSocket = new QUdpSocket(this);
    if (!udpSocket->bind(QHostAddress("193.40.1.100"), 8000)) {
        QMessageBox::information(nullptr,"Detector:" + QString::number(DetectorID) + " 网络连接错误", "相关功能将受限\n错误信息: UDP Binding Error-"+ udpSocket->errorString());
        qDebug()<<" 网络连接错误 "<<"网络相关功能将受限\n错误信息: UDP Binding Error-"<< udpSocket->errorString();
    }
    connect(udpSocket, &QUdpSocket::readyRead, this, &Detector1_DataTrans::readBuf);

    Socket=new QTcpSocket;
    //SocketWrite=new QTcpSocket;
//    connect(Socket,&QTcpSocket::connected,this,&Detector1_DataTrans::conetOK);
//    connect(Socket,&QTcpSocket::disconnected,this,&Detector1_DataTrans::disconet);
//    connect(Socket,&QTcpSocket::readyRead,this,&Detector1_DataTrans::readBuf);

    //connect(SocketWrite,&QTcpSocket::connected,this,&Detector1_DataTrans::WrconetOK);
    //connect(SocketWrite,&QTcpSocket::disconnected,this,&Detector1_DataTrans::Wrdisconet);

    TimerTcp=new QTimer(this);
    connect(TimerTcp, SIGNAL(timeout()), this, SLOT(timerRun()));
    TimerTcp->start(200);
}

void Detector1_DataTrans::timerRun()//运行主程序
{
    static int ReLinkCnt=0;
    static int WrReLinkCnt=0;
//    NetSt[m_DetectorID-1]++;
//    if(NetSt[m_DetectorID-1]>1000) NetSt[m_DetectorID-1]=10;
//        //断线重连
//        if(!ConnectSt)
//        {
//            ReLinkCnt++;
//            if(ReLinkCnt>50)
//            {
//                ReLinkCnt=0;

//                DataBase::Str_communication communication;
//                communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable(QString("Detector%1").arg(m_DetectorID));
//                conetHost(communication.IP,communication.Port.toInt());
//            }
//        }
//        if((!WrConnectSt)&&(m_DetectorID==1)) //配置模块1的差分通道
//        {
//            WrReLinkCnt++;
//            if(WrReLinkCnt>50)
//            {
//                WrReLinkCnt=0;

//                DataBase::Str_communication communication;
//                communication = m_Database->SelectCommunicationInforFromCommunicationConfigTable(QString("Detector%1").arg(m_DetectorID));
//                conetWrHost(communication.IP,7341);
//            }
//        }

        //产生随机数
        //qsrand(static_cast<unsigned int>(QTime(0, 0, 0).secsTo(QTime::currentTime())));
        //Derect1 = static_cast<double>((qrand() % 100))/(static_cast<double>((qrand() % 50))+50);//产生0-2的随机数

        //加锁实现对m_RuleVariablePool写操作的线程互斥

        //变量控制实现5个写线程和1个诊断线程的顺序执行，即当m_RuleVariablePool.GetCurrentStep()==0时本线程进行写操作，写完之后将Step置1
        if(m_DetectorID==1){//m_RuleVariablePool.GetCurrentStep()==0&&
//            unsigned char FetchBuf[11]={0x53,0x35,0x02,0x02,0x01,0x20,0x03,0x01,0x20,0xFF,0x02};
//            if(ConnectSt) Socket->write((char *)FetchBuf,11);
            if(DetectVIsUpdated)
            {
                m_RuleVariablePool.SetVariableValue("WCC_PLC_HeartBeat",static_cast<int>(DetectVPara[2]));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_HeartBeat",static_cast<int>(DetectVPara[3]));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_HeartBeat",static_cast<int>(DetectVPara[4]));
                m_RuleVariablePool.SetVariableValue("WCC_VFD3_HeartBeat",static_cast<int>(DetectVPara[5]));
                m_RuleVariablePool.SetVariableValue("WCC_IAU_HeartBeat",static_cast<int>(DetectVPara[6]));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_Para_CableLength",static_cast<double>(DetectVPara[8]*0.01+DetectVPara[9]*2.56+DetectVPara[10]*655.36+DetectVPara[11]*167772.16));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_Para_ArrayLength",static_cast<double>(DetectVPara[12]*0.01+DetectVPara[13]*2.56+DetectVPara[14]*655.36+DetectVPara[15]*167772.16));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_Para_ArrayDepth",static_cast<double>(DetectVPara[16]*0.01+DetectVPara[17]*2.56+DetectVPara[18]*655.36+DetectVPara[19]*167772.16));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_Para_SeaDepth",static_cast<double>(DetectVPara[20]*0.01+DetectVPara[21]*2.56+DetectVPara[22]*655.36+DetectVPara[23]*167772.16));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_Para_Tension",static_cast<double>(DetectVPara[24]+DetectVPara[25]*256+DetectVPara[26]*65536+DetectVPara[27]*16777216));

                // 设置 WCC_PLC_Alarm1 到 WCC_PLC_Alarm8
                for (int i = 0; i < 8; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_Alarm" + std::to_string(i + 1));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[28] & (1 << i)));
                }

                // 设置 WCC_PLC_Alarm9 到 WCC_PLC_Alarm12
                for (int i = 0; i < 4; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_Alarm" + std::to_string(i + 9));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[29] & (1 << i)));
                }


                // 继续设置基础信号类型的变量
                m_RuleVariablePool.SetVariableValue("WCC_PLC_WorkMode", static_cast<int>(DetectVPara[30]));

                // 设置序号32.0至32.7的BOOL类型变量
                for (int i = 0; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_I0_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[32] & (1 << i)));
                }

                // 设置序号33.0至33.7的BOOL类型变量
                for (int i = 0; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_I1_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[33] & (1 << i)));
                }

                // 设置序号34.0至34.7的BOOL类型变量
                for (int i = 0; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_I2_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[34] & (1 << i)));
                }

                // 设置序号35.0至35.7的BOOL类型变量
                for (int i = 0; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_I80_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[35] & (1 << i)));
                }

                // 设置序号36.0至36.7的BOOL类型变量
                for (int i = 0; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_Q0_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[36] & (1 << i)));
                }

                // 设置序号37.0至37.7的BOOL类型变量
                for (int i = 0; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_Q1_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[37] & (1 << i)));
                }

                // 设置序号38.4至38.7的BOOL类型变量
                for (int i = 4; i <= 7; ++i) {
                    QString varName = QString::fromStdString("WCC_PLC_Q64_" + std::to_string(i));
                    m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[38] & (1 << i)));
                }

                // 设置DOUBLE类型的变量
                m_RuleVariablePool.SetVariableValue("WCC_PLC_QW112", static_cast<double>((DetectVPara[40]+DetectVPara[41]*256) /1600.0));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_QW114", static_cast<double>((DetectVPara[42]+DetectVPara[43]*256)/1600.0));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_QW48", static_cast<double>((DetectVPara[44]+DetectVPara[45]*256) /1600.0));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_IW96", static_cast<double>((DetectVPara[46]+DetectVPara[47]*256)/1614.0));

                // 设置INT类型的变量
                int16_t wcc_plc_cnt0 = static_cast<int16_t>((static_cast<uint16_t>(DetectVPara[49]) << 8)|static_cast<uint16_t>(DetectVPara[48]));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_CNT0", wcc_plc_cnt0);

                int16_t wcc_plc_cnt1 = static_cast<int16_t>((static_cast<uint16_t>(DetectVPara[51]) << 8)|static_cast<uint16_t>(DetectVPara[50]));
                m_RuleVariablePool.SetVariableValue("WCC_PLC_CNT1", wcc_plc_cnt1);

                // 设置其他DOUBLE类型变量
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_AI1", static_cast<double>((DetectVPara[52]+DetectVPara[53]*256) * 0.001));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_AI1", static_cast<double>((DetectVPara[54]+DetectVPara[55]*256) * 0.001));
                m_RuleVariablePool.SetVariableValue("WCC_VFD3_AI2", static_cast<double>((DetectVPara[56]+DetectVPara[57]*256) * 0.02));

                //qDebug()<<"VFD1 58:" +QString::number(DetectVPara[58],16) +"  59:"+ QString::number(DetectVPara[59],16);
                // 设置序号58.0至58.7的BOOL类型变量
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DI1",static_cast<bool>(DetectVPara[58] & (1 << 1)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DI2",static_cast<bool>(DetectVPara[58] & (1 << 2)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DI4",static_cast<bool>(DetectVPara[58] & (1 << 3)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DI6",static_cast<bool>(DetectVPara[58] & (1 << 4)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DO1",static_cast<bool>(DetectVPara[58] & (1 << 5)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DO2",static_cast<bool>(DetectVPara[58] & (1 << 6)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD1_DO3",static_cast<bool>(DetectVPara[58] & (1 << 7)));

                // 设置序号59.0至59.7的BOOL类型变量
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DI1",static_cast<bool>(DetectVPara[59] & (1 << 1)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DI2",static_cast<bool>(DetectVPara[59] & (1 << 2)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DI4",static_cast<bool>(DetectVPara[59] & (1 << 3)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DI6",static_cast<bool>(DetectVPara[59] & (1 << 4)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DO1",static_cast<bool>(DetectVPara[59] & (1 << 5)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DO2",static_cast<bool>(DetectVPara[59] & (1 << 6)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD2_DO3",static_cast<bool>(DetectVPara[59] & (1 << 7)));

                // 设置序号60.0至60.3的BOOL类型变量
                m_RuleVariablePool.SetVariableValue("WCC_VFD3_DI1",static_cast<bool>(DetectVPara[60] & (1 << 1)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD3_DI2",static_cast<bool>(DetectVPara[60] & (1 << 2)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD3_DI5",static_cast<bool>(DetectVPara[60] & (1 << 3)));
                m_RuleVariablePool.SetVariableValue("WCC_VFD3_DO5",static_cast<bool>(DetectVPara[60] & (1 << 4)));

                // 设置JB_IAU相关的DOUBLE和INT类型变量
                m_RuleVariablePool.SetVariableValue("JB_IAU_IW64", static_cast<double>((DetectVPara[62]+DetectVPara[63]*256)*20.0/27648.0));

                int32_t jb_iau_iw1000 = static_cast<int32_t>(
                    (static_cast<uint32_t>(DetectVPara[67]) << 24) |
                    (static_cast<uint32_t>(DetectVPara[66]) << 16) |
                    (static_cast<uint32_t>(DetectVPara[65]) << 8)  |
                     static_cast<uint32_t>(DetectVPara[64]));
                m_RuleVariablePool.SetVariableValue("JB_IAU_IW1000", jb_iau_iw1000/4/(-1024));

                int32_t jb_iau_iw1004 = static_cast<int32_t>(
                    (static_cast<uint32_t>(DetectVPara[71]) << 24) |
                    (static_cast<uint32_t>(DetectVPara[70]) << 16) |
                    (static_cast<uint32_t>(DetectVPara[69]) << 8)  |
                     static_cast<uint32_t>(DetectVPara[68]));
                m_RuleVariablePool.SetVariableValue("JB_IAU_IW1004",jb_iau_iw1004);

                int32_t jb_iau_iw1008 = static_cast<int32_t>(
                    (static_cast<uint32_t>(DetectVPara[75]) << 24) |
                    (static_cast<uint32_t>(DetectVPara[74]) << 16) |
                    (static_cast<uint32_t>(DetectVPara[73]) << 8)  |
                     static_cast<uint32_t>(DetectVPara[72]));
                m_RuleVariablePool.SetVariableValue("JB_IAU_IW1008",jb_iau_iw1008);

                // 设置JB_IAU相关的BOOL类型变量
                for (int byteNum = 76; byteNum <= 78; ++byteNum) {
                    for (int bitPos = 0; bitPos <= 7; ++bitPos) {
                        QString varName = QString::fromStdString("JB_IAU_I" + std::to_string(byteNum - 76) + "_" + std::to_string(bitPos));
                        m_RuleVariablePool.SetVariableValue(varName, static_cast<bool>(DetectVPara[byteNum] & (1 << bitPos)));
                    }
                }

                // 请根据实际情况调整变量名和数组索引

                //qDebug()<< DetectVPara[6];
                DetectVIsUpdated = false;
            }
//            if(DetectVIsUpdated)
//            {
//                //待修改
//                m_RuleVariablePool.SetVariableValue("CentreBox_U01",static_cast<double>(DetectVPara[12]/100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U02",static_cast<double>(DetectVPara[13]/100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U03",static_cast<double>(DetectVPara[14]/100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U04",static_cast<double>(DetectVPara[15]/100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U05",static_cast<double>(DetectVPara[3]/100.0));//改成~3
//                //U06是差分信号，对应通道8和通道9，读取通道8和通道9的数值，如果通道8有数值则为正数，如果通道9有数值则为负数
//                m_RuleVariablePool.SetVariableValue("CentreBox_U06",static_cast<double>(DetectVPara[8]>DetectVPara[9]?DetectVPara[8]/100.0:DetectVPara[9]/-100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U07",static_cast<double>(DetectVPara[6]>DetectVPara[7]?DetectVPara[6]/100.0:DetectVPara[7]/-100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U08",static_cast<double>(DetectVPara[4]>DetectVPara[5]?DetectVPara[4]/100.0:DetectVPara[5]/-100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U09",static_cast<double>(DetectVPara[10]/100.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_U10",static_cast<double>(DetectVPara[3]/100.0));
//                Data_DR.CentreBox_U01=static_cast<double>(DetectVPara[12]/100.0);
//                Data_DR.CentreBox_U02=static_cast<double>(DetectVPara[13]/100.0);
//                Data_DR.CentreBox_U03=static_cast<double>(DetectVPara[14]/100.0);
//                Data_DR.CentreBox_U04=static_cast<double>(DetectVPara[15]/100.0);
//                Data_DR.CentreBox_U05=static_cast<double>(DetectVPara[3]/100.0);
//                Data_DR.CentreBox_U06=static_cast<double>(DetectVPara[8]>DetectVPara[9]?DetectVPara[8]/100.0:DetectVPara[9]/-100.0);
//                Data_DR.CentreBox_U07=static_cast<double>(DetectVPara[6]>DetectVPara[7]?DetectVPara[6]/100.0:DetectVPara[7]/-100.0);
//                Data_DR.CentreBox_U08=static_cast<double>(DetectVPara[4]>DetectVPara[5]?DetectVPara[4]/100.0:DetectVPara[5]/-100.0);
//                Data_DR.CentreBox_U09=static_cast<double>(DetectVPara[10]/100.0);
//                Data_DR.CentreBox_U10=static_cast<double>(DetectVPara[3]/100.0);
//                DetectVIsUpdated=false;
//            }
//            if(DetectIIsUpdated)
//            {
//                m_RuleVariablePool.SetVariableValue("CentreBox_I01",static_cast<double>(DetectIPara[1]/10.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_I02",static_cast<double>(DetectIPara[0]/10.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_I03",static_cast<double>(DetectIPara[2]/10.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_I04",static_cast<double>(DetectIPara[3]/10.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_I05",static_cast<double>(DetectIPara[4]/10.0));
//                m_RuleVariablePool.SetVariableValue("CentreBox_I06",static_cast<double>(DetectIPara[5]/10.0));
//                Data_DR.CentreBox_I01=static_cast<double>(DetectIPara[1]/10.0);
//                Data_DR.CentreBox_I02=static_cast<double>(DetectIPara[0]/10.0);
//                Data_DR.CentreBox_I03=static_cast<double>(DetectIPara[2]/10.0);
//                DetectIIsUpdated=false;
//            }
            //m_RuleVariablePool.SetCurrentStep(1);
            //qDebug()<<"SetCurrentStep(1)";
        }

//        if(m_DetectorID==2){//m_RuleVariablePool.GetCurrentStep()==1&&
//            unsigned char FetchBuf[11]={0x53,0x35,0x02,0x02,0x01,0x20,0x03,0x01,0x20,0xFF,0x02};
//            if(ConnectSt) Socket->write((char *)FetchBuf,11);
//            if(DetectVIsUpdated)
//            {
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U01",static_cast<double>(DetectVPara[12]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U02",static_cast<double>(DetectVPara[13]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U03",static_cast<double>(DetectVPara[14]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U04",static_cast<double>(DetectVPara[15]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U05",static_cast<double>(DetectVPara[11]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U06",static_cast<double>(DetectVPara[10]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U07",static_cast<double>(DetectVPara[9]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U08",static_cast<double>(DetectVPara[8]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U09",static_cast<double>(DetectVPara[7]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U10",static_cast<double>(DetectVPara[6]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U11",static_cast<double>(DetectVPara[5]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U12",static_cast<double>(DetectVPara[4]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U13",static_cast<double>(DetectVPara[3]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U14",static_cast<double>(DetectVPara[2]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U15",static_cast<double>(DetectVPara[1]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U16",static_cast<double>(DetectVPara[0]/100.0));

//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U17",static_cast<double>(DetectV2Para[12]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U18",static_cast<double>(DetectV2Para[13]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U19",static_cast<double>(DetectV2Para[14]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U20",static_cast<double>(DetectV2Para[15]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U21",static_cast<double>(DetectV2Para[11]/100.0));
//                m_RuleVariablePool.SetVariableValue("MechCtrolBox_U22",static_cast<double>(DetectV2Para[10]/100.0));

//                Data_DR.MechCtrolBox_U01=static_cast<double>(DetectVPara[12]/100.0);
//                Data_DR.MechCtrolBox_U02=static_cast<double>(DetectVPara[13]/100.0);
//                Data_DR.MechCtrolBox_U03=static_cast<double>(DetectVPara[14]/100.0);
//                Data_DR.MechCtrolBox_U04=static_cast<double>(DetectVPara[15]/100.0);
//                Data_DR.MechCtrolBox_U05=static_cast<double>(DetectVPara[11]/100.0);
//                Data_DR.MechCtrolBox_U06=static_cast<double>(DetectVPara[10]/100.0);
//                Data_DR.MechCtrolBox_U07=static_cast<double>(DetectVPara[9]/100.0);
//                Data_DR.MechCtrolBox_U08=static_cast<double>(DetectVPara[8]/100.0);
//                Data_DR.MechCtrolBox_U09=static_cast<double>(DetectVPara[7]/100.0);
//                Data_DR.MechCtrolBox_U10=static_cast<double>(DetectVPara[6]/100.0);
//                Data_DR.MechCtrolBox_U11=static_cast<double>(DetectVPara[5]/100.0);
//                Data_DR.MechCtrolBox_U12=static_cast<double>(DetectVPara[4]/100.0);
//                Data_DR.MechCtrolBox_U13=static_cast<double>(DetectVPara[3]/100.0);
//                Data_DR.MechCtrolBox_U14=static_cast<double>(DetectVPara[2]/100.0);
//                Data_DR.MechCtrolBox_U15=static_cast<double>(DetectVPara[1]/100.0);
//                Data_DR.MechCtrolBox_U16=static_cast<double>(DetectVPara[0]/100.0);
//                Data_DR.MechCtrolBox_U17=static_cast<double>(DetectV2Para[12]/100.0);
//                Data_DR.MechCtrolBox_U18=static_cast<double>(DetectV2Para[13]/100.0);
//                Data_DR.MechCtrolBox_U19=static_cast<double>(DetectV2Para[14]/100.0);
//                Data_DR.MechCtrolBox_U20=static_cast<double>(DetectV2Para[15]/100.0);
//                Data_DR.MechCtrolBox_U21=static_cast<double>(DetectV2Para[11]/100.0);
//                Data_DR.MechCtrolBox_U22=static_cast<double>(DetectV2Para[10]/100.0);

//                DetectVIsUpdated=false;
//            }
//            //m_RuleVariablePool.SetCurrentStep(2);
//            //qDebug()<<"SetCurrentStep(2)";
//        }

//        if(m_DetectorID==3){//m_RuleVariablePool.GetCurrentStep()==2&&
//            unsigned char FetchBuf[11]={0x53,0x35,0x02,0x02,0x01,0x20,0x03,0x01,0x20,0xFF,0x02};
//            if(ConnectSt) Socket->write((char *)FetchBuf,11);
//            if(DetectVIsUpdated)
//            {
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U02",static_cast<double>(DetectVPara[15]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U03",static_cast<double>(DetectVPara[2]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U04",static_cast<double>(DetectVPara[14]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U05",static_cast<double>(DetectVPara[11]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U06",static_cast<double>(DetectVPara[10]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U07",static_cast<double>(DetectVPara[9]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U08",static_cast<double>(DetectVPara[8]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U09",static_cast<double>(DetectVPara[7]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U10",static_cast<double>(DetectVPara[6]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U11",static_cast<double>(DetectVPara[5]/100.0));
//                m_RuleVariablePool.SetVariableValue("ImprovePump_U12",static_cast<double>(DetectVPara[4]/100.0));

//                m_RuleVariablePool.SetVariableValue("BackPump_U02",static_cast<double>(DetectV2Para[12]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U03",static_cast<double>(DetectV2Para[3]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U04",static_cast<double>(DetectV2Para[14]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U05",static_cast<double>(DetectV2Para[11]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U06",static_cast<double>(DetectV2Para[10]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U07",static_cast<double>(DetectV2Para[9]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U08",static_cast<double>(DetectV2Para[8]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U09",static_cast<double>(DetectV2Para[7]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U10",static_cast<double>(DetectV2Para[6]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U11",static_cast<double>(DetectV2Para[5]/100.0));
//                m_RuleVariablePool.SetVariableValue("BackPump_U12",static_cast<double>(DetectV2Para[4]/100.0));

//                Data_DR.ImprovePump_U02=static_cast<double>(DetectVPara[15]/100.0);
//                Data_DR.ImprovePump_U03=static_cast<double>(DetectVPara[2]/100.0);
//                Data_DR.ImprovePump_U04=static_cast<double>(DetectVPara[14]/100.0);
//                Data_DR.ImprovePump_U05=static_cast<double>(DetectVPara[11]/100.0);
//                Data_DR.ImprovePump_U06=static_cast<double>(DetectVPara[10]/100.0);
//                Data_DR.ImprovePump_U07=static_cast<double>(DetectVPara[9]/100.0);
//                Data_DR.ImprovePump_U08=static_cast<double>(DetectVPara[8]/100.0);
//                Data_DR.ImprovePump_U09=static_cast<double>(DetectVPara[7]/100.0);
//                Data_DR.ImprovePump_U10=static_cast<double>(DetectVPara[6]/100.0);
//                Data_DR.ImprovePump_U11=static_cast<double>(DetectVPara[5]/100.0);
//                Data_DR.ImprovePump_U12=static_cast<double>(DetectVPara[4]/100.0);

//                Data_DR.BackPump_U02=static_cast<double>(DetectV2Para[12]/100.0);
//                Data_DR.BackPump_U03=static_cast<double>(DetectV2Para[3]/100.0);
//                Data_DR.BackPump_U04=static_cast<double>(DetectV2Para[14]/100.0);
//                Data_DR.BackPump_U05=static_cast<double>(DetectV2Para[11]/100.0);
//                Data_DR.BackPump_U06=static_cast<double>(DetectV2Para[10]/100.0);
//                Data_DR.BackPump_U07=static_cast<double>(DetectV2Para[9]/100.0);
//                Data_DR.BackPump_U08=static_cast<double>(DetectV2Para[8]/100.0);
//                Data_DR.BackPump_U09=static_cast<double>(DetectV2Para[7]/100.0);
//                Data_DR.BackPump_U10=static_cast<double>(DetectV2Para[6]/100.0);
//                Data_DR.BackPump_U11=static_cast<double>(DetectV2Para[5]/100.0);
//                Data_DR.BackPump_U12=static_cast<double>(DetectV2Para[4]/100.0);

//                DetectVIsUpdated=false;
//            }
//            //m_RuleVariablePool.SetCurrentStep(3);
//            //qDebug()<<"SetCurrentStep(3)";
//        }
}

void Detector1_DataTrans::conetHost(QString hostIP,quint16 port)
{
     Socket->abort();//丢弃数据，退出当前连接，重置Socket
     Socket->connectToHost(hostIP,port); //连接对应IP和端口的服务器
}

void Detector1_DataTrans::conetWrHost(QString hostIP,quint16 port)
{
     //SocketWrite->abort();//丢弃数据，退出当前连接，重置Socket
     //SocketWrite->connectToHost(hostIP,port); //连接对应IP和端口的服务器
}

void Detector1_DataTrans::readBuf()
{
//    QByteArray rdBuf;
//    //qDebug()<<"rev buf";
//    rdBuf = Socket->readAll();
//    ProcessBuf((unsigned char *)rdBuf.data(),rdBuf.size());
//    //emit rdSignal("Rev:"+BufToStr((unsigned char *)rdBuf.data(),rdBuf.size()));
//    //emit cpSignal(rdBuf,Type);

    while (udpSocket->hasPendingDatagrams()) {
            qint64 datagramSize = udpSocket->pendingDatagramSize();
            if (datagramSize > INT_MAX) {
                // 处理错误或者跳过当前数据包
                qDebug() << "Datagram size is too large to handle.";
                return;
            }
            QByteArray datagram;
            datagram.resize(static_cast<int>(datagramSize));
            udpSocket->readDatagram(datagram.data(), datagram.size());
            ProcessBuf(reinterpret_cast<unsigned char*>(datagram.data()), static_cast<int>(datagram.size()));
        }
}

//待修改
void Detector1_DataTrans::ProcessBuf(unsigned char *Buf,int Len)
{
    for(int i=0;i<Len;i++)
     {
         switch(RevLMCFetchLen)
         {
         case 0:
             if(Buf[i]==0x53) RevLMCFetchBuf[RevLMCFetchLen++]=Buf[i]; else RevLMCFetchLen=0;
             break;
         case 1:
             if(Buf[i]==0x50) RevLMCFetchBuf[RevLMCFetchLen++]=Buf[i]; else RevLMCFetchLen=0;
             break;
         default:
             RevLMCFetchBuf[RevLMCFetchLen++]=Buf[i];
             break;
         }
         if(RevLMCFetchLen>(80)) RevLMCFetchLen=0;
         if(RevLMCFetchLen==(80))
         {
             //qDebug()<<" 解析成功";
             NetSt[m_DetectorID-1]=0;
             //lu
             NetSt[1]=0;
             NetSt[2]=0;
             RevLMCFetchLen=0;
                      for(int k=0;k<80;k++) { DetectVPara[k]=(RevLMCFetchBuf[k]);}
                      DetectVIsUpdated=true;           
         }
     }

}

//功能：将QByteArray对象转换成空格隔开的16进制字符串
//实现：通过将QByteArray中的每个字符转换成对应的16进制字符串，再用空格连接。
QString Detector1_DataTrans::BufToStr(unsigned char* buf,int len)
{
    QString Str;
    Str="";
    for (int i=0;i<len;i++)
    {
      Str=Str+" "+QString::number(buf[i],16);
    }
    return Str;
}

void Detector1_DataTrans::conetOK()
{
    //emit conetOkSignal();
    ConnectSt=true;
    qDebug()<<"connect ok";
}

void Detector1_DataTrans::disconet()
{
    //emit disconetSignal();
    ConnectSt=false;
}

void Detector1_DataTrans::WrconetOK()
{
    //emit conetOkSignal();
    WrConnectSt=true;
    qDebug()<<"connect ok";
    if(m_DetectorID==1)//将模块1的通道4 通道5 通道6 通道7 通道8 通道9设置为差分信号
    {
        unsigned char WriteBuf[8]={0x53,0x35,0x81,0x02,0x00,0x38,0xEE,0xFF};
        //if(WrConnectSt) SocketWrite->write((char *)WriteBuf,8);
    }
}

void Detector1_DataTrans::Wrdisconet()
{
    //emit disconetSignal();
    WrConnectSt=false;
}
