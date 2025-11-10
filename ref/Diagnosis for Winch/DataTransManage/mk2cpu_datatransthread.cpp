#include "mk2cpu_datatransthread.h"
#include <QDebug>
#include "WinSock2.h"
#include "WS2tcpip.h"
#include <fcntl.h>
#pragma comment(lib,"ws2_32.lib")

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

extern RuleVariablePool m_RuleVariablePool;
extern QMutex mutex;
extern int NetSt[5];

#define TRAM_STATUS_ADDR "239.0.0.30"
#define TRAM_STATUS_RECV_PORT 9200

int fd=-1;
int UpdIdx=0;
struct ip_mreq mreq;
unsigned char RevUdpPack[200];
float PLCPara[300];
MK2CPU_DataTransThread::MK2CPU_DataTransThread()
{
    //TimerRunner=new QTimer(this);
    //connect(TimerRunner, SIGNAL(timeout()), this, SLOT(timerRun()));
    //TimerRunner->start(20);
}

int StartRevUDP()
{
    struct sockaddr_in addr;
    unsigned long ul=1;
    //int flags;
    int on;
    if ((fd = socket(AF_INET, SOCK_DGRAM, 0)) < 0)  {return -1;}

    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(TRAM_STATUS_RECV_PORT);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0)
    {
        qDebug("RevTimeUDP  Bind FAILED:port=%d\n",TRAM_STATUS_RECV_PORT);
        closesocket(fd);
        fd=-1;
        return -1;
    }

    //flags = fcntl(fd, F_GETFL, 0); //
    //fcntl(fd, F_SETFL, flags | O_NONBLOCK);   //non block
    ioctlsocket(fd, FIONBIO, (unsigned long *)&ul);//xcc modify

    on = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, (char *)&on, sizeof(on)) < 0)
    {
        qDebug("RevTimeUDP  setsockopt1 FAILED\n");
        closesocket(fd);
        fd=-1;
        return -1;
    }

    mreq.imr_multiaddr.s_addr = inet_addr(TRAM_STATUS_ADDR);
    mreq.imr_interface.s_addr = htonl(INADDR_ANY);
    if (setsockopt(fd, IPPROTO_IP, IP_ADD_MEMBERSHIP, (char *)&mreq, sizeof(mreq)) < 0)
    {
        qDebug("RevTimeUDP  Add member FAILED\n");
        closesocket(fd);
        fd=-1;
        return -1;
    }
    qDebug("Add member success");

    return 0;

}
void LoadDataToBase()
{
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA1",static_cast<bool>(PLCPara[PARA101]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA2",static_cast<bool>(PLCPara[PARA102]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA3",static_cast<bool>(PLCPara[PARA103]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA4",static_cast<bool>(PLCPara[PARA104]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA5",static_cast<bool>(PLCPara[PARA105]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA6",static_cast<bool>(PLCPara[PARA106]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA7",static_cast<bool>(PLCPara[PARA107]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA8",static_cast<bool>(PLCPara[PARA108]>0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA9",static_cast<double>(PLCPara[PARA109]*1.0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA10",static_cast<double>(PLCPara[PARA110]*1.0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA11",static_cast<double>(PLCPara[PARA111]*1.0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA12",static_cast<double>(PLCPara[PARA112]*1.0));
    m_RuleVariablePool.SetVariableValue("CentreBox_PARA13",static_cast<double>(PLCPara[PARA113]*1.0));

    Data_DR.CentreBox_PARA1=static_cast<bool>(PLCPara[PARA101]>0);
    Data_DR.CentreBox_PARA2=static_cast<bool>(PLCPara[PARA102]>0);
    Data_DR.CentreBox_PARA3=static_cast<bool>(PLCPara[PARA103]>0);
    Data_DR.CentreBox_PARA4=static_cast<bool>(PLCPara[PARA104]>0);
    Data_DR.CentreBox_PARA5=static_cast<bool>(PLCPara[PARA105]>0);
    Data_DR.CentreBox_PARA6=static_cast<bool>(PLCPara[PARA106]>0);
    Data_DR.CentreBox_PARA7=static_cast<bool>(PLCPara[PARA107]>0);
    Data_DR.CentreBox_PARA8=static_cast<bool>(PLCPara[PARA108]>0);
    Data_DR.CentreBox_PARA9=static_cast<double>(PLCPara[PARA109]*1.0);
    Data_DR.CentreBox_PARA10=static_cast<double>(PLCPara[PARA110]*1.0);
    Data_DR.CentreBox_PARA11=static_cast<double>(PLCPara[PARA111]*1.0);
    Data_DR.CentreBox_PARA12=static_cast<double>(PLCPara[PARA112]*1.0);
    Data_DR.CentreBox_PARA13=static_cast<double>(PLCPara[PARA113]*1.0);


    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA1",static_cast<bool>(PLCPara[PARA120]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA2",static_cast<bool>(PLCPara[PARA121]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA3",static_cast<bool>(PLCPara[PARA122]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA4",static_cast<bool>(PLCPara[PARA123]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA5",static_cast<bool>(PLCPara[PARA124]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA6",static_cast<bool>(PLCPara[PARA125]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA7",static_cast<bool>(PLCPara[PARA126]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA8",static_cast<bool>(PLCPara[PARA127]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA9",static_cast<bool>(PLCPara[PARA128]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA10",static_cast<bool>(PLCPara[PARA129]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA11",static_cast<bool>(PLCPara[PARA130]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA12",static_cast<bool>(PLCPara[PARA131]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA13",static_cast<bool>(PLCPara[PARA132]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA14",static_cast<bool>(PLCPara[PARA133]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA15",static_cast<bool>(PLCPara[PARA134]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA16",static_cast<bool>(PLCPara[PARA135]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA17",static_cast<bool>(PLCPara[PARA136]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA18",static_cast<bool>(PLCPara[PARA137]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA19",static_cast<bool>(PLCPara[PARA138]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA20",static_cast<bool>(PLCPara[PARA139]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA21",static_cast<bool>(PLCPara[PARA140]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA22",static_cast<bool>(PLCPara[PARA141]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA23",static_cast<bool>(PLCPara[PARA142]>0));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA24",static_cast<double>(PLCPara[PARA143]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA25",static_cast<double>(PLCPara[PARA144]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA26",static_cast<double>(PLCPara[PARA145]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA27",static_cast<double>(PLCPara[PARA146]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA28",static_cast<double>(PLCPara[PARA147]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA29",static_cast<double>(PLCPara[PARA148]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA30",static_cast<double>(PLCPara[PARA149]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA31",static_cast<double>(PLCPara[PARA150]));
    m_RuleVariablePool.SetVariableValue("MechCtrolBox_PARA32",static_cast<bool>(PLCPara[PARA151]>0));

    Data_DR.MechCtrolBox_PARA1=static_cast<bool>(PLCPara[PARA120]>0);
    Data_DR.MechCtrolBox_PARA2=static_cast<bool>(PLCPara[PARA121]>0);
    Data_DR.MechCtrolBox_PARA3=static_cast<bool>(PLCPara[PARA122]>0);
    Data_DR.MechCtrolBox_PARA4=static_cast<bool>(PLCPara[PARA123]>0);
    Data_DR.MechCtrolBox_PARA5=static_cast<bool>(PLCPara[PARA124]>0);
    Data_DR.MechCtrolBox_PARA6=static_cast<bool>(PLCPara[PARA125]>0);
    Data_DR.MechCtrolBox_PARA7=static_cast<bool>(PLCPara[PARA126]>0);
    Data_DR.MechCtrolBox_PARA8=static_cast<bool>(PLCPara[PARA127]>0);
    Data_DR.MechCtrolBox_PARA9=static_cast<bool>(PLCPara[PARA128]>0);
    Data_DR.MechCtrolBox_PARA10=static_cast<bool>(PLCPara[PARA129]>0);
    Data_DR.MechCtrolBox_PARA11=static_cast<bool>(PLCPara[PARA130]>0);
    Data_DR.MechCtrolBox_PARA12=static_cast<bool>(PLCPara[PARA131]>0);
    Data_DR.MechCtrolBox_PARA13=static_cast<bool>(PLCPara[PARA132]>0);
    Data_DR.MechCtrolBox_PARA14=static_cast<bool>(PLCPara[PARA133]>0);
    Data_DR.MechCtrolBox_PARA15=static_cast<bool>(PLCPara[PARA134]>0);
    Data_DR.MechCtrolBox_PARA16=static_cast<bool>(PLCPara[PARA135]>0);
    Data_DR.MechCtrolBox_PARA17=static_cast<bool>(PLCPara[PARA136]>0);
    Data_DR.MechCtrolBox_PARA18=static_cast<bool>(PLCPara[PARA137]>0);
    Data_DR.MechCtrolBox_PARA19=static_cast<bool>(PLCPara[PARA138]>0);
    Data_DR.MechCtrolBox_PARA20=static_cast<bool>(PLCPara[PARA139]>0);
    Data_DR.MechCtrolBox_PARA21=static_cast<bool>(PLCPara[PARA140]>0);
    Data_DR.MechCtrolBox_PARA22=static_cast<bool>(PLCPara[PARA141]>0);
    Data_DR.MechCtrolBox_PARA23=static_cast<bool>(PLCPara[PARA142]>0);
    Data_DR.MechCtrolBox_PARA24=static_cast<bool>(PLCPara[PARA143]>0);
    Data_DR.MechCtrolBox_PARA25=static_cast<bool>(PLCPara[PARA144]>0);
    Data_DR.MechCtrolBox_PARA26=static_cast<bool>(PLCPara[PARA145]>0);
    Data_DR.MechCtrolBox_PARA27=static_cast<bool>(PLCPara[PARA146]>0);
    Data_DR.MechCtrolBox_PARA28=static_cast<bool>(PLCPara[PARA147]>0);
    Data_DR.MechCtrolBox_PARA29=static_cast<bool>(PLCPara[PARA148]>0);
    Data_DR.MechCtrolBox_PARA30=static_cast<bool>(PLCPara[PARA149]>0);
    Data_DR.MechCtrolBox_PARA31=static_cast<bool>(PLCPara[PARA150]>0);
    Data_DR.MechCtrolBox_PARA32=static_cast<bool>(PLCPara[PARA151]>0);

    m_RuleVariablePool.SetVariableValue("BackPump_PARA1",static_cast<bool>(PLCPara[PARA160]>0));
    m_RuleVariablePool.SetVariableValue("BackPump_PARA2",static_cast<bool>(PLCPara[PARA161]>0));
    m_RuleVariablePool.SetVariableValue("BackPump_PARA3",static_cast<double>(PLCPara[PARA162]));//运行电流
    m_RuleVariablePool.SetVariableValue("BackPump_PARA4",static_cast<bool>(PLCPara[PARA163]>0));
    m_RuleVariablePool.SetVariableValue("BackPump_PARA5",static_cast<bool>(PLCPara[PARA164]>0));
    m_RuleVariablePool.SetVariableValue("BackPump_PARA6",static_cast<bool>(PLCPara[PARA165]>0));//故障
    m_RuleVariablePool.SetVariableValue("BackPump_PARA7",static_cast<bool>(PLCPara[PARA166]>0));

    Data_DR.BackPump_PARA1=static_cast<bool>(PLCPara[PARA160]>0);
    Data_DR.BackPump_PARA2=static_cast<bool>(PLCPara[PARA161]>0);
    Data_DR.BackPump_PARA3=static_cast<double>(PLCPara[PARA162]);
    Data_DR.BackPump_PARA4=static_cast<bool>(PLCPara[PARA163]>0);
    Data_DR.BackPump_PARA5=static_cast<bool>(PLCPara[PARA164]>0);
    Data_DR.BackPump_PARA6=static_cast<bool>(PLCPara[PARA165]>0);

    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA1",static_cast<bool>(PLCPara[PARA180]>0));
    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA2",static_cast<bool>(PLCPara[PARA181]>0));
    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA3",static_cast<double>(PLCPara[PARA182]));//运行电流
    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA4",static_cast<bool>(PLCPara[PARA183]>0));
    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA5",static_cast<bool>(PLCPara[PARA184]>0));
    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA6",static_cast<bool>(PLCPara[PARA185]>0));//故障
    m_RuleVariablePool.SetVariableValue("ImprovePump_PARA7",static_cast<bool>(PLCPara[PARA186]>0));

    Data_DR.ImprovePump_PARA1=static_cast<bool>(PLCPara[PARA180]>0);
    Data_DR.ImprovePump_PARA2=static_cast<bool>(PLCPara[PARA181]>0);
    Data_DR.ImprovePump_PARA3=static_cast<double>(PLCPara[PARA182]);
    Data_DR.ImprovePump_PARA4=static_cast<bool>(PLCPara[PARA183]>0);
    Data_DR.ImprovePump_PARA5=static_cast<bool>(PLCPara[PARA184]>0);
    Data_DR.ImprovePump_PARA6=static_cast<bool>(PLCPara[PARA185]>0);

    m_RuleVariablePool.SetVariableValue("Hydro_PARA1",static_cast<double>(PLCPara[PARA201]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA2",static_cast<double>(PLCPara[PARA202]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA3",static_cast<double>(PLCPara[PARA203]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA4",static_cast<double>(PLCPara[PARA204]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA5",static_cast<double>(PLCPara[PARA205]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA6",static_cast<double>(PLCPara[PARA206]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA7",static_cast<double>(PLCPara[PARA207]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA8",static_cast<double>(PLCPara[PARA208]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA9",static_cast<double>(PLCPara[PARA209]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA10",static_cast<double>(PLCPara[PARA210]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA11",static_cast<double>(PLCPara[PARA211]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA12",static_cast<double>(PLCPara[PARA212]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA13",static_cast<double>(PLCPara[PARA213]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA14",static_cast<double>(PLCPara[PARA214]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA15",static_cast<double>(PLCPara[PARA215]));
    m_RuleVariablePool.SetVariableValue("Hydro_PARA16",static_cast<double>(PLCPara[PARA216]));

    Data_DR.Hydro_PARA1=static_cast<double>(PLCPara[PARA201]);
    Data_DR.Hydro_PARA2=static_cast<double>(PLCPara[PARA202]);
    Data_DR.Hydro_PARA3=static_cast<double>(PLCPara[PARA203]);
    Data_DR.Hydro_PARA4=static_cast<double>(PLCPara[PARA204]);
    Data_DR.Hydro_PARA5=static_cast<double>(PLCPara[PARA205]);
    Data_DR.Hydro_PARA6=static_cast<double>(PLCPara[PARA206]);
    Data_DR.Hydro_PARA7=static_cast<double>(PLCPara[PARA207]);
    Data_DR.Hydro_PARA8=static_cast<double>(PLCPara[PARA208]);
    Data_DR.Hydro_PARA9=static_cast<double>(PLCPara[PARA209]);
    Data_DR.Hydro_PARA10=static_cast<double>(PLCPara[PARA210]);
    Data_DR.Hydro_PARA11=static_cast<double>(PLCPara[PARA211]);
    Data_DR.Hydro_PARA12=static_cast<double>(PLCPara[PARA212]);
    Data_DR.Hydro_PARA13=static_cast<double>(PLCPara[PARA213]);
    Data_DR.Hydro_PARA14=static_cast<double>(PLCPara[PARA214]);
    Data_DR.Hydro_PARA15=static_cast<double>(PLCPara[PARA215]);
    Data_DR.Hydro_PARA16=static_cast<double>(PLCPara[PARA216]);
}
void RevUdp()//运行主程序
{
    //if(m_RuleVariablePool.GetCurrentStep()==3){
        //m_RuleVariablePool.SetCurrentStep(4);
        //return;

        struct sockaddr_in addr;
        int i;
        //struct tm timenow;
        //struct timeval tv;
        //time_t t;
        int RetVal=0;
        static int Connect_Tick=100;

        int addrlen,nbytes;
        unsigned char RevBuf[2000];
        addrlen = sizeof(addr);
        NetSt[3]++;
        if(fd<0)
        {
            Connect_Tick--;
            if(Connect_Tick==0)
            {
             Connect_Tick=100;
             StartRevUDP();
            }
           return;
        }
        if ((nbytes = recvfrom(fd,(char *)RevBuf, 2000, 0, (struct sockaddr *)&addr, (socklen_t *)&addrlen)) < 0)   return;

        for(i=0;i<nbytes;i++)
        {
            //qDebug()<<RevBuf[i];

            if((RevBuf[i]>='0')&&(RevBuf[i]<='9'))
            {
                //qDebug()<<">=0,<=9";
                if(i%2==0) RevUdpPack[i/2]=(RevBuf[i]-'0')*16;
                else RevUdpPack[i/2]+=RevBuf[i]-'0';
            }
            else if((RevBuf[i]>='A')&&(RevBuf[i]<='F'))
            {
                //qDebug()<<">=A,<=F";
                if(i%2==0) RevUdpPack[i/2]=(RevBuf[i]-'A'+10)*16;
                else RevUdpPack[i/2]+=RevBuf[i]-'A'+10;
            }
            else RevUdpPack[i/2]=0;

            //if(i%2) qDebug()<<RevUdpPack[i/2];
            if(i>=286)  break;

            if(i==285)//13+31+7+7+16
            {
                //qDebug()<<"接收长度正确，RevUdpPack[108]="<<RevUdpPack[108]<<" RevUdpPack[109]="<<RevUdpPack[109]<<"开始解析UDP参数";
                //qDebug()<<"rev udp buf,len="<<nbytes;
                //qDebug()<<"RevUdpPack[0]="<<RevUdpPack[HEADLEN];
                unsigned char tmpchar[4];
                PLCPara[PARA101]=(RevUdpPack[HEADLEN]&0x08)>0?1:0;//备用控制信号   
                PLCPara[PARA102]=(RevUdpPack[HEADLEN]&0x04)>0?1:0;//机旁就地控制信号
                PLCPara[PARA103]=(RevUdpPack[HEADLEN]&0x02)>0?1:0;//零螺距状态信号
                PLCPara[PARA104]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//闭环控制信号
                PLCPara[PARA105]=(RevUdpPack[HEADLEN+1]&0x04)>0?1:0;//闭环电磁阀正车信号
                PLCPara[PARA106]=(RevUdpPack[HEADLEN+1]&0x08)>0?1:0;//闭环电磁阀倒车信号
                PLCPara[PARA107]=(RevUdpPack[HEADLEN+1]&0x10)>0?1:0;//闭环卸荷阀信号
                PLCPara[PARA108]=(RevUdpPack[HEADLEN]&0x01)>0?1:0;//控制系统故障信号

                tmpchar[0]=RevUdpPack[HEADLEN+3];tmpchar[1]=RevUdpPack[HEADLEN+2];
                tmpchar[2]=RevUdpPack[HEADLEN+5];tmpchar[3]=RevUdpPack[HEADLEN+4];
                PLCPara[PARA109]=*(float*)(tmpchar)*10;//单位0.1mA 手柄指令信号

                tmpchar[0]=RevUdpPack[HEADLEN+7];tmpchar[1]=RevUdpPack[HEADLEN+6];
                tmpchar[2]=RevUdpPack[HEADLEN+9];tmpchar[3]=RevUdpPack[HEADLEN+8];
                PLCPara[PARA110]=*(float*)(&tmpchar[0])*10;//单位0.1mA //初始螺距反馈信号

                tmpchar[0]=RevUdpPack[HEADLEN+15];tmpchar[1]=RevUdpPack[HEADLEN+14];
                tmpchar[2]=RevUdpPack[HEADLEN+17];tmpchar[3]=RevUdpPack[HEADLEN+16];
                PLCPara[PARA111]=*(float*)(&tmpchar[0])*10;//单位0.1mA //螺距反馈指示信号

                tmpchar[0]=RevUdpPack[HEADLEN+11];tmpchar[1]=RevUdpPack[HEADLEN+10];
                tmpchar[2]=RevUdpPack[HEADLEN+13];tmpchar[3]=RevUdpPack[HEADLEN+12];
                PLCPara[PARA112]=*(float*)(&tmpchar[0])*10;//单位0.1V //比例阀控制输出信号

                tmpchar[0]=RevUdpPack[HEADLEN+15];tmpchar[1]=RevUdpPack[HEADLEN+14];
                tmpchar[2]=RevUdpPack[HEADLEN+17];tmpchar[3]=RevUdpPack[HEADLEN+16];
                PLCPara[PARA113]=*(float*)(&tmpchar[0])*10;//螺距反馈信号（计算输入）无此信号

                PLCPara[PARA120]=(RevUdpPack[HEADLEN+18]&0x01)>0?1:0;//备用控制信号
                PLCPara[PARA121]=(RevUdpPack[HEADLEN+18]&0x02)>0?1:0;//备用正车控制信号
                PLCPara[PARA122]=(RevUdpPack[HEADLEN+18]&0x04)>0?1:0;//备用倒车控制信号
                PLCPara[PARA123]=(RevUdpPack[HEADLEN+18]&0x08)>0?1:0;//本地控制信号
                PLCPara[PARA124]=(RevUdpPack[HEADLEN+18]&0x10)>0?1:0;//本地正车控制信号
                PLCPara[PARA125]=(RevUdpPack[HEADLEN+18]&0x20)>0?1:0;//本地倒车控制信号
                PLCPara[PARA126]=(RevUdpPack[HEADLEN+18]&0x40)>0?1:0;//PTO泵卸荷信号
                PLCPara[PARA127]=(RevUdpPack[HEADLEN+19]&0x01)>0?1:0;//备用泵遥控信号
                PLCPara[PARA128]=(RevUdpPack[HEADLEN+19]&0x02)>0?1:0;//备用泵电源信号
                PLCPara[PARA129]=(RevUdpPack[HEADLEN+19]&0x04)>0?1:0;//备用泵电机运行故障信号
                PLCPara[PARA130]=(RevUdpPack[HEADLEN+19]&0x10)>0?1:0;//提升泵电源信号
                PLCPara[PARA131]=(RevUdpPack[HEADLEN+19]&0x20)>0?1:0;//提升泵运行信号
                PLCPara[PARA132]=(RevUdpPack[HEADLEN+19]&0x40)>0?1:0;//提升泵遥控信号
                PLCPara[PARA133]=(RevUdpPack[HEADLEN+19]&0x80)>0?1:0;//提升泵运行故障信号
                PLCPara[PARA134]=(RevUdpPack[HEADLEN+19]&0x08)>0?1:0;//重力油箱液位低信号
                PLCPara[PARA135]=(RevUdpPack[HEADLEN+20]&0x01)>0?1:0;//PTO泵出口滤器堵塞状态信号
                PLCPara[PARA136]=(RevUdpPack[HEADLEN+20]&0x02)>0?1:0;//主油泵出口滤器堵塞状态信号
                PLCPara[PARA137]=(RevUdpPack[HEADLEN+20]&0x02)>0?1:0;//主油泵出口滤器堵塞状态信号****重复
                PLCPara[PARA138]=(RevUdpPack[HEADLEN+20]&0x08)>0?1:0;//PTO一级泵运行信号
                PLCPara[PARA139]=(RevUdpPack[HEADLEN+20]&0x10)>0?1:0;//PTO二级泵运行信号
                PLCPara[PARA140]=(RevUdpPack[HEADLEN+20]&0x20)>0?1:0;//主油箱液位低信号
                PLCPara[PARA141]=(RevUdpPack[HEADLEN+21]&0x10)>0?1:0;//主电源失电信号
                PLCPara[PARA142]=(RevUdpPack[HEADLEN+21]&0x20)>0?1:0;//备用电源失电信号

                tmpchar[0]=RevUdpPack[HEADLEN+32];tmpchar[1]=RevUdpPack[HEADLEN+31];
                tmpchar[2]=RevUdpPack[HEADLEN+34];tmpchar[3]=RevUdpPack[HEADLEN+33];
                //qDebug()<<RevUdpPack[HEADLEN+31]<<" "<<RevUdpPack[HEADLEN+32]<<" "<<RevUdpPack[HEADLEN+33]<<" "<<RevUdpPack[HEADLEN+34];
                PLCPara[PARA143]=*(float*)(&tmpchar[0]);// //系统油压传感器信号

                tmpchar[0]=RevUdpPack[HEADLEN+36];tmpchar[1]=RevUdpPack[HEADLEN+35];
                tmpchar[2]=RevUdpPack[HEADLEN+38];tmpchar[3]=RevUdpPack[HEADLEN+37];
                PLCPara[PARA144]=*(float*)(&tmpchar[0]);//A口油压传感器信号

                tmpchar[0]=RevUdpPack[HEADLEN+40];tmpchar[1]=RevUdpPack[HEADLEN+39];
                tmpchar[2]=RevUdpPack[HEADLEN+42];tmpchar[3]=RevUdpPack[HEADLEN+41];
                PLCPara[PARA145]=*(float*)(&tmpchar[0]);//B口油压传感器信号

                tmpchar[0]=RevUdpPack[HEADLEN+44];tmpchar[1]=RevUdpPack[HEADLEN+43];
                tmpchar[2]=RevUdpPack[HEADLEN+46];tmpchar[3]=RevUdpPack[HEADLEN+45];
                PLCPara[PARA146]=*(float*)(&tmpchar[0]);//静压腔油压传感器信号

                tmpchar[0]=RevUdpPack[HEADLEN+48];tmpchar[1]=RevUdpPack[HEADLEN+47];
                tmpchar[2]=RevUdpPack[HEADLEN+50];tmpchar[3]=RevUdpPack[HEADLEN+49];
                PLCPara[PARA147]=*(float*)(&tmpchar[0]);//主油箱液位传感器信号

                tmpchar[0]=RevUdpPack[HEADLEN+56];tmpchar[1]=RevUdpPack[HEADLEN+55];
                tmpchar[2]=RevUdpPack[HEADLEN+58];tmpchar[3]=RevUdpPack[HEADLEN+57];
                PLCPara[PARA148]=*(float*)(&tmpchar[0])*10;//单位0.1V 比例阀阀芯位移信号

                tmpchar[0]=RevUdpPack[HEADLEN+52];tmpchar[1]=RevUdpPack[HEADLEN+51];
                tmpchar[2]=RevUdpPack[HEADLEN+54];tmpchar[3]=RevUdpPack[HEADLEN+53];
                PLCPara[PARA149]=*(float*)(&tmpchar[0]);//系统油温信号

                tmpchar[0]=RevUdpPack[HEADLEN+24];tmpchar[1]=RevUdpPack[HEADLEN+23];
                tmpchar[2]=RevUdpPack[HEADLEN+26];tmpchar[3]=RevUdpPack[HEADLEN+25];
                PLCPara[PARA150]=*(float*)(&tmpchar[0])*10;//单位0.1mA 初始螺距指示

                PLCPara[PARA151]=(RevUdpPack[HEADLEN+18]&0x80)>0?1:0;//备用泵运行

                //PLCPara[PARA160]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//电压监测信号********
                //PLCPara[PARA161]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//电源相序监测信号********
                tmpchar[0]=RevUdpPack[HEADLEN+68];tmpchar[1]=RevUdpPack[HEADLEN+67];
                tmpchar[2]=RevUdpPack[HEADLEN+70];tmpchar[3]=RevUdpPack[HEADLEN+69];
                PLCPara[PARA162]=*(float*)(&tmpchar[0]);//备用泵电机运行电流********
                //PLCPara[PARA163]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//热元件保护监测信号********
                //PLCPara[PARA164]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//电机热保护信号********


                PLCPara[PARA165]=(RevUdpPack[HEADLEN+22]&0x02)>0?1:0;//备用泵电机保护器故障********

               // PLCPara[PARA166]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//无********
                //PLCPara[PARA180]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//电压监测信号********
                //PLCPara[PARA181]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//电源相序监测信号********
                tmpchar[0]=RevUdpPack[HEADLEN+72];tmpchar[1]=RevUdpPack[HEADLEN+71];
                tmpchar[2]=RevUdpPack[HEADLEN+74];tmpchar[3]=RevUdpPack[HEADLEN+73];
                PLCPara[PARA182]=*(float*)(&tmpchar[0]);//提升泵电机运行电流********
                //PLCPara[PARA183]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//热元件保护监测信号********
                //PLCPara[PARA184]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//电机热保护信号********

                PLCPara[PARA185]=(RevUdpPack[HEADLEN+22]&0x04)>0?1:0;//提升泵电机保护器故障********
                //PLCPara[PARA186]=(RevUdpPack[HEADLEN]&0x10)>0?1:0;//无********

                PLCPara[PARA201]=(RevUdpPack[HEADLEN+119]*256+RevUdpPack[HEADLEN+120])*10.0/65535;//PZ1压力传感器 单位MPA
                PLCPara[PARA202]=(RevUdpPack[HEADLEN+121]*256+RevUdpPack[HEADLEN+122])*10.0/65535;//PZ2压力传感器
                PLCPara[PARA203]=(RevUdpPack[HEADLEN+123]*256+RevUdpPack[HEADLEN+124])*10.0/65535;//PZ3压力传感器
                PLCPara[PARA204]=(RevUdpPack[HEADLEN+125]*256+RevUdpPack[HEADLEN+126])*10.0/65535;//PZ4压力传感器
                PLCPara[PARA205]=(RevUdpPack[HEADLEN+95]*256+RevUdpPack[HEADLEN+96])*1.0/65535;//PZ5压力传感器
                PLCPara[PARA206]=(RevUdpPack[HEADLEN+105]*256+RevUdpPack[HEADLEN+106])*40.0/65535;//PZ6压力传感器
                PLCPara[PARA207]=(RevUdpPack[HEADLEN+107]*256+RevUdpPack[HEADLEN+108])*40.0/65535;//PZ7压力传感器
                PLCPara[PARA208]=(RevUdpPack[HEADLEN+109]*256+RevUdpPack[HEADLEN+110])*40.0/65535;//PZ8压力传感器
                PLCPara[PARA209]=(RevUdpPack[HEADLEN+111]*256+RevUdpPack[HEADLEN+112])*40.0/65535;//PZ9压力传感器*****

                tmpchar[0]=RevUdpPack[HEADLEN+32];tmpchar[1]=RevUdpPack[HEADLEN+31];
                tmpchar[2]=RevUdpPack[HEADLEN+34];tmpchar[3]=RevUdpPack[HEADLEN+33];
                PLCPara[PARA210]=*(float*)(&tmpchar[0]);//PT2压力传感器

                PLCPara[PARA211]=-250+(RevUdpPack[HEADLEN+127]*256+RevUdpPack[HEADLEN+128])*600.0/65535;//FZ1流量传感器
                PLCPara[PARA212]=-250+(RevUdpPack[HEADLEN+129]*256+RevUdpPack[HEADLEN+130])*600.0/65535;//FZ2流量传感器
                PLCPara[PARA213]=-230+(RevUdpPack[HEADLEN+131]*256+RevUdpPack[HEADLEN+132])*600.0/65535;//FZ3流量传感器
                PLCPara[PARA214]=-400+(RevUdpPack[HEADLEN+133]*256+RevUdpPack[HEADLEN+134])*600.0/65535;//FZ4流量传感器
                PLCPara[PARA215]=(RevUdpPack[HEADLEN+135]*256+RevUdpPack[HEADLEN+136])*600.0/65535;//FZ5流量传感器
                PLCPara[PARA216]=(RevUdpPack[HEADLEN+97]*256+RevUdpPack[HEADLEN+98])*100.0/65535;//FZ6流量传感器 0~100%

                NetSt[3]=0;
                LoadDataToBase();
                UpdIdx=0;
                break;
            }
        }

        //m_RuleVariablePool.SetCurrentStep(5);
        //qDebug()<<"SetCurrentStep(5)";
    //}
}
//功能：将QByteArray对象转换成空格隔开的16进制字符串
//实现：通过将QByteArray中的每个字符转换成对应的16进制字符串，再用空格连接。
QString MK2CPU_DataTransThread::BufToStr(unsigned char* buf,int len)
{
    QString Str;
    Str="";
    for (int i=0;i<len;i++)
    {
      Str=Str+" "+QString::number(buf[i],16);
    }
    return Str;
}
