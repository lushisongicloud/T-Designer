#include "Data_Save.h"
#include "CommDef.h"
#include "mainwindow.h"
#include <qdebug.h>
#include <QDateTime>
#include <QTime>
#include "windows.h"
#include <stdio.h>
#include "time.h"
//每10分钟（按照绝对时间计算）保存一个文件数据，文件第一个位置保存当前时间的保存一个结构体，然后依次保存数据
//每10分钟建立一个新文件，系统开始存储的第一个文件可能不是全长度的。
//为了避免频繁地写文件，系统按照一分钟的时间间隔缓存数据
extern int timeDiff;
extern char TestInfo[1000];
STRU_DataDR Data_DR;
ST_DR_FILEBUF DR_FileBuf;
bool DRRecording_Now=false;
bool EndTestSignal=false;//停止试验信号
int Record_Idx=0;
int Recoring_Minute=0;
struct  timeval StartTime;
unsigned long DiskTotal,DiskAvailable;
extern bool IsInTest;
char CurFileName[500];
int PrintRecord_Idx=0;
char DRFileName[500]="";
char NewDRFileName[500]="";
int TimeOfRecording=0;
//===========================================================================
int gettimeofday(struct timeval *tp, void *tzp)
{
  time_t clock;
  struct tm tm;
  SYSTEMTIME wtm;
  GetLocalTime(&wtm);
  tm.tm_year   = wtm.wYear - 1900;
  tm.tm_mon   = wtm.wMonth - 1;
  tm.tm_mday   = wtm.wDay;
  tm.tm_hour   = wtm.wHour;
  tm.tm_min   = wtm.wMinute;
  tm.tm_sec   = wtm.wSecond;
  tm. tm_isdst  = -1;
  clock = mktime(&tm);
  tp->tv_sec = clock;
  tp->tv_usec = wtm.wMilliseconds * 1000;
  return (0);
}
void GetDiskInfo(unsigned long *TotalMB, unsigned long * FreeMB)
{
    QString strDisk;
    strDisk="C:/";
    LPCWSTR lpcwstrDriver = (LPCWSTR)strDisk.utf16();
    ULARGE_INTEGER lFreeBytesAvailable, lTotalBytesTemp, lTotalFreeBytes;

    if( !GetDiskFreeSpaceEx( lpcwstrDriver, &lFreeBytesAvailable, &lTotalBytesTemp, &lTotalFreeBytes ) )
    {
       printf("Acquire Disk Space Failed !" );
       //TotalMB = -1;
       //FreeMB = -1;
       return ;
    }

    //unit : MB
    *TotalMB = (unsigned long)(lTotalBytesTemp.QuadPart / 1024 / 1024);
    *FreeMB = (unsigned long)(lTotalFreeBytes.QuadPart / 1024 / 1024);


    //printf ("D Disk Total Space=%dMB!\n",*TotalMB);
    //printf ("D Disk Free Space=%dMB!\n",*FreeMB);
 }


int IDX=0;

void SaveThread()
{
     struct  timeval    tv,tvLast;  //函数 gettimeofday 时间参数结构体
     gettimeofday(&tvLast,NULL);//获取当前时间
     unsigned long TimeDif;
     static int TickCnt =  0;
     struct tm *p;
     int i;

     int MSecTickCnt=0;

    while(1)
    {
        //printf("********************************DATA SAVE Thread is running .\n");
        Sleep(1);//每过1毫秒检查一下，是否存储 数据
        TickCnt++;
        if(TickCnt>=50)
        {
            TickCnt = 0;
        }
        gettimeofday(&tv,NULL);//获取当前时间
        if(tv.tv_usec>tvLast.tv_usec)
            TimeDif=tv.tv_usec-tvLast.tv_usec;
        else
             TimeDif=tv.tv_usec+(1000000-tvLast.tv_usec);
       //printf("TimeDif=%d",TimeDif);
       if(TimeDif>100000)
       {
        if(IsInTest) TimeOfRecording++;
        signal_handler();
        MSecTickCnt++;

        if(tvLast.tv_usec>=900000 )
        {
            tvLast.tv_sec++;tvLast.tv_usec=(tvLast.tv_usec+100000)%1000000;
        }
        else
            tvLast.tv_usec=tvLast.tv_usec+100000;
       }
    }
    //return NULL;
}

//=====================================================================================

void  signal_handler()
{
    QTextCodec *codec = QTextCodec::codecForName("UTF-8");
    QTextCodec::setCodecForLocale(codec); //解决汉字乱码问题
   // if(m!=SIGALRM) return;
    FILE * fp;
    FILE * allfp;
  //  static int TimeCnt=0;
    int i;
    struct  timeval    tv;  //函数 gettimeofday 时间参数结构体
    //struct  timezone   tz;  //函数 gettimeofday 用于保存时区结构体


    bool CheckTimeSig;
    char AllFileName[500];


    gettimeofday(&tv,NULL);//获取当前时间
    CheckTimeSig=true; //值为true:还是上一数据块

    if(EndTestSignal)
    {
        EndTestSignal=false;
        DRRecording_Now=false;
        TimeOfRecording=0;

        QFile m_File(DRFileName);
        if(m_File.exists()) m_File.rename(QString::fromUtf8(NewDRFileName));
        else  m_File.setFileName(NewDRFileName);
        DR_FileBuf.EndMinute=tv.tv_sec/60;//分钟，绝对时间从1970年开始
        DR_FileBuf.EndSecond=tv.tv_sec%60;//秒
        DR_FileBuf.EndmSec=tv.tv_usec/1000;//毫秒
        memcpy(DR_FileBuf.TestInfo,TestInfo,sizeof(TestInfo));
        //qDebug()<<QString::fromUtf8(DR_FileBuf.TestResult);
        DR_FileBuf.DataDR[Record_Idx++]=Data_DR;

        m_File.open(QIODevice::ReadWrite);  //不存在的情况下，打开包含了新建文件的操作
        m_File.seek(m_File.size());
        m_File.write((char *)(&DR_FileBuf),sizeof(DR_FileBuf));
        m_File.close();
    }

    if(DRRecording_Now)
    {
        if(Recoring_Minute!=(tv.tv_sec/60)) CheckTimeSig=false; //开始新1min数据缓存
        if((Record_Idx<60*10)&&(CheckTimeSig)) DR_FileBuf.DataDR[Record_Idx++]=Data_DR; //xcc modify

       //if((!CheckTimeSig)||(Record_Idx>=60*5)) //写入fd //xcc modify
        if(!CheckTimeSig) //写入fd //xcc modify
        {
            if((Record_Idx)>0&&(Record_Idx!=600))
            {
              for(i=Record_Idx;i<600;i++) DR_FileBuf.DataDR[i]=DR_FileBuf.DataDR[i-1];
            }
            PrintRecord_Idx=Record_Idx;
            memcpy(CurFileName,DRFileName,sizeof(DRFileName));
            if(IsInTest)
            {
                fp=fopen(DRFileName,"ab+");
                if(fp!=NULL)
                {
                    fwrite(&DR_FileBuf,sizeof(DR_FileBuf),1,fp);
                    fclose(fp);
                    printf("SAVE DATA TO THE DISK OK....%s....\n",DRFileName);
                }
            }
            DRRecording_Now=false;
        }
        if(CheckTimeSig) return;//还是上一块的数据
    }

    if(!DRRecording_Now)
    {
       //printf("Start a new block now...........................\n");
       Recoring_Minute=tv.tv_sec/60;
       DR_FileBuf.Minute=Recoring_Minute;//分钟，绝对时间从1970年开始
       DR_FileBuf.StartSecond=tv.tv_sec%60;//秒
       DR_FileBuf.StartmSec=tv.tv_usec/1000;//毫秒
       Record_Idx=0;
       DR_FileBuf.DataDR[Record_Idx++]=Data_DR;
       DRRecording_Now=true;
       StartTime=tv;
       //printf("start one block recording, CurTime Sec=%ld USec=%ld Recoring_Minute=%d,StartSecond=%d,StartmSec=%d\n",tv.tv_sec,tv.tv_usec,Recoring_Minute,DR_FileBuf.StartSecond,DR_FileBuf.StartmSec);
       return;
    }
  //  printf("CurTime Sec=%ld USec=%ld",tv.tv_usec,tv.tv_usec);
}

