#ifndef COMMDEF_H
#define COMMDEF_H

#include<QFile>
#include <QColor>
#include <QDateTime>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

typedef struct
{
 int SYS_ID;
 float ParaAddr;
 int GraphIdx;
 QString Var_Name;
 QString Var_Type;
 QString Var_Note;
 QString Var_Group;//开关量 模拟量 自定义变量等
 float Var_Range;//量程
 bool Transform;//是否变换
 bool IsVisible;
 QColor  Clr;
 double SFCoef;
 double PYVal;
 QString DW;//单位
} STRU_DRAW_DEF;

typedef struct
{
  bool TimeSearchIsEnabled;
  QDateTime StartTime;
  QDateTime FinishTime;
  bool ParaConditionSearchIsEnabled;
  bool ParaConditionIsEnabled[4];
  STRU_DRAW_DEF ParaDef[4];
  QString ParaSymble[4];
  float ParaConditionVal[4];
  bool FilterIsSet=false;
} STRU_SEARCH_DEF;

typedef struct
{
    double CentreBox_U01;
    double CentreBox_U02;
    double CentreBox_U03;
    double CentreBox_U04;
    double CentreBox_U05;
    double CentreBox_U06;
    double CentreBox_U07;
    double CentreBox_U08;
    double CentreBox_U09;
    double CentreBox_U10;
    double CentreBox_I01;
    double CentreBox_I02;
    double CentreBox_I03;
    double CentreBox_bak1;
    double CentreBox_bak2;
    double CentreBox_bak3;//16
    double MechCtrolBox_U01;
    double MechCtrolBox_U02;
    double MechCtrolBox_U03;
    double MechCtrolBox_U04;
    double MechCtrolBox_U05;
    double MechCtrolBox_U06;
    double MechCtrolBox_U07;
    double MechCtrolBox_U08;
    double MechCtrolBox_U09;
    double MechCtrolBox_U10;
    double MechCtrolBox_U11;
    double MechCtrolBox_U12;
    double MechCtrolBox_U13;
    double MechCtrolBox_U14;
    double MechCtrolBox_U15;
    double MechCtrolBox_U16;
    double MechCtrolBox_U17;
    double MechCtrolBox_U18;
    double MechCtrolBox_U19;
    double MechCtrolBox_U20;
    double MechCtrolBox_U21;
    double MechCtrolBox_U22;
    double MechCtrolBox_bak1;
    double MechCtrolBox_bak2;
    double MechCtrolBox_bak3;//25
    double BackPump_U01;
    double BackPump_U02;
    double BackPump_U03;
    double BackPump_U04;
    double BackPump_U05;
    double BackPump_U06;
    double BackPump_U07;
    double BackPump_U08;
    double BackPump_U09;
    double BackPump_U10;
    double BackPump_U11;
    double BackPump_U12;
    double BackPump_U13;
    double BackPump_bak1;
    double BackPump_bak2;
    double BackPump_bak3;//16
    double ImprovePump_U01;
    double ImprovePump_U02;
    double ImprovePump_U03;
    double ImprovePump_U04;
    double ImprovePump_U05;
    double ImprovePump_U06;
    double ImprovePump_U07;
    double ImprovePump_U08;
    double ImprovePump_U09;
    double ImprovePump_U10;
    double ImprovePump_U11;
    double ImprovePump_U12;
    double ImprovePump_U13;
    double ImprovePump_bak1;
    double ImprovePump_bak2;
    double ImprovePump_bak3;//16
    bool CentreBox_PARA1;
    bool CentreBox_PARA2;
    bool CentreBox_PARA3;
    bool CentreBox_PARA4;
    bool CentreBox_PARA5;
    bool CentreBox_PARA6;
    bool CentreBox_PARA7;
    bool CentreBox_PARA8;
    double CentreBox_PARA9;
    double CentreBox_PARA10;
    double CentreBox_PARA11;
    double CentreBox_PARA12;
    double CentreBox_PARA13;
    double CentreBox_PARA_bak1;
    double CentreBox_PARA_bak2;
    double CentreBox_PARA_bak3;//16
    bool MechCtrolBox_PARA1;
    bool MechCtrolBox_PARA2;
    bool MechCtrolBox_PARA3;
    bool MechCtrolBox_PARA4;
    bool MechCtrolBox_PARA5;
    bool MechCtrolBox_PARA6;
    bool MechCtrolBox_PARA7;
    bool MechCtrolBox_PARA8;
    bool MechCtrolBox_PARA9;
    bool MechCtrolBox_PARA10;
    bool MechCtrolBox_PARA11;
    bool MechCtrolBox_PARA12;
    bool MechCtrolBox_PARA13;
    bool MechCtrolBox_PARA14;
    bool MechCtrolBox_PARA15;
    bool MechCtrolBox_PARA16;
    bool MechCtrolBox_PARA17;
    bool MechCtrolBox_PARA18;
    bool MechCtrolBox_PARA19;
    bool MechCtrolBox_PARA20;
    bool MechCtrolBox_PARA21;
    bool MechCtrolBox_PARA22;
    bool MechCtrolBox_PARA23;
    double MechCtrolBox_PARA24;
    double MechCtrolBox_PARA25;
    double MechCtrolBox_PARA26;
    double MechCtrolBox_PARA27;
    double MechCtrolBox_PARA28;
    double MechCtrolBox_PARA29;
    double MechCtrolBox_PARA30;
    double MechCtrolBox_PARA31;
    bool MechCtrolBox_PARA32;
    double MechCtrolBox_PARA_bak1;
    double MechCtrolBox_PARA_bak2;
    double MechCtrolBox_PARA_bak3;//35
    bool BackPump_PARA1;
    bool BackPump_PARA2;
    double BackPump_PARA3;
    bool BackPump_PARA4;
    bool BackPump_PARA5;
    bool BackPump_PARA6;
    double BackPump_PARA_bak1;
    double BackPump_PARA_bak2;
    double BackPump_PARA_bak3;//9
    bool ImprovePump_PARA1;
    bool ImprovePump_PARA2;
    double ImprovePump_PARA3;
    bool ImprovePump_PARA4;
    bool ImprovePump_PARA5;
    bool ImprovePump_PARA6;
    double ImprovePump_PARA_bak1;
    double ImprovePump_PARA_bak2;
    double ImprovePump_PARA_bak3;//9
    double Hydro_PARA1;
    double Hydro_PARA2;
    double Hydro_PARA3;
    double Hydro_PARA4;
    double Hydro_PARA5;
    double Hydro_PARA6;
    double Hydro_PARA7;
    double Hydro_PARA8;
    double Hydro_PARA9;
    double Hydro_PARA10;
    double Hydro_PARA11;
    double Hydro_PARA12;
    double Hydro_PARA13;
    double Hydro_PARA14;
    double Hydro_PARA15;
    double Hydro_PARA16;
    double Hydro_PARA_bak1;
    double Hydro_PARA_bak2;
    double Hydro_PARA_bak3;//19
} STRU_DataDR;

typedef struct
{
    long  Minute=0;
    int StartSecond=0;//S
    int StartmSec=0;   //mS
    long  EndMinute=0;
    int EndSecond=0;//S
    int EndmSec=0;   //mS
    char TestInfo[1000];//测试信息
    STRU_DataDR DataDR[1*60*10];//1分钟的数据 更新为10Hz
}  ST_DR_FILEBUF;

extern STRU_DataDR Data_DR;
#define DATA_SAVE_DISK "/home/zju/DATA_OF_RECORD/"  //"/media/F228139828135AC5/"
#define EXCEL_SAVE_DISK "/home/zju/EXCEL_OF_RECORD/"
#endif // COMMDEF_H
