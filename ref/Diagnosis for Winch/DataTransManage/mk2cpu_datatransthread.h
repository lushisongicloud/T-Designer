#ifndef MK2CPU_DATATRANSTHREAD_H
#define MK2CPU_DATATRANSTHREAD_H


#include <QThread>
#include "Diagnosis/rulevariablepool.h"
#include "CommDef.h"
#include <QTcpSocket>
#include "qstring.h"
extern int StartRevUDP();
extern void RevUdp();
#define HEADLEN 0

#define PARA101 0
#define PARA102 1
#define PARA103 2
#define PARA104 3
#define PARA105 4
#define PARA106 5
#define PARA107 6
#define PARA108 7
#define PARA109 8
#define PARA110 9
#define PARA111 10
#define PARA112 11
#define PARA113 12
#define PARA120 19
#define PARA121 20
#define PARA122 21
#define PARA123 22
#define PARA124 23
#define PARA125 24
#define PARA126 25
#define PARA127 26
#define PARA128 27
#define PARA129 28
#define PARA130 29
#define PARA131 30
#define PARA132 31
#define PARA133 32
#define PARA134 33
#define PARA135 34
#define PARA136 35
#define PARA137 36
#define PARA138 37
#define PARA139 38
#define PARA140 39
#define PARA141 40
#define PARA142 41
#define PARA143 42
#define PARA144 43
#define PARA145 44
#define PARA146 45
#define PARA147 46
#define PARA148 47
#define PARA149 48
#define PARA150 49
#define PARA151 50
#define PARA160 59
#define PARA161 60
#define PARA162 61
#define PARA163 62
#define PARA164 63
#define PARA165 64
#define PARA166 65
#define PARA180 79
#define PARA181 80
#define PARA182 81
#define PARA183 82
#define PARA184 83
#define PARA185 84
#define PARA186 85
#define PARA201 100
#define PARA202 101
#define PARA203 102
#define PARA204 103
#define PARA205 104
#define PARA206 105
#define PARA207 106
#define PARA208 107
#define PARA209 108
#define PARA210 109
#define PARA211 110
#define PARA212 111
#define PARA213 112
#define PARA214 113
#define PARA215 114
#define PARA216 115
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:1.MK2CPU通信端口的通信线程
 * Description:2.实时更新m_RuleVariablePool中由MK2CPU通信的变量
 * Description:3.目前通信协议未写，暂以一个随机数代替
**************************************************/

class MK2CPU_DataTransThread : public QObject
{
    Q_OBJECT
public:
    explicit MK2CPU_DataTransThread();

    void ProcessBuf(unsigned char *Buf,int Len);

    QString BufToStr(unsigned char* buf,int len);

    //void LoadDataToBase();

    //QTimer *TimerRunner;

    bool ConnectSt=false;


public slots:
    //void readBuf(); //读取报文（自动监听）
    //void timerRun();
};

#endif // MK2CPU_DATATRANSTHREAD_H
