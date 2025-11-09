#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>
#include <QTimer>
#include "myqsqldatabase.h"
#include <QTextEdit>
#include <QRadioButton>
#include <QTcpSocket>
#include <QMetaType>
#include <QStandardItemModel>

#include "UserManage/usermanage.h"
#include "UserManage/qdlglogin.h"
#include "ConnectManage/connectset.h"
#include "VariableManage/variablemanage.h"
#include "RuleManage/rulemanage.h"
#include "WarnManage/rulewarnmanage.h"
#include "RealTimeDisplayManage/formhydraulicstate.h"
#include "RealTimeDisplayManage/formrealtimedata.h"
#include "RealTimeDisplayManage/formalarminformation.h"
#include "RealTimeDisplayManage/formwarninformation.h"
#include "DataTransManage/detector1_datatransthread.h"
#include "DataTransManage/detector2_datatransthread.h"
#include "DataTransManage/detector3_datatransthread.h"
#include "DataTransManage/mk2cpu_datatransthread.h"
#include "DataTransManage/mk5cpu_datatransthread.h"
#include "Diagnosis/diagnosis.h"
#include "Diagnosis/rulevariablepool.h"
#include "Diagnosis/rulepool.h"
#include "drawgridset.h"
#include "CommDef.h"
#include "time.h"
#include "dlgmessage.h"
#include "bqgraphicsitem.h"
#include "bqgraphicsscene.h"
#include "dlgtestprio.h"

extern RuleVariablePool m_RuleVariablePool;
extern DataBase::Str_account  m_loginAccount;//当前登陆账户信息
extern RulePool m_RulePool;
extern QMutex mutex;
extern QString m_strFilePath;
/*************************************************
 * Copyright:浙江大学先进技术研究院
 * Author:许伟
 * Date:2021-5-8
 * Description:规则库诊断主程序
**************************************************/
typedef struct
{
    QString StrTestName;//诊断测试名称 如“观察PLC_I1_2_LED指示灯”
    QString StrCurFault;//当前异常 如“手动排缆左移功能异常——未检测到按钮输入”
    QString StrTestPos;//测试位置 如“收放控制机柜->PLC-> PLC_I1_2_LED”
    QStringList ListImgPosPath;//位置图片
    QStringList ListImgTermPath;//观测点位图片
    QString TestTool;//测试工具 若为空则工具按钮不可点
    QString ImgToolPath;//工具图片 如"万用表.png"
    QString StrQuestion;//对话框内容
    QString StrButton1;//按钮1文字
    QString StrButton2;//按钮2文字
    QString StrDesc;//步骤
    QList<QStringList> ListFuzzyProb;//可能故障列表
}STRU_OneTestStepSet;

namespace Ui {
class MainWindow;
}

class MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    explicit MainWindow(QWidget *parent = nullptr);
    ~MainWindow();
    void closeEvent(QCloseEvent *event);

    //设置登陆账户并初始化登陆账户名称及权限
    void setLoginAccount(DataBase::Str_account loginAccount);
    void UpdateRealTimeWarnInfo();
    void LoadDataList();
    void DelDR();
    void LoadFile(QString InitFileName,int GraphIdx);
    void InitChart();
    void setupSimpleDemo(QCustomPlot *customPlot);
    void TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex);
    void tableParaInit();
    void DrawSet();
    void InitTabWidget_test_image();
    //=========================================================新加函数20231209===========================
    void InitTableChoose_Alarm();//初始化供手动选择的待诊断的功能列表
    void InitTableFuzzl_Alarm();//初始化可能故障表格
    void InitTestStepSet();//初始化所有可选测试
    void CreateDiagnoisTree();//(QString StrTestName);//诊断树生成
    void LoadDiagnosisUI();//载入当前测试的UI
    void UpdateHisTest();//更新历史测试记录
    dlgMessage *mdlgMessage;
    DlgTestPrio *mdlgTestPrio;
    BQGraphicsScene m_scene_pos,m_scene_term;
    //=========================================================新加函数20231209===========================

    void InitTableHisStep();
    void AdjustGraphicScene(QGraphicsView *mGraphicsView,BQGraphicsScene *pGraphicsScene,QString Path);
    void AdjustIamgeLayout(QLabel *pLabel,QString Path);
    void AdjustImageLayout(QLabel *label, const QString &imagePath);


    QTcpSocket *Socket;
    QThread * Detector1Thread;
    int CurPageNum=1;
    int CurTestInfoIdx=-1;
    int CurPageNum_Test=1;
    //QCustomPlot *m_customPlot[4];

    int CurveMode;//0:历史曲线 1：实时曲线
    QSignalMapper * myMapper;

private slots:
    void on_pushButtonSwitchUser_clicked();

    void on_pushButtonQuit_clicked();

    void on_pushButtonClearWarnningRecord_clicked();

    void on_pushButtonStopDiagnosis_clicked();

    void on_pushButtonStartupDiagnosis_clicked();

    void slotRealAlarmMoveToDiagnosis();//点击实时诊断文字跳转函数=====新加函数20231209===========================

private:

    //设置软件状态为故障诊断中
    void policyTroubleshootStart();

    //设置软件状态为故障诊断结束
    void policyTroubleshootEnd();

    double GetVarVal(QString ValName);

    void GetCurveData(int GraphIdx,double key);

    void LoadDataInfo();
    void ToExcel();
    void FileToExcel();

    //DlgAnalysis *m_DlgAnalysis;
    //DlgDFastParaSet *m_DlgDFastParaSet;
    QMenu *table_para_menu;
    QMenu *file_menu,*file_menu_all;
    QMenu *table_DFastPara_menu;
    QAction *actAddToChart1,*actAddToChart2,*actAddToChart3,*actAddToChart4;
    QAction *actFileToChart1,*actFileToChart2,*actFileToChart3,*actFileToChart4;
    STRU_DRAW_DEF stDraw[MAX_LINE_CNT];
    //STRU_DRAW_DEF stDraw[4][MAX_LINE_CNT];
    STRU_SEARCH_DEF stSearch;
    int LineCount=0;
    int TotalTimeOfGraph=0;
    //int LineCount[4]={0,0,0,0};
    QVector<QPointF> SeriesPoints[MAX_LINE_CNT];
    int CurYMax=10,CurYMin=-10;
    int TimeRangeVal,HzVal;


private:
    Ui::MainWindow *ui;
    //UI右上角时间显示
    QTimer* timerUpdateUI;

    //数据库检索类
    myQSqlDatabase *TMATE_Database = nullptr;

    //用户管理界面
    UserManage *WidgetUserManage = nullptr;

    //连接管理界面
    ConnectSet *WidgetConnectManage = nullptr;

    //变量库管理界面
    VariableManage *WidgetVariableManage = nullptr;

    //规则管理界面
    RuleManage *WidgetRuleManage = nullptr;

    //预警规则管理界面
    WarnManage *WidgetWarnManage = nullptr;

    //液压状态显示界面
    FormHydraulicState *WidgetHydraulicState = nullptr;

    //实时数据显示界面
    FormRealTimeData *WidgetRealTimeData = nullptr;

    //故障信息显示界面
    FormAlarmInformation *WidgetFaultInformation = nullptr;

    //预报警信息显示界面
    FormWarnInformation *WidgetWarnningInformation = nullptr;

    //数据传输线程
    Detector1_DataTrans *m_Detector1_DataTrans = nullptr;
    Detector1_DataTrans *m_Detector2_DataTrans = nullptr;
    Detector1_DataTrans *m_Detector3_DataTrans = nullptr;
    MK2CPU_DataTransThread *MK2CPU_DataTrans = nullptr;
    MK5CPU_DataTransThread *MK5CPU_DataTrans = nullptr;
    //故障诊断线程
    Diagnosis *DiagnosisThread = nullptr;
    QTextEdit *m_TextEdit;


private slots:
    //故障报警信号处理槽函数
    void  on_newFaliureError();

    //预警报警信号处理槽函数
    void  on_newWarnningError();

    //基础信号更新处理槽函数
    void  on_newBasicSignalUpdate();

    //变量名称更新处理槽函数
    void  on_VariableNameChange(QString OraginVariableName,QString ChangeVariableName);

    //变量删除处理槽函数
    void  on_VariableDelete(QString VariableName);

    void on_UpdateFaliureOrWarnning(QVector<DataBase::Signal> signal);
    void UpdateRealTimeFaliureOrWarnning();
    void UpdateHisFaliureOrWarnning();
    void on_radioButton_realtimeAlarm_clicked(bool checked);
    void on_radioButton_HisAlarm_clicked(bool checked);
    void on_pushButton_DMS_TableControl_FirstPage_clicked();
    void on_pushButton_DMS_TableControl_PreviousPage_clicked();
    void on_pushButton_DMS_TableControl_NextPage_clicked();
    void on_pushButton_DMS_TableControl_LastPage_clicked();
    void on_comboBox_DMS_TableControl_PageRecordsNumber_currentIndexChanged(int index);
    void on_pushButton_UpdateMannulSet_clicked();
    void on_tabWidgetMain_currentChanged(int index);
    void DoUpdateUI();
    void on_BtnSearch_clicked();
    void on_BtnClearCurAllRecords_clicked();
    void on_BtnClearCurSelectRecords_clicked();
    void on_BtnClearCurPageRecords_clicked();
    void on_spinBoxPageNum_valueChanged(int arg1);
    void on_BtnStartSaveData_clicked();
    void on_BtnFinishSaveData_clicked();
    void on_BtnUpdateFile_clicked();
    void on_BtnDelDR_clicked();
    void on_pushButton_DMS_TableControl_FirstPage_2_clicked();
    void on_pushButton_DMS_TableControl_PreviousPage_2_clicked();
    void on_pushButton_DMS_TableControl_NextPage_2_clicked();
    void on_pushButton_DMS_TableControl_LastPage_2_clicked();
    void on_TblPara_doubleClicked(const QModelIndex &index);
    void on_TblDRList_doubleClicked(const QModelIndex &index);

    void on_Btn_UpdateTestInfo_clicked();

    void on_BtnToExcel_clicked();

    void on_BtnLoadCurve_clicked();

    void on_CbParaSystem_currentTextChanged(const QString &arg1);

    void on_pushButton_last_test_photo_clicked();

    void on_BtnNextImgPos_clicked();

    void on_pushButton_2_clicked();

    void on_pushButton_clicked();

    void on_BtnLastImgTerm_clicked();

    void on_BtnLastImgPos_clicked();

    void on_BtnChooseFunc_clicked();

    void on_BtnNextImgTerm_clicked();

    void on_pushButton1_clicked();

    void on_pushButton2_clicked();

    void on_BtnRestart_clicked();

    void on_BtnTestPrio_clicked();

protected:
    virtual bool eventFilter(QObject * obj,QEvent *event) override;
};

#endif // MAINWINDOW_H
