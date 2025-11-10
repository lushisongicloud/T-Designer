#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>
#include <QMessageBox>
#include <QFormLayout>
//#include "windows.h"
#include "sqlitedatabase.h"
#include "formaxwidget.h"
#include "common.h"
#include "dialogmultilib.h"
#include "dialognewproject.h"
#include "dialogloadsymbol.h"
#include "dialogsymbols.h"
#include "dialogunitmanage.h"
#include "dialogpageattr.h"
#include "dialogUnitAttr.h"
#include "dialogterminalattr.h"
#include "dialoggenerate.h"
#include "dialognewspur.h"
#include "dialogfunctionmanage.h"
#include "dialogdiagnoseui.h"
#include "dialog_select_another_test.h"
#include "dialogflurunit.h"
#include "dialog_wait.h"
#include "dialogdiagusertest.h"
#include "dialogsettestpreference.h"
#include "dialogaddterminal.h"
#include "dialogtestreport.h"
#include <QFile>
#include <Qsci/qsciscintilla.h>
#include <Qsci/qscilexercpp.h>
#include <Qsci/qsciapis.h>
#include "qscilexercppattach.h"
#include <QProcess>
#include <QMultiMap>
#include "graphadjlist.h"
#include "widget/selectfunctiondialog.h"
#include "BO/diagnosisengine.h"
#include "projectdatacache.h"

namespace Ui {
class MainWindow;
}

extern QSqlDatabase  T_ProjectDatabase;
extern QString CurProjectPath;
extern QString CurProjectName;
extern int CurComponentCount;
extern int SelectEquipment_ID;
extern int SelectSymbol_ID;
extern int SelectTerminalStrip_ID;
extern int SelectTerminal_ID;
extern int SelectPage_ID;
extern QStringList RemovedUnitsInfo;

struct CandidateData
{
    QString FaultSpur;
    QString modeTransition;
    QString PriorVal;

    double FaultProbability;
};

struct TestUnit
{
    QString Name;
    int Equipment_ID;
    QString DT;
    QString TModel;
    QString CurrentInOutName;
};


class MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    explicit MainWindow(QWidget *parent = nullptr);
    ~MainWindow();
    void InitTEdit();
    void closeEvent(QCloseEvent *event);
    void UpdateFuncTable();
    QString GetValidTermIDString(QString OneComponentInfo,QString CurrentInOutName);
    void DrawTestPoint(QString OneComponentInfo,QString CurrentInOutName);
    void LoadProject();
    void createDemoProject();
    void LoadModel();
    void UpdateFuncTree();
    void LoadProjectSystemDescription();
    QStringList selectSystemUnitStripLineInfo();
    QStringList selectSystemConnections();
    //void MakeListFinalLinkInfo();
    void DrawArrow(QStringList ListTermID);
    void InitNavigatorTree();
    void LoadProjectPages();
    void FilterPage();
    void FilterUnit();
    void FilterLines();
    void FilterTerminal();
    void OpenDwgPageByPageID(int PageID);   
    QString resolvePageFilePath(const QString &displayName) const;
    formaxwidget* GetOpenedDwgaxwidget(QString Symbol_Handle,int Category);
    QString CreateUnusedFileName(QString CurSelectPageName,QString ProjectStructure_ID);
    void AddDwgFileToIndex(QStandardItem *item,QSqlQuery query,QList<int> listPagesExpend);
    void AddIndexToIndex(QStandardItem *FatherItem,QSqlQuery query,bool AddProjectStructure_ID,QString Type);
    void DeleteDwgSymbolByPageAndHandle(QString Page_ID,QString Symbol_Handle);
    void DeleteGroup(QString Page_ID,QString GroupName);
    void DeleteDwgTerminalByPageAndHandle(QString Page_ID,QString Handle);
    QString GetUnitTermStrByTermID(QString TermID);
    QString GetTerminalTermStrByTermID(QString TermID);
    QString FindTermConnectInDB(QString Page_ID,QString Coordinate,unsigned char Range,QString LineDir);
    void ProduceDBJXB();
    void InsertLineToItem(QStandardItem *Item,QSqlQuery QueryJXBLine);
    void InsertTermToUnitStrip(QStandardItem *Item,QSqlQuery QueryJXBLine,QString Symb_ID,QString Symb_Category,int index);
    void InsertUnitTerminalToItem(QStandardItem *Item,QSqlQuery QueryJXBLine,int index);
    void LoadLastOpenedProject();
    QString GetCurIndexProTag(int Mode);
    QStringList GetAllIDFromProjectStructure(int Mode,QString StrGaoceng,QString StrPos,bool AllGaoceng,bool AllPos);
    void ShowSpurInDwgBySymbolID(QString SymbolID);
    void ShowTerminalInDwgByTerminalID(QString TerminalID);
    QString GetEquipment_IDByDT(QString DT);
    void initDiagnoseUI();
    void LoadAllFunction();
    void LoadAllTools();
    void SetStackIndex(int index);
    void displayCurrentTest();  // 显示当前推荐的测试
    void recordCurrentTestResult(TestOutcome outcome);  // 记录测试结果并获取下一个测试
    void init_symptom_list();//初始化征兆信号UI列表
    void AddOrModifyExec(int Mode,QString StrSelectedCmd,QString StrExecState,QString StrExecStateVal);//Mode=1:add Mode=2:modify
    void LoadTestPointInfo(QString TestPointName,QString CurrentInOutName,QStringList ListTermStr);
    void GetRecommendedTestPoint();//获取推荐的测点（跳过人为选择跳过的测点）
    void FinishDiagnose();
    void AddTestPicture(QString Tabname,QString PicName,QString Path);
    QString GetTermJpgPath(QString Type,QString ConnNum);
    void DoSetTestPointHighLight();
    void ReDiagnose(QString StrDiagnose);
    void SelectTestPoint(QString TestPointName);
    bool SetEntityRed(QString Handle);
    void ClearListRedEntity();
    void SetDiagResultRed(QString StrFaultComponentInfo);
    double GetTestCost(QString testpointName);
    void LoadUserTestInfo();
    bool GetTerminalTagVisible(int TerminalInstanceID,bool Update,bool Visible);
    void RemakeLinkRoad(QStringList ListExecSpurID);
    void UpdateConnectLine_CO_Connection(QString Connector_ID1,QString Connector_ID2);

    QStandardItemModel *ModelPages,*ModelUnits,*ModelTerminals,*ModelLineDT,*ModelLineByUnits;
    DialogLoadSymbol *dlgLoadSymbol;
    DialogSymbols *dlgDialogSymbols;
    DialogUnitManage *dlgUnitManage;
    DialogGenerate dlgGenerate;
    DialogFuncDefine *dlgFuncDefine;
    DialogUnitAttr *dlgUnitAttr;
    dialogFunctionManage *dlgFunctionManage;
    //dialogDiagnoseUI *dlgDiagnoseUI;
    int CopyEquipment_ID=0,CopySymbol_ID=0,CopyTerminalStrip_ID=0;
    bool ShowPreViewWidget=false;//是否显示预览窗口
    QsciScintilla *QsciEdit;
    bool cmdStarted = false;
    QStringList ListRedEntity;
    int DiagnoseStepNumber=0;
    QString CurFunctionID,CurTestPointName;
    QStringList ListSkipTestPoint;
    bool FlagSetTestPointHighLight=false;
    double dCenterX,dCenterY;
    //QTimer TimerDelay,TimerWaitForCmdResult;
    QDialog *dlg_showPicture;//展示图片窗口
    QLabel *picture_Label;
    Dialog_wait *dlg_delay;//模态对话框
    QString DiagnoseInitStr;
    QString CurDiagnoseDwgFilePath;
    QStringList ListFinalLinkInfo;
    QString StrSystemDefine;
    bool FlurWndIsActive=false;
    int TestPointPreference=3;//1:只看信息熵 2：只看测试代价 3：信息熵优先 4：测试代价优先
    QStringList ListUserTest,ListAllObserve;
    TestUnit CurTestUnit;

    //model相关变量
    SQliteDatabase *database = nullptr;
    SystemEntity *systemEntity = nullptr;
    QString currentModelName;
    QString functionDescription;
    model currentModel;

    //static QMap<QString, QStringList> obsTemplates;
    SelectFunctionDialog *pDlgSelectFunctionDialog = nullptr;
    
    // 故障诊断引擎
    DiagnosisEngine *diagnosisEngine = nullptr;

private:
    void initializeMxModules();
    TestReportMetrics buildTestReportMetrics() const;
    bool tryGetPrecomputedMetrics(const QString &projectName, TestReportMetrics &metrics) const;

private slots:
    void initAfterShow();
    void UpdateDwgBlkTagByPage_ID(int Page_ID,QString Handle,QString TagStr,QString ProjectStructure_ID);

    void on_BtnNavigatorShow_clicked();

    void on_BtnCloseNavigator_clicked();

    void on_BtnNewProject_clicked();

    void on_BtnOpenProject_clicked();

    void on_treeViewPages_doubleClicked(const QModelIndex &index);

    void CloseMdiWnd(int Mode);

    void on_treeViewPages_clicked(const QModelIndex &index);

    void on_Btn_SymbolLoad_clicked();

    void on_BtnSymbolBaseManage_clicked();

    void on_BtnLocalDB_clicked();

    void on_Btn_ContainerTree_clicked();
    void on_BtnFunctionManage_clicked();
    void actionAddComponentContainers();
    void actionRemoveComponentContainers();
    void actionAttachComponentsToHigher();

    void NewDwgPage();

    void AddExistPage();

    void ShowtreeViewPagePopMenu(const QPoint &pos);

    void ShowtreeViewUnitsPopMenu(const QPoint &pos);
    void createFunctionForSymbol();

    void ShowtreeViewTerminalPopMenu(const QPoint &pos);

    void ShowtreeViewLineDTPopMenu(const QPoint &pos);

    void ShowtreeViewLineByUnitPopMenu(const QPoint &pos);

    void UpdateSpurBySymbol_ID(int Symbol_ID);

    void UpdateTerminalByTerminal_ID(int Terminal_ID);

    void UpdateTerminalInstanceByTerminalInstance_ID(int TerminalInstance_ID);

    void DwgPageAttr();

    void Rename();

    void actSlotDelete();

    void LoadProjectUnits();

    void LoadUnitTable();

    void LoadProjectTerminals();

    void LoadProjectLines();
    void handleConnectLinesChanged(int pageId);

    void LoadModelLineDT();

    void LoadModelLineByUnits();

    void NewUnit();

    void LoadWholeUnit(int Mode);

    void LoadUnitStamp();

    void LoadWholeUnitAllTermsUp();

    void LoadWholeUnitAllTermsDown();

    void LoadWholeUnitOddTermsUp();

    void LoadWholeUnitEvenTermsUp();

    void LoadWholeUnitFirstHalfUp();

    void LoadWholeUnitLastHalfUp();

    void NewTerminalStrip();

    void NewTerminal();

    void DeleteUnit();

    void DeleteSpur();

    void SlotNewSpur();

    void NewSpurTemplate();

    void CopyUnit();

    void CopyTerminalStrip();

    void PasteUnit();

    //void GetLinkRoad();//获取信号链路

    //QString GetLinkRoadBySymbol(int Symbol_ID);//获取信号链路(针对功能子块)

    //QList<QStringList> GetLinkRoadByUnitStripID(int Symb2TermInfo_ID);

    //int GetUnitStripOtherSideTerm(int &Symb2TermInfo_ID,int &Category);

    //bool CheckLinkRoad(QString LineStr,QStringList KnownLineValidRoadCnt);//QList<QStringList>ErrorlistLinkRoad,QList<QList<int>> &ErrorListNodeSpurCount);

    void PasteTerminalStrip();

    void PasteSpur();

    void CopySpur();

    int PasteSpurBySymbol_ID(int Equipment_ID,int Symbol_ID);

    int PasteTerminalByTerminal_ID(int TerminalStrip_ID,int Terminal_ID);

    void DeleteTerminal();

    void DeleteTerminalStrip();

    void ShowSpurInDwg();

    void ShowTerminalInDwg();

    void ShowUnitAttr();

    void ShowUnitAttrByEquipment_ID(int Equipment_ID);

    void ShowTerminalStripAttr(int Terminal_ID);

    void SlotTerminalStripAttr();

    void SlotTerminalAttr();

    void SlotLoadTerminal();

    void DrawTerminalEqualDistance();

    void DrawSpurEqualDistance();

    void ShowSpurAttr(int Symbol_ID);

    void ShowTerminalAttr(int Mode,int ID);

    void updateCounterLink(int Link_ID,QString LinkText);

    void SlotSpurAttr();

    void SlotLoadSpur();

    void SlotNewSymbol(int Mode);

    void on_BtnShowHidePreViewWidget_clicked();

    void on_Btn_GeneratePageList_clicked();

    void on_Btn_GenerateUnitList_clicked();

    void on_Btn_GenerateConnectList_clicked();

    void on_Btn_GenerateTerminalList_clicked();

    void on_BtnLineConnect_clicked();

    void on_Btn_MultiLine_clicked();

    void on_Btn_RemakeConnectLine_clicked();

    void on_Btn_LineDefine_clicked();

    void on_Btn_CableDefine_clicked();

    void on_BtnNodeRightDown_clicked();

    void on_BtnNodeLeftDown_clicked();

    void on_BtnNodeRightUp_clicked();

    void on_BtnNodeLeftUp_clicked();

    void on_BtnTNodeDown_clicked();

    void on_BtnTNodeUp_clicked();

    void on_BtnTNodeRight_clicked();

    void on_BtnTNodeLeft_clicked();

    void on_BtnTNodeTX_clicked();

    void on_BtnTNodeCross_clicked();

    void on_BtnLinkRight_clicked();

    void on_BtnLinkUp_clicked();

    void on_BtnLinkLeft_clicked();

    void on_BtnLinkDown_clicked();

    void on_Btn_BlackBox_clicked();

    void on_Btn_StructBox_clicked();

    void UpdateSymbolLib(QString CurSelectSymb2Class_ID);

    void SlotSetCurMdiActive();

    void on_BtnFuncManage_clicked();

    void on_treeViewUnits_clicked(const QModelIndex &index);

    void on_treeViewTerminal_clicked(const QModelIndex &index);

    void on_tabWidget_Navigator_currentChanged(int index);

    void on_Btn_GeneratePartList_clicked();

    void on_Btn_GenerateCableList_clicked();

    void ShowLineTargetInDwg();

    void ShowLineByUnitTargetInDwg();

    void ShowLineSourceInDwg();

    void ShowLineByUnitSourceInDwg();

    void on_CbUnitTogether_clicked();

    void on_TabUnit_currentChanged(int index);

    void on_tableWidgetUnit_doubleClicked(const QModelIndex &index);

    void on_BtnPageFilter_clicked();

    void on_CbPageGaocengFilter_currentIndexChanged(const QString &arg1);

    void on_CbPagePosFilter_currentIndexChanged(const QString &arg1);

    void on_CbPageTypeFilter_currentIndexChanged(const QString &arg1);

    void on_EdPageFilter_editingFinished();

    void on_BtnUnitFilter_clicked();

    void on_CbUnitGaoceng_currentIndexChanged(const QString &arg1);

    void on_CbUnitPos_currentIndexChanged(const QString &arg1);

    void on_CbUnitPage_currentIndexChanged(const QString &arg1);

    void on_EdUnitTagSearch_editingFinished();

    void on_BtnTermFilter_clicked();

    void on_CbTermGaoceng_currentIndexChanged(const QString &arg1);

    void on_CbTermPos_currentIndexChanged(const QString &arg1);

    void on_CbTermPage_currentIndexChanged(const QString &arg1);

    void on_EdTermTagFilter_editingFinished();

    void on_tabWidgetLine_currentChanged(int index);

    void on_BtnLineFilter_clicked();

    void on_CbLineGaoceng_currentIndexChanged(const QString &arg1);

    void on_CbLinePos_currentIndexChanged(const QString &arg1);

    void on_CbLinePage_currentIndexChanged(const QString &arg1);

    void on_EdLineTagFilter_editingFinished();

    void on_BtnOpenPage_clicked();

    void on_BtnRefreshExecConn_clicked();

    void on_BtnShowLinkRoad_clicked();

    void on_BtnRemakeLinkRoad_clicked();

    void on_CbAllExecConn_clicked();

    void on_readoutput();

    void on_readerror();

    void on_BtnStartDiagnose_clicked();

    void on_BtnSendCmd_clicked();

    void on_BtnEndDiagnose_clicked();

    void on_tableWidgetDiagResult_clicked(const QModelIndex &index);

    void on_BtnSaveDwg_clicked();

    void UpdateUnitAttrLib();

    void on_tableWidgetTestPoint_clicked(const QModelIndex &index);

    void on_BtnModifyFunction_clicked();

    void on_BtnDiagnose_clicked();

    void UpdateXmplInfo(QString FunctionID);

    void StartDiagnose(QString SendCmdStr);
    
    // 诊断对话框信号处理槽
    void onDiagnoseUpdateExec(QString FunctionID);
    void onDiagnoseSendCmd(QString SendCmdStr);

    void SendCmd(QString SendCmdStr,bool print);

    QStringList GetTestPointTermID(QString OneComponentInfo,QString CurrentInOutName);

    void on_toolButton_start_diagnosis_clicked();

    void on_btm_CalTestResult_clicked();

    void on_toolButton_known_symptom_select_next_clicked();

    void on_toolButton_known_symptom_delete_clicked();

    void on_toolButton_not_exit_symptom_modify_clicked();

    void on_toolButton_known_symptom_add_clicked();

    void on_BtnEndDiagnose_2_clicked();

    void on_BtnEndDiagnose_3_clicked();

    void on_toolButton_resule_OK_next_clicked();

    void on_toolButton_all_result_next_clicked();

    void DrawArrow(QString Conn_Coordinate,QString Tag,QString ConnDirection);

    void ClearDrawArrow();

    void on_BtnShowMdi_clicked();

    void on_toolButton_skip_this_test_clicked();

    void on_toolButton_slelct_other_test_clicked();

    void on_axWidgetDiagnose_CommandEnded(const QString &sCmdName);

    void on_axWidgetDiagnose_ImplementCommandEvent(int iCommandId);

    void timerSetTestPointHighLight();

    void timerDealCmdResult();

    void OpenPic(int ID);

    void on_BtnLastStep_clicked();

    void on_toolButton_known_symptom_select_last_clicked();

    void on_BtnLastStep_2_clicked();

    void on_BtnFlurUnits_clicked();

    void on_BtnSetTestPreference_clicked();

    void UpdateFuncStrSystemDefine(QStringList ListExec);

    void on_BtnUserTest_clicked();

private:
    Ui::MainWindow *ui;   
    QProcess *cmdDiagnose;
protected:

public:
    QList<TestPoint>  GetTestPoint();
    double CalculateInformation(QString& module_name);      //用来计算针对module_name测试的信息熵
    void CalculateCustomInformation(QString& base, QStringList& list);
    //QList<TestPoint> SortTestPoint(int type);

private:
    void PrintCandidateList();  //打印CandidateList
    bool isHaveCandidate(const CandidateData& data);

    void GetGraphList(QFile& file);

    double CalculateRank(const QString& port_name, const QStringList& front, const QStringList& back);

    void GetInputTestPoint(QString& cmd);

    void UpdateModuleFaultProb();       // 重新计算模块的概率

    void RemoveRepeatTestPoint(QList<TestPoint>& test_pt);       //去除重复的节点，主要是两个节点接在一起的情况，这时候优先去掉线上的测点

    void RemoveTestedPoint(QList<TestPoint>& test_pt);            //去除已经测量过的点以及和他直接相连的点

    QStringList GetInterLogicConnect();

    //自定义测试专用
    void StartCustomProcess();

private slots:
    void on_custom_read();

    void on_Btn_SetTerminal_clicked();

    void on_BtnDataAnalyse_clicked();

    void on_BtnMultiLibManage_clicked();

    void on_BtnSetCentrePoint_clicked();

    void on_mdiArea_subWindowActivated(QMdiSubWindow *arg1);

    void on_BtnPutText_clicked();

    void on_BtnClearDB_clicked();    

    void on_CbTestType_currentIndexChanged(const QString &arg1);
    
    // 新诊断系统槽函数
    void on_btnTestPass_clicked();    // 测试通过按钮
    void on_btnTestFail_clicked();    // 测试失败按钮
    void on_btnSkipTest_clicked();    // 跳过测试按钮

private:
    QList<CandidateData> candidate_list;
    GraphAdjList* graph_list;
    QList<TestPoint>   test_point;

    QMap<QString, int>  input_test_point;  //测试输入的测点，记录下来避免测点推荐时重复推荐已经测过的点

    QMap<QString, double> module_fault_prob;
    
    // 性能优化：项目数据缓存（避免重复查询数据库）
    ProjectDataCache* m_projectCache;
    bool m_useCacheOptimization;  // 缓存优化开关（默认true，可通过环境变量关闭）

    //下面的部分用来处理自定义测点
    QProcess* custom_process;
    QMap<QString, double> custom_module_fault_prob;   //模块的故障了，QString是模块的名称不是端口的名称。这里的故障概率没有 归一化处理

    double information;        //用来记录针对一个自定义测试所有结果的信息熵
    QString base;
    QStringList list;
    int depth;

};



#endif // MAINWINDOW_H
