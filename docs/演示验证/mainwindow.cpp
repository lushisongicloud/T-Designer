#include "mainwindow.h"
#include "ui_mainwindow.h"

#include <QSize>
#include <QMessageBox>

#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

DataBase::Str_account  m_loginAccount;//当前登陆账户信息
RuleVariablePool m_RuleVariablePool;//当前规则库变量池
RulePool m_RulePool;//规则库变量池
QMutex mutex;//线程互斥锁
QString m_strFilePath = "C:/MDB/ControllablePitchPropeller.db3";//数据库文件地址

//================================20231209 xcc=======================
QStandardItemModel *ModelTestSet;
QMap<QString,STRU_OneTestStepSet> TestStepCandidates;//所有可选的诊断测试配置表
QStandardItem *CurTestNode;//当前测试节点
QString CurImgPosPath;//当前位置图片
QString CurImgTermPath;//当前观测点位图片
//================================20231209 xcc=======================

extern bool EndTestSignal;
extern bool DRRecording_Now;
char TestInfo[1000];
ST_DR_FILEBUF CurFileBuf;
STRU_DataDR CurRecord;
bool IsInTest=false;
double TimeIdx=0;
float CalculateStr(QString CalStr);//进行计算结果
QString ConvertTimeStrNew(QString StrName);
extern char DRFileName[500];
extern char NewDRFileName[500];
extern int TimeOfRecording;
MainWindow::MainWindow(QWidget *parent) :
    QMainWindow(parent),
    ui(new Ui::MainWindow)
{
    ui->setupUi(this);
    this->setWindowIcon(QIcon(":/widget/Logo.ico"));

    qDebug()<<"MainWindow  "<<QThread::currentThreadId();

    //初始化主界面名称
    this->setWindowTitle("Diagnosis");

    //初始化主界面大小
    //QSize MainWindowSize(1920,1040);
    //this->setMaximumSize(MainWindowSize);


    //隐藏窗口边框
    this->setWindowFlags(Qt::Dialog| Qt::FramelessWindowHint);
    QSize MainWindowSize(1920,1080);
    this->setMinimumSize(MainWindowSize);
    //this->setMaximumSize(MainWindowSize);

    this->setWindowFlags(windowFlags() | Qt::WindowMaximizeButtonHint);

    //设置主界面时钟
    ui->dateTimeMain->setDateTime(QDateTime::currentDateTime());
    timerUpdateUI = new QTimer(this);
    connect(timerUpdateUI,SIGNAL(timeout()),this,SLOT(DoUpdateUI()));
    timerUpdateUI->start(1000);

    //连接到数据库
    TMATE_Database = new myQSqlDatabase(m_strFilePath);
    qDebug()<<"连接到数据库";
    if(!TMATE_Database->isopen()){
        delete TMATE_Database;
        TMATE_Database = nullptr;
        return;
    }

    //规则变量池添加数据库指针
    m_RuleVariablePool.SetDatabase(TMATE_Database);

    //规则库添加数据库指针
    m_RulePool.SetDatabase(TMATE_Database);
    ui->stackedDiagnosis->setCurrentIndex(0);

    //创建用户管理界面
    WidgetUserManage = new UserManage(nullptr,TMATE_Database);
    ui->verticalLayout_UserManager->addWidget(WidgetUserManage);

    //创建IP连接管理界面
    WidgetConnectManage = new ConnectSet(nullptr,TMATE_Database);
    ui->verticalLayout_ConnectManager->addWidget(WidgetConnectManage);
    //创建变量管理界面
    WidgetVariableManage = new VariableManage(nullptr,TMATE_Database);
    ui->verticalLayout_VariableBase->addWidget(WidgetVariableManage);

    connect(WidgetVariableManage,SIGNAL(VariableNameChange(QString,QString)),this,SLOT(on_VariableNameChange(QString,QString)));
    connect(WidgetVariableManage,SIGNAL(VariableDelete(QString)),this,SLOT(on_VariableDelete(QString)));
    //创建规则管理界面
    WidgetRuleManage = new RuleManage(nullptr,TMATE_Database);
    ui->verticalLayout_RuleBase->addWidget(WidgetRuleManage);

    //创建规则管理界面
    WidgetWarnManage = new WarnManage(nullptr,TMATE_Database);
    ui->verticalLayout_WarnBase->addWidget(WidgetWarnManage);

    //创建液压显示界面
    WidgetHydraulicState = new FormHydraulicState(nullptr,TMATE_Database);
    ui->horizontalLayout_HydraulicState->addWidget(WidgetHydraulicState);
    WidgetHydraulicState->Set3DWidgetPNG(0);
    //实时报警PlainTextEdit显示
    m_TextEdit =new QTextEdit;
    m_TextEdit->setStyleSheet("background-color: rgba(255, 255, 255,0.2); border-width:0; border-style:outset; color: rgba(102, 249, 247, 1);  font: 12pt '微软雅黑';");

    //    connect(m_TextEdit,SIGNAL(cursorPositionChanged()),
    //            this,SLOT(slotRealAlarmMoveToDiagnosis()));
    ui->horizontalLayout_HydraulicState->addWidget(m_TextEdit);

    //创建实时数据显示界面
    WidgetRealTimeData = new FormRealTimeData(nullptr);
    ui->Layout_RealData->addWidget(WidgetRealTimeData);

    //计算故障、报警统计信息
    //TMATE_Database-

    //创建故障信息显示界面
    WidgetFaultInformation = new FormAlarmInformation(nullptr,TMATE_Database);
    ui->horizontalLayout_Alarm->addWidget(WidgetFaultInformation);
    //创建预报警信息显示界面
    WidgetWarnningInformation = new FormWarnInformation(nullptr,TMATE_Database);
    ui->horizontalLayout_Warn->addWidget(WidgetWarnningInformation);

    //信号传输线程
    m_Detector1_DataTrans = new Detector1_DataTrans(TMATE_Database,1);//中心控制箱测点
    //    m_Detector2_DataTrans = new Detector1_DataTrans(TMATE_Database,2);//机旁控制箱测点
    //    m_Detector3_DataTrans = new Detector1_DataTrans(TMATE_Database,3);//备用泵电机启动箱、提升泵电机启动箱
    //    MK2CPU_DataTrans = new MK2CPU_DataTransThread();
    //MK5CPU_DataTrans = new MK5CPU_DataTransThread();

    //故障诊断线程

    DiagnosisThread = new Diagnosis();

    //connect(DiagnosisThread,SIGNAL(newFaliureError()),this,SLOT(on_newFaliureError()));
    //connect(DiagnosisThread,SIGNAL(newWarnningError()),this,SLOT(on_newWarnningError()));
    connect(DiagnosisThread,SIGNAL(newBasicSignalUpdate()),this,SLOT(on_newBasicSignalUpdate()));
    qRegisterMetaType<QVector<DataBase::Signal>>("QVector<DataBase::Signal>");
    connect(DiagnosisThread,SIGNAL(newFaliureError(QVector<DataBase::Signal>)),this,SLOT(on_UpdateFaliureOrWarnning(QVector<DataBase::Signal>)));
    connect(WidgetHydraulicState,SIGNAL(newFaliureError()),this,SLOT(UpdateRealTimeFaliureOrWarnning()));
    //转到首页
    ui->tabWidgetMain->setCurrentIndex(0);
    policyTroubleshootEnd();
    this->setWindowTitle("装备智能故障诊断软件");
    //ui->comboBox_DMS_TableControl_PageRecordsNumber->setCurrentText("12");
    ui->dateEditEnd->setDate(QDate::currentDate());
    ui->widgetSearch->setEnabled(false);
    InitChart();//初始化图标
    LoadDataList();
    tableParaInit();
    TimeRangeVal=1;
    HzVal=1;
    for(int i=0;i<MAX_LINE_CNT;i++)
    {
        stDraw[i].SFCoef=1;
        stDraw[i].PYVal=0;
    }

    //初始化筛选设置
    stSearch.FilterIsSet=true;
    stSearch.TimeSearchIsEnabled=false;
    stSearch.FinishTime=QDateTime::currentDateTime();
    stSearch.ParaConditionIsEnabled[0]=false;
    stSearch.ParaConditionIsEnabled[1]=false;
    stSearch.ParaConditionIsEnabled[2]=false;
    stSearch.ParaConditionIsEnabled[3]=false;
    stSearch.ParaConditionSearchIsEnabled=false;
    stSearch.ParaConditionVal[0]=0;
    stSearch.ParaConditionVal[1]=0;
    stSearch.ParaConditionVal[2]=0;
    stSearch.ParaConditionVal[3]=0;
    qDebug()<<"init 9";
    //查看文件目录是否存在 不存在则创建目录
    QDir *temp = new QDir;
    bool exist = temp->exists(DATA_SAVE_DISK);
    if(!exist) qDebug()<<temp->mkpath(DATA_SAVE_DISK);
    exist = temp->exists(EXCEL_SAVE_DISK);
    if(!exist) qDebug()<<temp->mkpath(EXCEL_SAVE_DISK);

    ui->customPlot->installEventFilter(this);//widget控件安装事件过滤器
    ui->BtnSearchSet->setVisible(false);
    ui->RbAllData->setVisible(false);
    ui->RbSearchData->setVisible(false);

    InitTabWidget_test_image();

    //===========================20231209 xcc===============================
    InitTableChoose_Alarm();
    InitTableFuzzl_Alarm();
    InitTableHisStep();
    InitTestStepSet();
    CreateDiagnoisTree();
    connect(m_TextEdit,SIGNAL(cursorPositionChanged()),
            this,SLOT(slotRealAlarmMoveToDiagnosis()));
    mdlgMessage=new dlgMessage(this);
    mdlgMessage->move(this->width()/2 - mdlgMessage->width()/2,
                      this->height()/2 - mdlgMessage->height()/2);
    mdlgMessage->hide();
    mdlgTestPrio=new DlgTestPrio(this);
    mdlgTestPrio->move(this->width()/2 - mdlgTestPrio->width()/2,
                       this->height()/2 - mdlgTestPrio->height()/2);
    mdlgTestPrio->hide();
    QPixmap pix("");
    ui->graphicsView_Pos->setScene(&m_scene_pos);
    m_scene_pos.SetBackGroundImage(pix, ui->graphicsView_Pos->width(), ui->graphicsView_Pos->height());
    ui->graphicsView_Term->setScene(&m_scene_term);
    m_scene_term.SetBackGroundImage(pix, ui->graphicsView_Term->width(), ui->graphicsView_Term->height());
    ui->LbImgPos->setVisible(false);
    ui->LbImgTerm->setVisible(false);
    //===========================20231209 xcc===============================
    //    ui->list_ImgPos->setViewMode(QListWidget::IconMode);//显示模式
    //    ui->list_ImgPos->setIconSize(QSize(900, 700));//设置图片大小
    //    ui->list_ImgPos->setSpacing(10);//间距
    //    ui->list_ImgPos->setResizeMode(QListView::Adjust);//适应布局调整
    //    ui->list_ImgPos->setMovement(QListView::Static);//不能移动
    //    QListWidgetItem *imageItem1 = new QListWidgetItem;
    //    imageItem1->setIcon(QIcon("C:/MDB/DiagnoseImages/01-00-安全插销拔出状态.png"));
    //    //imageItem1->setText("china");
    //    imageItem1->setSizeHint(QSize(920, 700));
    //    ui->list_ImgPos->addItem(imageItem1);

    //    QListWidgetItem *imageItem2 = new QListWidgetItem;
    //    imageItem2->setIcon(QIcon("C:/MDB/DiagnoseImages/01-01-安全插销未拔出状态.png.png"));
    //    //imageItem1->setText("china");
    //    imageItem2->setSizeHint(QSize(920, 700));
    //    ui->list_ImgPos->addItem(imageItem2);

    //setWindowFlag(Qt::FramelessWindowHint);
}
MainWindow::~MainWindow()
{
    delete ui;
    if(timerUpdateUI) delete timerUpdateUI;
    if(WidgetUserManage) delete WidgetUserManage;
    if(WidgetConnectManage) delete WidgetConnectManage;
    if(WidgetVariableManage) delete WidgetVariableManage;
    if(WidgetRuleManage) delete WidgetRuleManage;
    if(WidgetHydraulicState) delete WidgetHydraulicState;
    if(WidgetRealTimeData) delete WidgetRealTimeData;
    if(WidgetFaultInformation) delete WidgetFaultInformation;
    if(WidgetWarnningInformation) delete WidgetWarnningInformation;
    if(m_Detector1_DataTrans) delete m_Detector1_DataTrans;
    if(m_Detector2_DataTrans) delete m_Detector2_DataTrans;
    if(m_Detector3_DataTrans) delete m_Detector3_DataTrans;
    if(MK2CPU_DataTrans) delete MK2CPU_DataTrans;
    if(MK5CPU_DataTrans) delete MK5CPU_DataTrans;
    if(DiagnosisThread) delete DiagnosisThread;
}

bool MainWindow::eventFilter(QObject *obj, QEvent *event)
{
    if (obj == ui->customPlot) // 你要过滤的对象
    {
        if (event->type() == QEvent::MouseButtonDblClick)
        { // 你要过滤的对象的事件类型
            // 你自己期望实现的功能，在这里我的实现是新建一个标签页以及新的文本编辑栏
            DrawSet();
            return true; // 注意这里一定要返回true，表示你要过滤该事件原本的实现
        }
    }
    return false; // 返回false表示不过滤，还按默认的来
}

//初始化供手动选择的待诊断的功能列表
void MainWindow::InitTableChoose_Alarm()
{
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString<< tr("序号")  << tr("功能名称") << tr("功能说明");

    StretchHorizontalIndex<<2;
    TableWidgetQss(headerString,ui->tableFuncChoose,StretchHorizontalIndex);
    ui->tableFuncChoose->setColumnWidth(0,50);
    ui->tableFuncChoose->setColumnWidth(1,250);
    ui->tableFuncChoose->setColumnWidth(2,300);

    QStringList StringFunc,StringInfo;
    StringFunc<<"手动排缆左移"<<"手动排缆右移"<<"卷筒低速释放"<<"卷筒高速释放"<<"卷筒低速回收"<<"卷筒高速回收"<<"卷筒刹车（电磁刹车）"
             <<"自动排缆左移"<<"自动排缆右移"<<"自动排缆向右换向"<<"自动排缆向左换向"<<"1#电机应急回收"<<"2#电机应急回收";
    StringInfo<<"便携式操作盒“手动/自动”切换开关置于“手动”位置，按下收放控制机柜上的“手动排缆左移”按钮，在未触发排缆左位行程开关的前提下，排缆机构向左移动。"
             <<"便携式操作盒“手动/自动”切换开关置于“手动”位置，按下收放控制机柜上的“手动排缆右移”按钮，在未触发排缆右位行程开关的前提下，排缆机构向右移动。"
            <<"便携式操作盒“回收/停机/释放”切换开关置于“释放”位置，“低速/高速”切换开关置于“低速”位置，在手动带式刹车松开、手动安全插销拔出的前提下，卷筒慢速朝释放方向转动。"
           <<"便携式操作盒“回收/停机/释放”切换开关置于“释放”位置，“低速/高速”切换开关置于“高速”位置，在手动带式刹车松开、手动安全插销拔出的前提下，卷筒快速朝释放方向转动。"
          <<"便携式操作盒“回收/停机/释放”切换开关置于“回收”位置，“低速/高速”切换开关置于“低速”位置，在手动带式刹车松开、手动安全插销拔出的前提下，卷筒慢速朝回收方向转动。"
         <<"便携式操作盒“回收/停机/释放”切换开关置于“回收”位置，“低速/高速”切换开关置于“高速”位置，在手动带式刹车松开、手动安全插销拔出的前提下，卷筒快速朝回收方向转动。"
        <<"便携式操作盒“回收/停机/释放”切换开关置于“停机”位置，卷筒停止转动，电机电磁刹车抱闸刹车。"
       <<"便携式操作盒“手动/自动”切换开关置于“自动”位置，“回收/停机/释放”切换开关置于“释放”或“回收”位置，排缆机构随着卷筒转动自动左移。"
      <<"便携式操作盒“手动/自动”切换开关置于“自动”位置，“回收/停机/释放”切换开关置于“释放”或“回收”位置，排缆机构随着卷筒转动自动右移。"
     <<"便携式操作盒“手动/自动”切换开关置于“自动”位置，“回收/停机/释放”切换开关置于“释放”或“回收”位置，排缆机构随着卷筒转动自动左移的过程中，在排缆左位行程开关触发后排缆机构切换移动方向，向右移动。"
    <<"便携式操作盒“手动/自动”切换开关置于“自动”位置，“回收/停机/释放”切换开关置于“释放”或“回收”位置，排缆机构随着卷筒转动自动右移的过程中，在排缆右位行程开关触发后排缆机构切换移动方向，向左移动。"
    <<"便携式操作盒“手动/自动”切换开关置于“手动”位置，按下收放控制机柜上的“1#应急回收”按钮，便携式操作盒“回收/停机/释放”切换开关置于“回收”位置，卷筒慢速朝回收方向转动。"
    <<"便携式操作盒“手动/自动”切换开关置于“手动”位置，按下收放控制机柜上的“2#应急回收”按钮，便携式操作盒“回收/停机/释放”切换开关置于“回收”位置，卷筒慢速朝回收方向转动。";
    ui->tableFuncChoose->setRowCount(StringFunc.count());
    for(int i=0;i<StringFunc.count();i++)
    {
        QTableWidgetItem *itemSerial = new QTableWidgetItem(QString::number(i + 1));
        // 设置对齐方式为居中
        itemSerial->setTextAlignment(Qt::AlignCenter);
        // 在表格中设置该项
        ui->tableFuncChoose->setItem(i, 0, itemSerial);
        ui->tableFuncChoose->item(i,0)->setCheckState(Qt::Unchecked);
        //ui->tableListFalut->setItem(i,0,new QTableWidgetItem(QString::number(i+1)));
        ui->tableFuncChoose->setItem(i,1,new QTableWidgetItem(StringFunc.at(i)));
        ui->tableFuncChoose->setItem(i,2,new QTableWidgetItem(StringInfo.at(i)));
        ui->tableFuncChoose->setRowHeight(i,100);
        //ui->tableFuncChoose->resizeRowToContents(i);
        //ui->tableListFalut->resizeRowsToContents();
    }

}

//初始化可能故障表格
void MainWindow::InitTableFuzzl_Alarm()
{
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString<< tr("序号")  << tr("可能故障") << tr("概率");

    StretchHorizontalIndex<<1;
    TableWidgetQss(headerString,ui->tableListFalut,StretchHorizontalIndex);
    ui->tableListFalut->setColumnWidth(0,50);
    ui->tableListFalut->setColumnWidth(1,200);
    ui->tableListFalut->setColumnWidth(2,80);
    QStringList StringFault,StringProb;
    StringFault<<"插销接近开关故障"<<"传感器线缆L054接触不良"<<"柜内导线L033接触不良"<<"柜内导线L012接触不良"<<"DI208-1模块故障";
    StringProb<<"21%"<<"25%"<<"25%"<<"25%"<<"4%";
    ui->tableListFalut->setRowCount(StringFault.count());
    for(int i=0;i<StringFault.count();i++)
    {
        QTableWidgetItem *itemSerial = new QTableWidgetItem(QString::number(i + 1));
        // 设置对齐方式为居中
        itemSerial->setTextAlignment(Qt::AlignCenter);
        // 在表格中设置该项
        ui->tableListFalut->setItem(i, 0, itemSerial);
        //ui->tableListFalut->setItem(i,0,new QTableWidgetItem(QString::number(i+1)));
        ui->tableListFalut->setItem(i,1,new QTableWidgetItem(StringFault.at(i)));
        ui->tableListFalut->setItem(i,2,new QTableWidgetItem(StringProb.at(i)));
        //ui->tableListFalut->resizeRowsToContents();

    }
}

//初始化所有可选测试
void MainWindow::InitTestStepSet()
{
    ModelTestSet = new QStandardItemModel();
    //测试1
    STRU_OneTestStepSet mOneTestStepSet={"观察PLC_I1_2_LED指示灯",
                                         "手动排缆左移功能异常——未检测到按钮输入",
                                         "收放控制机柜->PLC->PLC_I1_2_LED",
                                         {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I1_2.png"},
                                         {"点位-PLC_I1_2_LED.png"},
                                         "无（直接人眼观察）",
                                         "",
                                         "观察PLC_I1_2_LED指示灯是否点亮？",
                                         "亮",
                                         "不亮",
                                         "1. 便携式操作盒“手动/自动”切换开关置于“手动”位置\n2. 按下收放控制机柜上的“手动排缆左移”按钮（保持按下）\n3. 观察PLC_I1_2_LED指示灯是否点亮",
                                         {
                                             {"L_UK3-1，导线松动或断开","UK3-1，端子连接失效","UK3-13，端子连接失效","L_UK3-13，导线松动或断开","X6-10，航插引脚虚焊或接触不良","L_SB6+，导线松动或断开","SB6，按钮接触不良","L_SB6-，导线松动或断开","X6-14，航插引脚虚焊或接触不良","L_PLC_I1_2，导线断开","PLC_I1_2，输入通道失效"},
                                             {"14.12%","0.56%","0.56%","14.12%","8.47%","14.12%","5.65%","14.12%","8.47%","14.12%","5.65%"}
                                         }
                                        };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试2
    mOneTestStepSet={"测量PLC_I1_2端子电压",
                     "手动排缆左移功能异常——未检测到按钮输入",
                     "收放控制机柜->PLC->PLC_I1_2",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I1_2.png"},
                     {"点位-PLC_I1_2.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量PLC模块的PLC_I1_2端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 按下收放控制机柜上的“手动排缆左移”按钮（保持按下）\n3. 万用表红表笔接PLC_I1_2\n4. 万用表黑表笔接PLC_I0_M",
                     {
                         {"L_UK3-1，导线松动或断开","UK3-1，端子连接失效","UK3-13，端子连接失效","L_UK3-13，导线松动或断开","X6-10，航插引脚虚焊或接触不良","L_SB6+，导线松动或断开","SB6，按钮接触不良","L_SB6-，导线松动或断开","X6-14，航插引脚虚焊或接触不良","L_PLC_I1_2，导线断开","PLC_I1_2，输入通道失效"},
                         {"9.36%","0.37%","0.37%","9.36%","5.62%","9.36%","3.75%","9.36%","5.62%","9.36%","37.45%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试3
    mOneTestStepSet={"测量X6-10与X6-14的导通",
                     "手动排缆左移功能异常——未检测到按钮输入",
                     "收放控制机柜->X6->X6插座",
                     {"位置-收放控制机柜.png","位置-X6.png","位置-X6-旋下航插.png"},
                     {"点位-X6-10&X6-14.png"},
                     "万用表（导通档）",
                     "万用表-导通档.png",
                     "测量X6航插插座的X6-10与X6-14引脚是否导通？",
                     "导通",
                     "不导通",
                     "1. 万用表切换到导通档\n2. 按下收放控制机柜上的“手动排缆左移”按钮（保持按下）\n3. 万用表红表笔接X6-10\n4. 万用表黑表笔接X6-14",
                     {
                         {"L_UK3-1，导线松动或断开","UK3-1，端子连接失效","UK3-13，端子连接失效","L_UK3-13，导线松动或断开","X6-10，航插引脚虚焊或接触不良","L_SB6+，导线松动或断开","SB6，按钮接触不良","L_SB6-，导线松动或断开","X6-14，航插引脚虚焊或接触不良","L_PLC_I1_2，导线断开","PLC_I1_2，输入通道失效"},
                         {"14.97%","0.6%","0.6%","14.97%","8.98%","14.97%","5.99%","14.97%","8.98%","14.97%","0.00%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试4
    mOneTestStepSet={"测量UK3-13的电压",
                     "手动排缆左移功能异常——未检测到按钮输入",
                     "收放控制机柜->UK3->UK3-13",
                     {"位置-收放控制机柜.png","位置-UK3.png"},
                     {"点位-UK3-13.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量UK3的13端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 按下收放控制机柜上的“手动排缆左移”按钮（保持按下）\n3. 万用表红表笔接UK3-13\n4. 万用表黑表笔接X4-6",
                     {
                         {"L_UK3-1，导线松动或断开","UK3-1，端子连接失效","UK3-13，端子连接失效","L_UK3-13，导线松动或断开","X6-10，航插引脚虚焊或接触不良","L_SB6+，导线松动或断开","SB6，按钮接触不良","L_SB6-，导线松动或断开","X6-14，航插引脚虚焊或接触不良","L_PLC_I1_2，导线断开","PLC_I1_2，输入通道失效"},
                         {"23.36%","0.93%","0.93%","23.36%","14.02%","0.00%","0.00%","0.00%","14.02%","23.36%","0.00%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试5
    mOneTestStepSet={"测量X6-10到UK3-13的导通",
                     "手动排缆左移功能异常——未检测到按钮输入",
                     "收放控制机柜->UK3->UK3-13；收放控制机柜->X6->X6插头",
                     {"位置-收放控制机柜.png","位置-UK3.png","位置-X6.png","位置-X6-旋下航插.png"},
                     {"点位-X6-10&UK3-13.png"},
                     "万用表（导通档）",
                     "万用表-导通档.png",
                     "测量UK3的13端子与X6航插头的X6-10是否导通？",
                     "导通",
                     "不导通",
                     "1. 万用表切换到导通档\n2. 万用表红表笔接UK3-13\n3. 万用表黑表笔接X6-10",
                     {
                         {"L_UK3-1，导线松动或断开","UK3-1，端子连接失效","UK3-13，端子连接失效","L_UK3-13，导线松动或断开","X6-10，航插引脚虚焊或接触不良","L_SB6+，导线松动或断开","SB6，按钮接触不良","L_SB6-，导线松动或断开","X6-14，航插引脚虚焊或接触不良","L_PLC_I1_2，导线断开","PLC_I1_2，输入通道失效"},
                         {"0.00%","0.00%","0.00%","31.25%","18.75%","0.00%","0.00%","0.00%","18.75%","31.25%","0.00%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试6
    mOneTestStepSet={"测量X6-14到PLC_I1_2的导通",
                     "手动排缆左移功能异常——未检测到按钮输入",
                     "收放控制机柜->X6->X6插头；收放控制机柜->PLC-> PLC_I1_2",
                     {"位置-收放控制机柜.png","位置-X6.png","位置-X6-旋下航插.png","位置-PLC.png","位置-PLC_I1_2.png"},
                     {"点位-X6-14&PLC_I1_2.png"},
                     "万用表（导通档）",
                     "万用表-导通档.png",
                     "测量PLC模块的PLC_I1_2端子与X6航插头的X6-14是否导通？",
                     "导通",
                     "不导通",
                     "1. 万用表切换到导通档\n2. 万用表红表笔接PLC_I1_2\n3. 万用表黑表笔接X6-14",
                     {
                         {"L_UK3-1，导线松动或断开","UK3-1，端子连接失效","UK3-13，端子连接失效","L_UK3-13，导线松动或断开","X6-10，航插引脚虚焊或接触不良","L_SB6+，导线松动或断开","SB6，按钮接触不良","L_SB6-，导线松动或断开","X6-14，航插引脚虚焊或接触不良","L_PLC_I1_2，导线断开","PLC_I1_2，输入通道失效"},
                         {"0.00%","0.00%","0.00%","0.00%","27.27%","0.00%","0.00%","0.00%","27.27%","45.45%","0.00%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试11
    mOneTestStepSet={"检查左限位行程开关U24状态",
                     "手动排缆左移功能异常——左限位行程开关信号异常",
                     "绞车->排缆机构->U24行程开关",
                     {"位置-U24行程开关.png","位置-U24行程开关-详细位置.png"},
                     {"点位-U24行程开关状态.png"},
                     "无（直接人眼观察）",
                     "",
                     "检查左限位行程开关U24状态？",
                     "触发",
                     "未触发",
                     "1. 检查左限位行程开关U24的状态",
                     {
                         {"U24，卡在触发状态或异常导通","W14，线缆芯线间异常导通","X25，航插引脚间异常导通","L_UK13-18，导线异常搭接","UK13-18，端子异常搭接","X17，航插引脚间异常导通","W14，线缆芯线间异常导通","X16，航插引脚间异常导通","L_PLC_I80_1，导线异常搭接","未知故障1","未知故障2","未知故障3"},
                         {"80.65%", "3.23%", "2.42%", "0.81%", "1.61%", "2.42%", "3.23%", "2.42%", "0.81%", "0.81%", "0.81%", "0.81%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试21
    mOneTestStepSet={"观察PLC_I80_1_LED指示灯状态",
                     "手动排缆左移功能异常——左限位接近开关信号异常",
                     "收放控制机柜->PLC->PLC_I80_1_LED",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I80_1.png"},
                     {"点位-PLC_I80_1_LED.png"},
                     "无（直接人眼观察）",
                     "",
                     "观察PLC_I80_1_LED指示灯是否点亮？",
                     "亮",
                     "不亮",
                     "1. 观察PLC_I80_1_LED指示灯是否点亮",
                     {
                         {"PLC_I80_1，输入通道失效","W14，线缆芯线间异常导通","X16，航插引脚间异常导通","L_PLC_I80_1，导线异常搭接"},
                         {"83.33%","5.56%","4.17%","6.94%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试22
    mOneTestStepSet={"测量PLC_I80_1端子电压",
                     "手动排缆左移功能异常——左限位接近开关信号异常",
                     "收放控制机柜->PLC->PLC_I80_1",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I80_1.png"},
                     {"点位-PLC_I80_1.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量PLC模块的PLC_I80_1端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接PLC_I80_1\n3. 万用表黑表笔接PLC_I80_M",
                     {
                         {"PLC_I80_1，输入通道失效","W14，线缆芯线间异常导通","X16，航插引脚间异常导通","L_PLC_I80_1，导线异常搭接"},
                         {"89.29%","3.57%","2.68%","4.46%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试31
    mOneTestStepSet={"观察PLC_I2_6_LED指示灯状态",
                     "手动抱闸未松开报警——柜内信号异常",
                     "收放控制机柜->PLC->PLC_I2_6_LED",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I2_6.png"},
                     {"点位-PLC_I2_6_LED.png"},
                     "无（直接人眼观察）",
                     "",
                     "观察PLC_I2_6_LED指示灯是否点亮？",
                     "亮",
                     "不亮",
                     "1. 观察PLC_I2_6_LED指示灯是否点亮",
                     {
                         {"L_X16-17，导线松动或断开","X16-17，接触不良","L_PLC_I2_6，导线松动或断开","PLC_I2_6，输入通道失效"},
                         {"33.33%","20.00%","33.33%","13.33%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试32
    mOneTestStepSet={"测量PLC_I2_6端子电压",
                     "手动抱闸未松开报警——柜内信号异常",
                     "收放控制机柜->PLC->PLC_I2_6",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I2_6.png"},
                     {"点位-PLC_I2_6.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量PLC模块的PLC_I2_6端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接PLC_I2_6\n3. 万用表黑表笔接PLC_I2_6_M",
                     {
                         {"L_X16-17，导线松动或断开","X16-17，接触不良","L_PLC_I2_6，导线松动或断开","PLC_I2_6，输入通道失效"},
                         {"37.88%","22.73%","37.88%","1.52%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试41
    mOneTestStepSet={"目视检查手动抱闸状态",
                     "手动抱闸未松开报警——外部信号异常",
                     "绞车->手动抱闸",
                     {"位置-手动抱闸.png"},
                     {"点位-手动抱闸状态.png"},
                     "无（直接人眼观察）",
                     "",
                     "目视检查手动抱闸状态？",
                     "松开",
                     "未松开",
                     "1. 目视检查手动抱闸状态是否松开",
                     {
                         {"手动抱闸未松开", "W21，线缆松动或断开", "U19，接近开关失效", "X20，航插接触不良", "L_X20-1，导线松动或断开", "L_X20-2，导线松动或断开", "L_X20-3，导线松动或断开", "X17-17，航插接触不良", "UK13-13，端子连接失效", "L_UK13-13，导线松动或断开"},
                         {"23.55%", "9.64%", "10.71%", "6.42%", "10.71%", "10.71%", "10.71%", "6.42%", "0.43%", "10.71%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试51
    mOneTestStepSet={"测量PLC_Q1_7端子电压",
                     "排缆左移失效——变频器控制信号异常",
                     "收放控制机柜->PLC->PLC_Q1_7",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_Q1_7.png"},
                     {"点位-PLC_Q1_7.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量PLC模块的PLC_Q1_7端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接PLC_Q1_7\n3. 万用表黑表笔接PLC_Q1_7_M",
                     {
                         {"MD520_DI2，输入通道失效","L_MD520_DI2，导线松动或断开","PLC_Q1_7，输出通道失效"},
                         {"20.43%","53.76%","25.81%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试52
    mOneTestStepSet={"测量MD520_DI2端子电压",
                     "排缆左移失效——变频器控制信号异常",
                     "收放控制机柜->MD520->MD520_DI2",
                     {"位置-收放控制机柜.png","位置-MD520.png","位置-MD520_DI2.png"},
                     {"点位-MD520_DI2.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量MD520模块的MD520_DI2端子电压否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接MD520_DI2\n3. 万用表黑表笔接MD520_DI2_GND",
                     {
                         {"MD520_DI2，输入通道失效","L_MD520_DI2，导线松动或断开","PLC_Q1_7，输出通道失效"},
                         {"27.54%","72.46%","0.00%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试61
    mOneTestStepSet={"目视检查手动抱闸状态 ",
                     "手动抱闸未松开报警",
                     "绞车->手动抱闸",
                     {"位置-手动抱闸.png"},
                     {"点位-手动抱闸状态.png"},
                     "无（直接人眼观察）",
                     "",
                     "目视检查手动抱闸状态？",
                     "松开",
                     "未松开",
                     "1. 目视检查手动抱闸状态是否松开",
                     {
                         {"手动抱闸未松开", "W21，线缆松动或断开", "U19，接近开关失效", "X20，航插接触不良", "L_X20-1，导线松动或断开", "L_X20-2，导线松动或断开", "L_X20-3，导线松动或断开", "X17-17，航插接触不良", "UK13-13，端子连接失效", "L_UK13-13，导线松动或断开", "W12，线缆松动或断开", "X16-17，航插接触不良", "L_PLC_I2_6，导线松动或断开", "PLC_I2_6，输入通道失效"},
                         {"18.74%", "7.67%", "8.52%", "5.11%", "8.52%", "8.52%", "8.52%", "5.11%", "0.34%", "8.52%", "3.41%", "5.11%", "8.52%", "3.41%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;
    //测试62
    mOneTestStepSet={"观察U19_LED接近开关指示灯",
                     "手动抱闸未松开报警",
                     "绞车->U19接近开关",
                     {"位置-U19.png","位置-U19_2.png"},
                     {"点位-U19_LED.png"},
                     "无（直接人眼观察）",
                     "",
                     "观察U19_LED指示灯是否点亮？",
                     "亮",
                     "不亮",
                     "1. 观察U19_LED指示灯是否点亮",
                     {
                         {"手动抱闸未松开","W21，线缆松动或断开","U19，接近开关失效","X20，航插接触不良","L_X20-1，导线松动或断开","L_X20-2，导线松动或断开","L_X20-3，导线松动或断开","X17-17，航插接触不良","UK13-13，端子连接失效","L_UK13-13，导线松动或断开","W12，线缆松动或断开","X16-17，航插接触不良","L_PLC_I2_6，导线松动或断开","PLC_I2_6，输入通道失效"},
                         {"0.00%", "9.43%", "10.48%", "6.29%", "10.48%", "10.48%", "10.48%", "6.29%", "0.42%", "10.48%", "4.19%", "6.29%", "10.48%", "4.19%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试63
    mOneTestStepSet={"测量UK13-13的电压",
                     "手动抱闸未松开报警",
                     "绞车->绞车接线盒->UK13->UK13-13",
                     {"位置-绞车接线盒.png","位置-UK13.png"},
                     {"点位-UK13-13.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量UK13的13端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接UK13-13\n4. 万用表黑表笔接UK12-4",
                     {
                         {"手动抱闸未松开", "W21，线缆松动或断开", "U19，接近开关失效", "X20，航插接触不良", "L_X20-1，导线松动或断开", "L_X20-2，导线松动或断开", "L_X20-3，导线松动或断开", "X17-17，航插接触不良", "UK13-13，端子连接失效", "L_UK13-13，导线松动或断开", "W12，线缆松动或断开", "X16-17，航插接触不良", "L_PLC_I2_6，导线松动或断开", "PLC_I2_6，输入通道失效"},
                         {"0.00%", "12.78%", "7.10%", "8.52%", "0.00%", "14.20%", "0.00%", "8.52%", "0.57%", "14.20%", "5.68%", "8.52%", "14.20%", "5.68%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试64
    mOneTestStepSet={"观察PLC_I2_6_LED指示灯",
                     "手动抱闸未松开报警",
                     "收放控制机柜->PLC->PLC_I2_6_LED",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I2_6.png"},
                     {"点位-PLC_I2_6_LED.png"},
                     "无（直接人眼观察）",
                     "",
                     "观察PLC_I2_6_LED指示灯是否点亮？",
                     "亮",
                     "不亮",
                     "1. 观察PLC_I2_6_LED指示灯是否点亮",
                     {
                         {"手动抱闸未松开", "W21，线缆松动或断开", "U19，接近开关失效", "X20，航插接触不良", "L_X20-1，导线松动或断开", "L_X20-2，导线松动或断开", "L_X20-3，导线松动或断开", "X17-17，航插接触不良", "UK13-13，端子连接失效", "L_UK13-13，导线松动或断开", "W12，线缆松动或断开", "X16-17，航插接触不良", "L_PLC_I2_6，导线松动或断开", "PLC_I2_6，输入通道失效"},
                         {"0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "15.00%", "0.00%", "25.00%", "10.00%", "15.00%", "25.00%", "10.00%"}
                    }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;
    //测试65
    mOneTestStepSet={"测量PLC_I2_6端子电压 ",
                     "手动抱闸未松开报警",
                     "收放控制机柜->PLC->PLC_I2_6",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I2_6.png"},
                     {"点位-PLC_I2_6.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量PLC模块的PLC_I2_6端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接PLC_I2_6\n3. 万用表黑表笔接PLC_I2_6_M",
                     {
                         {"手动抱闸未松开", "W21，线缆松动或断开", "U19，接近开关失效", "X20，航插接触不良", "L_X20-1，导线松动或断开", "L_X20-2，导线松动或断开", "L_X20-3，导线松动或断开", "X17-17，航插接触不良", "UK13-13，端子连接失效", "L_UK13-13，导线松动或断开", "W12，线缆松动或断开", "X16-17，航插接触不良", "L_PLC_I2_6，导线松动或断开", "PLC_I2_6，输入通道失效"},
                         {"0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "15.79%", "0.00%", "26.32%", "10.53%", "15.79%", "26.32%", "5.26%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;

    //测试66
    mOneTestStepSet={"测量PLC_I2_6端子电压  ",
                     "手动抱闸未松开报警",
                     "收放控制机柜->PLC->PLC_I2_6",
                     {"位置-收放控制机柜.png","位置-PLC.png","位置-PLC_I2_6.png"},
                     {"点位-PLC_I2_6.png"},
                     "万用表（直流电压档）",
                     "万用表-直流电压档.png",
                     "测量PLC模块的PLC_I2_6端子电压是否大于18V？",
                     ">18V",
                     "<18V",
                     "1. 万用表切换到直流电压档\n2. 万用表红表笔接PLC_I2_6\n3. 万用表黑表笔接PLC_I2_6_M",
                     {
                         {"手动抱闸未松开", "W21，线缆松动或断开", "U19，接近开关失效", "X20，航插接触不良", "L_X20-1，导线松动或断开", "L_X20-2，导线松动或断开", "L_X20-3，导线松动或断开", "X17-17，航插接触不良", "UK13-13，端子连接失效", "L_UK13-13，导线松动或断开", "W12，线缆松动或断开", "X16-17，航插接触不良", "L_PLC_I2_6，导线松动或断开", "PLC_I2_6，输入通道失效"},
                         {"0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "0.00%", "7.89%", "0.00%", "13.16%", "5.26%", "7.89%", "13.16%", "52.63%"}
                     }
                    };
    TestStepCandidates[mOneTestStepSet.StrTestName]=mOneTestStepSet;
}

//点击实时诊断文字跳转函数
void MainWindow::slotRealAlarmMoveToDiagnosis()
{
    qDebug()<<"slotRealAlarmMoveToDiagnosis";
    QTextCursor cursor;
    cursor=m_TextEdit->textCursor();
    int row=cursor.blockNumber();
    QString RealTimeAlarmName=m_TextEdit->document()->findBlockByLineNumber(row).text();
    if(RealTimeAlarmName.contains("Alarm1_BrakeSignalDifferent"))
    {
        CurTestNode=ModelTestSet->item(3,0);
        LoadDiagnosisUI();
    }
    else if(RealTimeAlarmName.contains("Alarm3_BrakeAlarm_SensorCableFailure"))
    {
        CurTestNode=ModelTestSet->item(4,0);
        LoadDiagnosisUI();
    }
    else if(RealTimeAlarmName.contains("Alarm2_PL_ReverseCtrlDifferent"))
    {
        CurTestNode=ModelTestSet->item(5,0);
        LoadDiagnosisUI();
    }
}

//选择功能后点击确认跳转函数
void MainWindow::on_BtnChooseFunc_clicked()
{
    if(m_Detector1_DataTrans)
    {
        if(m_Detector1_DataTrans->ConnectError)
        {
            QMessageBox::critical(nullptr,"网络连接错误", "诊断未启动\n错误信息: UDP Binding Error-"+ m_Detector1_DataTrans->udpSocket->errorString());
            return;
        }
    }

    QString StrTestName;
    for(int i=0;i<ui->tableFuncChoose->rowCount();i++)
    {
        if(ui->tableFuncChoose->item(i,0)->checkState()==Qt::Checked)
        {
            //这里需要关联对应的测试名称
            QString FuncName=ui->tableFuncChoose->item(i,0)->text();
            QMap<QString,DataBase::Signal> signal=m_RuleVariablePool.GetBasicSignalMap();
            //CurTestNode=ModelTestSet->item(2,0);
            bool WCC_PLC_I1_2=false;
            bool WCC_PLC_I80_1=false;
            bool JB_IAU_I2_0=false;
            if(signal.contains("WCC_PLC_I1_2"))WCC_PLC_I1_2=signal["WCC_PLC_I1_2"].value.BOOL;
            if(signal.contains("WCC_PLC_I80_1"))WCC_PLC_I80_1=signal["WCC_PLC_I80_1"].value.BOOL;
            if(signal.contains("JB_IAU_I2_0"))JB_IAU_I2_0=signal["JB_IAU_I2_0"].value.BOOL;
            qDebug()<<WCC_PLC_I1_2<<WCC_PLC_I80_1<<JB_IAU_I2_0;
            if(!WCC_PLC_I1_2)
            {
                CurTestNode=ModelTestSet->item(0,0);
                CalCostTime(CurTestNode);
                //LoadDiagnosisUI();
            }
            if(WCC_PLC_I1_2 && WCC_PLC_I80_1 && JB_IAU_I2_0)
            {
                CurTestNode=ModelTestSet->item(1,0);
                CalCostTime(CurTestNode);
                //LoadDiagnosisUI();
            }
            else if(WCC_PLC_I80_1 && (!JB_IAU_I2_0))
            {
                CurTestNode=ModelTestSet->item(2,0);
                CalCostTime(CurTestNode);
                //LoadDiagnosisUI();
            }

            if(i>=2 && i<=5){
                CurTestNode=ModelTestSet->item(6,0);
                CalCostTime(CurTestNode);
            }
            break;
        }
    }

    //if(StrTestName!="") CreateDiagnoisTree()//(StrTestName);
}

//诊断树生成
void MainWindow::CreateDiagnoisTree()//(QString StrTestName)
{
    ModelTestSet->clear();

    //*********************************1.1排缆左移失效——未检测到按钮输入：航插头中虚焊*******************
    //母节点是测试1
    QStandardItem *FirstTestNode = new QStandardItem("观察PLC_I1_2_LED指示灯");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    //子节点是按钮1关联的下一步测试名称和按钮2关联的下一步测试名称
    //测试1：是 转入测试2
    QStandardItem *NextNode1 = new QStandardItem("测量PLC_I1_2端子电压");//这里填写按钮1关联的下一步测试名称
    NextNode1->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);
    //测试1：否 转入测试3
    QStandardItem *NextNode2 = new QStandardItem("测量X6-10与X6-14的导通");//这里填写按钮2关联的下一步测试名称
    NextNode2->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);
    //===========================================================================================

    //===========================================================================================
    //测试1-测试2：是 诊断结束 诊断解为第11项
    QStandardItem *NextNode1_1 = new QStandardItem("PLC_I1_2，输入通道失效");
    NextNode1_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_1);

    //测试1-测试2：否 转入测试3
    QStandardItem *NextNode1_2 = new QStandardItem("测量X6-10与X6-14的导通");
    NextNode1_2->setData("测试",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_2);

    //测试1-测试3：是 转入测试4
    QStandardItem *NextNode2_1 = new QStandardItem("测量UK3-13的电压");
    NextNode2_1->setData("测试",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_1);

    //测试1-测试3：否 诊断结束 诊断解为诊断解为6、7、8项中的一项
    QStandardItem *NextNode2_2 = new QStandardItem("L_SB6+，导线松动或断开|SB6，按钮接触不良|L_SB6-，导线松动或断开");
    NextNode2_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_2);
    //===========================================================================================

    //===========================================================================================
    //测试1-测试2-测试3：是 转入测试4
    QStandardItem *NextNode1_2_1 = new QStandardItem("测量UK3-13的电压");
    NextNode1_2_1->setData("测试",Qt::WhatsThisRole);
    NextNode1_2->appendRow(NextNode1_2_1);

    //测试1-测试2-测试3：否 诊断结束 诊断解为诊断解为6、7、8项中的一项
    QStandardItem *NextNode1_2_2 = new QStandardItem("L_SB6+，导线松动或断开|SB6，按钮接触不良|L_SB6-，导线松动或断开");
    NextNode1_2_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_2->appendRow(NextNode1_2_2);

    //测试1-测试2-测试4：是 转入测试5
    QStandardItem *NextNode2_1_1 = new QStandardItem("测量X6-10到UK3-13的导通");
    NextNode2_1_1->setData("测试",Qt::WhatsThisRole);
    NextNode2_1->appendRow(NextNode2_1_1);

    //测试1-测试2-测试4：否 诊断结束 诊断解为诊断解为1、2、3项中的一项
    QStandardItem *NextNode2_1_2 = new QStandardItem("L_UK3-1，导线松动或断开|UK3-1，端子连接失效|UK3-13，端子连接失效");
    NextNode2_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2_1->appendRow(NextNode2_1_2);
    //===========================================================================================

    //===========================================================================================
    //测试1-测试2-测试3-测试4：是 转入测试5
    QStandardItem *NextNode1_2_1_1 = new QStandardItem("测量X6-10到UK3-13的导通");
    NextNode1_2_1_1->setData("测试",Qt::WhatsThisRole);
    NextNode1_2_1->appendRow(NextNode1_2_1_1);

    //测试1-测试2-测试3-测试4：否 诊断结束 诊断解为诊断解为1、2、3项中的一项
    QStandardItem *NextNode1_2_1_2 = new QStandardItem("L_UK3-1，导线松动或断开|UK3-1，端子连接失效|UK3-13，端子连接失效");
    NextNode1_2_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_2_1->appendRow(NextNode1_2_1_2);

    //测试1-测试2-测试4-测试5：是 转入测试6
    QStandardItem *NextNode2_1_1_1 = new QStandardItem("测量X6-14到PLC_I1_2的导通");
    NextNode2_1_1_1->setData("测试",Qt::WhatsThisRole);
    NextNode2_1_1->appendRow(NextNode2_1_1_1);

    //测试1-测试2-测试4-测试5：否 诊断结束 诊断解为第4项
    QStandardItem *NextNode2_1_1_2 = new QStandardItem("L_UK3-13，导线松动或断开");
    NextNode2_1_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2_1_1->appendRow(NextNode2_1_1_2);
    //===========================================================================================

    //===========================================================================================
    //测试1-测试2-测试3-测试4-测试5：是 转入测试6
    QStandardItem *NextNode1_2_1_1_1 = new QStandardItem("测量X6-14到PLC_I1_2的导通");
    NextNode1_2_1_1_1->setData("测试",Qt::WhatsThisRole);
    NextNode1_2_1_1->appendRow(NextNode1_2_1_1_1);

    //测试1-测试2-测试3-测试4-测试5：否 诊断结束 诊断解为第4项
    QStandardItem *NextNode1_2_1_1_2 = new QStandardItem("L_UK3-13，导线松动或断开");
    NextNode1_2_1_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_2_1_1->appendRow(NextNode1_2_1_1_2);

    //测试1-测试2-测试4-测试5-测试6：是 诊断结束 诊断解为第5、9项
    QStandardItem *NextNode2_1_1_1_1 = new QStandardItem("X6接触不良（X6-10或X6-14）");
    NextNode2_1_1_1_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode2_1_1_1->appendRow(NextNode2_1_1_1_1);

    //测试1-测试2-测试4-测试5-测试6：否 诊断结束 诊断解为第10项
    QStandardItem *NextNode2_1_1_1_2 = new QStandardItem("L_PLC_I1_2，导线松动或断开");
    NextNode2_1_1_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2_1_1_1->appendRow(NextNode2_1_1_1_2);
    //*********************************1.1排缆左移失效——未检测到按钮输入：航插头中虚焊END*******************


    //*********************************1.2排缆左移失效——左限位行程开关信号异常：传感器失效（常1）*******************
    //母节点是测试11
    FirstTestNode = new QStandardItem("检查左限位行程开关U24状态");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    NextNode1 = new QStandardItem("U24，行程开关卡在触发状态或异常导通");
    NextNode1->setData("诊断解",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);

    NextNode2 = new QStandardItem("未知故障");
    NextNode2->setData("诊断解",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);
    //*********************************1.2排缆左移失效——左限位行程开关信号异常：传感器失效（常1）END*******************

    //*********************************1.3排缆左移失效——左限位接近开关信号异常：定位到接线盒到IAU到CPU这一段*******************
    //母节点是测试21
    FirstTestNode = new QStandardItem("观察PLC_I80_1_LED指示灯状态");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    //测试21：是 转入测试22
    NextNode1 = new QStandardItem("测量PLC_I80_1端子电压");
    NextNode1->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);

    //测试21：否 转入测试22
    NextNode2 = new QStandardItem("测量PLC_I80_1端子电压");
    NextNode2->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);
    //============================================================================================
    //测试21-测试22：是
    NextNode1_1 = new QStandardItem("PLC_I80_1，输入通道失效");
    NextNode1_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_1);

    //测试21-测试22：否
    NextNode1_2 = new QStandardItem("PLC_I80_1，输入通道失效");
    NextNode1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_2);

    //测试21-测试22：是
    NextNode2_1 = new QStandardItem("PLC_I80_1，输入通道失效");
    NextNode2_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_1);

    //测试21-测试22：否
    NextNode2_2 = new QStandardItem("PLC_I80_1，输入通道失效");
    NextNode2_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_2);
    //*********************************1.3排缆左移失效——左限位接近开关信号异常：定位到接线盒到IAU到CPU这一段END*******************

    //*********************************2.1控制系统的故障报警，安全销未拔出报警——柜内检测信号异常：柜内导线L012导线松动或断开*******************
    //母节点是测试31
    FirstTestNode = new QStandardItem("观察PLC_I2_6_LED指示灯状态");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    //测试31：是 转入测试32
    NextNode1 = new QStandardItem("测量PLC_I2_6端子电压");
    NextNode1->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);

    //测试31：否 转入测试32
    NextNode2 = new QStandardItem("测量PLC_I2_6端子电压");
    NextNode2->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);
    //============================================================================================

    //测试31-测试32：是
    NextNode1_1 = new QStandardItem("L_PLC_I2_6，导线松动或断开");
    NextNode1_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_1);

    //测试31-测试32：否
    NextNode1_2 = new QStandardItem("L_PLC_I2_6，导线松动或断开");
    NextNode1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_2);

    //测试31-测试32：是
    NextNode2_1 = new QStandardItem("L_PLC_I2_6，导线松动或断开");
    NextNode2_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_1);

    //测试31-测试32：否
    NextNode2_2 = new QStandardItem("L_PLC_I2_6，导线松动或断开");
    NextNode2_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_2);
    //*********************************2.1控制系统的故障报警，安全销未拔出报警——柜内检测信号异常：柜内导线L012导线松动或断开END*******************

    //*********************************2.2控制系统的故障报警，安全销未拔出报警——外部传感器信号异常：传感器线缆松动或断开*******************
    //母节点是测试41
    FirstTestNode = new QStandardItem("目视检查手动抱闸状态");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    //测试41：是 未定义下一步测试或诊断解
    NextNode1 = new QStandardItem("手动抱闸未松开");
    NextNode1->setData("诊断解",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);

    //测试41：否 转入测试42
    NextNode2 = new QStandardItem("手动抱闸未松开");
    NextNode2->setData("诊断解",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);

    //*********************************3.1控制系统的故障报警，安全销未拔出报警——外部传感器信号异常：传感器线缆松动或断开END*******************

    //*********************************2.3排缆左移失效——变频器控制信号异常： L_MD520_DI2导线松动或断开*******************
    //母节点是测试51
    FirstTestNode = new QStandardItem("测量PLC_Q1_7端子电压");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    //测试51：是 转入测试52
    NextNode1 = new QStandardItem("测量MD520_DI2端子电压");
    NextNode1->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);

    //测试51：否 转入测试52
    NextNode2 = new QStandardItem("测量MD520_DI2端子电压");
    NextNode2->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);
    //============================================================================================

    //测试51-测试52：是
    NextNode1_1 = new QStandardItem("L_MD520_DI2，导线松动或断开");
    NextNode1_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_1);

    //测试51-测试52：否
    NextNode1_2 = new QStandardItem("L_MD520_DI2，导线松动或断开");
    NextNode1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_2);

    //测试51-测试52：是
    NextNode2_1 = new QStandardItem("L_MD520_DI2，导线松动或断开");
    NextNode2_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_1);

    //测试51-测试52：否
    NextNode2_2 = new QStandardItem("L_MD520_DI2，导线松动或断开");
    NextNode2_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode2->appendRow(NextNode2_2);
    //*********************************2.3排缆左移失效——变频器控制信号异常： L_MD520_DI2导线松动或断开END*******************

    //*********************************6.1控制系统的故障报警，“手动抱闸未松开报警”报警：PLC_I2_6输入通道失效*******************
    //母节点是测试61
    FirstTestNode = new QStandardItem("目视检查手动抱闸状态 ");
    FirstTestNode->setData("测试",Qt::WhatsThisRole);
    ModelTestSet->appendRow(FirstTestNode);

    //===========================================================================================
    //测试61：是 转入测试62
    NextNode1 = new QStandardItem("观察U19_LED接近开关指示灯");
    NextNode1->setData("测试",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode1);

    //测试61：否 诊断结束
    NextNode2 = new QStandardItem("手动抱闸未松开");
    NextNode2->setData("诊断解",Qt::WhatsThisRole);
    FirstTestNode->appendRow(NextNode2);
    //============================================================================================

    //测试61-测试62：是
    NextNode1_1 = new QStandardItem("测量UK13-13的电压");
    NextNode1_1->setData("测试",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_1);

    //测试61-测试62：否
    NextNode1_2 = new QStandardItem("U19，接近开关失效");
    NextNode1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1->appendRow(NextNode1_2);
    //============================================================================================

    //测试61-测试62-测试63：是
    QStandardItem *NextNode1_1_1 = new QStandardItem("观察PLC_I2_6_LED指示灯");
    NextNode1_1_1->setData("测试",Qt::WhatsThisRole);
    NextNode1_1->appendRow(NextNode1_1_1);

    //测试61-测试62-测试63：否
    QStandardItem *NextNode1_1_2 = new QStandardItem("W21，线缆松动或断开|U19，接近开关失效|X20，航插接触不良|L_X20-2，导线松动或断开");
    NextNode1_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_1->appendRow(NextNode1_1_2);
    //============================================================================================

    //测试61-测试62-测试63-测试64：是
    QStandardItem *NextNode1_1_1_1 = new QStandardItem("测量PLC_I2_6端子电压  ");
    NextNode1_1_1_1->setData("测试",Qt::WhatsThisRole);
    NextNode1_1_1->appendRow(NextNode1_1_1_1);

    //测试61-测试62-测试63-测试64：否
    QStandardItem *NextNode1_1_1_2 = new QStandardItem("测量PLC_I2_6端子电压 ");
    NextNode1_1_1_2->setData("测试",Qt::WhatsThisRole);
    NextNode1_1_1->appendRow(NextNode1_1_1_2);
    //============================================================================================

    //测试61-测试62-测试63-测试64-测试65：是
    QStandardItem *NextNode1_1_1_2_1 = new QStandardItem("PLC_I2_6，输入通道失效");
    NextNode1_1_1_2_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_1_1_2->appendRow(NextNode1_1_1_2_1);

    //测试61-测试62-测试63-测试64-测试65：否
    QStandardItem *NextNode1_1_1_2_2 = new QStandardItem("X17-17，航插接触不良|L_UK13-13，导线松动或断开|W12，线缆松动或断开|X16-17，航插接触不良|L_PLC_I2_6，导线松动或断开");
    NextNode1_1_1_2_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_1_1_2->appendRow(NextNode1_1_1_2_2);
    //============================================================================================

    //测试61-测试62-测试63-测试64-测试66：是
    QStandardItem *NextNode1_1_1_1_1 = new QStandardItem("PLC_I2_6，输入通道失效");
    NextNode1_1_1_1_1->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_1_1_1->appendRow(NextNode1_1_1_1_1);

    //测试61-测试62-测试63-测试64-测试66：否
    QStandardItem *NextNode1_1_1_1_2 = new QStandardItem("X17-17，航插接触不良|L_UK13-13，导线松动或断开|W12，线缆松动或断开|X16-17，航插接触不良|L_PLC_I2_6，导线松动或断开");
    NextNode1_1_1_1_2->setData("诊断解",Qt::WhatsThisRole);
    NextNode1_1_1_1->appendRow(NextNode1_1_1_1_2);


    //*********************************2.1控制系统的故障报警，“手动抱闸未松开报警”报警：PLC_I2_6输入通道失效 END*******************
}

//载入当前测试的UI
void MainWindow::LoadDiagnosisUI()
{
    QString CurTestName=CurTestNode->text();
    ui->GroupTest->setTitle(TestStepCandidates[CurTestName].StrCurFault);//当前异常

    ui->labelTestPos->setText(TestStepCandidates[CurTestName].StrTestPos);//测试位置
    ui->labelTestQuestion->setText(TestStepCandidates[CurTestName].StrQuestion);//对话框内容
    ui->pushButton1->setText(TestStepCandidates[CurTestName].StrButton1);//按钮1文字
    ui->pushButton2->setText(TestStepCandidates[CurTestName].StrButton2);//按钮1文字
    ui->labelTool->setText(TestStepCandidates[CurTestName].TestTool);//测试工具
    ui->textEditTestDesc->setText(TestStepCandidates[CurTestName].StrDesc);//步骤
    ui->textEditTestDesc->setTextColor (Qt::yellow);
    ui->LbImgPos->setScaledContents(false);
    if(TestStepCandidates[CurTestName].ListImgPosPath.count()>0)
    {
        AdjustImageLayout(ui->LbImgPos,"C:/MDB/DiagnoseImages/"+TestStepCandidates[CurTestName].ListImgPosPath.at(0));
        AdjustGraphicScene(ui->graphicsView_Pos,&m_scene_pos,"C:/MDB/DiagnoseImages/"+TestStepCandidates[CurTestName].ListImgPosPath.at(0));
        CurImgPosPath=TestStepCandidates[CurTestName].ListImgPosPath.at(0);
        ui->BtnLastImgPos->setEnabled(false);
        if(TestStepCandidates[CurTestName].ListImgPosPath.count()>1) ui->BtnNextImgPos->setEnabled(true);
        else ui->BtnNextImgPos->setEnabled(false);
    }
    if(TestStepCandidates[CurTestName].ListImgTermPath.count()>0)
    {
        AdjustImageLayout(ui->LbImgTerm,"C:/MDB/DiagnoseImages/"+TestStepCandidates[CurTestName].ListImgTermPath.at(0));
        AdjustGraphicScene(ui->graphicsView_Term,&m_scene_term,"C:/MDB/DiagnoseImages/"+TestStepCandidates[CurTestName].ListImgTermPath.at(0));
        CurImgTermPath=TestStepCandidates[CurTestName].ListImgTermPath.at(0);
        ui->BtnLastImgTerm->setEnabled(false);
        if(TestStepCandidates[CurTestName].ListImgTermPath.count()>1) ui->BtnLastImgTerm->setEnabled(true);
        else ui->BtnLastImgTerm->setEnabled(false);
    }
    if(TestStepCandidates[CurTestName].TestTool=="") ui->tabWidget->setTabEnabled(2,false);//ui->tab_Tool->setEnabled(false);
    else
    {
        ui->tabWidget->setTabEnabled(2,true);//ui->tab_Tool->setEnabled(true);
        AdjustImageLayout(ui->LbImgTool,"C:/MDB/ToolImages/"+TestStepCandidates[CurTestName].ImgToolPath);
    }
    ui->tableListFalut->clearContents();
    ui->tableListFalut->setRowCount(0);
    //诊断候选解列表中显示的候选解按候选概率由大到小排序,隐藏概率为0的候选解
    ui->tableListFalut->setRowCount(TestStepCandidates[CurTestName].ListFuzzyProb.at(0).count());
    for(int i=0;i<TestStepCandidates[CurTestName].ListFuzzyProb.at(0).count();i++)
    {
        QTableWidgetItem *itemSerial = new QTableWidgetItem(QString::number(i + 1));
        // 设置对齐方式为居中
        itemSerial->setTextAlignment(Qt::AlignCenter);
        // 在表格中设置该项
        ui->tableListFalut->setItem(i, 0, itemSerial);
        //        ui->tableListFalut->setItem(i,0,new QTableWidgetItem(QString::number(i+1)));
        ui->tableListFalut->setItem(i,1,new QTableWidgetItem(TestStepCandidates[CurTestName].ListFuzzyProb.at(0).at(i)));
        ui->tableListFalut->setItem(i,2,new QTableWidgetItem(TestStepCandidates[CurTestName].ListFuzzyProb.at(1).at(i)));

    }
    //排序
    for(int i=0;i<ui->tableListFalut->rowCount()-1;i++)
    {
        for(int j=i+1;j<ui->tableListFalut->rowCount();j++)
        {
            if(ui->tableListFalut->item(i,2)->text().remove("%").toDouble()<ui->tableListFalut->item(j,2)->text().remove("%").toDouble())
            {
                QString temp1,temp2;
                temp1=ui->tableListFalut->item(i,1)->text();
                temp2=ui->tableListFalut->item(i,2)->text();
                ui->tableListFalut->item(i,0)->setText(QString::number(i+1));
                ui->tableListFalut->item(i,1)->setText(ui->tableListFalut->item(j,1)->text());
                ui->tableListFalut->item(i,2)->setText(ui->tableListFalut->item(j,2)->text());
                ui->tableListFalut->item(j,1)->setText(temp1);
                ui->tableListFalut->item(j,2)->setText(temp2);
            }
        }
    }
    ui->tableListFalut->item(ui->tableListFalut->rowCount()-1,0)->setText(QString::number(ui->tableListFalut->rowCount()));
    //隐藏概率为0的候选解
    for(int i=0;i<ui->tableListFalut->rowCount();i++)
    {
        if(ui->tableListFalut->item(i,2)->text()=="0.00%") ui->tableListFalut->hideRow(i);
    }
    ui->tabWidgetMain->setCurrentIndex(2);
    ui->stackedDiagnosis->setCurrentIndex(1);
}

QString GetTimeStr(long Minute ,int Second, int mSec)
{
    time_t tval;
    char Strbuf[100];
    struct tm *tblock;
    tval=Minute*60+Second;
    tblock = localtime(&tval);
    sprintf(Strbuf,"%4d年%02d月%02d日%02d时%02d分%d秒",tblock->tm_year+1900,tblock->tm_mon+1,tblock->tm_mday, tblock->tm_hour,tblock->tm_min,tblock->tm_sec);
    return (QString)Strbuf;
}

void MainWindow::DoUpdateUI()
{
    ui->dateTimeMain->setDateTime(QDateTime::currentDateTime());
    if(CurveMode!=1) return;
    on_newBasicSignalUpdate();

    //if(CurveMode!=1) return;
    ui->Lb_RecordTime->setText("当前记录时长："+QString::number(TimeOfRecording/10)+"秒");
    QFile m_file(DRFileName);
    ui->LbDRSize->setText("当前数据大小："+QString::number(m_file.size()/1024)+"KB");//字节数
    QFileInfo fileinfo = QFileInfo(DRFileName);
    ui->LbFileName->setText(fileinfo.fileName());
}

void MainWindow::setLoginAccount(DataBase::Str_account loginAccount)
{//设置登陆账户并初始化登陆账户名称及权限

    m_loginAccount=loginAccount;
    qDebug()<<m_loginAccount.Operating_user<<" 已登陆";
    ui->labelLoginUser->setText(m_loginAccount.Operating_user);
    ui->labelLoginUser->adjustSize();

    //权限设置
    if(m_loginAccount.Operating_limit>1){
        //ui->tabWidgetMain->setTabEnabled(0,true);
        ui->tabWidgetMain->setTabEnabled(3,false);
        ui->tabWidgetMain->setTabEnabled(4,false);
        ui->tabWidgetMain->setTabEnabled(5,false);
    }
    if(m_loginAccount.Operating_limit<=1){
        //ui->tabWidgetMain->setTabEnabled(0,true);
        ui->tabWidgetMain->setTabEnabled(3,true);
        ui->tabWidgetMain->setTabEnabled(4,true);
        ui->tabWidgetMain->setTabEnabled(5,true);
    }
}

void MainWindow::on_pushButtonStopDiagnosis_clicked()
{//停止故障诊断按钮点击

    //MK2CPU信号传输线程停止
    //MK2CPU_DataTrans->stopThread();
    //MK2CPU_DataTrans->wait();

    //MK5CPU信号传输线程停止
    //MK5CPU_DataTrans->stopThread();
    //MK5CPU_DataTrans->wait();

    //诊断线程停止
    DiagnosisThread->stopThread();
    DiagnosisThread->wait();

    policyTroubleshootEnd();

    //报警指示灯
    WidgetHydraulicState->DelDisPlayRadioButton();
}

void MainWindow::on_pushButtonStartupDiagnosis_clicked()
{//启动故障诊断按钮点击
    if(m_Detector1_DataTrans)
    {
        if(m_Detector1_DataTrans->ConnectError)
        {
            QMessageBox::critical(nullptr,"网络连接错误", "诊断未启动\n错误信息: UDP Binding Error-"+ m_Detector1_DataTrans->udpSocket->errorString());
            return;
        }
    }

    policyTroubleshootStart();

    //初始化变量池
    if(!m_RuleVariablePool.InitVariableVector()) return;
    m_RuleVariablePool.SetAllUnchecked();

    //初始化规则池
    if(!m_RulePool.InitRuleVector()) return;
    m_RulePool.SetAllRuleUnused();

    //初始化报警指示灯
    WidgetHydraulicState->InitDisPlayRadioButton();

    //启动所有信号传输和诊断线程
    //MK2CPU_DataTrans->start();
    //MK5CPU_DataTrans->start();
    DiagnosisThread->start();
}

void MainWindow::policyTroubleshootStart()
{
    //设置停止诊断按钮不可用
    ui->pushButtonStopDiagnosis->setEnabled(true);

    //设置启动诊断按钮不可用
    ui->pushButtonStartupDiagnosis->setEnabled(false);

    //设置清除报警信息按钮不可用
    ui->pushButtonClearWarnningRecord->setEnabled(false);
    //设置更改用户按钮不可用
    ui->pushButtonSwitchUser->setEnabled(false);
    //设置退出按钮不可用
    ui->pushButtonQuit->setEnabled(false);

    //设置用户管理界面不可用
    WidgetUserManage->SetChangeEnabled(false);
    //设置IP连接管理界面不可用
    WidgetConnectManage->SetConfigurationEnabled(false);
    //设置变量管理界面不可用
    WidgetVariableManage->SetChangeEnabled(false);
    //设置规则管理界面不可用
    WidgetRuleManage->SetChangeEnabled(false);
    //设置预警规则管理界面不可用
    WidgetWarnManage->SetChangeEnabled(false);

    //设置测试按钮不可用
    //ui->pushButtonTest->setEnabled(false);
}

void MainWindow::policyTroubleshootEnd()
{
    //设置停止诊断按钮不可用
    ui->pushButtonStopDiagnosis->setEnabled(false);

    //设置启动诊断按钮可用
    ui->pushButtonStartupDiagnosis->setEnabled(true);
    //设置清除报警信息按钮可用
    ui->pushButtonClearWarnningRecord->setEnabled(true);
    //设置更改用户按钮可用
    ui->pushButtonSwitchUser->setEnabled(true);
    //设置退出按钮可用
    ui->pushButtonQuit->setEnabled(true);

    //设置用户管理界面可用
    WidgetUserManage->SetChangeEnabled(true);
    //设置IP连接管理界面可用
    WidgetConnectManage->SetConfigurationEnabled(true);
    //设置变量管理界面可用
    WidgetVariableManage->SetChangeEnabled(true);
    //设置规则管理界面可用
    WidgetRuleManage->SetChangeEnabled(true);
    //设置预警规则管理界面可用
    WidgetWarnManage->SetChangeEnabled(true);
}

void MainWindow::UpdateRealTimeFaliureOrWarnning()
{
    WidgetFaultInformation->ClearLoggingUI();
    int MinRecordIdx,MaxRecordIdx;
    MinRecordIdx=(CurPageNum-1)*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt();
    MaxRecordIdx=CurPageNum*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt();
    //更新实时报警信息
    QVector<DataBase::Signal> realtime_signal  = m_RuleVariablePool.FindRealtimeAlarmOrFaliure();
    ui->label_DMS_TableControl_TotalNum->setText(QString::number(realtime_signal.size()));
    if((realtime_signal.size()%ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt())==0)
        ui->LbTotalPageNum->setText(QString::number(realtime_signal.size()/ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()));
    else
        ui->LbTotalPageNum->setText(QString::number(realtime_signal.size()/ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()+1));

    QString FaliureErrorString;
    QString PlainTextEditShowStr="";
    m_TextEdit->clear();
    m_TextEdit->document()->clear();
    m_TextEdit->update();

    if(realtime_signal.size()==0)
    {
        WidgetHydraulicState->Set3DWidgetPNG(0);
    }
    bool FirstShow=true;
    unsigned char PNGCode=0x00;
    for(int i=0;i<realtime_signal.size();i++)
    {
        //更新实时报警总表
        if(ui->radioButton_realtimeAlarm->isChecked())
        {
            if((i>MinRecordIdx-1)&&(i<=MaxRecordIdx-1))   WidgetFaultInformation->AddRecord(realtime_signal[i],i+1,true);
        }

        //更新主界面报警信息
        bool showflag=false;
        //qDebug()<<"GetStackWidgetPageName="<<WidgetHydraulicState->GetStackWidgetPageName();
        //qDebug()<<"SignalPos="<<realtime_signal[i].SignalPos;
        if(WidgetHydraulicState->GetStackWidgetPageName()==0&&realtime_signal[i].SignalPos=="传感器信号-外部")
        {
            PNGCode=PNGCode|0x10;
            showflag=true;
        }
        if(WidgetHydraulicState->GetStackWidgetPageName()==1&&realtime_signal[i].SignalPos=="传感器信号-内部")
        {
            PNGCode=PNGCode|0x01;
            showflag=true;
        }
        if(WidgetHydraulicState->GetStackWidgetPageName()==2&&realtime_signal[i].SignalPos=="变频器控制信号")
        {
            PNGCode=PNGCode|0x02;
            showflag=true;
        }
        if(WidgetHydraulicState->GetStackWidgetPageName()==3&&realtime_signal[i].SignalPos=="备用泵电机启动箱")
        {
            PNGCode=PNGCode|0x08;
            showflag=true;
        }
        if(WidgetHydraulicState->GetStackWidgetPageName()==4&&realtime_signal[i].SignalPos=="提升泵电机启动箱")
        {
            PNGCode=PNGCode|0x04;
            showflag=true;
        }
        if(WidgetHydraulicState->GetStackWidgetPageName()==5)
        {
            showflag=true;
            //更新3D界面
            if(realtime_signal[i].SignalPos=="传感器信号-外部") {PNGCode=PNGCode|0x10; }
            if(realtime_signal[i].SignalPos=="传感器信号-内部") {PNGCode=PNGCode|0x01;}
            if(realtime_signal[i].SignalPos=="变频器控制信号") {PNGCode=PNGCode|0x02;}
            if(realtime_signal[i].SignalPos=="备用泵电机启动箱") {PNGCode=PNGCode|0x08;}
            if(realtime_signal[i].SignalPos=="提升泵电机启动箱") {PNGCode=PNGCode|0x04;}
            WidgetHydraulicState->Set3DWidgetPNG(PNGCode);
        }

        if(showflag)
        {
            if(FirstShow) {PlainTextEditShowStr="";FirstShow=false;}
            else PlainTextEditShowStr="\n";
            PlainTextEditShowStr+=realtime_signal[i].signalType+"\n";
            PlainTextEditShowStr+="名称："+realtime_signal[i].Name+"\n";
            PlainTextEditShowStr+="位置："+realtime_signal[i].SignalPos+"\n";
            PlainTextEditShowStr+="报警内容："+realtime_signal[i].Note+"\n";
            PlainTextEditShowStr+="规则库分析："+realtime_signal[i].Detail+"\n";
            if(realtime_signal[i].signalType=="报警信息") m_TextEdit->setTextColor(Qt::yellow);
            else  m_TextEdit->setTextColor(Qt::red);
            m_TextEdit->append(PlainTextEditShowStr);
        }

        //qDebug()<<m_TextEdit->document()->toPlainText();
        m_TextEdit->update();
    }
}
void MainWindow::UpdateHisFaliureOrWarnning()
{
    //历史报警列表
    QVector<DataBase::Signal> His_signal;
    //if(ui->radioButton_realtimeAlarm->isChecked()) realtime_signal  = m_RuleVariablePool.FindRealtimeAlarmOrFaliure();
    int MinRecordIdx,MaxRecordIdx;
    MinRecordIdx=(CurPageNum-1)*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt();
    MaxRecordIdx=CurPageNum*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt();
    if(!ui->radioButton_realtimeAlarm->isChecked())
    {
        WidgetFaultInformation->ClearLoggingUI();
        int TotalRecords;
        His_signal = TMATE_Database->SelectHisAlarmSignalFromDataBase(ui->dateEditStart->date(),ui->dateEditEnd->date(),ui->EdSearchRecord->text(),ui->CbAlarmPos->currentText(),MinRecordIdx,MaxRecordIdx,TotalRecords);
        ui->label_DMS_TableControl_TotalNum->setText(QString::number(TotalRecords));
        if((TotalRecords%ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt())==0)
            ui->LbTotalPageNum->setText(QString::number(TotalRecords/ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()));
        else
            ui->LbTotalPageNum->setText(QString::number(TotalRecords/ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()+1));
        for(int i=0;i<His_signal.size();i++)
            WidgetFaultInformation->AddRecord(His_signal[i],i+1+MinRecordIdx,false);
    }
}
void MainWindow::on_UpdateFaliureOrWarnning(QVector<DataBase::Signal> signal)
{

    UpdateRealTimeFaliureOrWarnning();
    //故障报警信号处理槽函数

    //更新数据库
    //QVector<DataBase::Signal> signal = m_RuleVariablePool.FindChangeSignal();

    for(int i=0;i<signal.size();i++){
        //更新数据库
        if(signal[i].value.BOOL==true) //新报警/新故障
        {
            //将故障信息存储到数据库
            m_RuleVariablePool.SetSignalRecordID(signal[i].Name,TMATE_Database->InsertFailToFailureRecord(signal[i].Name,signal[i].SignalPos));
        }
        else//原报警/故障消除
        {
            if(signal[i].value.BOOL==false) //新报警/新故障
                TMATE_Database->UpdateFailToFailureRecord(signal[i].RecordID);
        }
    }
    UpdateHisFaliureOrWarnning();
}

void MainWindow::on_newFaliureError()
{//故障报警信号处理槽函数
    QVector<DataBase::Signal> signal = m_RuleVariablePool.GetFaliureError();
    QString FaliureErrorString;
    for(int i=0;i<signal.size();i++){
        FaliureErrorString.append(signal[i].Name).append("  故障  ").append(QDateTime::currentDateTime().toString("yyyy/MM/dd hh:mm:ss"));
        if(i<signal.size()-1) FaliureErrorString.append("\n");

        //将故障信息存储到数据库
        TMATE_Database->InsertFailToFailureRecord(signal[i].Name,signal[i].SignalPos);
    }
    WidgetFaultInformation->updateLoggingUI(FaliureErrorString);
}

void MainWindow::on_newWarnningError()
{//预警报警信号处理槽函数
    QVector<DataBase::Signal> signal = m_RuleVariablePool.GetWarnningError();
    QString WarnningErrorString;
    for(int i=0;i<signal.size();i++){
        WarnningErrorString.append(signal[i].Name).append(" 预报警  ").append(QDateTime::currentDateTime().toString("yyyy/MM/dd hh:mm:ss"));
        if(i<signal.size()-1) WarnningErrorString.append("\n");

        //将报警信息存储到数据库
        TMATE_Database->InsertFailToFailureRecord(signal[i].Name,signal[i].SignalPos);
    }
    WidgetFaultInformation->updateLoggingUI(WarnningErrorString);
}

void MainWindow::on_newBasicSignalUpdate()
{//基础信号更新处理槽函数
    //更新液压显示界面
    if(DiagnosisThread->isRunning()) WidgetHydraulicState->UpDate(m_RuleVariablePool.GetBasicSignalMap());
    //更新实时数据显示界面
    WidgetRealTimeData->UpDate(m_RuleVariablePool.GetBasicSignalMap());
}

void MainWindow::on_VariableNameChange(QString OraginVariableName, QString ChangeVariableName)
{
    qDebug()<<"on_VariableNameChange 待完成";
}

void MainWindow::on_VariableDelete(QString VariableName)
{
    qDebug()<<"on_VariableNameChange 待完成";
}


///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
/// \brief 已完成程序段区域
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

void MainWindow::on_pushButtonSwitchUser_clicked()
{//切换登录用户按钮
    qdlglogin   *dlgLogin=new qdlglogin(this); //创建对话框

    if (dlgLogin->exec()==QDialog::Accepted){
        //设置当前登陆账户
        setLoginAccount(dlgLogin->getLoginAccount());
        delete dlgLogin;
    }
    else
        delete dlgLogin;
}
void MainWindow::closeEvent(QCloseEvent *event)
{
    QString dlgTitle="退出";
    QString strInfo="是否确认退出诊断程序?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        if(DiagnosisThread->isRunning())
        {
            DiagnosisThread->stopThread();
            DiagnosisThread->wait();
        }

        policyTroubleshootEnd();

        event->accept();
    }
    else event->ignore();
}
void MainWindow::on_pushButtonQuit_clicked()
{
    //退出程序按钮点击
    if(DiagnosisThread->isRunning())
    {
        DiagnosisThread->stopThread();
        DiagnosisThread->wait();
    }

    policyTroubleshootEnd();

    //报警指示灯
    this->close();
}

void MainWindow::on_pushButtonClearWarnningRecord_clicked()
{//清除报警记录
    //WidgetWarnningInformation->ClearLoggingUI();
    m_TextEdit->clear();
    m_TextEdit->document()->clear();
    m_TextEdit->update();
    WidgetHydraulicState->Set3DWidgetPNG(0);
    if(ui->radioButton_realtimeAlarm->isChecked())
    {
        WidgetFaultInformation->ClearLoggingUI();
    }
}

void MainWindow::on_radioButton_realtimeAlarm_clicked(bool checked)
{
    ui->widgetSearch->setEnabled(false);
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
    //ui->pushButton_UpdateMannulSet->setEnabled(true);
}

void MainWindow::on_radioButton_HisAlarm_clicked(bool checked)
{
    ui->widgetSearch->setEnabled(true);
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
    //ui->pushButton_UpdateMannulSet->setEnabled(false);
}

void MainWindow::on_pushButton_DMS_TableControl_FirstPage_clicked()
{
    CurPageNum=1;
    ui->spinBoxPageNum->setValue(CurPageNum);
    //ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum));
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}

void MainWindow::on_pushButton_DMS_TableControl_PreviousPage_clicked()
{
    if(CurPageNum==1) return;
    CurPageNum--;
    ui->spinBoxPageNum->setValue(CurPageNum);
    //ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum));
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}

void MainWindow::on_pushButton_DMS_TableControl_NextPage_clicked()
{
    if(CurPageNum*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()>=ui->label_DMS_TableControl_TotalNum->text().toInt()) return;
    CurPageNum++;
    ui->spinBoxPageNum->setValue(CurPageNum);
    //ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum));
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}

void MainWindow::on_pushButton_DMS_TableControl_LastPage_clicked()
{
    CurPageNum=ui->label_DMS_TableControl_TotalNum->text().toInt()/ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt();
    if(CurPageNum*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()!=ui->label_DMS_TableControl_TotalNum->text().toInt()) CurPageNum++;
    ui->spinBoxPageNum->setValue(CurPageNum);
    //ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum));
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}

void MainWindow::on_comboBox_DMS_TableControl_PageRecordsNumber_currentIndexChanged(int index)
{
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}

void MainWindow::on_pushButton_UpdateMannulSet_clicked()
{
    //if(!ui->radioButton_realtimeAlarm->isChecked()) return;
    //实时报警列表
    QString dlgTitle="新增变量";
    QString strInfo;
    if(WidgetFaultInformation->UpdateMannulSet()) strInfo=QString::asprintf("修改成功！");
    else strInfo=QString::asprintf("修改失败！");
    QMessageBox::information(nullptr, dlgTitle, strInfo,
                             QMessageBox::Ok,QMessageBox::NoButton);
}

void MainWindow::on_tabWidgetMain_currentChanged(int index)
{
    if(index==4) WidgetVariableManage->update();
    //on_UpdateFaliureOrWarnning();
}

void MainWindow::on_BtnSearch_clicked()
{
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}

void MainWindow::on_BtnClearCurAllRecords_clicked()
{
    if(!ui->radioButton_HisAlarm->isChecked()) return;
    QString dlgTitle="Question消息框";
    QString strInfo="是否删除所有筛选记录?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        TMATE_Database->DeleteHisRecord(1,0,ui->dateEditStart->date(),ui->dateEditEnd->date(),ui->EdSearchRecord->text(),ui->CbAlarmPos->currentText());
        UpdateHisFaliureOrWarnning();
    }

}

void MainWindow::on_BtnClearCurSelectRecords_clicked()
{
    if(!ui->radioButton_HisAlarm->isChecked()) return;
    QString dlgTitle="Question消息框";
    QString strInfo="是否删除选中记录?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        WidgetFaultInformation->DeleteRecord(0,TMATE_Database);
        UpdateHisFaliureOrWarnning();
    }

}

void MainWindow::on_BtnClearCurPageRecords_clicked()
{
    if(!ui->radioButton_HisAlarm->isChecked()) return;
    QString dlgTitle="Question消息框";
    QString strInfo="是否删除当前页记录?";
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;

    result=QMessageBox::question(this,dlgTitle,strInfo,
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result==QMessageBox::Yes){
        WidgetFaultInformation->DeleteRecord(1,TMATE_Database);
        UpdateHisFaliureOrWarnning();
    }

}

void MainWindow::on_spinBoxPageNum_valueChanged(int arg1)
{
    CurPageNum=ui->spinBoxPageNum->value();
    if(ui->radioButton_realtimeAlarm->isChecked()) UpdateRealTimeFaliureOrWarnning();
    else UpdateHisFaliureOrWarnning();
}




void MainWindow::on_BtnStartSaveData_clicked()
{
    CurveMode=1;
    IsInTest=true;
    EndTestSignal=false;
    //默认数据文件名称为起始时间
    sprintf(DRFileName,"%sDR%s.dat",DATA_SAVE_DISK,QDateTime::currentDateTime().toString("yyyy-MM-dd_hh-mm-ss").toLatin1().data());//StartTime.tv_sec/(10*60));  //10min SAVE TO FILE

}

void MainWindow::on_BtnFinishSaveData_clicked()
{
    //输入数据文件名称
    QDialog *dialogDRNameEdit =new QDialog();
    dialogDRNameEdit->setWindowTitle("输入文件名称");
    dialogDRNameEdit->setMinimumSize(QSize(600,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogDRNameEdit);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogDRNameEdit);
    pushbuttonOK->setText("确认");

    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogDRNameEdit);
    m_label1->setText("采集数据名称");
    QLineEdit *m_LineEdit = new QLineEdit(dialogDRNameEdit);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_LineEdit);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addLayout(linelayout1);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogDRNameEdit,SLOT(accept()));
    QFileInfo fileinfo = QFileInfo(DRFileName);
    m_LineEdit->setText(fileinfo.fileName());
    if (dialogDRNameEdit->exec()==QDialog::Accepted)
    {
        sprintf(NewDRFileName,"%s%s",DATA_SAVE_DISK,m_LineEdit->text().toUtf8().data());
    }
    else return;

    CurveMode=0;
    IsInTest=false;
    EndTestSignal=true;
    strcpy(TestInfo,ui->EditTestInfo->toPlainText().toUtf8().data());
    ui->Lb_RecordTime->setText("当前记录时长：无");
    ui->LbDRSize->setText("当前数据大小：未知");

}

void MainWindow::LoadDataList()
{
    QString StrName,FilePath;
    int MinRecordIdx,MaxRecordIdx;
    int rowcount=0;
    QTableWidget *m_TableWidget;
    QRadioButton *m_RbSearchData;
    QComboBox *m_CbTableControl_PageRecordsNumber;
    QLabel *m_LbTableControl_TotalNum;
    int m_CurPageNum;

    m_TableWidget=ui->TblDRList;
    m_RbSearchData=ui->RbSearchData;
    m_CbTableControl_PageRecordsNumber=ui->comboBox_DMS_TableControl_PageRecordsNumber;
    m_LbTableControl_TotalNum=ui->label_DMS_TableControl_TotalNum;
    FilePath=DATA_SAVE_DISK;
    m_CurPageNum=CurPageNum_Test;

    //判断路径是否存在
    QDir dir(FilePath);
    if(!dir.exists())
    {
        printf("No Files find\n");
        return;
    }

    //获取所选文件类型过滤器
    QStringList filters;

    //文件过滤
    filters<<QString("DR*.dat");

    //定义迭代器并设置过滤器
    QDirIterator dir_iterator(FilePath,
                              filters,
                              QDir::Files | QDir::NoSymLinks);

    m_TableWidget->setRowCount(0);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();

        //if(m_RbSearchData->isChecked()) {if(!CheckFileFilter(FILE_TYPE,file_info.fileName())) continue;}
        rowcount++;

        MinRecordIdx=(m_CurPageNum-1)*m_CbTableControl_PageRecordsNumber->currentText().toInt();//0
        MaxRecordIdx=m_CurPageNum*m_CbTableControl_PageRecordsNumber->currentText().toInt();//20
        if(rowcount<=MinRecordIdx) continue;//
        if(rowcount>MaxRecordIdx) continue;
        m_TableWidget->setRowCount(rowcount-MinRecordIdx);
        //ui->TblDRList->setRowCount(ui->TblDRList->rowCount()+1);
        m_TableWidget->setItem(rowcount-MinRecordIdx-1, 1, new QTableWidgetItem(file_info.fileName()));
        m_TableWidget->resizeRowToContents(rowcount-MinRecordIdx-1);
        QCheckBox *mQCheckBox=new QCheckBox();
        m_TableWidget->setCellWidget(rowcount-MinRecordIdx-1,0,mQCheckBox);
    }
    m_LbTableControl_TotalNum->setText(QString::number(rowcount));

}

void MainWindow::on_BtnUpdateFile_clicked()
{
    LoadDataList();
}

void MainWindow::DelDR()
{
    //确认是否删除
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("是否确认删除选择数据?"),
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result!=QMessageBox::Yes) return;

    QFile TmpFile;
    QTableWidget *m_TableWidget;
    QString Path;
    m_TableWidget=ui->TblDRList;Path=DATA_SAVE_DISK;
    for(int i=0;i<m_TableWidget->rowCount();i++)
    {
        QCheckBox m_QCheckBox;
        if(((QCheckBox *)m_TableWidget->cellWidget(i,0))->isChecked())
        {
            TmpFile.setFileName(Path+m_TableWidget->item(i,1)->text());
            if (TmpFile.exists())  TmpFile.remove();
        }
    }
    LoadDataList();
}


void MainWindow::on_BtnDelDR_clicked()
{
    DelDR();
}

void MainWindow::on_pushButton_DMS_TableControl_FirstPage_2_clicked()
{
    CurPageNum_Test=1;
    ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum_Test));
    LoadDataList();
}

void MainWindow::on_pushButton_DMS_TableControl_PreviousPage_2_clicked()
{
    if(CurPageNum_Test==1) return;
    CurPageNum_Test--;
    ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum_Test));
    LoadDataList();
}

void MainWindow::on_pushButton_DMS_TableControl_NextPage_2_clicked()
{
    if(CurPageNum_Test*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()>=ui->label_DMS_TableControl_TotalNum->text().toInt()) return;
    CurPageNum_Test++;
    ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum_Test));
    LoadDataList();
}

void MainWindow::on_pushButton_DMS_TableControl_LastPage_2_clicked()
{
    CurPageNum_Test=ui->label_DMS_TableControl_TotalNum->text().toInt()/ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt();
    if(CurPageNum_Test*ui->comboBox_DMS_TableControl_PageRecordsNumber->currentText().toInt()!=ui->label_DMS_TableControl_TotalNum->text().toInt()) CurPageNum_Test++;
    ui->label_DMS_TableControl_PageNum->setText(QString::number(CurPageNum_Test));
    LoadDataList();
}

double MainWindow::GetVarVal(QString ValName)
{
    double RetVal;
    if(ValName=="CentreBox_U01") return CurRecord.CentreBox_U01;
    if(ValName=="CentreBox_U02") return CurRecord.CentreBox_U02;
    if(ValName=="CentreBox_U03") return CurRecord.CentreBox_U03;
    if(ValName=="CentreBox_U04") return CurRecord.CentreBox_U04;
    if(ValName=="CentreBox_U05") return CurRecord.CentreBox_U05;
    if(ValName=="CentreBox_U06") return CurRecord.CentreBox_U06;
    if(ValName=="CentreBox_U07") return CurRecord.CentreBox_U07;
    if(ValName=="CentreBox_U08") return CurRecord.CentreBox_U08;
    if(ValName=="CentreBox_U09") return CurRecord.CentreBox_U09;
    if(ValName=="CentreBox_U10") return CurRecord.CentreBox_U10;

    if(ValName=="CentreBox_I01") return CurRecord.CentreBox_I01;
    if(ValName=="CentreBox_I02") return CurRecord.CentreBox_I02;
    if(ValName=="CentreBox_I03") return CurRecord.CentreBox_I03;
    if(ValName=="CentreBox_bak1") return CurRecord.CentreBox_bak1;
    if(ValName=="CentreBox_bak2") return CurRecord.CentreBox_bak2;
    if(ValName=="CentreBox_bak3") return CurRecord.CentreBox_bak3;

    if(ValName=="MechCtrolBox_U01") return CurRecord.MechCtrolBox_U01;
    if(ValName=="MechCtrolBox_U02") return CurRecord.MechCtrolBox_U02;
    if(ValName=="MechCtrolBox_U03") return CurRecord.MechCtrolBox_U03;
    if(ValName=="MechCtrolBox_U04") return CurRecord.MechCtrolBox_U04;
    if(ValName=="MechCtrolBox_U05") return CurRecord.MechCtrolBox_U05;
    if(ValName=="MechCtrolBox_U06") return CurRecord.MechCtrolBox_U06;
    if(ValName=="MechCtrolBox_U07") return CurRecord.MechCtrolBox_U07;
    if(ValName=="MechCtrolBox_U08") return CurRecord.MechCtrolBox_U08;
    if(ValName=="MechCtrolBox_U09") return CurRecord.MechCtrolBox_U09;
    if(ValName=="MechCtrolBox_U10") return CurRecord.MechCtrolBox_U10;
    if(ValName=="MechCtrolBox_U11") return CurRecord.MechCtrolBox_U11;
    if(ValName=="MechCtrolBox_U12") return CurRecord.MechCtrolBox_U12;
    if(ValName=="MechCtrolBox_U13") return CurRecord.MechCtrolBox_U13;
    if(ValName=="MechCtrolBox_U14") return CurRecord.MechCtrolBox_U14;
    if(ValName=="MechCtrolBox_U15") return CurRecord.MechCtrolBox_U15;
    if(ValName=="MechCtrolBox_U16") return CurRecord.MechCtrolBox_U16;
    if(ValName=="MechCtrolBox_U17") return CurRecord.MechCtrolBox_U17;
    if(ValName=="MechCtrolBox_U18") return CurRecord.MechCtrolBox_U18;
    if(ValName=="MechCtrolBox_U19") return CurRecord.MechCtrolBox_U19;
    if(ValName=="MechCtrolBox_U20") return CurRecord.MechCtrolBox_U20;
    if(ValName=="MechCtrolBox_U21") return CurRecord.MechCtrolBox_U21;
    if(ValName=="MechCtrolBox_U22") return CurRecord.MechCtrolBox_U22;
    if(ValName=="MechCtrolBox_bak1") return CurRecord.MechCtrolBox_bak1;
    if(ValName=="MechCtrolBox_bak2") return CurRecord.MechCtrolBox_bak2;
    if(ValName=="MechCtrolBox_bak3") return CurRecord.MechCtrolBox_bak3;

    if(ValName=="BackPump_U01") return CurRecord.BackPump_U01;
    if(ValName=="BackPump_U02") return CurRecord.BackPump_U02;
    if(ValName=="BackPump_U03") return CurRecord.BackPump_U03;
    if(ValName=="BackPump_U04") return CurRecord.BackPump_U04;
    if(ValName=="BackPump_U05") return CurRecord.BackPump_U05;
    if(ValName=="BackPump_U06") return CurRecord.BackPump_U06;
    if(ValName=="BackPump_U07") return CurRecord.BackPump_U07;
    if(ValName=="BackPump_U08") return CurRecord.BackPump_U08;
    if(ValName=="BackPump_U09") return CurRecord.BackPump_U09;
    if(ValName=="BackPump_U10") return CurRecord.BackPump_U10;
    if(ValName=="BackPump_U11") return CurRecord.BackPump_U11;
    if(ValName=="BackPump_U12") return CurRecord.BackPump_U12;
    if(ValName=="BackPump_U13") return CurRecord.BackPump_U13;
    if(ValName=="BackPump_bak1") return CurRecord.BackPump_bak1;
    if(ValName=="BackPump_bak2") return CurRecord.BackPump_bak2;
    if(ValName=="BackPump_bak3") return CurRecord.BackPump_bak3;

    if(ValName=="ImprovePump_U01") return CurRecord.ImprovePump_U01;
    if(ValName=="ImprovePump_U02") return CurRecord.ImprovePump_U02;
    if(ValName=="ImprovePump_U03") return CurRecord.ImprovePump_U03;
    if(ValName=="ImprovePump_U04") return CurRecord.ImprovePump_U04;
    if(ValName=="ImprovePump_U05") return CurRecord.ImprovePump_U05;
    if(ValName=="ImprovePump_U06") return CurRecord.ImprovePump_U06;
    if(ValName=="ImprovePump_U07") return CurRecord.ImprovePump_U07;
    if(ValName=="ImprovePump_U08") return CurRecord.ImprovePump_U08;
    if(ValName=="ImprovePump_U09") return CurRecord.ImprovePump_U09;
    if(ValName=="ImprovePump_U10") return CurRecord.ImprovePump_U10;
    if(ValName=="ImprovePump_U11") return CurRecord.ImprovePump_U11;
    if(ValName=="ImprovePump_U12") return CurRecord.ImprovePump_U12;
    if(ValName=="ImprovePump_U13") return CurRecord.ImprovePump_U13;
    if(ValName=="ImprovePump_bak1") return CurRecord.ImprovePump_bak1;
    if(ValName=="ImprovePump_bak2") return CurRecord.ImprovePump_bak2;
    if(ValName=="ImprovePump_bak3") return CurRecord.ImprovePump_bak3;

    if(ValName=="CentreBox_PARA1") return CurRecord.CentreBox_PARA1;
    if(ValName=="CentreBox_PARA2") return CurRecord.CentreBox_PARA2;
    if(ValName=="CentreBox_PARA3") return CurRecord.CentreBox_PARA3;
    if(ValName=="CentreBox_PARA4") return CurRecord.CentreBox_PARA4;
    if(ValName=="CentreBox_PARA5") return CurRecord.CentreBox_PARA5;
    if(ValName=="CentreBox_PARA6") return CurRecord.CentreBox_PARA6;
    if(ValName=="CentreBox_PARA7") return CurRecord.CentreBox_PARA7;
    if(ValName=="CentreBox_PARA8") return CurRecord.CentreBox_PARA8;
    if(ValName=="CentreBox_PARA9") return CurRecord.CentreBox_PARA9;
    if(ValName=="CentreBox_PARA10") return CurRecord.CentreBox_PARA10;
    if(ValName=="CentreBox_PARA11") return CurRecord.CentreBox_PARA11;
    if(ValName=="CentreBox_PARA12") return CurRecord.CentreBox_PARA12;
    if(ValName=="CentreBox_PARA13") return CurRecord.CentreBox_PARA13;
    if(ValName=="CentreBox_PARA_bak1") return CurRecord.CentreBox_PARA_bak1;
    if(ValName=="CentreBox_PARA_bak2") return CurRecord.CentreBox_PARA_bak2;
    if(ValName=="CentreBox_PARA_bak3") return CurRecord.CentreBox_PARA_bak3;

    if(ValName=="MechCtrolBox_PARA1") return CurRecord.MechCtrolBox_PARA1;
    if(ValName=="MechCtrolBox_PARA2") return CurRecord.MechCtrolBox_PARA2;
    if(ValName=="MechCtrolBox_PARA3") return CurRecord.MechCtrolBox_PARA3;
    if(ValName=="MechCtrolBox_PARA4") return CurRecord.MechCtrolBox_PARA4;
    if(ValName=="MechCtrolBox_PARA5") return CurRecord.MechCtrolBox_PARA5;
    if(ValName=="MechCtrolBox_PARA6") return CurRecord.MechCtrolBox_PARA6;
    if(ValName=="MechCtrolBox_PARA7") return CurRecord.MechCtrolBox_PARA7;
    if(ValName=="MechCtrolBox_PARA8") return CurRecord.MechCtrolBox_PARA8;
    if(ValName=="MechCtrolBox_PARA9") return CurRecord.MechCtrolBox_PARA9;
    if(ValName=="MechCtrolBox_PARA10") return CurRecord.MechCtrolBox_PARA10;
    if(ValName=="MechCtrolBox_PARA11") return CurRecord.MechCtrolBox_PARA11;
    if(ValName=="MechCtrolBox_PARA12") return CurRecord.MechCtrolBox_PARA12;
    if(ValName=="MechCtrolBox_PARA13") return CurRecord.MechCtrolBox_PARA13;
    if(ValName=="MechCtrolBox_PARA14") return CurRecord.MechCtrolBox_PARA14;
    if(ValName=="MechCtrolBox_PARA15") return CurRecord.MechCtrolBox_PARA15;
    if(ValName=="MechCtrolBox_PARA16") return CurRecord.MechCtrolBox_PARA16;
    if(ValName=="MechCtrolBox_PARA17") return CurRecord.MechCtrolBox_PARA17;
    if(ValName=="MechCtrolBox_PARA18") return CurRecord.MechCtrolBox_PARA18;
    if(ValName=="MechCtrolBox_PARA19") return CurRecord.MechCtrolBox_PARA19;
    if(ValName=="MechCtrolBox_PARA20") return CurRecord.MechCtrolBox_PARA20;
    if(ValName=="MechCtrolBox_PARA21") return CurRecord.MechCtrolBox_PARA21;
    if(ValName=="MechCtrolBox_PARA22") return CurRecord.MechCtrolBox_PARA22;
    if(ValName=="MechCtrolBox_PARA23") return CurRecord.MechCtrolBox_PARA23;
    if(ValName=="MechCtrolBox_PARA24") return CurRecord.MechCtrolBox_PARA24;
    if(ValName=="MechCtrolBox_PARA25") return CurRecord.MechCtrolBox_PARA25;
    if(ValName=="MechCtrolBox_PARA26") return CurRecord.MechCtrolBox_PARA26;
    if(ValName=="MechCtrolBox_PARA27") return CurRecord.MechCtrolBox_PARA27;
    if(ValName=="MechCtrolBox_PARA28") return CurRecord.MechCtrolBox_PARA28;
    if(ValName=="MechCtrolBox_PARA29") return CurRecord.MechCtrolBox_PARA29;
    if(ValName=="MechCtrolBox_PARA30") return CurRecord.MechCtrolBox_PARA30;
    if(ValName=="MechCtrolBox_PARA31") return CurRecord.MechCtrolBox_PARA31;
    if(ValName=="MechCtrolBox_PARA32") return CurRecord.MechCtrolBox_PARA32;
    if(ValName=="MechCtrolBox_PARA_bak1") return CurRecord.MechCtrolBox_PARA_bak1;
    if(ValName=="MechCtrolBox_PARA_bak2") return CurRecord.MechCtrolBox_PARA_bak2;
    if(ValName=="MechCtrolBox_PARA_bak3") return CurRecord.MechCtrolBox_PARA_bak3;


    if(ValName=="BackPump_PARA1") return CurRecord.BackPump_PARA1;
    if(ValName=="BackPump_PARA2") return CurRecord.BackPump_PARA2;
    if(ValName=="BackPump_PARA3") return CurRecord.BackPump_PARA3;
    if(ValName=="BackPump_PARA4") return CurRecord.BackPump_PARA4;
    if(ValName=="BackPump_PARA5") return CurRecord.BackPump_PARA5;
    if(ValName=="BackPump_PARA6") return CurRecord.BackPump_PARA6;
    if(ValName=="BackPump_PARA_bak1") return CurRecord.BackPump_PARA_bak1;
    if(ValName=="BackPump_PARA_bak2") return CurRecord.BackPump_PARA_bak2;
    if(ValName=="BackPump_PARA_bak3") return CurRecord.BackPump_PARA_bak3;

    if(ValName=="ImprovePump_PARA1") return CurRecord.ImprovePump_PARA1;
    if(ValName=="ImprovePump_PARA2") return CurRecord.ImprovePump_PARA2;
    if(ValName=="ImprovePump_PARA3") return CurRecord.ImprovePump_PARA3;
    if(ValName=="ImprovePump_PARA4") return CurRecord.ImprovePump_PARA4;
    if(ValName=="ImprovePump_PARA5") return CurRecord.ImprovePump_PARA5;
    if(ValName=="ImprovePump_PARA6") return CurRecord.ImprovePump_PARA6;
    if(ValName=="ImprovePump_PARA_bak1") return CurRecord.ImprovePump_PARA_bak1;
    if(ValName=="ImprovePump_PARA_bak2") return CurRecord.ImprovePump_PARA_bak2;
    if(ValName=="ImprovePump_PARA_bak3") return CurRecord.ImprovePump_PARA_bak3;

    if(ValName=="Hydro_PARA1") return CurRecord.Hydro_PARA1;
    if(ValName=="Hydro_PARA2") return CurRecord.Hydro_PARA2;
    if(ValName=="Hydro_PARA3") return CurRecord.Hydro_PARA3;
    if(ValName=="Hydro_PARA4") return CurRecord.Hydro_PARA4;
    if(ValName=="Hydro_PARA5") return CurRecord.Hydro_PARA5;
    if(ValName=="Hydro_PARA6") return CurRecord.Hydro_PARA6;
    if(ValName=="Hydro_PARA7") return CurRecord.Hydro_PARA7;
    if(ValName=="Hydro_PARA8") return CurRecord.Hydro_PARA8;
    if(ValName=="Hydro_PARA9") return CurRecord.Hydro_PARA9;
    if(ValName=="Hydro_PARA10") return CurRecord.Hydro_PARA10;
    if(ValName=="Hydro_PARA11") return CurRecord.Hydro_PARA11;
    if(ValName=="Hydro_PARA12") return CurRecord.Hydro_PARA12;
    if(ValName=="Hydro_PARA13") return CurRecord.Hydro_PARA13;
    if(ValName=="Hydro_PARA14") return CurRecord.Hydro_PARA14;
    if(ValName=="Hydro_PARA15") return CurRecord.Hydro_PARA15;
    if(ValName=="Hydro_PARA16") return CurRecord.Hydro_PARA16;
    if(ValName=="Hydro_PARA_bak1") return CurRecord.Hydro_PARA_bak1;
    if(ValName=="Hydro_PARA_bak2") return CurRecord.Hydro_PARA_bak2;
    if(ValName=="Hydro_PARA_bak3") return CurRecord.Hydro_PARA_bak3;
    return RetVal;
}

void MainWindow::GetCurveData(int GraphIdx,double key)
{
    //根据地址找到对应的值
    int i;
    float Val,tmpVal;

    for(i=0;i<LineCount;i++)
    {
        if(!stDraw[i].IsVisible) continue;
        Val=GetVarVal(stDraw[i].Var_Name);
        //qDebug()<<"LineCount="<<LineCount[j]<<"Val= "<<Val<<"SFCoef="<<stDraw[j][i].SFCoef<<"PYVal="<<stDraw[j][i].PYVal;
        tmpVal=Val*1.0*stDraw[i].SFCoef+stDraw[i].PYVal;
        //qDebug()<<"TimeIdx="<<TimeIdx<<"tmpVal"<<tmpVal;
        try
        {
            if(CurveMode==0)//历史曲线
            {
                ui->customPlot->graph(i)->addData(TimeIdx,tmpVal);
                if(CurYMax<tmpVal)
                {
                    CurYMax=tmpVal+100;
                    ui->customPlot->yAxis->setRange(CurYMin,CurYMax);
                    ui->customPlot->replot();

                }
                if(CurYMin>tmpVal)
                {
                    CurYMin=tmpVal-100;
                    ui->customPlot->yAxis->setRange(CurYMin,CurYMax);
                    ui->customPlot->replot();
                }
            }
            else if(CurveMode==1)//实时曲线
            {
                ui->customPlot->graph(i)->addData(key,tmpVal);
                ui->customPlot->replot();
            }

        }
        catch(...)
        {
        }
    }
    TimeIdx+=0.2*5/HzVal;

}


void MainWindow::LoadFile(QString InitFileName,int GraphIdx)
{
    //FILE *in;
    int ret,k,nn2;
    QString FileName;
    bool FisrtBlock;
    int StartSec=0,StartMSec=0,EndSec=0,EndMSec=0,CurReadMin=0;
    bool FisrtLargeBlock;


    int TotalTimeOfFile=-1;

    if(InitFileName=="") {qDebug()<<"文件名为空";return;}
    FileName=DATA_SAVE_DISK+InitFileName;
    QFile My_File(FileName);
    if(!My_File.exists()) return;//{QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件不存在"),QMessageBox::Yes,QMessageBox::Yes);return;}
    if(!My_File.open(QIODevice::ReadWrite)){QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件打开失败"),QMessageBox::Yes,QMessageBox::Yes);return;}
    //in=fopen(FileName.toUtf8().data(),"rb");
    //if(in==NULL) {qDebug()<<"文件打开失败"; return;  }
    TotalTimeOfFile= My_File.size()/sizeof(ST_DR_FILEBUF);  //表示有多少分钟数据
    qDebug()<<"TotalTimeOfFile="<<TotalTimeOfFile;
    //注意，由于实际开始时可能从一分钟的中间时刻开始记录，数据块中有空白
    if(TotalTimeOfFile<=0) {My_File.close(); qDebug()<<"无效的数据文件";return;}
    My_File.close();
    FisrtBlock=true;
    TimeIdx=0;
    FisrtLargeBlock=true;
    //清除曲线
    for(nn2=0;nn2<LineCount;nn2++)
    {
        ui->customPlot->graph(nn2)->clearData();//series[i].clear();//ChartX->Series[i]->Clear()
        ui->customPlot->graph(nn2)->setName(stDraw[nn2].Var_Name);
    }
    for(nn2=LineCount;nn2<MAX_LINE_CNT;nn2++)
    {
        ui->customPlot->graph(nn2)->clearData();
        ui->customPlot->graph(nn2)->setName("");
    }
    CurYMax=10;
    CurYMin=-10;
    ui->customPlot->yAxis->setRange(CurYMin,CurYMax);
    ui->customPlot->replot();

    //清除曲线总分钟数
    TotalTimeOfGraph=0;

    if(!My_File.open(QIODevice::ReadWrite)){QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件打开失败"),QMessageBox::Yes,QMessageBox::Yes);return;}
    My_File.seek(0);
    while(1)
    {
        //ret=fread(&CurFileBuf,sizeof(CurFileBuf),1,in);
        My_File.seek(CurReadMin*sizeof(CurFileBuf));
        ret=My_File.read((char *)(&CurFileBuf),sizeof(CurFileBuf));
        CurReadMin++;
        if(ret==0) break;//读完了
        TotalTimeOfGraph++;
        //if(CurFileBuf.DataDR[0].DATA_VERSION!=6) {ShowMessage("数据文件版本 ="+IntToStr(CurFileBuf.DataDR[0].DATA_VERSION)+" 不正确,BLOCK="+IntToStr(BlockCnt)); break;}

        StartSec=CurFileBuf.StartSecond;
        StartMSec=CurFileBuf.StartmSec;
        EndSec=CurFileBuf.EndSecond;
        EndMSec=CurFileBuf.EndmSec;
        if(FisrtLargeBlock)
        {
            FisrtLargeBlock=false;
            //填写初始记录时刻
            ui->LbStartTime->setText(GetTimeStr(CurFileBuf.Minute ,CurFileBuf.StartSecond,CurFileBuf.StartmSec));
        }
        ui->LbFinishTime->setText(GetTimeStr(CurFileBuf.Minute ,CurFileBuf.EndSecond,CurFileBuf.EndmSec));
        k=0;
        while(k<600)
        {
            CurRecord=CurFileBuf.DataDR[k];
            GetCurveData(GraphIdx,0);
            if(FisrtBlock)
            {
                FisrtBlock=false;
            }
            StartMSec+=1000/HzVal; //过半秒
            if(StartMSec>=1000) { StartMSec-=1000;  StartSec++;}  //加一秒
            if(StartSec>=60) break;//一分钟已经完成
            if(CurReadMin==TotalTimeOfFile)
            {
                if((StartSec*1000+StartMSec)>(EndSec*1000+EndMSec))  break;
            }
            k+=10/HzVal;
        }
    }//end of while(1)
    My_File.close();
    ui->customPlot->xAxis->setRange(0,TimeIdx);
    ui->customPlot->replot();
}

void MainWindow::InitChart()//0:历史曲线 1：实时曲线
{
    myMapper = new QSignalMapper();
    ui->customPlot->installEventFilter(this);//widget控件安装事件过滤器
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString << tr("") <<tr("文件名称");
    TableWidgetQss(headerString,ui->TblDRList,StretchHorizontalIndex);
    ui->TblDRList->setColumnWidth(0,30);
    ui->TblDRList->setColumnWidth(1,320);

    headerString.clear();
    headerString<<"信号名称"<<"单位"<<"注释"<<"地址";
    TableWidgetQss(headerString,ui->TblPara,StretchHorizontalIndex);
    ui->TblPara->setColumnWidth(0,300);//信号名称
    ui->TblPara->setColumnWidth(1,80);//单位
    ui->TblPara->setColumnWidth(2,350);//注释

    setupSimpleDemo(ui->customPlot);//历史曲线
    ui->customPlot->installEventFilter(this);//widget控件安装事件过滤器
}


void MainWindow::TableWidgetQss(QStringList headerString, QTableWidget *TableWidget, QList<int> StretchHorizontalIndex)
{

    QString tableWidgetStyleSheet = "QTableWidget{border:0px;"
                                    "background-color: rgba(255, 255, 255, 0.2);"
                                    "alternate-background-color: rgba(243, 248, 251, 0.2);"
                                    "color: rgb(0, 0, 0);font: 14pt '微软雅黑';}"
                                    "QTableWidget::item:selected{"
                                    "color: rgb(0, 0, 0);"
                                    "background-color: rgba(191, 223, 252, 0.2);}"
                                    "QHeaderView::section{"
                                    "border:1px solid rgba(19, 67, 79, 1);"
                                    "background-color: rgba(19, 67, 79, 1);"
                                    "height: 35px;font: 75 14pt '微软雅黑';color: rgba(102, 249, 247, 1);"
                                    "padding-left: 4px;"
                                    "text-align:center;}"
                                    "QTableWidget::indicator {width: 50px;height: 50px;}"
                                    "QTableWidget::indicator:unchecked {image: url(:/widget/No.png);}"
                                    "QTableWidget::indicator:checked {image: url(:/widget/Yes.png);}"
                                    "QTableWidget::item{padding-top:15px;padding-bottom:15px;}";

    TableWidget->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    TableWidget->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选
    TableWidget->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色
    //设置表格的默认的列数
    TableWidget->setColumnCount(headerString.count());//设置列数
    TableWidget->setHorizontalHeaderLabels(headerString);//设置列标题

    for(int i=0;i<StretchHorizontalIndex.size();i++)
        TableWidget->horizontalHeader()->setSectionResizeMode(StretchHorizontalIndex[i], QHeaderView::Stretch);

    TableWidget->setAlternatingRowColors(true);//使表格颜色交错功能为真
    TableWidget->setFocusPolicy(Qt::NoFocus);
    TableWidget->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    TableWidget->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑
    TableWidget->setWordWrap(true);
}

void MainWindow::setupSimpleDemo(QCustomPlot *customPlot)
{
    //qDebug()<<"Simple Demo";

    // add two new graphs and set their look:添加两个新图形并设置它们的外观：
    customPlot->addGraph();
    customPlot->graph(0)->setPen(QPen(Qt::green)); // line color blue for first graph第一个图形的线颜色为蓝色
    customPlot->graph(0)->setBrush(QBrush(QColor(0, 0, 255, 20))); // first graph will be filled with translucent blue
    //customPlot->graph(0)->setVisible(false);
    customPlot->addGraph();                                        //第一个图形将填充半透明的蓝色
    customPlot->graph(1)->setPen(QPen(Qt::red)); // line color red for second graph第二张图的红色线条
    //customPlot->graph(1)->setVisible(false);
    customPlot->addGraph();
    customPlot->graph(2)->setPen(QPen(Qt::blue));
    //customPlot->graph(2)->setVisible(false);
    customPlot->addGraph();
    customPlot->graph(3)->setPen(QPen(Qt::yellow));
    //customPlot->graph(3)->setVisible(false);
    customPlot->addGraph();
    customPlot->graph(4)->setPen(QPen(Qt::cyan));
    //customPlot->graph(4)->setVisible(false);
    customPlot->addGraph();
    customPlot->graph(5)->setPen(QPen(Qt::magenta));
    customPlot->addGraph();
    customPlot->graph(6)->setPen(QPen(Qt::gray));
    customPlot->addGraph();
    customPlot->graph(7)->setPen(QPen(Qt::black));

    //   customPlot->graph(1)->setVisible(ui->CbSA2His->isChecked());
    customPlot->legend->setVisible(true);
    customPlot->legend->setBrush(QColor(255,255,255,0));//背景透明

    // configure right and top axis to show ticks but no labels:
    // (see QCPAxisRect::setupFullAxesBox for a quicker method to do this)
    //配置右上轴以显示刻度但不显示标签：
    //（请参阅QCPAxisRect：：setupFullAxesBox以获得更快的方法）
    //customPlot->xAxis2->setVisible(true);
    //customPlot->xAxis2->setTickLabels(false);
    //customPlot->yAxis2->setVisible(true);
    //customPlot->yAxis2->setTickLabels(false);
    // make left and bottom axes always transfer their ranges to right and top axes:
    //使左轴和下轴始终将其范围转移到右轴和上轴：
    //connect(customPlot->xAxis, SIGNAL(rangeChanged(QCPRange)), customPlot->xAxis2, SLOT(setRange(QCPRange)));
    //connect(customPlot->yAxis, SIGNAL(rangeChanged(QCPRange)), customPlot->yAxis2, SLOT(setRange(QCPRange)));
    // pass data points to graphs:
    //将数据点传递到图形：
    //customPlot->graph(0)->setData(x, y0);
    //customPlot->graph(1)->setData(x, y1);
    // let the ranges scale themselves so graph 0 fits perfectly in the visible area:
    //让范围自行缩放，以便图0完全适合可见区域：
    customPlot->graph(0)->rescaleAxes();
    // same thing for graph 1, but only enlarge ranges (in case graph 1 is smaller than graph 0):
    //对于图1也是一样，但只放大范围（如果图1小于图0）：
    customPlot->graph(1)->rescaleAxes(true);
    customPlot->graph(2)->rescaleAxes(true);
    customPlot->graph(3)->rescaleAxes(true);
    customPlot->graph(4)->rescaleAxes(true);
    customPlot->graph(5)->rescaleAxes(true);
    customPlot->graph(6)->rescaleAxes(true);
    customPlot->graph(7)->rescaleAxes(true);
    // Note: we could have also just called customPlot->rescaleAxes(); instead
    // Allow user to drag axis ranges with mouse, zoom with mouse wheel and select graphs by clicking:
    //注意：我们也可以调用customPlot->rescaleAxes（）；而不是
    //允许用户使用鼠标拖动轴范围，使用鼠标滚轮缩放并通过单击选择图形：
    customPlot->setInteractions(QCP::iRangeDrag | QCP::iRangeZoom | QCP::iSelectPlottables);

    //customPlot->xAxis->setRange(0, 600);
    //customPlot->yAxis->setRange(-32000, 32000);
}

void MainWindow::tableParaInit()
{
    /*
    QStringList headerText;
    QString tableWidgetStyleSheet = "QTableWidget{border:0px;"
                            "background-color: rgba(255, 255, 255, 1);"
                            "alternate-background-color: rgba(243, 248, 251, 1);"
                            "color: rgb(0, 0, 0);font: 14pt '微软雅黑';}"
                            "QTableWidget::item:selected{"
                            "color: rgb(0, 0, 0);"
                            "background-color: rgba(191, 223, 252, 1);}";

    ui->TblPara->horizontalHeader()->setStyleSheet("QHeaderView::section{"
                                                               "border:1px solid rgba(216, 216, 216, 1);"
                                                               "background-color: rgba(35, 147, 223, 1);"
                                                               "height: 50px;font: 75 14pt '微软雅黑';color: rgb(255, 255, 255);"
                                                               "padding-left: 4px;"
                                                               "text-align:center;}");

    ui->TblPara->verticalHeader()->setStyleSheet("QHeaderView::section{"
                                                               "border:1px solid rgba(216, 216, 216, 1);"
                                                               "background-color: rgba(35, 147, 223, 1);"
                                                               "width: 70px;font: 75 14pt '微软雅黑';color: rgb(255, 255, 255);"
                                                               "padding-left: 4px;"
                                                               "text-align:center;}");

    ui->TblPara->verticalHeader()->setDefaultSectionSize(60);//设置默认行高
    ui->TblPara->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选
    ui->TblPara->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色
    ui->TblPara->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->TblPara->setFocusPolicy(Qt::NoFocus);
    ui->TblPara->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->TblPara->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑

    //--------------设置表头--------------------
    ui->TblPara->clear();
    ui->TblPara->verticalHeader()->setVisible(false);
    ui->TblPara->verticalHeader()->setDefaultSectionSize(50);//设置默认行高

    ui->TblPara->setRowCount(0); //设置行数
    headerText<<"信号名称"<<"单位"<<"注释"<<"地址";

    ui->TblPara->setColumnCount(3);//列数设置为与 headerText的行数相等
    ui->TblPara->setHorizontalHeaderLabels(headerText);
    ui->TblPara->horizontalHeader()->setVisible(true);
    ui->TblPara->setColumnWidth(0,200);//信号名称
    ui->TblPara->setColumnWidth(1,80);//单位
    ui->TblPara->setColumnWidth(2,350);//注释
    //ui->TblPara->setColumnWidth(3,350);//地址
    ui->TblPara->clearContents();//只清除工作区，不清除表头
*/

    QStringList ListParaName,ListParaDW,ListParaRemark;
    for(int i=0;i<9;i++) {ListParaName.append("CentreBox_U0"+QString::number(i+1));ListParaDW.append("0.1V");}
    ListParaName<<"CentreBox_U10"<<"CentreBox_I01"<<"CentreBox_I02"<<"CentreBox_I03"<<"CentreBox_bak1"<<"CentreBox_bak2"<<"CentreBox_bak3";
    ListParaDW<<"0.1V"<<"0.1A"<<"0.1A"<<"0.1A"<<""<<""<<"";
    for(int i=0;i<9;i++) {ListParaName.append("MechCtrolBox_U0"+QString::number(i+1));ListParaDW.append("0.1V");}
    for(int i=0;i<10;i++) {ListParaName.append("MechCtrolBox_U1"+QString::number(i));ListParaDW.append("0.1V");}
    ListParaName<<"MechCtrolBox_U20"<<"MechCtrolBox_U21"<<"MechCtrolBox_U22"<<"MechCtrolBox_bak1"<<"MechCtrolBox_bak2"<<"MechCtrolBox_bak3";
    ListParaDW<<"0.1V"<<"0.1V"<<"0.1V"<<""<<""<<"";
    for(int i=0;i<9;i++) {ListParaName.append("BackPump_U0"+QString::number(i+1));ListParaDW.append("0.1V");}
    ListParaName<<"BackPump_U10"<<"BackPump_U11"<<"BackPump_U12"<<"BackPump_U13"<<"BackPump_bak1"<<"BackPump_bak2"<<"BackPump_bak3";
    ListParaDW<<"0.1V"<<"0.1V"<<"0.1V"<<"0.1V"<<""<<""<<"";
    for(int i=0;i<9;i++) {ListParaName.append("ImprovePump_U0"+QString::number(i+1));ListParaDW.append("0.1V");}
    ListParaName<<"ImprovePump_U10"<<"ImprovePump_U11"<<"ImprovePump_U12"<<"ImprovePump_U13"<<"ImprovePump_bak1"<<"ImprovePump_bak2"<<"ImprovePump_bak3";
    ListParaDW<<"0.1V"<<"0.1V"<<"0.1V"<<"0.1V"<<""<<""<<"";
    for(int i=0;i<13;i++) ListParaName.append("CentreBox_PARA"+QString::number(i+1));
    ListParaDW<<""<<""<<""<<""<<""<<""<<""<<""<<"0.1mA"<<"0.1mA"<<"0.1mA"<<"0.1"<<"0.1mA"<<""<<""<<"";
    ListParaName<<"CentreBox_PARA_bak1"<<"CentreBox_PARA_bak2"<<"CentreBox_PARA_bak3";
    for(int i=0;i<32;i++) ListParaName.append("MechCtrolBox_PARA"+QString::number(i+1));
    for(int i=0;i<23;i++) ListParaDW<<"";
    ListParaDW<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"mm"<<"0.1V"<<"℃"<<"0.1mA"<<""<<""<<""<<"";
    ListParaName<<"MechCtrolBox_PARA_bak1"<<"MechCtrolBox_PARA_bak2"<<"MechCtrolBox_PARA_bak3";
    for(int i=0;i<6;i++) ListParaName.append("BackPump_PARA"+QString::number(i+1));
    ListParaDW<<""<<""<<"mA"<<""<<""<<"";
    ListParaName<<"BackPump_PARA_bak1"<<"BackPump_PARA_bak2"<<"BackPump_PARA_bak3";
    ListParaDW<<""<<""<<"";
    for(int i=0;i<6;i++) ListParaName.append("ImprovePump_PARA"+QString::number(i+1));
    ListParaDW<<""<<""<<"mA"<<""<<""<<"";
    ListParaName<<"ImprovePump_PARA_bak1"<<"ImprovePump_PARA_bak2"<<"ImprovePump_PARA_bak3";
    ListParaDW<<""<<""<<"";
    for(int i=0;i<16;i++) ListParaName.append("Hydro_PARA"+QString::number(i+1));
    ListParaDW<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"MPa"<<"L/min"<<"L/min"<<"L/min"<<"L/min"<<"L/min"<<"%";
    ListParaName<<"Hydro_PARA_bak1"<<"Hydro_PARA_bak2"<<"Hydro_PARA_bak3";
    ListParaDW<<""<<""<<"";

    ListParaRemark.append("外部电源入口端电压信号");
    ListParaRemark.append("熔断器端口电源电压信号");
    ListParaRemark.append("EMI滤波器端口电源电压信号");
    ListParaRemark.append("开关端口电压信号");
    ListParaRemark.append("电源稳压模块端口输出电压信号");
    ListParaRemark.append("PLC输出比例阀控制电压信号");
    ListParaRemark.append("比例阀控制输出开关端口处电压信号");
    ListParaRemark.append("比例放大板信号输入端口电压");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("指令信号输入端口电流信号");
    ListParaRemark.append("反馈信号输入端口电流信号");
    ListParaRemark.append("反馈信号输出端口电流信号");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("外部电源入口端电压信号");
    ListParaRemark.append("熔断器1端口电源电压信号");
    ListParaRemark.append("EMI滤波器端口输出电压信号");
    ListParaRemark.append("开关SA端口电压信号");
    ListParaRemark.append("电源稳压模块端口输出电压信号");
    ListParaRemark.append("电位器1端口电压输出信号");
    ListParaRemark.append("电位器2端口电压输出信号");
    ListParaRemark.append("熔断器2端口电源电压信号");
    ListParaRemark.append("备用控制按钮端口电压信号");
    ListParaRemark.append("备用控制使能端口电压信号");
    ListParaRemark.append("备用正车按钮端口电压信号");
    ListParaRemark.append("备用倒车按钮端口电压信号");
    ListParaRemark.append("备用正倒车使能端口电压信号");
    ListParaRemark.append("本地控制按钮端口电压信号");
    ListParaRemark.append("本地正车按钮端口电压信号");
    ListParaRemark.append("本地倒车按钮端口电压信号");
    ListParaRemark.append("本地正倒车使能端口电压信号");
    ListParaRemark.append("双联泵卸荷端口电压信号");
    ListParaRemark.append("正车电磁阀端口电压信号");
    ListParaRemark.append("倒车电磁阀端口电压信号");
    ListParaRemark.append("卸荷电磁阀端口电压信号");
    ListParaRemark.append("PTO泵卸荷电磁阀端口电压信号");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("控制电路电源电压信号");
    ListParaRemark.append("电机运行信号");
    ListParaRemark.append("电机运行指示信号");
    ListParaRemark.append("本控/遥控状态信号");
    ListParaRemark.append("本控状态下启动按钮和运行保持信号");
    ListParaRemark.append("启动继电器控制信号");
    ListParaRemark.append("遥控状态下自动和手动信号");
    ListParaRemark.append("本控/遥控状态信号");
    ListParaRemark.append("遥控状态下自动控制使能信号");
    ListParaRemark.append("遥控状态自动控制下启动继电器信号");
    ListParaRemark.append("压力继电器状态信号");
    ListParaRemark.append("电机故障信号");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("控制电路电源电压信号");
    ListParaRemark.append("电机运行信号");
    ListParaRemark.append("液位低信号");
    ListParaRemark.append("本控/遥控状态信号");
    ListParaRemark.append("本控状态下使能信号");
    ListParaRemark.append("启动继电器控制信号");
    ListParaRemark.append("遥控状态信号");
    ListParaRemark.append("港口模式使能信号");
    ListParaRemark.append("港口和航行模式状态信号");
    ListParaRemark.append("液位高位状态信号");
    ListParaRemark.append("电机故障信号");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("备用控制信号");
    ListParaRemark.append("机旁就地控制信号");
    ListParaRemark.append("零螺距状态信号");
    ListParaRemark.append("闭环控制信号");
    ListParaRemark.append("闭环电磁阀正车信号");
    ListParaRemark.append("闭环电磁阀倒车信号");
    ListParaRemark.append("闭环卸荷阀信号");
    ListParaRemark.append("控制系统故障信号");
    ListParaRemark.append("初始硬线螺距指令");
    ListParaRemark.append("初始螺距反馈信号");
    ListParaRemark.append("螺距反馈指示信号");
    ListParaRemark.append("比例阀控制输出信号");
    ListParaRemark.append("螺距反馈信号");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("备用控制信号");
    ListParaRemark.append("备用正车控制信号");
    ListParaRemark.append("备用倒车控制信号");
    ListParaRemark.append("本地控制信号");
    ListParaRemark.append("本地正车控制信号");
    ListParaRemark.append("本地倒车控制信号");
    ListParaRemark.append("PTO泵卸荷信号");
    ListParaRemark.append("备用泵遥控信号");
    ListParaRemark.append("备用泵电源信号");
    ListParaRemark.append("备用泵电机运行故障信号");
    ListParaRemark.append("提升泵电源信号");
    ListParaRemark.append("提升泵运行信号");
    ListParaRemark.append("提升泵遥控信号");
    ListParaRemark.append("提升泵运行故障信号");
    ListParaRemark.append("重力油箱液位低信号");
    ListParaRemark.append("PTO泵出口滤器堵塞状态信号");
    ListParaRemark.append("主油泵出口滤器堵塞状态信号");
    ListParaRemark.append("主油泵出口滤器堵塞状态信号");
    ListParaRemark.append("PTO一级泵运行信号");
    ListParaRemark.append("PTO二级泵运行信号");
    ListParaRemark.append("主油箱液位低信号");
    ListParaRemark.append("主电源失电信号");
    ListParaRemark.append("备用电源失电信号");
    ListParaRemark.append("系统油压传感器信号");
    ListParaRemark.append("A口油压传感器信号");
    ListParaRemark.append("B口油压传感器信号");
    ListParaRemark.append("静压腔油压传感器信号");
    ListParaRemark.append("主油箱液位传感器信号");
    ListParaRemark.append("比例阀阀芯位移信号");
    ListParaRemark.append("系统油温信号");
    ListParaRemark.append("初始螺距指示");
    ListParaRemark.append("备用泵运行");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("无");
    ListParaRemark.append("无");
    ListParaRemark.append("备用泵电机运行电流");
    ListParaRemark.append("无");
    ListParaRemark.append("无");
    ListParaRemark.append("备用泵电机保护器故障");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("无");
    ListParaRemark.append("无");
    ListParaRemark.append("提升泵电机运行电流");
    ListParaRemark.append("无");
    ListParaRemark.append("无");
    ListParaRemark.append("提升泵电机保护器故障");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("PZ1压力传感器");
    ListParaRemark.append("PZ2压力传感器");
    ListParaRemark.append("PZ3压力传感器");
    ListParaRemark.append("PZ4压力传感器");
    ListParaRemark.append("PZ5压力传感器");
    ListParaRemark.append("PZ6压力传感器");
    ListParaRemark.append("PZ7压力传感器");
    ListParaRemark.append("PZ8压力传感器");
    ListParaRemark.append("PZ9压力传感器");
    ListParaRemark.append("PT2压力传感器");
    ListParaRemark.append("FZ1流量传感器");
    ListParaRemark.append("FZ2流量传感器");
    ListParaRemark.append("FZ3流量传感器");
    ListParaRemark.append("FZ4流量传感器");
    ListParaRemark.append("FZ5流量传感器");
    ListParaRemark.append("FZ6流量传感器");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ListParaRemark.append("");
    ui->TblPara->setRowCount(ListParaName.count());
    for(int i=0;i<ListParaName.count();i++)
    {
        ui->TblPara->setItem(i,0,new  QTableWidgetItem(ListParaName.at(i)));//信号名称
        ui->TblPara->setItem(i,1,new  QTableWidgetItem(ListParaDW.at(i)));//单位
        ui->TblPara->setItem(i,2,new  QTableWidgetItem(ListParaRemark.at(i)));//注释
    }

}

void MainWindow::on_TblPara_doubleClicked(const QModelIndex &index)
{
    if(ui->LbFileName->text()=="")
    {
        QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("未打开有效的数据文件"),QMessageBox::Yes,QMessageBox::Yes);
        return;
    }
    if(LineCount>=MAX_LINE_CNT) return;
    stDraw[LineCount].Clr.setRgb(255,255,255);
    //stDraw[LineCount].ParaAddr=ui->TblPara->item(ui->TblPara->currentRow(),5)->text().toFloat();
    stDraw[LineCount].Var_Name=ui->TblPara->item(ui->TblPara->currentRow(),0)->text();//->Cells[1][SGridVR->Row];
    stDraw[LineCount].DW=ui->TblPara->item(ui->TblPara->currentRow(),1)->text();
    stDraw[LineCount].Var_Note=ui->TblPara->item(ui->TblPara->currentRow(),2)->text();
    //stDraw[LineCount].Var_Type=ui->TblPara->item(ui->TblPara->currentRow(),2)->text();
    //stDraw[LineCount].Var_Range=ui->TblPara->item(ui->TblPara->currentRow(),7)->text().toFloat();

    //stDraw[LineCount].Transform=ui->TblPara->item(ui->TblPara->currentRow(),8)->text()=="是"?true:false;
    stDraw[LineCount].IsVisible=true;
    //stDraw[LineCount].Var_Group=ui->TblPara->item(ui->TblPara->currentRow(),0)->text();

    ui->customPlot->graph(LineCount)->setVisible(true);
    ui->customPlot->graph(LineCount)->setName(stDraw[LineCount].Var_Name);
    LineCount++;

    //DrawGrd->Refresh();
    if(CurveMode==0) LoadFile(ui->LbFileName->text(),0);
}

void MainWindow::on_TblDRList_doubleClicked(const QModelIndex &index)
{
    CurveMode=0;
    ui->LbFileName->setText(ui->TblDRList->item(ui->TblDRList->currentRow(),1)->text());
    LoadFile(ui->LbFileName->text(),0);
    LoadDataInfo();
}

void MainWindow::LoadDataInfo()
{
    if(CurveMode!=0) return;//0:历史曲线 1：实时曲线
    ui->LbFileName->setText(ui->LbFileName->text());
    //打开文件，查看总时间
    if(ui->LbFileName->text()=="")
    {
        qDebug()<<"文件名为空";
        QMessageBox::information(NULL, QObject::tr("提示"), QObject::tr("文件名为空"), QMessageBox::Yes, QMessageBox::Yes);
        return;
    }
    QString FileName;
    FileName=DATA_SAVE_DISK+ui->LbFileName->text();

    QFile My_File(FileName);
    if(!My_File.exists()) {QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件不存在"),QMessageBox::Yes,QMessageBox::Yes);return;}
    if(!My_File.open(QIODevice::ReadWrite)){QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件打开失败"),QMessageBox::Yes,QMessageBox::Yes);return;}

    int TotalTimeOfFile= My_File.size()/sizeof(ST_DR_FILEBUF);

    //注意，由于实际开始时可能从一分钟的中间时刻开始记录，数据块中有空白
    if(TotalTimeOfFile<=0) {My_File.close(); qDebug()<<"无效的数据文件";return;}

    My_File.seek(sizeof(ST_DR_FILEBUF)*(TotalTimeOfFile-1));
    My_File.read((char *)(&CurFileBuf),sizeof(CurFileBuf));
    ui->EditTestInfo->clear();
    ui->EditTestInfo->appendPlainText( QString::fromUtf8(CurFileBuf.TestInfo));
    My_File.close();
}

void MainWindow::DrawSet()
{
    int i,j=0;
    //弹出曲线编辑窗口
    DrawGridSet *m_DrawGridSet=new DrawGridSet(this);
    m_DrawGridSet->setWindowTitle("参数曲线配置");
    for(i=0;i<LineCount;i++)
    {
        m_DrawGridSet->m_LbParaName[i]->setEnabled(true);
        m_DrawGridSet->m_LbParaName[i]->setText(stDraw[i].Var_Name);
        m_DrawGridSet->m_CbShow[i]->setEnabled(true);
        m_DrawGridSet->m_CbShow[i]->setChecked(stDraw[i].IsVisible);
        m_DrawGridSet->m_SpinPY[i]->setEnabled(true);
        m_DrawGridSet->m_SpinPY[i]->setValue(stDraw[i].PYVal);
        m_DrawGridSet->m_SpinSF[i]->setEnabled(true);
        m_DrawGridSet->m_SpinSF[i]->setValue(stDraw[i].SFCoef);
    }
    for(i=LineCount;i<MAX_LINE_CNT;i++)
    {
        m_DrawGridSet->m_LbParaName[i]->setEnabled(false);
        m_DrawGridSet->m_CbShow[i]->setEnabled(false);
        m_DrawGridSet->m_SpinPY[i]->setEnabled(false);
        m_DrawGridSet->m_SpinSF[i]->setEnabled(false);
    }
    if (m_DrawGridSet->exec()==QDialog::Accepted)
    {
        for(i=0;i<LineCount;i++)
        {
            if(m_DrawGridSet->m_CbShow[i]->isEnabled()) stDraw[j++]=stDraw[i];
        }
        LineCount=j;
        for(i=0;i<LineCount;i++)
        {
            stDraw[i].IsVisible=m_DrawGridSet->m_CbShow[i]->isChecked();
            stDraw[i].PYVal=m_DrawGridSet->m_SpinPY[i]->value();
            stDraw[i].SFCoef=m_DrawGridSet->m_SpinSF[i]->value();
        }
        LoadFile(ui->LbFileName->text(),0);
    }
    delete m_DrawGridSet;
}


void MainWindow::on_Btn_UpdateTestInfo_clicked()
{
    //FILE *in;
    QString CurFileName=ui->LbFileName->text();
    //打开文件，查看总时间
    if(CurFileName=="")   return;
    CurFileName=DATA_SAVE_DISK+CurFileName;

    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::question(this,"修改","是否修改试验记录？",
                                 QMessageBox::Yes|QMessageBox::No,defaultBtn);

    if(result!=QMessageBox::Yes) return;

    QFile My_File(CurFileName.toUtf8().data());
    if(!My_File.exists()) {QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件不存在"),QMessageBox::Yes,QMessageBox::Yes);return;}
    if(!My_File.open(QIODevice::ReadWrite)){QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件打开失败"),QMessageBox::Yes,QMessageBox::Yes);return;}

    int TotalTimeOfFile= My_File.size()/sizeof(ST_DR_FILEBUF);  //表示有多少分钟数据
    //注意，由于实际开始时可能从一分钟的中间时刻开始记录，数据块中有空白
    if(TotalTimeOfFile<=0)
    {
        My_File.close();
        qDebug()<<"无效的数据文件";
        return;
    }

    TimeIdx=0;
    My_File.seek(sizeof(ST_DR_FILEBUF)*(TotalTimeOfFile-1)+24);
    //fseek(in,sizeof(ST_DR_FILEBUF)*(TotalTimeOfFile-1)+24, SEEK_SET);
    strcpy(TestInfo,ui->EditTestInfo->toPlainText().toUtf8().data());
    //qDebug()<<QString::fromUtf8(TestInfo);
    My_File.write(TestInfo,sizeof(TestInfo));
    My_File.close();
}

void MainWindow::on_BtnToExcel_clicked()
{
    ToExcel();
}

void MainWindow::ToExcel()
{
    QTableWidget *m_TableWidget;
    m_TableWidget=ui->TblDRList;
    for(int i=0;i<m_TableWidget->rowCount();i++)
    {
        QCheckBox m_QCheckBox;
        if(((QCheckBox *)m_TableWidget->cellWidget(i,0))->isChecked())
        {
            m_TableWidget->selectRow(i);
            FileToExcel();
        }
    }
    QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("导出完成"),QMessageBox::Yes,QMessageBox::Yes);

}

void MainWindow::FileToExcel()
{
    qDebug()<<"in FileToExcel";
    QString InitFileName;
    InitFileName=ui->TblDRList->item(ui->TblDRList->currentRow(),1)->text();
    //读取DAT文件中的数据
    int ret;
    QString ParaNameStr;
    QString ValNameLine;//,ValNameLine1,ValNameLine2,ValNameLine3,ValNameLine4;
    QString mStr="";

    QString SelectedFileName,csvFileName,TimeStr;
    SelectedFileName=InitFileName;
    if(SelectedFileName=="") return;
    SelectedFileName=DATA_SAVE_DISK+SelectedFileName;
    QFile My_File(SelectedFileName);
    if(!My_File.exists()) {QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件不存在"),QMessageBox::Yes,QMessageBox::Yes);return;}
    if(!My_File.open(QIODevice::ReadWrite)){QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("文件打开失败"),QMessageBox::Yes,QMessageBox::Yes);return;}
    int TotalTimeOfFile= My_File.size()/sizeof(ST_DR_FILEBUF);  //表示有多少分钟数据
    qDebug()<<"TotalTimeOfFile="<<TotalTimeOfFile;
    //注意，由于实际开始时可能从一分钟的中间时刻开始记录，数据块中有空白
    if(TotalTimeOfFile<=0) {My_File.close(); qDebug()<<"无效的数据文件";return;}

    QDir *temp = new QDir;
    bool exist = temp->exists(EXCEL_SAVE_DISK);
    if(!exist) qDebug()<<temp->mkpath(EXCEL_SAVE_DISK);
    QFile csvfile;

    csvFileName = EXCEL_SAVE_DISK+InitFileName.left(InitFileName.lastIndexOf("."))+".CSV";
    csvfile.setFileName(csvFileName);
    if (csvfile.exists())  csvfile.remove();
    csvfile.open(QIODevice::ReadWrite);  //不存在的情况下，打开包含了新建文件的操作
    csvfile.seek(0);
    ParaNameStr="时间,";
    for(int k=0;k<ui->TblPara->rowCount();k++)
    {
        if(ui->TblPara->item(k,1)->text()!="")
            ParaNameStr+=ui->TblPara->item(k,0)->text()+"("+ui->TblPara->item(k,1)->text()+")"+",";
        else
            ParaNameStr+=ui->TblPara->item(k,0)->text()+",";
    }
    csvfile.write(ParaNameStr.toUtf8().data() ,ParaNameStr.toUtf8().length());
    ParaNameStr="\r\n";
    csvfile.seek(csvfile.size());
    csvfile.write(ParaNameStr.toLatin1().data() ,2);

    int CurReadMin=0;
    int StartSec,StartMSec,EndSec,EndMSec;
    while(1)
    {
        //ret=fread(&CurFileBuf,sizeof(CurFileBuf),1,in);
        My_File.seek(CurReadMin*sizeof(CurFileBuf));
        ret=My_File.read((char *)(&CurFileBuf),sizeof(CurFileBuf));
        CurReadMin++;
        if(ret==0) break;//读完了
        StartSec=CurFileBuf.StartSecond;
        StartMSec=CurFileBuf.StartmSec;
        EndSec=CurFileBuf.EndSecond;
        EndMSec=CurFileBuf.EndmSec;
        int k=0;
        while(k<600)
        {
            CurRecord=CurFileBuf.DataDR[k];
            TimeStr=GetTimeStr(CurFileBuf.Minute,StartSec,StartMSec);
            TimeStr+=QString::number(StartMSec)+"毫秒";

            ValNameLine="";
            ValNameLine=TimeStr+",";
            for(int k=0;k<ui->TblPara->rowCount();k++)
            {
                mStr=QString::number(GetVarVal(ui->TblPara->item(k,0)->text()));
                ValNameLine=ValNameLine+mStr+",";
            }
            csvfile.seek(csvfile.size());
            csvfile.write(ValNameLine.toUtf8().data(),ValNameLine.toUtf8().length());
            csvfile.seek(csvfile.size());
            ValNameLine="\r\n";
            csvfile.write(ValNameLine.toLatin1().data(),2);

            StartMSec+=1000/HzVal; //过半秒
            if(StartMSec>=1000) { StartMSec-=1000;  StartSec++;}  //加一秒
            if(StartSec>=60) break;//一分钟已经完成
            if(CurReadMin==TotalTimeOfFile)
            {
                if((StartSec*1000+StartMSec)>(EndSec*1000+EndMSec))  break;
            }
            k+=10/HzVal;
        }
    }//end of while(1)
    csvfile.close();
    My_File.close();
    //QMessageBox::information(NULL,QObject::tr("提示"),QObject::tr("数据导出完成"),QMessageBox::Yes,QMessageBox::Yes);
}

void MainWindow::on_BtnLoadCurve_clicked()
{
    LoadFile(ui->LbFileName->text(),0);
}

void MainWindow::on_CbParaSystem_currentTextChanged(const QString &arg1)
{
    if(arg1=="ALL")
    {
        for(int i=0;i<ui->TblPara->rowCount();i++)
            ui->TblPara->setRowHidden(i,false);
    }
    else if(arg1=="传感器信号-外部")//16+25+16+16  +16+35+9+9+  19
    {
        for(int i=0;i<16+25+16+16+16+35+9+9;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25+16+16+16+35+9+9;i<16+25+16+16+16+35+9+9+19;i++)
            ui->TblPara->setRowHidden(i,false);
    }
    else if(arg1=="传感器信号-内部")//16+25+16+16  +16+35+9+9+  19
    {
        for(int i=0;i<16;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16;i<16+25+16+16;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25+16+16;i<16+25+16+16+16;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25+16+16+16;i<16+25+16+16+16+35+9+9+19;i++)
            ui->TblPara->setRowHidden(i,true);
    }
    else if(arg1=="变频器控制信号")//16+25+16+16  +16+35+9+9+  19
    {
        for(int i=0;i<16;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16;i<16+25;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25;i<16+25+16+16+16;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25+16+16+16;i<16+25+16+16+16+35;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25+16+16+16+35;i<16+25+16+16+16+35+9+9+19;i++)
            ui->TblPara->setRowHidden(i,true);
    }
    else if(arg1=="备用泵电机启动箱")//16+25+16+16  +16+35+9+9+  19
    {
        for(int i=0;i<16+25;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25;i<16+25+16;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25+16;i<16+25+16+16+16+35;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25+16+16+16+35;i<16+25+16+16+16+35+9;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25+16+16+16+35+9;i<16+25+16+16+16+35+9+9+19;i++)
            ui->TblPara->setRowHidden(i,true);
    }
    else if(arg1=="提升泵电机启动箱")//16+25+16+16  +16+35+9+9+  19
    {
        for(int i=0;i<16+25+16;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25+16;i<16+25+16+16;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25+16+16;i<16+25+16+16+16+35+9;i++)
            ui->TblPara->setRowHidden(i,true);
        for(int i=16+25+16+16+16+35+9;i<16+25+16+16+16+35+9+9;i++)
            ui->TblPara->setRowHidden(i,false);
        for(int i=16+25+16+16+16+35+9+9;i<16+25+16+16+16+35+9+9+19;i++)
            ui->TblPara->setRowHidden(i,true);
    }
}

void MainWindow::on_pushButton_last_test_photo_clicked()
{

}



void MainWindow::InitTableHisStep()
{
    QStringList headerString;
    QList<int> StretchHorizontalIndex;

    headerString<< tr("序号")  << tr("观测历史") << tr("结果");

    StretchHorizontalIndex<<1;
    TableWidgetQss(headerString,ui->TableHisStep,StretchHorizontalIndex);
    ui->TableHisStep->setColumnWidth(0,50);
    ui->TableHisStep->setColumnWidth(1,200);
    ui->TableHisStep->setColumnWidth(2,80);
    //    QStringList StringFault,StringProb;
    //    StringFault<<"请检查安全销是否已拔出？"<<"查看DI208-1模块.0通道指示灯状态";
    //    StringProb<<"是"<<"不亮";
    //    ui->TableHisStep->setRowCount(StringFault.count());
    //    for(int i=0;i<StringFault.count();i++)
    //    {
    //        // 创建一个新的 QTableWidgetItem 用于"序号"
    //        QTableWidgetItem *itemSerial = new QTableWidgetItem(QString::number(i + 1));
    //        // 设置对齐方式为居中
    //        itemSerial->setTextAlignment(Qt::AlignCenter);
    //        // 在表格中设置该项
    //        ui->TableHisStep->setItem(i, 0, itemSerial);
    //        //ui->TableHisStep->setItem(i,0,new QTableWidgetItem(QString::number(i+1)));
    //        ui->TableHisStep->setItem(i,1,new QTableWidgetItem(StringFault.at(i)));

    //        //ui->TableHisStep->setItem(i,2,new QTableWidgetItem(StringProb.at(i)));
    //        // 创建一个新的 QTableWidgetItem
    //        QTableWidgetItem *item = new QTableWidgetItem(StringProb.at(i));
    //        // 设置字体颜色为蓝色
    //        item->setTextColor(Qt::blue);
    //        // 获取当前字体
    //        QFont font = item->font();
    //        // 设置字体为下划线
    //        font.setUnderline(true);
    //        // 应用字体设置
    //        item->setFont(font);
    //        // 设置对齐方式为居中
    //        item->setTextAlignment(Qt::AlignCenter);
    //        // 在表格中设置该项
    //        ui->TableHisStep->setItem(i, 2, item);
    //        //ui->tableListFalut->resizeRowsToContents();
    //    }
}

void MainWindow::InitTabWidget_test_image()
{
    //    ui->tabWidget_test_image->clear();
    //    ui->tabWidget_test_image->tabBar()->hide();

    //    //    if(ui->tabWidget_test_image->height()<ui->tabWidget_test_image->width()){
    //    //        ui->tabWidget_test_image->setMaximumWidth(ui->tabWidget_test_image->height());
    //    //        ui->tabWidget_test_image->setMinimumWidth(ui->tabWidget_test_image->height());
    //    //    }
    //    //    else{
    //    //        ui->tabWidget_test_image->setMaximumHeight(ui->tabWidget_test_image->width());
    //    //        ui->tabWidget_test_image->setMinimumHeight(ui->tabWidget_test_image->width());
    //    //    }

    //    int num_of_jpg = 0;
    //    //for(int i=0;i<TestMULTIMEDI.size();i++)
    //    {
    //        //if((TestMULTIMEDI[i].MEDIA_NAME.contains("jpg")||(TestMULTIMEDI[i].MEDIA_NAME.contains("JPG"))))
    //        {
    //            num_of_jpg++;

    //            QWidget* widget = new QWidget(this);
    //            QVBoxLayout * layout = new QVBoxLayout(widget);//铺满布局

    //            QLabel* pLabel = new QLabel(widget);
    //            pLabel->setSizePolicy(QSizePolicy::Preferred,QSizePolicy::Preferred);//铺满布局
    //            layout->addWidget(pLabel);

    //            QLabel* name_Label = new QLabel(widget);
    //            name_Label->setMaximumHeight(35);
    //            name_Label->setMinimumWidth(ui->tabWidget_test_image->width());
    //            name_Label->setMaximumWidth(ui->tabWidget_test_image->width());
    //            name_Label->setStyleSheet("font: 75 14pt '微软雅黑';");
    //            name_Label->setAlignment(Qt::AlignHCenter);

    //            QString picture_name = "万用表";//TestMULTIMEDI[i].MEDIA_NAME;
    //            picture_name.remove(".jpg").remove(".JPG");
    //            name_Label->setText(picture_name);
    //            layout->addWidget(name_Label);

    //            QPixmap photo;
    //            photo=QPixmap("C:/MDB/ToolImages/万用表.png");
    //            //photo.loadFromData(TestMULTIMEDI[i].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式为JPG，然后显示到QLabel里
    //            pLabel->setPixmap(photo);
    //            pLabel->setScaledContents(true);

    //            //QString name = QString("%1").arg(i);
    //            ui->tabWidget_test_image->addTab(widget,"万用表");
    //        }
    //    }
}



void MainWindow::on_pushButton_2_clicked()
{
    //    if(CurStep==0)
    //    {
    //        ui->label_11->setText("收放控制机柜打开柜门");
    //        ui->label_13->setStyleSheet("border-image: url(C:/MDB/DiagnoseImages/02-00-收放控制机柜位置)");
    //        ui->pushButton->setVisible(false);
    //        ui->pushButton_2->setText("完成");
    //        ui->label_14->setText("请检查安全销是否已拔出？");
    //        ui->label_15->setText(" >>否");
    //    }
    //    if(CurStep==1)
    //    {
    //        ui->label_11->setText("找到PLC-DI模块位置");
    //        ui->label_13->setStyleSheet("border-image: url(C:/MDB/DiagnoseImages/02-01-PLC-DI模块位置.png)");
    //        ui->pushButton->setVisible(false);
    //        ui->pushButton_2->setText("完成");
    //        ui->label_16->setText("收放控制机柜打开柜门");
    //    }
    //    if(CurStep==2)
    //    {
    //        ui->label_11->setText("查看DI208-1模块.0指示灯");
    //        ui->label_13->setStyleSheet("border-image: url(C:/MDB/DiagnoseImages/02-02-安全插销DI信号指示灯.png)");
    //        ui->pushButton->setVisible(true);
    //        ui->pushButton->setText("亮");
    //        ui->pushButton_2->setText("灭");
    //        ui->label_17->setText("找到PLC-DI模块位置");
    //    }
    //    CurStep++;
    //    if(CurStep>2)
    //    {
    //        CurStep=0;
    //        ui->label_11->setText("检查安全销是否已拔出？");
    //        ui->label_13->setStyleSheet("border-image: url(C:/MDB/DiagnoseImages/00-安全插销位置.png)");
    //        ui->pushButton->setVisible(true);
    //        ui->pushButton->setText("是");
    //        ui->pushButton_2->setText("否");
    //        ui->label_14->setText("");
    //        ui->label_15->setText("");
    //        ui->label_16->setText("");
    //        ui->label_17->setText("");
    //    }
}

void MainWindow::on_pushButton_clicked()
{

}

void MainWindow::AdjustImageLayout(QLabel *label, const QString &imagePath) {
    QPixmap pixmap(imagePath);
    // 调整 QPixmap 的尺寸来适应 QLabel 的大小
    QPixmap scaledPixmap = pixmap.scaled(label->size(), Qt::KeepAspectRatio, Qt::SmoothTransformation);
    // 设置 QLabel
    label->setAlignment(Qt::AlignCenter);  // 设置对齐方式为居中
    label->setPixmap(scaledPixmap);
}

void MainWindow::AdjustGraphicScene(QGraphicsView *mGraphicsView,BQGraphicsScene *pGraphicsScene,QString Path)
{
    qDebug()<<"AdjustGraphicScene,Path="<<Path;
    QPixmap pix(Path);
    pGraphicsScene->SetBackGroundImage(pix, mGraphicsView->width(), mGraphicsView->height());
}
void MainWindow::AdjustIamgeLayout(QLabel *pLabel,QString Path)
{
    QImage *img_mainicon;//主图标显示在右上角lable中
    img_mainicon =new QImage;//新建一个image对象
    img_mainicon->load(Path); //载入图片到img对象中
    img_mainicon->scaled(pLabel->size(),Qt::KeepAspectRatio);//把图片
    //pLabel->setScaledContents(true);
    pLabel->setPixmap(QPixmap::fromImage(*img_mainicon));


    //    QPixmap photo(Path);
    //    //pLabel->resize(photo.width()-40,photo.height());
    //    pLabel->setScaledContents(true);
    //    int wLabel=pLabel->width();
    //    int hLabel=pLabel->height();
    //    //pLabel->setScaledContents(false);
    //    int wPhoto=photo.width();
    //    int hPhoto=photo.height();
    //    int Finalw,Finalh;
    //    if((wPhoto>=wLabel)&&(hPhoto>=hLabel))
    //    {
    //        if((wPhoto/hPhoto)>(wLabel/hLabel))
    //        {
    //            Finalw=wLabel;
    //            Finalh=wLabel*hPhoto/wPhoto;
    //        }
    //        else
    //        {
    //            Finalh=hLabel;
    //            Finalw=hLabel*wPhoto/hPhoto;
    //        }
    //    }
    //    else if((wPhoto>=wLabel)&&(hPhoto<=hLabel))
    //    {
    //        Finalw=wLabel;
    //        Finalh=wLabel*hPhoto/wPhoto;
    //    }
    //    else if((wPhoto<=wLabel)&&(hPhoto>=hLabel))
    //    {
    //        Finalh=hLabel;
    //        Finalw=hLabel*wPhoto/hPhoto;
    //    }
    //    else
    //    {
    //        Finalw=wPhoto;
    //        Finalh=hPhoto;
    //    }
    //    //qDebug()<<"wLabel="<<wLabel<<",hLabel="<<hLabel<<",wPhoto="<<wPhoto<<",hPhoto="<<hPhoto<<",Finalw="<<Finalw<<",Finalh="<<Finalh;
    //    //pLabel->resize(Finalw,Finalh);
    //    //pLabel->move(0,0);
    //    //qDebug()<<"pLabel->width()="<<pLabel->width()<<",pLabel->height()="<<pLabel->height();
    //    pLabel->setPixmap(photo.scaled(Finalw,Finalh));//(photo.scaled(w,h,Qt::KeepAspectRatio,Qt::SmoothTransformation));

}

void MainWindow::on_BtnLastImgPos_clicked()
{
    QStringList ListImgPosPath=TestStepCandidates[CurTestNode->text()].ListImgPosPath;
    int index=-1;
    for(int i=0;i<ListImgPosPath.count();i++)
    {
        if(CurImgPosPath==ListImgPosPath.at(i))
        {
            index=i;
            break;
        }
    }
    index--;
    if(index>=0)
    {
        AdjustIamgeLayout(ui->LbImgPos,"C:/MDB/DiagnoseImages/"+ListImgPosPath.at(index));
        CurImgPosPath=ListImgPosPath.at(index);
        AdjustGraphicScene(ui->graphicsView_Pos,&m_scene_pos,"C:/MDB/DiagnoseImages/"+ListImgPosPath.at(index));
    }
    if(index<=0) ui->BtnLastImgPos->setEnabled(false);
    if(index<ListImgPosPath.count()-1) ui->BtnNextImgPos->setEnabled(true);
}

void MainWindow::on_BtnNextImgPos_clicked()
{
    QStringList ListImgPosPath=TestStepCandidates[CurTestNode->text()].ListImgPosPath;
    int index=ListImgPosPath.count();
    for(int i=ListImgPosPath.count()-1;i>=0;i--)
    {
        if(CurImgPosPath==ListImgPosPath.at(i))
        {
            index=i;
            break;
        }
    }
    index++;
    if(index<=ListImgPosPath.count()-1)
    {
        AdjustIamgeLayout(ui->LbImgPos,"C:/MDB/DiagnoseImages/"+ListImgPosPath.at(index));
        AdjustGraphicScene(ui->graphicsView_Pos,&m_scene_pos,"C:/MDB/DiagnoseImages/"+ListImgPosPath.at(index));
        CurImgPosPath=ListImgPosPath.at(index);
    }
    if(index>=ListImgPosPath.count()-1) ui->BtnNextImgPos->setEnabled(false);
    if(index>0) ui->BtnLastImgPos->setEnabled(true);
}

void MainWindow::on_BtnLastImgTerm_clicked()
{
    QStringList ListImgTermPath=TestStepCandidates[CurTestNode->text()].ListImgTermPath;
    int index=-1;
    for(int i=0;i<ListImgTermPath.count();i++)
    {
        if(CurImgTermPath==ListImgTermPath.at(i))
        {
            index=i;
            break;
        }
    }
    index--;
    if(index>=0)
    {
        AdjustIamgeLayout(ui->LbImgTerm,"C:/MDB/DiagnoseImages/"+ListImgTermPath.at(index));
        AdjustGraphicScene(ui->graphicsView_Term,&m_scene_term,"C:/MDB/DiagnoseImages/"+ListImgTermPath.at(index));
        CurImgTermPath=ListImgTermPath.at(index);
    }
    if(index<=0) ui->BtnLastImgTerm->setEnabled(false);
    if(index<ListImgTermPath.count()-1) ui->BtnNextImgTerm->setEnabled(true);
}

void MainWindow::on_BtnNextImgTerm_clicked()
{
    QStringList ListImgTermPath=TestStepCandidates[CurTestNode->text()].ListImgTermPath;
    int index=ListImgTermPath.count();
    for(int i=ListImgTermPath.count()-1;i>=0;i--)
    {
        if(CurImgTermPath==ListImgTermPath.at(i))
        {
            index=i;
            break;
        }
    }
    index++;
    if(index<=ListImgTermPath.count()-1)
    {
        AdjustIamgeLayout(ui->LbImgTerm,"C:/MDB/DiagnoseImages/"+ListImgTermPath.at(index));
        AdjustGraphicScene(ui->graphicsView_Term,&m_scene_term,"C:/MDB/DiagnoseImages/"+ListImgTermPath.at(index));
        CurImgTermPath=ListImgTermPath.at(index);
    }
    if(index>=ListImgTermPath.count()-1) ui->BtnNextImgTerm->setEnabled(false);
    if(index>0) ui->BtnLastImgTerm->setEnabled(true);
}

// 递归计算从某个节点开始的所有子孙节点的数量
int countDescendants(QStandardItem *node) {
    int total = 0;
    for (int i = 0; i < node->rowCount(); i++) {
        total += 1 + countDescendants(node->child(i));
    }
    return total;
}

int MainWindow::CalCostTime(QStandardItem *node,int singleCost) {
    int nodeCount = 0;
    int timeCost=0;
    if (node->hasChildren()){
        nodeCount = countDescendants(node);
    }
    if(nodeCount<=0)nodeCount=2;
    qsrand(QTime(0,0,0).secsTo(QTime::currentTime()));
    //timeCost=nodeCount*singleCost+qrand()%20;
    timeCost = static_cast<int>(sqrt(nodeCount) * singleCost) + qrand() % 20;

    // 创建对话框并设置样式
    QDialog *waitDialog = new QDialog(this, Qt::FramelessWindowHint | Qt::Dialog);
    waitDialog->setStyleSheet("background-color: #D3D3D3; color: black;font: 75 12pt;"); // 设置灰底黑字的样式
    waitDialog->setFixedSize(400, 100); // 设置对话框的大小

    // 创建布局和标签
    QVBoxLayout *layout = new QVBoxLayout(waitDialog);
    QLabel *label = new QLabel("推理计算中，请稍候...");
    //label->setFont(QFont("Arial", 10)); // 设置字体大小
    label->setAlignment(Qt::AlignCenter); // 文本居中
    layout->addWidget(label);
    waitDialog->setLayout(layout);

    // 设置对话框为模态
    waitDialog->setWindowModality(Qt::WindowModal);

    // 显示对话框
    waitDialog->show();

    QTimer::singleShot(timeCost, this, [this, waitDialog,timeCost]() {
        // 关闭等待对话框
        waitDialog->accept();
        // 删除对话框
        waitDialog->deleteLater();
        if(CurTestNode->data(Qt::WhatsThisRole).toString()=="测试") LoadDiagnosisUI();
        else if(CurTestNode->data(Qt::WhatsThisRole).toString()=="诊断解")
        {
            mdlgMessage->SetResult(CurTestNode->text());
            mdlgMessage->raise();
            mdlgMessage->show();
        }
        ui->label_inferenceTime->setText(QString("推理时间:%1ms").arg(timeCost));
    });
    return timeCost;
}

//反馈观测结果
void MainWindow::on_pushButton1_clicked()
{
    CurTestNode->setData(ui->pushButton1->text(),Qt::UserRole);
    UpdateHisTest();
    if(CurTestNode->hasChildren())
    {
        //这里判断CurTestNode->child(0,0)是测试还是诊断解
        CurTestNode=CurTestNode->child(0,0);
        CalCostTime(CurTestNode);
    }
}

//反馈观测结果
void MainWindow::on_pushButton2_clicked()
{
    CurTestNode->setData(ui->pushButton2->text(),Qt::UserRole);
    UpdateHisTest();
    if((CurTestNode->hasChildren())&&(CurTestNode->rowCount()>1))
    {
        CurTestNode=CurTestNode->child(1,0);
        CalCostTime(CurTestNode);
    }
}

//更新历史测试记录
void MainWindow::UpdateHisTest()
{
    ui->TableHisStep->clearContents();
    ui->TableHisStep->setRowCount(0);
    //根据ModelTestSet回溯历史测试结果
    QStandardItem *HisTestNode=CurTestNode;
    QStringList ListTestQuestion,ListTestResult;
    while(HisTestNode!=nullptr)
    {
        QString StrParentTestQuestion=TestStepCandidates[HisTestNode->text()].StrQuestion;//HisTestNode->text();
        QString StrParentTestResult=HisTestNode->data(Qt::UserRole).toString();
        ListTestQuestion.append(StrParentTestQuestion);
        ListTestResult.append(StrParentTestResult);
        HisTestNode=HisTestNode->parent();
    }
    ui->TableHisStep->setRowCount(ListTestQuestion.count());
    for(int i=0;i<ListTestQuestion.count();i++)
    {
        //        ui->TableHisStep->setItem(i,0,new QTableWidgetItem(QString::number(i+1)));
        //        ui->TableHisStep->setItem(i,1,new QTableWidgetItem(ListTestQuestion.at(ListTestQuestion.count()-i-1)));
        //        ui->TableHisStep->setItem(i,2,new QTableWidgetItem(ListTestResult.at(ListTestResult.count()-i-1)));
        // 设置第一列（序号）的单元格
        QTableWidgetItem *item0 = new QTableWidgetItem(QString::number(i + 1));
        item0->setTextAlignment(Qt::AlignCenter); // 居中对齐
        ui->TableHisStep->setItem(i, 0, item0);

        // 设置第二列的单元格
        ui->TableHisStep->setItem(i, 1, new QTableWidgetItem(ListTestQuestion.at(ListTestQuestion.count() - i - 1)));

        // 设置第三列（结果）的单元格
        QTableWidgetItem *item2 = new QTableWidgetItem(ListTestResult.at(ListTestResult.count() - i - 1));
        item2->setTextAlignment(Qt::AlignCenter); // 居中对齐
        ui->TableHisStep->setItem(i, 2, item2);
    }
}

void MainWindow::on_BtnRestart_clicked()
{
    CreateDiagnoisTree();
    ui->tableListFalut->setRowCount(0);
    //InitTableFuzzl_Alarm();
    ui->TableHisStep->setRowCount(0);
    ui->stackedDiagnosis->setCurrentIndex(0);
}

void MainWindow::on_BtnTestPrio_clicked()
{
    mdlgTestPrio->raise();
    mdlgTestPrio->show();
}
