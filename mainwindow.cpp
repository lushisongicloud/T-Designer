#include "mainwindow.h"
#include "ui_mainwindow.h"
#include <ActiveQt/QAxObject>
#include <ActiveQt/QAxWidget>
#include <QTimer>
#include <QFileInfo>
#include <QFile>
#include <QDir>
#include <QStringList>
#include <QMenu>
#include <QSet>
#include <QInputDialog>
#include <QShortcut>
#include "BO/containerrepository.h"
#include "widget/containertreedialog.h"
#include "DO/containerentity.h"
#include "widget/containerhierarchyutils.h"
#include "widget/functionmanagerdialog.h"
#include "widget/functioneditdialog.h"
#include "BO/function/functionrepository.h"
#include "demo_projectbuilder.h"
bool isPenetrativeSolve=true;
QMap<QString, QStringList> obsTemplates = {
    {"AC380_3P_u", {"AC380.u", "( 0 , 0 , 0 )", "( 380 , 0 , 0 )", "( 0 , 380 , 0 )", "( 0 , 0 , 380 )", "( 380 , 380 , 0 )", "( 380 , 0 , 380 )", "( 0 , 380 , 380 )", "( 380 , 380 , 380 )"}},
    {"AC380_3P_i", {"( 1.0 , 1.0 , 1.0 )", "( 0 , 0 , 0 )", "( 1.0 , 0 , 0 )", "( 0 , 1.0 , 0 )", "( 0 , 0 , 1.0 )", "( 1.0 , 1.0 , 0 )", "( 1.0 , 0 , 1.0 )", "( 0 , 1.0 , 1.0 )"}},
    {"AC380_1P_u", {"380","0"}},
    {"AC380_1P_i", {"1.0","0"}},
    {"AC220_1P_u", {"220","0","[210,230]","(200,240]",">200.2","<=1.2","smt(> %1 (* L7.1.i 1000))"}},
    {"AC220_1P_i", {"1.0","0","[0.5,1.5]","(0,2.0]",">0.5","<=0.5","smt(> L7.1.u (* %1 1000))"}}
};


QDebug operator<<(QDebug dbg, const TestItem& item) {
    dbg.nospace() << "TestItem(variable: " << item.variable
                  << ", value: " << item.value
                  << ", confidence: " << item.confidence
                  << ", type: " << item.testType
                  << ", checkState: " << item.checkState << ")\n";
    return dbg.space();
}
QDebug operator<<(QDebug dbg, const QList<TestItem>& list) {
    dbg.nospace() << "[";
    for(const auto& item: list){
        dbg.nospace() << item;
    }
    dbg.nospace() << "]";
    return dbg.space();
}

using namespace ContainerHierarchy;

QSqlDatabase  T_ProjectDatabase;
QString CurProjectPath,CurProjectName;
int CurComponentCount = 0;
int SelectEquipment_ID=0,SelectSymbol_ID=0,SelectTerminalStrip_ID=0,SelectTerminal_ID=0,SelectPage_ID=0;
QStringList RemovedUnitsInfo;//DT,ProjectStructure_ID,Type,Spec,Eqpt_Category,Name,Desc,PartCode,OrderNum,Factory,Remark,TVariable,TModel

MainWindow::MainWindow(QWidget *parent) :
    QMainWindow(parent),
    ui(new Ui::MainWindow)
{
    ui->setupUi(this);
    ui->mdiArea->setViewMode(QMdiArea::TabbedView); //Tab多页显示模式
    ui->mdiArea->setTabsClosable(true); //页面可关闭
    InitNavigatorTree();

    auto demoShortcut = new QShortcut(QKeySequence(Qt::CTRL | Qt::SHIFT | Qt::Key_H), this);
    connect(demoShortcut, &QShortcut::activated, this, &MainWindow::createDemoProject);

    dlgLoadSymbol=nullptr;
    dlgDialogSymbols=nullptr;
    dlgUnitManage=new DialogUnitManage(this);
    dlgFuncDefine=new DialogFuncDefine(this);
    dlgUnitAttr=new DialogUnitAttr(this);
    dlgFunctionManage=new dialogFunctionManage(this);
    //connect(dlgFunctionManage,SIGNAL(UpdateSystemDefine(QStringList)),this,SLOT(UpdateFuncStrSystemDefine(QStringList)));

    SetStackIndex(0);
    //connect(dlgDiagnoseUI,SIGNAL(signalUpdateExec(QString)),this,SLOT(UpdateXmplInfo(QString)));
    //connect(dlgDiagnoseUI,SIGNAL(signalStartDiagnose(QString)),this,SLOT(StartDiagnose(QString)));
    //connect(dlgDiagnoseUI,SIGNAL(signalSendCmdStr(QString)),this,SLOT(SendCmd(QString)));

    connect(dlgUnitManage,SIGNAL(SignalUpdated()),this,SLOT(UpdateUnitAttrLib()));
    ui->treeViewPages->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeViewPages,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewPagePopMenu(QPoint)));

    ui->treeViewUnits->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeViewUnits,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewUnitsPopMenu(QPoint)));

    ui->treeViewTerminal->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeViewTerminal,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewTerminalPopMenu(QPoint)));

    ui->treeViewLineDT->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeViewLineDT,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewLineDTPopMenu(QPoint)));

    ui->treeViewLineByUnit->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->treeViewLineByUnit,SIGNAL(customContextMenuRequested(QPoint)),this,SLOT(ShowtreeViewLineByUnitPopMenu(QPoint)));

    ui->BtnShowHidePreViewWidget->setText("图形预览▲");
    ui->widgetPreView->setVisible(false);
    QTimer::singleShot(0, this, &MainWindow::initAfterShow);
    ui->axWidgetPreview->setProperty("IsDrawCoord",false);
    ui->axWidgetPreview->setProperty("UseArrowCursor",true);
    ui->axWidgetDiagnose->setProperty("IsDrawCoord",false);
    ui->axWidgetDiagnose->setProperty("UseArrowCursor",true);

    ui->tableWidgetUnit->setColumnWidth(0,30);//序号
    ui->tableWidgetUnit->setColumnWidth(1,150);//项目代号
    //ui->tableWidgetUnit->setColumnWidth(2,150);//型号
    ui->CbUnitTogether->setVisible(false);

    ui->tableWidgetExecConn->setColumnWidth(0,20);//勾选框
    ui->tableWidgetExecConn->setColumnWidth(1,100);//高层
    ui->tableWidgetExecConn->setColumnWidth(2,100);//位置
    ui->tableWidgetExecConn->setColumnWidth(3,100);//元件名称
    ui->tableWidgetExecConn->setColumnWidth(4,95);//功能子块
    ui->tableWidgetExecConn->setColumnWidth(5,500);//诊断链路

    ui->tableWidgetDiagResult->setColumnWidth(0,400);//优先级
    ui->tableWidgetDiagResult->setFocusPolicy(Qt::NoFocus);
    ui->tableWidgetDiagResult->setRowCount(1);
    ui->tableWidgetDiagResult->setItem(ui->tableWidgetDiagResult->rowCount()-1,0,new QTableWidgetItem("诊断未开始"));

    ui->tableWidgetTestPoint->setColumnWidth(0,200);//测试点名称

    ui->tableWidget_DiagResult->setColumnWidth(0,200);//故障点位置
    ui->tableWidget_DiagResult->setColumnWidth(1,150);//故障点名称
    ui->tableWidget_DiagResult->setColumnWidth(2,100);//故障点代号
    ui->tableWidget_DiagResult->setColumnWidth(3,100);//失效模式
    ui->tableWidget_DiagResult->setColumnWidth(4,350);//解决方案
    ui->tableWidget_DiagResult->setColumnWidth(5,350);//所需资源
    ui->tableWidgetDiagResult->setFocusPolicy(Qt::NoFocus);

    ui->tableWidgetFunction->setColumnWidth(0,220);
    ui->tableWidgetFunction->setColumnWidth(1,300);

    InitTEdit();
    on_BtnRefreshExecConn_clicked();
    UpdateFuncTable();

    cmdDiagnose = new QProcess(this);
    cmdStarted = false;
    connect(cmdDiagnose , SIGNAL(readyReadStandardOutput()) , this , SLOT(on_readoutput()));
    connect(cmdDiagnose , SIGNAL(readyReadStandardError()) , this , SLOT(on_readerror()));

    ui->tabWidget_Navigator->removeTab(4);
    ui->tabWidget_Navigator->removeTab(4);
    ui->tabWidget_Navigator->removeTab(5);
    ui->tabWidget_Navigator->setCurrentIndex(0);
    ui->tabWidget->setCurrentIndex(0);
    ui->stackedWidget->setCurrentIndex(0);
    ui->tabWidget_Diagnose->setCurrentIndex(0);
    //ui->tableWidget_test_file->setVisible(false);
    ui->label_diagnosis_TestWord->setText("请选择系统功能");
    this->showMaximized();

    dlg_showPicture =new QDialog(this);
    dlg_showPicture->setModal(true);
    picture_Label = new QLabel(dlg_showPicture);
    QHBoxLayout *layout = new QHBoxLayout;
    layout->addWidget(picture_Label);
    dlg_showPicture->setLayout(layout);
    dlg_showPicture->setMinimumSize(200,200);
    dlg_delay=new Dialog_wait(this);
    dlg_delay->setModal(true);

    graph_list = new GraphAdjList(0);       //有向图

    ui->BtnClearDB->setVisible(false);
    ui->groupPageFilter->setVisible(false);
    ui->groupUnitFilter->setVisible(false);
    ui->stackedWidgetLine->setVisible(false);
    ui->groupTerminalFilter->setVisible(false);
}

MainWindow::~MainWindow()
{
    delete ui;
    delete pApp;
    delete GlobalBackAxWidget;
    delete dlgLoadSymbol;
    delete dlgUnitManage;
    delete dlgFuncDefine;
    delete ModelPages;
    delete ModelUnits;
    delete ModelTerminals;
    delete ModelLineDT;
    delete ModelLineByUnits;
    delete dlg_delay; //删除对话框
    delete dlg_showPicture;
    delete dlgDialogSymbols;
    delete dlgUnitAttr;
    delete dlgFunctionManage;
}



void MainWindow::UpdateFuncStrSystemDefine(QStringList ListExec)
{
    /*
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
       ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Unchecked);
    }
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        for(int j=0;j<ListExec.count();j++)
        {
           if(ListExec.at(j).contains(ui->tableWidgetExecConn->item(i,3)->text())&&ListExec.at(j).contains(ui->tableWidgetExecConn->item(i,4)->text()))
              ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Checked);
        }
    }
    on_BtnRemakeLinkRoad_clicked();*/
}

void MainWindow::UpdateUnitAttrLib()
{
    dlgUnitAttr->ReloadLib();
}

void MainWindow::on_readoutput()
{
    QString output = cmdDiagnose->readAllStandardOutput().data();
    qDebug()<<"output="<<output;
    //解析诊断结果

    while(1)
    {
        if(!output.contains("Candidate")) break;
        QString StrValidCandidate;
        int indexOfCandidate=output.indexOf("Candidate");
        output=output.mid(indexOfCandidate+9,output.count()-indexOfCandidate-9);
        int NextIndexOfCandidate=output.indexOf("Candidate");
        if(NextIndexOfCandidate>=0) StrValidCandidate=output.mid(0,NextIndexOfCandidate);
        else StrValidCandidate=output;
        //qDebug()<<"StrValidCandidate="<<StrValidCandidate;
        QStringList ListCandidate=StrValidCandidate.split("#");
        //qDebug()<<"ListCandidate="<<ListCandidate;
        QStringList ListFaultComponent;
        for(QString StrOneCandidate:ListCandidate)//test.L02.modeTransition=loose :4
        {
            if(!StrOneCandidate.contains(":")) continue;
            QStringList ListDetailInfo=StrOneCandidate.split(".");
            //if(ListDetailInfo.count()!=3) continue;
            QString StrFaultComponent;

            CandidateData data;
            for(int i=ListDetailInfo.last().indexOf(":")+1;i<ListDetailInfo.last().count();i++)
            {

                if(StrIsNumber(ListDetailInfo.last().at(i))) data.PriorVal+=ListDetailInfo.last().at(i);
                else break;
            }
            for(int i=ListDetailInfo.last().indexOf("=")+1;i<ListDetailInfo.last().count();i++)
            {
                if((ListDetailInfo.last().at(i)!="")&&(ListDetailInfo.last().at(i)!=" ")) data.modeTransition+=ListDetailInfo.last().at(i);
                else break;
            }
            for(int i=1;i<ListDetailInfo.count()-1;i++)
            {
                if(i>1) data.FaultSpur+=".";
                data.FaultSpur+=ListDetailInfo.at(i);
            }
            StrFaultComponent=data.FaultSpur+":"+data.modeTransition+"(Rank="+data.PriorVal+")";
            //计算概率和信息熵
            data.FaultProbability = 1 / qPow(2, data.PriorVal.toInt());

            ListFaultComponent.append(StrFaultComponent);

            if(!isHaveCandidate(data))
            {
                candidate_list.append(data);
                UpdateModuleFaultProb();
            }
        }
        if(ListFaultComponent.count()<1) continue;
        QString CombinedInfo;
        for(QString StrCombinedInfo:ListFaultComponent) CombinedInfo+=StrCombinedInfo+" ";
        bool Existed=false;
        for(int i=0;i<ui->tableWidgetDiagResult->rowCount();i++)
        {
            if(ui->tableWidgetDiagResult->item(i,0)->text()==CombinedInfo)
            {
                Existed=true;
                break;
            }
        }
        if(!Existed)
        {
            if(ui->tableWidgetDiagResult->rowCount()>0)
            {
                if(ui->tableWidgetDiagResult->item(ui->tableWidgetDiagResult->rowCount()-1,0)->text().trimmed()=="诊断流程已启动")
                    ui->tableWidgetDiagResult->removeRow(ui->tableWidgetDiagResult->rowCount()-1) ;
                if(ui->tableWidgetDiagResult->item(ui->tableWidgetDiagResult->rowCount()-1,0)->text().trimmed()=="当前没有发现故障")
                    ui->tableWidgetDiagResult->removeRow(ui->tableWidgetDiagResult->rowCount()-1) ;
            }
            ui->tableWidgetDiagResult->setRowCount(ui->tableWidgetDiagResult->rowCount()+1);
            ui->tableWidgetDiagResult->setItem(ui->tableWidgetDiagResult->rowCount()-1,0,new QTableWidgetItem(CombinedInfo));
        }
    }

    bool FlagTimerDelayStart=false;
    if(ui->tableWidgetDiagResult->rowCount()==0)
    {
        ui->tableWidgetDiagResult->setRowCount(1);
        ui->tableWidgetDiagResult->setItem(ui->tableWidgetDiagResult->rowCount()-1,0,new QTableWidgetItem("当前没有发现故障"));
    }
    else if((ui->tableWidgetDiagResult->rowCount()==1)&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()=="当前没有发现故障"))
    {
        //qDebug()<<"当前没有发现故障,FlagTimerDelayStart=true";
        FlagTimerDelayStart=true;
    }
    else if((ui->tableWidgetDiagResult->rowCount()==1)&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()!="诊断未开始")&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()!="当前没有发现故障"))
    {
        //qDebug()<<"only one candidate,FlagTimerDelayStart=true";
        FlagTimerDelayStart=true;
    }
    else if((ui->tableWidgetDiagResult->rowCount()==1)&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()=="诊断未开始"))
        ui->tableWidgetDiagResult->item(0,0)->setText("诊断流程已启动");

    //只有一种器件或没有推荐的测试点了
    if(ui->tableWidgetDiagResult->rowCount()>1)
    {
        QString FirstUnitName=ui->tableWidgetDiagResult->item(0,0)->text().mid(0,ui->tableWidgetDiagResult->item(0,0)->text().indexOf(":"));
        bool AllSame=true;
        for(int i=1;i<ui->tableWidgetDiagResult->rowCount();i++)
        {
            if(ui->tableWidgetDiagResult->item(i,0)->text().mid(0,ui->tableWidgetDiagResult->item(i,0)->text().indexOf(":"))!=FirstUnitName)
            {
                AllSame=false;
                break;
            }
        }
        if(AllSame)
        {
            //qDebug()<<"AllSame,FlagTimerDelayStart=true";
            FlagTimerDelayStart=true;
        }
        else
        {
            if(test_point.count()==0)
            {
                //qDebug()<<"test_point.count()==0,FlagTimerDelayStart=true";
                FlagTimerDelayStart=true;
            }
            else
            {
                bool AllZero=true;
                for(int i=0;i<test_point.count();i++)
                {
                    if(test_point.at(i).calculate>0) AllZero=false;
                }
                if(AllZero)
                {
                    //qDebug()<<"AllZero,FlagTimerDelayStart=true";
                    FlagTimerDelayStart=true;
                }
            }
        }
    }

    //PrintCandidateList();
    GetTestPoint();
    SortTestPoint(test_point,TestPointPreference);
    ui->tableWidgetTestPoint->setRowCount(0);
    for(int i=0;i<test_point.count();i++)
    {
        ui->tableWidgetTestPoint->setRowCount(ui->tableWidgetTestPoint->rowCount()+1);
        ui->tableWidgetTestPoint->setItem(ui->tableWidgetTestPoint->rowCount()-1,0,new QTableWidgetItem(test_point.at(i).point_name));
        ui->tableWidgetTestPoint->setItem(ui->tableWidgetTestPoint->rowCount()-1,1,new QTableWidgetItem(QString::number(test_point.at(i).calculate)));
    }

    //将推荐的测点告诉诊断页面
    GetRecommendedTestPoint();

    if(FlagTimerDelayStart)  QTimer::singleShot(1000, this,SLOT(timerDealCmdResult()));
}

void MainWindow::timerDealCmdResult()
{
    if(FlurWndIsActive) return;
    //qDebug()<<"timerDealCmdResult()";
    bool FlagShowFlurWnd=false;
    //TimerWaitForCmdResult.stop();

    if(ui->stackedWidget_main->currentIndex()!=2)
    {
        if((ui->tableWidgetDiagResult->rowCount()==1)&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()=="当前没有发现故障"))
        {
            SetStackIndex(6);
            ui->tableWidget_DiagResult->setRowCount(0);
            ui->label_diagnosis_TestWord->setText("诊断结束，当前没有发现故障");
            ui->label_result_2->setText("故障器件：无");
        }
    }

    if((ui->tableWidgetDiagResult->rowCount()==1)&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()!="诊断未开始")&&(ui->tableWidgetDiagResult->item(0,0)->text().trimmed()!="当前没有发现故障"))
    {
        FlagShowFlurWnd=true;
        //on_BtnFlurUnits_clicked();
    }

    //只有一种器件或没有推荐的测试点了
    if(ui->tableWidgetDiagResult->rowCount()>1)
    {
        QString FirstUnitName=ui->tableWidgetDiagResult->item(0,0)->text().mid(0,ui->tableWidgetDiagResult->item(0,0)->text().indexOf(":"));
        bool AllSame=true;
        for(int i=1;i<ui->tableWidgetDiagResult->rowCount();i++)
        {
            if(ui->tableWidgetDiagResult->item(i,0)->text().mid(0,ui->tableWidgetDiagResult->item(i,0)->text().indexOf(":"))!=FirstUnitName)
            {
                AllSame=false;
                break;
            }
        }
        if(AllSame) FlagShowFlurWnd=true;
        else
        {
            if(test_point.count()==0) FlagShowFlurWnd=true;
            else
            {
                bool AllZero=true;
                for(int i=0;i<test_point.count();i++)
                {
                    if(test_point.at(i).calculate>0) AllZero=false;
                }
                if(AllZero) FlagShowFlurWnd=true;
            }
        }
    }

    if(FlagShowFlurWnd) on_BtnFlurUnits_clicked();
}

void MainWindow::PrintCandidateList()
{
    qDebug()<<"Print Candidate Size " + QString::number(candidate_list.count());
    for(CandidateData data : candidate_list)
        qDebug()<<
                   "FaultSpur " + data.FaultSpur +
                   " modeTransition " + data.modeTransition +
                   " PriorVal " + data.PriorVal +
                   " FaultProbability " + QString::number(data.FaultProbability,'f',10); // f 表示非科学记数法 10表示小数点后保留10位
}
bool MainWindow::isHaveCandidate(const CandidateData& data)
{
    for(CandidateData temp_data : candidate_list)
    {
        if(temp_data.FaultSpur == data.FaultSpur
                && temp_data.modeTransition == data.modeTransition
                && temp_data.PriorVal == data.PriorVal)

            return true;
    }

    return false;
}

void MainWindow::UpdateModuleFaultProb()
{
    module_fault_prob.clear();
    for(CandidateData& data : candidate_list)
    {
        if(module_fault_prob.find(data.FaultSpur.split('.')[0]) == module_fault_prob.end())
        {
            module_fault_prob[data.FaultSpur.split('.')[0]] = data.FaultProbability;
        }
        else
        {
            module_fault_prob[data.FaultSpur.split('.')[0]] = module_fault_prob[data.FaultSpur.split('.')[0]] + data.FaultProbability - data.FaultProbability * module_fault_prob[data.FaultSpur.split('.')[0]];
        }

    }

    //    //输出module_fault_prob
    //    qDebug()<<"输出module_fault_prob";
    //    QMap<QString, double>::iterator it;
    //    for(it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
    //        qDebug()<<it.key()<<QString::number(it.value());
}

void MainWindow::on_readerror()
{
    //if(cmdStarted) QMessageBox::information(0, "Info", cmdDiagnose->readAllStandardError().data());
}

void MainWindow::InitTEdit()
{
    QsciEdit = new QsciScintilla();
    ui->TEditLayout->addWidget(QsciEdit);
    ui->frame_Edit->setLayout(ui->TEditLayout);
    //connect(QsciEdit, SIGNAL(textChanged()),this, SLOT(ModelWasModified()));
    //setCurrentFile("");
    //设置字体
    QFont font("Courier", 10, QFont::Normal);
    QsciEdit->setFont(font);
    QsciEdit->setMarginsFont(font);
    QFontMetrics fontmetrics = QFontMetrics(font);
    //设置左侧行号栏宽度等
    QsciEdit->setMarginWidth(0, fontmetrics.width("000"));
    QsciEdit->setMarginLineNumbers(0, true);
    QsciEdit->setBraceMatching(QsciScintilla::SloppyBraceMatch);
    QsciEdit->setTabWidth(4);
    //设置括号等自动补全
    QsciEdit->setAutoIndent(true);
    //初始设置c++解析器
    //textEdit->setLexer(new QsciLexerCPP(this));
    QscilexerCppAttach *textLexer = new QscilexerCppAttach;
    textLexer->setColor(QColor(Qt:: yellow),QsciLexerCPP::CommentLine);    //设置自带的注释行为绿色
    textLexer->setColor(QColor(Qt::red),QsciLexerCPP::KeywordSet2);
    QsciEdit->setLexer(textLexer);
    //设置自动补全

    QsciAPIs *apis = new QsciAPIs(textLexer);
    apis->add(QString("DEF"));
    apis->add(QString("PORT"));
    apis->add(QString("METER"));
    apis->add(QString("METER_PIC"));
    apis->add(QString("METER_MODE"));

    apis->prepare();

    QFont font1("Courier", 10, QFont::Normal);
    //    this->setFont(font1);

    QsciEdit->setAutoCompletionSource(QsciScintilla::AcsAll);   //设置源，自动补全所有地方出现的
    QsciEdit->setAutoCompletionCaseSensitivity(true);   //设置自动补全大小写敏感
    QsciEdit->setAutoCompletionThreshold(2);    //设置每输入2个字符就会出现自动补全的提示

    QsciEdit->setCaretLineVisible(true);
    //设置光标所在行背景色
    QsciEdit->setCaretLineBackgroundColor(Qt::lightGray);

    // ui->textEdit->setCursorPosition(2,2);
    //int markerDefine(MarkerSymbol sym, int markerNumber = -1);
    QsciEdit->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
    //得到光标位置
    int line,col;
    QsciEdit->getCursorPosition(&line,&col);

    //设置显示字体
    QsciEdit->setFont(QFont("Courier New"));
    //设置编码方式
    QsciEdit->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
}

void MainWindow::closeEvent(QCloseEvent *event)
{
//    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("warn"),"是否退出软件?",
//                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

//    if(result==QMessageBox::Yes)
//    {
//        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
//        {
//            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
//            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->dwgFileName);
//        }
//        cmdDiagnose->waitForFinished(500);
//        cmdDiagnose->close();
//        event->accept();
//    }
//    else event->ignore();
      event->accept();
}

