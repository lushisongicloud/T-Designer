#include "mainwindow.h"
#include "ui_mainwindow.h"
#include <ActiveQt/QAxObject>
#include <ActiveQt/QAxWidget>
#include <QTimer>
#include <QFileInfo>
#include <QStringList>
#include <QMenu>
#include <QSet>
#include <QInputDialog>
#include "BO/containerrepository.h"
#include "widget/containertreedialog.h"
#include "DO/containerentity.h"
#include "widget/containerhierarchyutils.h"
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

void MainWindow::updateCounterLink(int Link_ID,QString LinkText)
{
    qDebug()<<"updateCounterLink,Link_ID="<<Link_ID<<"LinkText="<<LinkText;
    QSqlQuery QueryCounterLink = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Link WHERE Link_ID = "+QString::number(Link_ID);
    QueryCounterLink.exec(SqlStr);
    if(!QueryCounterLink.next()) return;
    QString dwgfilename=GetPageNameByPageID(QueryCounterLink.value("Page_ID").toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"dwgfilename="<<dwgfilename<<" dwgfilepath="<<dwgfilepath<<"blk handle="<<QueryCounterLink.value("Link_Handle").toString();
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    IMxDrawBlockReference *blkNode;
    //查看是否已经打开改图纸
    bool DwgOpened=false;
    int MdiIndex=0;
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            blkNode= (IMxDrawBlockReference*) ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->querySubObject("HandleToObject(const QString)",QueryCounterLink.value("Link_Handle").toString());
            DwgOpened=true;
            MdiIndex=i;
            break;
        }
    }
    qDebug()<<"DwgOpened="<<DwgOpened<<" ,MdiIndex="<<MdiIndex;
    if(!DwgOpened)
    {
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath);
        blkNode= (IMxDrawBlockReference*) GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryCounterLink.value("Link_Handle").toString());
    }
    if(blkNode==nullptr) {qDebug()<<"blkNode=null";return;}
    QString RetStrLinkTextPosition;
    if(QueryCounterLink.value("LinkText_Location").toString()=="0") RetStrLinkTextPosition="箭头";
    else RetStrLinkTextPosition="箭尾";
    if(DwgOpened) LoadLinkText(((formaxwidget *)ui->mdiArea->subWindowList().at(MdiIndex)->widget())->GetAxWidget(),blkNode,QueryCounterLink.value("Link_Label").toString(),LinkText,RetStrLinkTextPosition,QueryCounterLink.value("Link_Name").toString());
    else LoadLinkText(GlobalBackAxWidget,blkNode,QueryCounterLink.value("Link_Label").toString(),LinkText,RetStrLinkTextPosition,QueryCounterLink.value("Link_Name").toString());
    if(!DwgOpened) //((formaxwidget *)ui->mdiArea->subWindowList().at(MdiIndex)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
        GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}
void MainWindow::DeleteDwgTerminalByPageAndHandle(QString Page_ID,QString Handle)
{
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"DeleteDwgSymbolByPageAndHandle,dwgfilepath="<<dwgfilepath<<"Handle="<<Handle;
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->DeleteEnty(Handle);
            return;
        }
    }
    bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    qDebug()<<"DeleteDwgTerminalByPageAndHandle,OpenDwgFile "<<opened;
    IMxDrawEntity *EntyDelete=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",Handle);
    if(EntyDelete!=nullptr) EntyDelete->dynamicCall("Erase()");
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::UpdateDwgBlkTagByPage_ID(int Page_ID,QString Handle,QString TagStr,QString ProjectStructure_ID)
{
    QString dwgfilename=GetPageNameByPageID(Page_ID);
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->querySubObject("HandleToObject(const QString)",Handle);
            if(BlkEnty!=nullptr)
            {
                if(GetProjectStructureIDByPageID(Page_ID)==ProjectStructure_ID)
                    UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr.mid(TagStr.lastIndexOf("-"),TagStr.count()-TagStr.lastIndexOf("-")));
                else
                    UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr);
                //((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
                return;
            }
        }
    }
    const bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    Q_UNUSED(opened);
    IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",Handle);
    if(BlkEnty!=nullptr)
    {
        if(GetProjectStructureIDByPageID(Page_ID)==ProjectStructure_ID)
            UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr.mid(TagStr.lastIndexOf("-"),TagStr.count()-TagStr.lastIndexOf("-")));
        else
            UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TagStr);
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::DeleteGroup(QString Page_ID,QString GroupName)
{
    qDebug()<<"DeleteGroup";
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("DeleteGroup(QString)",GroupName);
            return;
        }
    }
    const bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    Q_UNUSED(opened);
    GlobalBackAxWidget->dynamicCall("DeleteGroup(QString)",GroupName);
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::DeleteDwgSymbolByPageAndHandle(QString Page_ID,QString Symbol_Handle)
{
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"DeleteDwgSymbolByPageAndHandle,dwgfilepath="<<dwgfilepath<<"Symbol_Handle="<<Symbol_Handle;
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看page是否已打开
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->DeleteEnty(Symbol_Handle);
            return;
        }
    }
    bool opened = GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath).toBool();
    qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<opened;
    IMxDrawEntity *EntyDelete=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",Symbol_Handle);
    if(EntyDelete!=nullptr)
    {
        //如果是黑盒，删除对应的MText
        QString LD_GROUPCPXRECT_TEXT=EntyDelete->dynamicCall("GetxDataString2(QString,0)","LD_GROUPCPXRECT_TEXT",0).toString();
        if(GlobalBackAxWidget->dynamicCall("IsOk()").toString()=="true")
        {
            IMxDrawMText *EntyMText=(IMxDrawMText *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",LD_GROUPCPXRECT_TEXT);
            if(EntyMText!=nullptr) EntyMText->dynamicCall("Erase()");
        }
        EntyDelete->dynamicCall("Erase()");
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
}

void MainWindow::SlotSpurAttr()
{
    ShowSpurAttr(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
}

void MainWindow::UpdateTerminalInstanceByTerminalInstance_ID(int TerminalInstance_ID)
{
    //如果符号名称发生变化，则删除原图块并重新绘制图块
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID= "+QString::number(TerminalInstance_ID);
    QueryTerminalInstance.exec(SqlStr);
    while(QueryTerminalInstance.next())
    {
        if(QueryTerminalInstance.value("Handle").toString()=="") return;
        QString Page_ID=QueryTerminalInstance.value("Page_ID").toString();
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        qDebug()<<"dwgfilepath="<<dwgfilepath;
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) return;

        formaxwidget *formMxdraw;
        bool DwgIsOpened=false;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
                DwgIsOpened=true;
                break;
            }
        }
        if(!DwgIsOpened) {formMxdraw=new formaxwidget(this,dwgfilepath,Page_ID.toInt());formMxdraw->setVisible(false);}
        IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",QueryTerminalInstance.value("Handle").toString());

        //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字
        if(BlkEnty!=nullptr)
        {
            QSqlQuery QueryTerminalStrip=QSqlQuery(T_ProjectDatabase);
            QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QueryTerminalInstance.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(SqlStr);
            if(QueryTerminalStrip.next())
            {
                qDebug()<<"端子/插针代号="<<QueryTerminalInstance.value("Designation").toString();
                //如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
                QString TerminalTag;
                TerminalTag=QueryTerminalStrip.value("DT").toString();
                if(CheckTerminalBeside(TerminalInstance_ID,formMxdraw->GetAxWidget())) TerminalTag="";
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TerminalTag);
                UpdateBlockAttr(BlkEnty,"端子/插针代号",QueryTerminalInstance.value("Designation").toString());
                UpdateBlockAttr(BlkEnty,"左连接点",QueryTerminalInstance.value("LeftTerm").toString());
                UpdateBlockAttr(BlkEnty,"右连接点",QueryTerminalInstance.value("RightTerm").toString());
                UpdateBlockAttr(BlkEnty,"上连接点",QueryTerminalInstance.value("UpTerm").toString());
                UpdateBlockAttr(BlkEnty,"下连接点",QueryTerminalInstance.value("DownTerm").toString());

            }
            formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
        }
        if(!DwgIsOpened) delete formMxdraw;
    }
}

void MainWindow::UpdateTerminalByTerminal_ID(int Terminal_ID)
{
    //如果符号名称发生变化，则删除原图块并重新绘制图块
    QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE Terminal_ID= '"+QString::number(Terminal_ID)+"'";
    QueryTerminalInstance.exec(SqlStr);
    while(QueryTerminalInstance.next())
    {
        if(QueryTerminalInstance.value("Handle").toString()=="") return;
        QString Page_ID=QueryTerminalInstance.value("Page_ID").toString();
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        qDebug()<<"dwgfilepath="<<dwgfilepath;
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) return;

        formaxwidget *formMxdraw;
        bool DwgIsOpened=false;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
                DwgIsOpened=true;
                break;
            }
        }
        if(!DwgIsOpened) {formMxdraw=new formaxwidget(this,dwgfilepath,Page_ID.toInt());formMxdraw->setVisible(false);}
        IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",QueryTerminalInstance.value("Handle").toString());
        //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字
        if(BlkEnty!=nullptr)
        {
            QSqlQuery QueryTerminalStrip=QSqlQuery(T_ProjectDatabase);
            QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QueryTerminalInstance.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(SqlStr);
            if(QueryTerminalStrip.next())
            {
                //如果元件和Page在同一个高层和位置，则不显示高层和代号，反之则显示高层和代号
                QString TerminalTag;
                TerminalTag=QueryTerminalStrip.value("DT").toString();

                if(CheckTerminalBeside(Terminal_ID,formMxdraw->GetAxWidget())) TerminalTag="";
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)",TerminalTag);
                UpdateBlockAttr(BlkEnty,"端子/插针代号",QueryTerminalInstance.value("Designation").toString());
                UpdateBlockAttr(BlkEnty,"左连接点",QueryTerminalInstance.value("LeftTerm").toString());
                UpdateBlockAttr(BlkEnty,"右连接点",QueryTerminalInstance.value("RightTerm").toString());
                UpdateBlockAttr(BlkEnty,"上连接点",QueryTerminalInstance.value("UpTerm").toString());
                UpdateBlockAttr(BlkEnty,"下连接点",QueryTerminalInstance.value("DownTerm").toString());

            }
            formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
        }
        if(!DwgIsOpened) delete formMxdraw;
    }
}

void MainWindow::UpdateSpurBySymbol_ID(int Symbol_ID)
{
    qDebug()<<"UpdateSpurBySymbol_ID,Symbol_ID="<<Symbol_ID;
    //如果符号名称发生变化，则删除原图块并重新绘制图块
    QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(Symbol_ID);
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return;
    if(QuerySymbol.value("Symbol_Handle").toString()=="") return;
    QString Page_ID=QuerySymbol.value("Page_ID").toString();
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"dwgfilepath="<<dwgfilepath;
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    formaxwidget *formMxdraw;
    bool DwgIsOpened=false;
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
            DwgIsOpened=true;
            break;
        }
    }
    if(!DwgIsOpened) {formMxdraw=new formaxwidget(this,dwgfilepath,Page_ID.toInt());formMxdraw->setVisible(false);}

    if((QuerySymbol.value("Symbol").toString()=="")&&(QuerySymbol.value("FunDefine").toString()=="黑盒"))//黑盒
    {
        QString DT_Handle=QuerySymbol.value("DT_Handle").toString();
        IMxDrawMText* DTMText=(IMxDrawMText *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",DT_Handle);
        int Equipment_ID=GetUnitStripIDBySymbolID(QString::number(Symbol_ID),0);
        QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID);
        QueryEquipment.exec(SqlStr);
        QueryEquipment.next();
        QString SymbolTag;
        if(GetProjectStructureIDByPageID(QuerySymbol.value("Page_ID").toInt())==QueryEquipment.value("ProjectStructure_ID").toString())
            SymbolTag="-"+QueryEquipment.value("DT").toString();
        else
            SymbolTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();

        DTMText->dynamicCall("SetContents(QString)",SymbolTag);
        formMxdraw->GetAxWidget()->dynamicCall("UpdateDisplay()");
        return;
    }

    IMxDrawBlockReference *BlkEnty=formMxdraw->UpdateSymbolBlock(QuerySymbol.value("Symbol_Handle").toString(),QuerySymbol.value("Symbol").toString());
    //如果BlkEnty和数据库Terminal表中记录的Handle不一致，则重新插入BlkEnty的块属性文字
    if(BlkEnty!=nullptr)
    {
        QString Symbol_Category=QuerySymbol.value("Symbol_Category").toString();
        QString OriginalHandle=QuerySymbol.value("Symbol_Handle").toString();
        qDebug()<<"OriginalHandle="<<OriginalHandle<<" now="<<BlkEnty->dynamicCall("handle()").toString();
        //更新Symbol表
        QSqlQuery QuerySymbolUpdate=QSqlQuery(T_ProjectDatabase);
        QString tempSQL="UPDATE Symbol SET Symbol_Handle=:Symbol_Handle WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbolUpdate.prepare(tempSQL);
        QuerySymbolUpdate.bindValue(":Symbol_Handle",BlkEnty->dynamicCall("handle()").toString());
        QuerySymbolUpdate.exec();

        QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QuerySymbol.value("Equipment_ID").toString();
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QString SymbolTag;
            QSqlQuery QueryProjectStructure = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryEquipment.value("ProjectStructure_ID").toString());
            QueryProjectStructure.exec(SqlStr);
            qDebug()<<"CheckProjectStructure_IDSameOrNot,"<<GetProjectStructureIDByPageID(QuerySymbol.value("Page_ID").toInt())<<" ,"<<QueryEquipment.value("ProjectStructure_ID").toString();
            if(GetProjectStructureIDByPageID(QuerySymbol.value("Page_ID").toInt())==QueryEquipment.value("ProjectStructure_ID").toString())
                SymbolTag="-"+QueryEquipment.value("DT").toString();
            else
                SymbolTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();

            //如果在结构盒内部，则SymbolTag为-Tag
            int  StructBoxVal=CheckStructBox(formMxdraw->GetAxWidget(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y());
            if(StructBoxVal>0) SymbolTag="-"+QueryEquipment.value("DT").toString();

            if(CheckSpinBeside(Symbol_ID,formMxdraw->GetAxWidget())) SymbolTag="";
            int  BlackBoxVal=CheckBlackBox(formMxdraw->GetAxWidget(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->x(),((IMxDrawPoint *)BlkEnty->querySubObject("Position()"))->y(),Symbol_ID);
            //查看Symbol是否在黑盒内部，如果不是的话返回0，如果是并且黑盒和Symbol是同元件则返回Equipment_ID，如果是并且黑盒和Symbol是不同元件则返回-1
            if(BlackBoxVal!=0) SymbolTag="";
            //这里需要判断是否在黑盒内
            if(OriginalHandle!=BlkEnty->dynamicCall("handle()").toString())
                FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"设备标识符(显示)",SymbolTag);
            else
                UpdateBlockAttr(BlkEnty,"设备标识符(显示)",SymbolTag);
        }
        if(Symbol_Category=="插针")
        {
            if(OriginalHandle!=BlkEnty->dynamicCall("handle()").toString())
                FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"端子/插针代号",QuerySymbol.value("Designation").toString());
            else
                UpdateBlockAttr(BlkEnty,"端子/插针代号",QuerySymbol.value("Designation").toString());
        }
        //更新Symb2TermInfo表
        //更新Symb2TermInfo表，包括Conn_Coordinate，ConnDirection
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QString::number(Symbol_ID)+"'";
        QuerySymb2TermInfo.exec(SqlStr);
        while(QuerySymb2TermInfo.next())
        {
            //如果Symbol_Category是插针，则不添加连接点代号和连接点描述，添加端子/插针代号
            //找到端点并添加块属性
            QString ConnNum_Logic=QuerySymb2TermInfo.value("ConnNum_Logic").toString();
            QString ConnNum=QuerySymb2TermInfo.value("ConnNum").toString();
            QString ConnDesc=QuerySymb2TermInfo.value("ConnDesc").toString();
            if(Symbol_Category!="插针")
            {
                if(OriginalHandle!=BlkEnty->dynamicCall("handle()").toString())
                {
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,ConnNum_Logic,ConnNum);//连接点代号
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"符号的连接点描述["+ConnNum_Logic+"]",ConnDesc);//连接点描述
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"连接点描述（全部）",ConnDesc);//连接点描述（全部）
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"连接点代号（带显示设备标识符）",QueryEquipment.value("DT").toString()+":"+ConnNum);//连接点代号
                    FindAttrDefAndAddAttrToBlock(formMxdraw->GetAxWidget(),BlkEnty,"连接点代号（全部）",ConnNum);//连接点代号（全部）
                }
                else
                {
                    UpdateBlockAttr(BlkEnty,ConnNum_Logic,ConnNum);//连接点代号
                    UpdateBlockAttr(BlkEnty,"符号的连接点描述["+ConnNum_Logic+"]",ConnDesc);
                    UpdateBlockAttr(BlkEnty,"连接点描述（全部）",ConnDesc);
                    UpdateBlockAttr(BlkEnty,"连接点代号（带显示设备标识符）",QueryEquipment.value("DT").toString()+":"+ConnNum);//连接点代号
                    UpdateBlockAttr(BlkEnty,"连接点代号（全部）",ConnNum);
                }
            }
            SqlStr="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate WHERE Symb2TermInfo_ID= "+QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString();
            QSqlQuery QueryUpdate = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QueryUpdate.prepare(SqlStr);
            QString InsertionPoint=QString::number(GetSymbolBlockTermPos(formMxdraw->GetAxWidget(),BlkEnty,ConnNum_Logic)->x(),'f',0)+".000000";
            InsertionPoint+=","+QString::number(GetSymbolBlockTermPos(formMxdraw->GetAxWidget(),BlkEnty,ConnNum_Logic)->y(),'f',0)+".000000";
            InsertionPoint+=",0.000000";
            QueryUpdate.bindValue(":Conn_Coordinate",InsertionPoint);
            QueryUpdate.exec();
        }
        formMxdraw->GetAxWidget()->dynamicCall("UpdateDisplay()");
        if(!DwgIsOpened) formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
    }
    if(!DwgIsOpened) delete formMxdraw;
}

void MainWindow::ShowSpurAttr(int Symbol_ID)
{
    DialogBranchAttr *dlgBranchAttr=new DialogBranchAttr(this);
    //dlgBranchAttr->move(QApplication::desktop()->screenGeometry().width()/2-dlgBranchAttr->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgBranchAttr->height()/2);
    dlgBranchAttr->LoadSymbolInfo(QString::number(Symbol_ID));
    dlgBranchAttr->show();
    dlgBranchAttr->exec();
    qDebug()<<"dlgBranchAttr->RetCode="<<dlgBranchAttr->RetCode;
    if(dlgBranchAttr->RetCode==1)
    {
        //如果符号发生变化，则删除原图块并重新绘制图块
        QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
        int Equipment_ID=0;
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
        UpdateSpurBySymbol_ID(Symbol_ID);

        SelectEquipment_ID=Equipment_ID;
        SelectSymbol_ID=Symbol_ID;

        if(dlgBranchAttr->DTChanged)
        {
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"' AND Symbol_ID <> "+QString::number(Symbol_ID);
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                UpdateSpurBySymbol_ID(QuerySymbol.value("Symbol_ID").toInt());
            }
        }
        //更新导航窗口
        LoadProjectUnits();
    }
    else if(dlgBranchAttr->RetCode==2)//显示元件属性窗口
    {
        QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
        int Equipment_ID=0;
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
        SelectEquipment_ID=Equipment_ID;
        SelectSymbol_ID=Symbol_ID;
        LoadProjectUnits();
        ShowUnitAttr();
    }
}

bool MainWindow::GetTerminalTagVisible(int TerminalInstanceID,bool Update,bool Visible)
{
    QSqlQuery QueryTerminalInstance= QSqlQuery(T_ProjectDatabase);
    //QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(Terminal_ID);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+QString::number(TerminalInstanceID);
    QueryTerminalInstance.exec(SqlStr);
    if(QueryTerminalInstance.next())
    {
        QString TerminalHandle=QueryTerminalInstance.value("Handle").toString();
        if(TerminalHandle=="") return true;
        QString Page_ID=QueryTerminalInstance.value("Page_ID").toString();
        QSqlQuery queryPage=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Page WHERE Page_ID= "+Page_ID;
        queryPage.exec(SqlStr);
        if(!queryPage.next()) return true;
        //查看是否已经打开改图纸
        bool AlreadyOpened=false;
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                AlreadyOpened=true;
                break;
            }
        }
        if(!AlreadyOpened) return true;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
            if(formMxdraw->Page_IDInDB==Page_ID.toInt())
            {
                IMxDrawBlockReference *BlkEnty=(IMxDrawBlockReference *)formMxdraw->GetAxWidget()->querySubObject("HandleToObject(const QString)",TerminalHandle);
                if(!Update)
                {
                    if(GetBlockAttrTextString(BlkEnty,"设备标识符(显示)")=="") return false;
                    else return true;
                }
                else
                {
                    if(Visible)
                    {
                        QSqlQuery QueryTerminalStrip= QSqlQuery(T_ProjectDatabase);
                        QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+QueryTerminalInstance.value("TerminalStrip_ID").toString();
                        QueryTerminalStrip.exec(SqlStr);
                        if(QueryTerminalStrip.next())
                            UpdateBlockAttr(BlkEnty,"设备标识符(显示)",QueryTerminalStrip.value("DT").toString());
                    }
                    else
                        UpdateBlockAttr(BlkEnty,"设备标识符(显示)","");
                    formMxdraw->GetAxWidget()->dynamicCall("UpdateDisplay()");
                }
                break;
            }
        }
    }
    return false; //Lu ToDo 默认返回值
}

//Mode=0:图纸中双击显示属性 Mode=1:导航栏右键显示端子属性
void MainWindow::ShowTerminalAttr(int Mode,int ID)
{
    DialogSingleTermAttr *dlg=new DialogSingleTermAttr(this);
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    if(Mode==1) dlg->SetCbShowTagVisible(false);
    else if(Mode==0)
    {
        dlg->SetCbShowTagVisible(true);
        dlg->TerminalTagVisible=GetTerminalTagVisible(ID,false,true);
        qDebug()<<"dlg->TerminalTagVisible="<<dlg->TerminalTagVisible;
    }
    int Terminal_ID;
    if(Mode==0) Terminal_ID=GetTerminal_IDByTerminalInstanceID(ID);
    else Terminal_ID=ID;
    if(Mode==0) dlg->LoadInfo(Terminal_ID,ID);
    else dlg->LoadInfo(Terminal_ID,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //如果符号名称发生变化，则删除原图块并重新绘制图块
        QSqlQuery QueryTerminal= QSqlQuery(T_ProjectDatabase);
        int TerminalStrip_ID=0;
        QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(Terminal_ID);
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next())
        {
            TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toInt();
        }
        qDebug()<<"UpdateTerminalByTerminal_ID,ID="<<ID<<",Terminal_ID="<<Terminal_ID<<",Mode="<<Mode;
        if(Mode==0) UpdateTerminalInstanceByTerminalInstance_ID(ID);
        else UpdateTerminalByTerminal_ID(Terminal_ID);
        qDebug()<<"GetTerminalTagVisible";

        qDebug()<<"GetTerminalTagVisible over";
        SelectTerminalStrip_ID=TerminalStrip_ID;
        SelectTerminal_ID=Terminal_ID;
        if(Mode==0) GetTerminalTagVisible(ID,true,dlg->TerminalTagVisible);

        if(dlg->DTChanged)
        {
            SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QString::number(TerminalStrip_ID)+"' AND Terminal_ID <> "+QString::number(Terminal_ID);
            QueryTerminal.exec(SqlStr);
            while(QueryTerminal.next())
            {
                UpdateTerminalByTerminal_ID(QueryTerminal.value("Terminal_ID").toInt());
            }
        }

        //更新导航窗口
        LoadProjectTerminals();
    }
}
void MainWindow::SlotTerminalStripAttr()
{
    SelectTerminalStrip_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
    SelectTerminal_ID=0;
    ShowTerminalStripAttr(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
}

void MainWindow::SlotTerminalAttr()
{
    //Mode=0:图纸中双击显示属性 Mode=1:导航栏右键显示端子属性
    ShowTerminalAttr(1,ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
}
void MainWindow::ShowTerminalStripAttr(int TerminalStrip_ID)
{
    QSqlQuery QueryTerminalStrip_ID=QSqlQuery(T_ProjectDatabase);
    QString SqlStr=QString("SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(TerminalStrip_ID));
    QueryTerminalStrip_ID.exec(SqlStr);
    if(!QueryTerminalStrip_ID.next()) return;
    QString ProjectStructure_ID=QueryTerminalStrip_ID.value("ProjectStructure_ID").toString();
    qDebug()<<"ProjectStructure_ID="<<ProjectStructure_ID;
    QSqlQuery QueryProjectStructure=QSqlQuery(T_ProjectDatabase);
    SqlStr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID= "+ProjectStructure_ID);
    QueryProjectStructure.exec(SqlStr);
    if(!QueryProjectStructure.next()) return;
    QString StrProTag,StrGaoceng,StrPos;
    StrPos=QueryProjectStructure.value("Structure_INT").toString();
    StrProTag+="+"+StrPos;
    qDebug()<<"StrProTag="<<StrProTag;
    DialogTerminalAttr *dlg=new DialogTerminalAttr(this);
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    dlg->setWindowTitle("端子排属性");
    dlg->StrProTag=StrProTag;
    dlg->LoadInfo(2,TerminalStrip_ID);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) {delete dlg;return;}

    QSqlQuery QueryTerminal=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(TerminalStrip_ID)+"'";
    QueryTerminal.exec(SqlStr);
    while(QueryTerminal.next())
    {
        UpdateTerminalByTerminal_ID(QueryTerminal.value("Terminal_ID").toInt());
    }

    LoadProjectTerminals();
    delete dlg;
}

void MainWindow::ShowUnitAttrByEquipment_ID(int Equipment_ID)
{
    QSqlQuery QueryEquipment=QSqlQuery(T_ProjectDatabase);
    QString SqlStr=QString("SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID));
    QueryEquipment.exec(SqlStr);
    if(!QueryEquipment.next()) return;
    QString StrProTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt());
    //DialogUnitAttr *dlg=new DialogUnitAttr(this);
    //dlgUnitAttr->setGeometry(ui->mdiArea->x(),ui->mdiArea->y(),ui->mdiArea->width()+100,ui->mdiArea->height());
    //dlgUnitAttr->move(QApplication::desktop()->screenGeometry().width()/2-dlgUnitAttr->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgUnitAttr->height()/2);
    dlgUnitAttr->setWindowTitle("元件属性");
    dlgUnitAttr->StrProTag=StrProTag;
    dlgUnitAttr->LoadInfo(2,Equipment_ID);
    dlgUnitAttr->UnitTagChanged=false;
    dlgUnitAttr->UnitTypeChanged=false;
    dlgUnitAttr->setModal(true);
    dlgUnitAttr->show();
    dlgUnitAttr->exec();
    if(dlgUnitAttr->Canceled) {return;}
    SelectEquipment_ID=Equipment_ID;
    SelectSymbol_ID=0;
    if(dlgUnitAttr->UnitTypeChanged)
    {
        qDebug()<<"UnitTypeChanged";
        QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"元件型号改变，是否删除原元件下的功能子块?",
                                                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);
        if(result==QMessageBox::Yes)
        {
            QSqlQuery QueryDeleteSymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(SelectEquipment_ID)+"'";
            QueryDeleteSymbol.exec(SqlStr);
            while(QueryDeleteSymbol.next())
            {
                QString Symbol_ID=QueryDeleteSymbol.value("Symbol_ID").toString();
                //删除已绘制的符号
                if(QueryDeleteSymbol.value("Symbol_Handle").toString()!="")
                {
                    DeleteDwgSymbolByPageAndHandle(QueryDeleteSymbol.value("Page_ID").toString(),QueryDeleteSymbol.value("Symbol_Handle").toString());
                }
                QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                QString temp =  QString("DELETE FROM Symb2TermInfo WHERE Symbol_ID = '"+Symbol_ID+"'");
                querySymb2TermInfo.exec(temp);
            }
            SqlStr =  QString("DELETE FROM Symbol WHERE Equipment_ID= '"+QString::number(SelectEquipment_ID)+"'");
            QueryDeleteSymbol.exec(SqlStr);
        }
        //更新Symbol表和Symb2TermInfo表
        AddSymbTblAndSymb2TermInfoTbl(dlgUnitAttr->LibEquipment_ID,QString::number(SelectEquipment_ID),"",dlgUnitAttr->ListSymbolSpurInfo);
    }
    else
    {
        qDebug()<<"else";
        //如果标号修改了，则更新标号
        if(dlgUnitAttr->UnitTagChanged)
        {
            qDebug()<<"UnitTagChanged";
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+dlgUnitAttr->CurEquipment_ID+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")
                {
                    UpdateSpurBySymbol_ID(QuerySymbol.value("Symbol_ID").toInt());
                }
            }
        }
    }
    LoadProjectUnits();
}

void MainWindow::ShowUnitAttr()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
    ShowUnitAttrByEquipment_ID(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
}

void MainWindow::NewTerminalStrip()//新建端子排
{
    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增端子排；如果是高层，则在高层下的第一个位置新增端子排；如果是位置，则在位置下新增端子排
    QString StrProTag,StrGaoceng,StrPos;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        qDebug()<<"项目";
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在高层
        {
            StrGaoceng=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            qDebug()<<"StrGaoceng="<<StrGaoceng;
            if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->rowCount()>0)//存在位置
                StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
            qDebug()<<"StrPos="<<StrPos;
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        qDebug()<<"高层";
        StrGaoceng=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        qDebug()<<"StrGaoceng="<<StrGaoceng;
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在位置
        {
            StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            qDebug()<<"StrPos="<<StrPos;
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        qDebug()<<"位置";
        StrPos=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        if(ui->treeViewTerminal->currentIndex().parent().isValid())//高层
        {
            StrGaoceng=ui->treeViewTerminal->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
    }
    StrProTag+="="+StrGaoceng+"+"+StrPos;
    DialogTerminalAttr *dlg=new DialogTerminalAttr(this);
    connect(dlg,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
    dlg->move(QApplication::desktop()->screenGeometry().width()/2-dlg->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlg->height()/2);
    dlg->setWindowTitle("新建端子排");
    dlg->StrProTag=StrProTag;
    dlg->LoadInfo(1,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        LoadProjectTerminals();
    }
    //如果端子符号变更，需要更新dwg文件中的符号

    delete dlg;

}

int MainWindow::PasteTerminalByTerminal_ID(int TerminalStrip_ID,int Terminal_ID)
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID= "+QString::number(Terminal_ID);
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next()) return 0;

    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = QString("INSERT INTO Terminal (Terminal_ID,TerminalStrip_ID,Designation,Symbol,Terminalfunction,TerminalType,TerminalName,PartCode,FunctionText,FunDefine,Factory,OrderNum) "
                     "VALUES (:Terminal_ID,:TerminalStrip_ID,:Designation,:Symbol,:Terminalfunction,:TerminalType,:TerminalName,:PartCode,:FunctionText,:FunDefine,:Factory,:OrderNum)");
    QueryVar.prepare(SqlStr);
    int MaxTerminal_ID=GetMaxIDOfDB(T_ProjectDatabase,"Terminal","Terminal_ID");
    QueryVar.bindValue(":Terminal_ID",MaxTerminal_ID);
    QueryVar.bindValue(":TerminalStrip_ID",QString::number(TerminalStrip_ID));
    QueryVar.bindValue(":Designation",QuerySearch.value("Designation").toString());
    QueryVar.bindValue(":Symbol",QuerySearch.value("Symbol").toString());
    QueryVar.bindValue(":Terminalfunction",QuerySearch.value("Terminalfunction").toString());
    QueryVar.bindValue(":TerminalType",QuerySearch.value("TerminalType").toString());
    QueryVar.bindValue(":TerminalName",QuerySearch.value("TerminalName").toString());
    QueryVar.bindValue(":PartCode",QuerySearch.value("PartCode").toString());
    QueryVar.bindValue(":FunctionText",QuerySearch.value("FunctionText").toString());
    QueryVar.bindValue(":FunDefine",QuerySearch.value("FunDefine").toString());
    QueryVar.bindValue(":Factory",QuerySearch.value("Factory").toString());
    QueryVar.bindValue(":OrderNum",QuerySearch.value("OrderNum").toString());
    QueryVar.exec();

    SqlStr="SELECT * FROM TerminalTerm WHERE Terminal_ID= '"+QString::number(Terminal_ID)+"'";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum) "
                         "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum)");
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":TerminalTerm_ID",GetMaxIDOfDB(T_ProjectDatabase,"TerminalTerm","TerminalTerm_ID"));
        QueryVar.bindValue(":Terminal_ID",QString::number(MaxTerminal_ID));
        QueryVar.bindValue(":ConnNum_Logic",QuerySearch.value("ConnNum_Logic").toString());
        QueryVar.bindValue(":ConnNum",QuerySearch.value("ConnNum").toString());
        QueryVar.exec();
    }
    return MaxTerminal_ID;
}

int MainWindow::PasteSpurBySymbol_ID(int Equipment_ID,int Symbol_ID)
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(Symbol_ID);
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next()) return 0;

    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Designation,Symbol_Handle,Symbol_Remark,FunDefine,FuncType,SourceConn,ExecConn,SourcePrior)"
             " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Designation,:Symbol_Handle,:Symbol_Remark,:FunDefine,:FuncType,:SourceConn,:ExecConn,:SourcePrior)";
    QuerySymbol.prepare(SqlStr);
    int MaxSymbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");
    QuerySymbol.bindValue(":Symbol_ID",MaxSymbol_ID);
    QuerySymbol.bindValue(":Page_ID","");
    QuerySymbol.bindValue(":Equipment_ID",QString::number(Equipment_ID));
    QuerySymbol.bindValue(":Symbol",QuerySearch.value("Symbol").toString());
    QuerySymbol.bindValue(":Symbol_Category",QuerySearch.value("Symbol_Category").toString());
    QuerySymbol.bindValue(":Symbol_Desc",QuerySearch.value("Symbol_Desc").toString());
    QuerySymbol.bindValue(":Designation",QuerySearch.value("Designation").toString());
    QuerySymbol.bindValue(":Symbol_Handle","");
    QuerySymbol.bindValue(":Symbol_Remark",QuerySearch.value("Symbol_Remark").toString());
    QuerySymbol.bindValue(":FunDefine",QuerySearch.value("FunDefine").toString());
    QuerySymbol.bindValue(":FuncType",QuerySearch.value("FuncType").toString());
    QuerySymbol.bindValue(":SourceConn",QuerySearch.value("SourceConn").toBool());
    QuerySymbol.bindValue(":ExecConn",QuerySearch.value("ExecConn").toBool());
    QuerySymbol.bindValue(":SourcePrior",QuerySearch.value("SourcePrior").toString());
    QuerySymbol.exec();

    SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = QString("INSERT INTO Symb2TermInfo (Symb2TermInfo_ID,Symbol_ID,ConnNum_Logic,ConnNum,ConnDirection,Internal,ConnDesc,TestCost)"
                         "VALUES (:Symb2TermInfo_ID,:Symbol_ID,:ConnNum_Logic,:ConnNum,:ConnDirection,:Internal,:ConnDesc,:TestCost)");
        QuerySymb2TermInfo.prepare(SqlStr);
        QuerySymb2TermInfo.bindValue(":Symb2TermInfo_ID",GetMaxIDOfDB(T_ProjectDatabase,"Symb2TermInfo","Symb2TermInfo_ID"));
        QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(MaxSymbol_ID));
        QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QuerySearch.value("ConnNum_Logic").toString());
        QuerySymb2TermInfo.bindValue(":ConnNum",QuerySearch.value("ConnNum").toString());
        QuerySymb2TermInfo.bindValue(":ConnDirection",QuerySearch.value("ConnDirection").toString());
        QuerySymb2TermInfo.bindValue(":Internal",QuerySearch.value("Internal").toString());
        QuerySymb2TermInfo.bindValue(":ConnDesc",QuerySearch.value("ConnDesc").toString());
        QuerySymb2TermInfo.bindValue(":TestCost",QuerySearch.value("TestCost").toString());
        QuerySymb2TermInfo.exec();
    }
    return MaxSymbol_ID;
}

void MainWindow::PasteSpur()//粘贴功能子块
{
    if(CopySymbol_ID<=0) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="元件")
    {
        SelectSymbol_ID=PasteSpurBySymbol_ID(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt(),CopySymbol_ID);
        SelectEquipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
    }
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            SelectSymbol_ID=PasteSpurBySymbol_ID(QuerySearch.value("Equipment_ID").toInt(),CopySymbol_ID);
            SelectEquipment_ID=QuerySearch.value("Equipment_ID").toInt();
        }
    }
    LoadProjectUnits();
}

void MainWindow::PasteTerminalStrip()//粘贴端子排
{
    QString StrProTag,StrGaoceng,StrPos;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在高层
        {
            StrGaoceng=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->rowCount()>0)//存在位置
                StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        StrGaoceng=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        if(ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->rowCount()>0)//存在位置
        {
            StrPos=ModelTerminals->itemFromIndex(ui->treeViewTerminal->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        StrPos=ui->treeViewTerminal->currentIndex().data(Qt::DisplayRole).toString();
        if(ui->treeViewTerminal->currentIndex().parent().isValid())//高层
        {
            StrGaoceng=ui->treeViewTerminal->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
    }
    QString ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(CopyTerminalStrip_ID);
    QuerySearch.exec(SqlStr);
    if(!QuerySearch.next()) return;

    int MaxTerminalStrip_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalStrip","TerminalStrip_ID");
    //更新T_ProjectDatabase数据库的Equipment表
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = QString("INSERT INTO TerminalStrip (TerminalStrip_ID,DT,ProjectStructure_ID) VALUES (:TerminalStrip_ID,:DT,:ProjectStructure_ID)");
    QueryVar.prepare(SqlStr);
    QueryVar.bindValue(":TerminalStrip_ID",MaxTerminalStrip_ID);
    QueryVar.bindValue(":DT",GetStrRemoveLastNum(QuerySearch.value("DT").toString())+QString::number(GetStrLastNum(QuerySearch.value("DT").toString())+1));
    QueryVar.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
    QueryVar.exec();

    SqlStr="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(CopyTerminalStrip_ID)+"'";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        PasteTerminalByTerminal_ID(MaxTerminalStrip_ID,QuerySearch.value("Terminal_ID").toInt());
    }
    SelectTerminalStrip_ID=MaxTerminalStrip_ID;
    SelectTerminal_ID=0;
    LoadProjectTerminals();
}

//void MainWindow::PasteUnit()//粘贴元件
//{
//    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增元件；如果是高层，则在高层下的第一个位置新增元件；如果是位置，则在位置下新增元件
//    QString StrProTag,StrGaoceng,StrPos;
//    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
//    {
//        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在高层
//        {
//            StrGaoceng=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
//            if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->rowCount()>0)//存在位置
//                StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
//        }
//    }
//    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
//    {
//        StrGaoceng=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
//        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在位置
//        {
//            StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
//        }
//    }
//    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
//    {
//        StrPos=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
//        if(ui->treeViewUnits->currentIndex().parent().isValid())//高层
//        {
//            StrGaoceng=ui->treeViewUnits->currentIndex().parent().data(Qt::DisplayRole).toString();
//        }
//    }
//    QString ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
//    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
//    QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(CopyEquipment_ID);
//    QuerySearch.exec(SqlStr);
//    if(!QuerySearch.next()) return;

//    int MaxEquipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
//    //更新T_ProjectDatabase数据库的Equipment表
//    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
//    SqlStr = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Eqpt_Category,Name,Desc,PartCode,SymbRemark,OrderNum,Factory,TModel,Structure,RepairInfo,Picture)"
//                     "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Eqpt_Category,:Name,:Desc,:PartCode,:SymbRemark,:OrderNum,:Factory,:TModel,:Structure,:RepairInfo,:Picture)");
//    QueryVar.prepare(SqlStr);
//    QueryVar.bindValue(":Equipment_ID",MaxEquipment_ID);
//    QueryVar.bindValue(":DT",GetStrRemoveLastNum(QuerySearch.value("DT").toString())+QString::number(GetStrLastNum(QuerySearch.value("DT").toString())+1));
//    QueryVar.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
//    QueryVar.bindValue(":Type",QuerySearch.value("Type").toString());
//    QueryVar.bindValue(":Eqpt_Category",QuerySearch.value("Eqpt_Category").toString());//普通元件还是PLC元件
//    QueryVar.bindValue(":Name",QuerySearch.value("Name").toString());
//    QueryVar.bindValue(":Desc",QuerySearch.value("Desc").toString());
//    QueryVar.bindValue(":PartCode",QuerySearch.value("PartCode").toString());
//    QueryVar.bindValue(":SymbRemark",QuerySearch.value("SymbRemark").toString());
//    QueryVar.bindValue(":OrderNum",QuerySearch.value("OrderNum").toString());
//    QueryVar.bindValue(":Factory",QuerySearch.value("Factory").toString());
//    QueryVar.bindValue(":TModel",QuerySearch.value("TModel").toString());
//    QueryVar.bindValue(":Structure",QuerySearch.value("Structure").toString());
//    QueryVar.bindValue(":RepairInfo",QuerySearch.value("RepairInfo").toString());
//    QueryVar.bindValue(":Picture",QuerySearch.value("Picture").toString());
//    QueryVar.exec();

//    SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(CopyEquipment_ID)+"'";
//    QuerySearch.exec(SqlStr);
//    while(QuerySearch.next())
//    {
//        PasteSpurBySymbol_ID(MaxEquipment_ID,QuerySearch.value("Symbol_ID").toInt());
//    }
//    SelectEquipment_ID=MaxEquipment_ID;
//    SelectSymbol_ID=0;
//    LoadProjectUnits();
//}
void MainWindow::PasteUnit()//粘贴元件
{
    // 弹出对话框询问需要粘贴的元件数量
    bool ok;
    int pasteCount = QInputDialog::getInt(this, tr("粘贴元件数量"), tr("请输入要粘贴的元件数量:"), 1, 1, INT_MAX, 1, &ok);
    if (!ok) return; // 用户取消了输入，直接返回

    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增元件；如果是高层，则在高层下的第一个位置新增元件；如果是位置，则在位置下新增元件
    QString StrProTag,StrGaoceng,StrPos;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在高层
        {
            StrGaoceng=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->rowCount()>0)//存在位置
                StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        StrGaoceng=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在位置
        {
            StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        StrPos=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
        if(ui->treeViewUnits->currentIndex().parent().isValid())//高层
        {
            StrGaoceng=ui->treeViewUnits->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
    }

    // 循环粘贴逻辑
    int MaxEquipment_ID = 0;
    for (int i = 0; i < pasteCount; ++i) {
        QString ProjectStructure_ID=GetPosProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(CopyEquipment_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) return;

        MaxEquipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Eqpt_Category,Name,Desc,PartCode,SymbRemark,OrderNum,Factory,TModel,Structure,RepairInfo,Picture)"
                         "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Eqpt_Category,:Name,:Desc,:PartCode,:SymbRemark,:OrderNum,:Factory,:TModel,:Structure,:RepairInfo,:Picture)");
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":Equipment_ID",MaxEquipment_ID);
        QueryVar.bindValue(":DT",GetStrRemoveLastNum(QuerySearch.value("DT").toString())+QString::number(GetStrLastNum(QuerySearch.value("DT").toString())+1));
        QueryVar.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
        QueryVar.bindValue(":Type",QuerySearch.value("Type").toString());
        QueryVar.bindValue(":Eqpt_Category",QuerySearch.value("Eqpt_Category").toString());//普通元件还是PLC元件
        QueryVar.bindValue(":Name",QuerySearch.value("Name").toString());
        QueryVar.bindValue(":Desc",QuerySearch.value("Desc").toString());
        QueryVar.bindValue(":PartCode",QuerySearch.value("PartCode").toString());
        QueryVar.bindValue(":SymbRemark",QuerySearch.value("SymbRemark").toString());
        QueryVar.bindValue(":OrderNum",QuerySearch.value("OrderNum").toString());
        QueryVar.bindValue(":Factory",QuerySearch.value("Factory").toString());
        QueryVar.bindValue(":TModel",QuerySearch.value("TModel").toString());
        QueryVar.bindValue(":Structure",QuerySearch.value("Structure").toString());
        QueryVar.bindValue(":RepairInfo",QuerySearch.value("RepairInfo").toString());
        QueryVar.bindValue(":Picture",QuerySearch.value("Picture").toString());
        QueryVar.exec();

        SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(CopyEquipment_ID)+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            PasteSpurBySymbol_ID(MaxEquipment_ID,QuerySearch.value("Symbol_ID").toInt());
        }
        CopyEquipment_ID = MaxEquipment_ID;
    }

    // 设置最后一次粘贴的Equipment_ID和Symbol_ID
    SelectEquipment_ID = MaxEquipment_ID;
    SelectSymbol_ID = 0;
    LoadProjectUnits();
}
void MainWindow::CopySpur()
{
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    CopySymbol_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
}

void MainWindow::CopyTerminalStrip()//复制端子排
{
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子排") return;
    CopyTerminalStrip_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
}

void MainWindow::CopyUnit()//复制元件
{
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
    CopyEquipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
}

void MainWindow::NewUnit()
{
    //查看当前节点是项目还是高层还是位置，如果是项目则在项目下第一个高层位置下新增元件；如果是高层，则在高层下的第一个位置新增元件；如果是位置，则在位置下新增元件
    QString StrProTag,StrGaoceng,StrPos;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在高层
        {
            StrGaoceng=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
            if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->rowCount()>0)//存在位置
                StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        StrGaoceng=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
        if(ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->rowCount()>0)//存在位置
        {
            StrPos=ModelUnits->itemFromIndex(ui->treeViewUnits->currentIndex())->child(0,0)->data(Qt::DisplayRole).toString();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        StrPos=ui->treeViewUnits->currentIndex().data(Qt::DisplayRole).toString();
        if(ui->treeViewUnits->currentIndex().parent().isValid())//高层
        {
            StrGaoceng=ui->treeViewUnits->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
    }
    StrProTag+="="+StrGaoceng+"+"+StrPos;
    //DialogUnitAttr *dlg=new DialogUnitAttr(this);
    //dlgUnitAttr->setGeometry(ui->mdiArea->x(),ui->mdiArea->y(),ui->mdiArea->width(),ui->mdiArea->height());
    connect(dlgUnitAttr,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
    //connect(dlg,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
    //dlgUnitAttr->move(QApplication::desktop()->screenGeometry().width()/2-dlgUnitAttr->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgUnitAttr->height()/2);
    dlgUnitAttr->setWindowTitle("新建元件");
    dlgUnitAttr->StrProTag=StrProTag;
    dlgUnitAttr->InitUIInfo();
    dlgUnitAttr->LoadInfo(1,0);
    dlgUnitAttr->setModal(true);
    dlgUnitAttr->show();
    dlgUnitAttr->exec();
}

void MainWindow::DeleteTerminalStrip()
{
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子排") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除端子排?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewTerminal->selectionModel()->selectedIndexes().count();i++)
    {
        int TerminalStrip_ID=ui->treeViewTerminal->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
        SelectTerminalStrip_ID=0;
        SelectTerminal_ID=0;

        QSqlQuery query=QSqlQuery(T_ProjectDatabase);
        QString temp =  QString("DELETE FROM TerminalStrip WHERE TerminalStrip_ID="+QString::number(TerminalStrip_ID));
        query.exec(temp);
        temp="SELECT * FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(TerminalStrip_ID)+"'";
        query.exec(temp);
        while(query.next())
        {
            QString Terminal_ID=query.value("Terminal_ID").toString();
            //删除已绘制的符号
            if(query.value("Handle").toString()!="") DeleteDwgTerminalByPageAndHandle(query.value("Page_ID").toString(),query.value("Handle").toString());
            QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM queryTerminalTerm WHERE Terminal_ID = '"+Terminal_ID+"'");
            queryTerminalTerm.exec(temp);
        }
        temp =  QString("DELETE FROM Terminal WHERE TerminalStrip_ID= '"+QString::number(TerminalStrip_ID)+"'");
        query.exec(temp);
    }
    LoadProjectTerminals();
}

void MainWindow::DeleteTerminal()
{
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除端子?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    SelectTerminalStrip_ID=0;
    SelectTerminal_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
    QSqlQuery query=QSqlQuery(T_ProjectDatabase);
    QString temp =  "DELETE FROM TerminalTerm WHERE Terminal_ID= '"+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt())+"'";
    query.exec(temp);

    temp= "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
    query.exec(temp);
    if(query.next())
    {
        DeleteDwgTerminalByPageAndHandle(query.value("Page_ID").toString(),query.value("Handle").toString());
    }

    temp =  "DELETE FROM Terminal WHERE Terminal_ID= "+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
    query.exec(temp);
    LoadProjectTerminals();
}

void MainWindow::NewSpurTemplate()
{
    DialogUnitManage *dlg=new DialogUnitManage(this);
    dlg->setModal(true);
    dlg->SetStackWidget(0);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    qDebug()<<"EquipmentTemplate_ID="<<dlg->EquipmentTemplate_ID;
    if(dlg->EquipmentTemplate_ID<=0) {delete dlg;return;}
    //确认当前的元件Equipment_ID
    int Equipment_ID=0;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="元件")
    {
        Equipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
    }
    qDebug()<<"Equipment_ID="<<Equipment_ID;
    SelectSymbol_ID=AddSymbTblAndSymb2TermInfoTbl(dlg->CurEquipment_ID,QString::number(Equipment_ID),QString::number(dlg->EquipmentTemplate_ID),{});
    SelectEquipment_ID=Equipment_ID;
    LoadProjectUnits();
    delete dlg;
}

void MainWindow::NewTerminal()//新建端子
{
    int TerminalStrip_ID=0;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="端子")
    {
        QSqlQuery QueryTerminal=QSqlQuery(T_ProjectDatabase);
        QString SqlStr= "SELECT * FROM Terminal WHERE Terminal_ID = "+QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt());
        QueryTerminal.exec(SqlStr);
        if(QueryTerminal.next())
        {
            TerminalStrip_ID=QueryTerminal.value("TerminalStrip_ID").toInt();
        }
    }
    else if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()=="端子排")
    {
        TerminalStrip_ID=ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt();
    }

    DialogNewSpur *dlg =new DialogNewSpur(this,1);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    //检查是否与已有端号重复
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    for(int i=0;i<dlg->ListTermNum.count();i++)
    {
        SqlStr= "SELECT * FROM Terminal WHERE TerminalStrip_ID = "+QString::number(TerminalStrip_ID)+" AND Designation = '"+dlg->ListTermNum.at(i)+"'";
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"存在增加端子与已有序号重复，是否继续添加端子?",
                                                                    QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

            if(result!=QMessageBox::Yes)
            {
                return;
            }
        }
    }


    int Terminal_ID;
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    for(int i=0;i<dlg->SpurCount;i++)
    {
        QString SqlStr = QString("INSERT INTO Terminal (Terminal_ID,TerminalStrip_ID,Designation,Symbol,Terminalfunction,TerminalType,TerminalName,PartCode,FunctionText,FunDefine,Factory,OrderNum) "
                                 "VALUES (:Terminal_ID,:TerminalStrip_ID,:Designation,:Symbol,:Terminalfunction,:TerminalType,:TerminalName,:PartCode,:FunctionText,:FunDefine,:Factory,:OrderNum)");
        QueryVar.prepare(SqlStr);
        Terminal_ID=GetMaxIDOfDB(T_ProjectDatabase,"Terminal","Terminal_ID");
        QueryVar.bindValue(":Terminal_ID",Terminal_ID);
        QueryVar.bindValue(":TerminalStrip_ID",QString::number(TerminalStrip_ID));
        QueryVar.bindValue(":Designation",dlg->ListTermNum.at(i));
        QueryVar.bindValue(":Symbol",dlg->SPSName);
        QueryVar.bindValue(":Terminalfunction","");
        QueryVar.bindValue(":TerminalType","");
        QueryVar.bindValue(":TerminalName","");
        QueryVar.bindValue(":PartCode","");
        QueryVar.bindValue(":FunctionText","");
        QueryVar.bindValue(":FunDefine",dlg->FunctionDefineName);
        QueryVar.bindValue(":Factory","");
        QueryVar.bindValue(":OrderNum","");
        QueryVar.exec();
        //根据端子有几个连接点insert记录到TerminalTerm表
        QString DwgPath;
        DwgPath="C:/TBD/SPS/"+dlg->SPSName+".dwg";
        int TermCount=GetDwgTermCount(DwgPath,dlg->SPSName);
        for(int j=0;j<TermCount;j++)
        {
            int MaxTerminalTerm_ID=GetMaxIDOfDB(T_ProjectDatabase,"TerminalTerm","TerminalTerm_ID");
            SqlStr = QString("INSERT INTO TerminalTerm (TerminalTerm_ID,Terminal_ID,ConnNum_Logic,ConnNum) "
                             "VALUES (:TerminalTerm_ID,:Terminal_ID,:ConnNum_Logic,:ConnNum)");
            QueryVar.prepare(SqlStr);
            QueryVar.bindValue(":TerminalTerm_ID",MaxTerminalTerm_ID);
            QueryVar.bindValue(":Terminal_ID",QString::number(Terminal_ID));
            QueryVar.bindValue(":ConnNum_Logic",QString::number(j+1));
            QueryVar.bindValue(":ConnNum",QString::number(j+1));
            QueryVar.exec();
        }
    }
    SelectTerminalStrip_ID=TerminalStrip_ID;
    SelectTerminal_ID=Terminal_ID;
    LoadProjectTerminals();
    delete dlg;
}


void MainWindow::SlotNewSpur()
{
    //确认当前的元件Equipment_ID
    int Equipment_ID=0;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            Equipment_ID=QuerySymbol.value("Equipment_ID").toInt();
        }
    }
    else if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()=="元件")
    {
        Equipment_ID=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
    }

    DialogNewSpur *dlg =new DialogNewSpur(this,0);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(dlg->Canceled) return;
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    QString Symbol_Category="",FunDefine="",Symbol_Desc="";
    QSqlQuery QueryFunctionDefineClass = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+dlg->FunctionDefineClass_ID+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    QueryFunctionDefineClass.next();

    FunDefine=QueryFunctionDefineClass.value("FunctionDefineName").toString();
    Symbol_Desc=QueryFunctionDefineClass.value("Desc").toString();
    SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QueryFunctionDefineClass.value("ParentNo").toString()+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    QueryFunctionDefineClass.next();
    SqlStr = "SELECT * FROM FunctionDefineClass WHERE FunctionDefineClass_ID = '"+QueryFunctionDefineClass.value("ParentNo").toString()+"'";
    QueryFunctionDefineClass.exec(SqlStr);
    QueryFunctionDefineClass.next();
    Symbol_Category=QueryFunctionDefineClass.value("FunctionDefineName").toString();
    int Symbol_ID;
    qDebug()<<"dlg->SpurCount="<<dlg->SpurCount;
    for(int i=0;i<dlg->SpurCount;i++)
    {
        SqlStr = "INSERT INTO Symbol (Symbol_ID,Page_ID,Equipment_ID,Symbol,Symbol_Category,Symbol_Desc,Designation,Symbol_Handle,Symbol_Remark,FunDefine,InsertionPoint)"
                 " VALUES (:Symbol_ID,:Page_ID,:Equipment_ID,:Symbol,:Symbol_Category,:Symbol_Desc,:Designation,:Symbol_Handle,:Symbol_Remark,:FunDefine,:InsertionPoint)";
        QuerySymbol.prepare(SqlStr);
        Symbol_ID=GetMaxIDOfDB(T_ProjectDatabase,"Symbol","Symbol_ID");
        QuerySymbol.bindValue(":Symbol_ID",Symbol_ID);
        QuerySymbol.bindValue(":Page_ID","");
        QuerySymbol.bindValue(":Equipment_ID",QString::number(Equipment_ID));
        QuerySymbol.bindValue(":Symbol",dlg->SPSName);
        QuerySymbol.bindValue(":Symbol_Category",Symbol_Category);
        QuerySymbol.bindValue(":Symbol_Desc",Symbol_Desc);
        QuerySymbol.bindValue(":Designation","");
        QString DwgPath="C:/TBD/SPS/"+dlg->SPSName+".dwg";
        QuerySymbol.bindValue(":Symbol_Remark",GetDwgDicData(DwgPath,dlg->SPSName,"推荐名称"));
        QuerySymbol.bindValue(":FunDefine",FunDefine);
        QuerySymbol.bindValue(":Symbol_Handle","");
        QuerySymbol.bindValue(":InsertionPoint","");
        QuerySymbol.exec();

        for(int j=0;j<dlg->TermCount;j++)
        {
            //更新Symb2TermInfo表
            QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = QString("INSERT INTO Symb2TermInfo (Symb2TermInfo_ID,Symbol_ID,ConnNum_Logic,ConnNum,ConnDirection,Internal,ConnDesc,TestCost)"
                             "VALUES (:Symb2TermInfo_ID,:Symbol_ID,:ConnNum_Logic,:ConnNum,:ConnDirection,:Internal,:ConnDesc,:TestCost)");
            QuerySymb2TermInfo.prepare(SqlStr);
            QuerySymb2TermInfo.bindValue(":Symb2TermInfo_ID",GetMaxIDOfDB(T_ProjectDatabase,"Symb2TermInfo","Symb2TermInfo_ID"));
            QuerySymb2TermInfo.bindValue(":Symbol_ID",QString::number(Symbol_ID));
            QuerySymb2TermInfo.bindValue(":ConnNum_Logic",QString::number(j+1));
            if(dlg->ListTermNum.count()==dlg->TermCount) QuerySymb2TermInfo.bindValue(":ConnNum",dlg->ListTermNum.at(j));
            else QuerySymb2TermInfo.bindValue(":ConnNum",QString::number(j+1));
            //根据dwg文件确定连接点连线方向
            QStringList listTermInfo=GetDwgTermData(DwgPath,dlg->SPSName,j+1);
            if(listTermInfo.count()==2)
            {
                QuerySymb2TermInfo.bindValue(":ConnDirection",listTermInfo.at(0));
                if(listTermInfo.at(1)=="是")
                    QuerySymb2TermInfo.bindValue(":Internal",1);
                else QuerySymb2TermInfo.bindValue(":Internal",0);
            }
            else
            {
                QuerySymb2TermInfo.bindValue(":ConnDirection","");
                QuerySymb2TermInfo.bindValue(":Internal",0);
            }
            QuerySymb2TermInfo.bindValue(":ConnDesc","");
            QuerySymb2TermInfo.bindValue(":TestCost","");
            QuerySymb2TermInfo.exec();
        }
    }
    SelectEquipment_ID=Equipment_ID;
    SelectSymbol_ID=Symbol_ID;
    LoadProjectUnits();

    delete dlg;
}

void MainWindow::DeleteSpur()
{
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="功能子块") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除功能子块?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
    {
        int Symbol_ID=ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
        qDebug()<<"Symbol_ID="<<Symbol_ID;
        QSqlQuery query=QSqlQuery(T_ProjectDatabase);
        QString temp =  "DELETE FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
        query.exec(temp);

        temp= "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(Symbol_ID);
        query.exec(temp);
        if(query.next())
        {
            DeleteDwgSymbolByPageAndHandle(query.value("Page_ID").toString(),query.value("Symbol_Handle").toString());
        }
        temp =  "DELETE FROM Symbol WHERE Symbol_ID= "+QString::number(Symbol_ID);
        query.exec(temp);
        SelectEquipment_ID=0;
        SelectSymbol_ID=0;
    }

    LoadProjectUnits();
}
void MainWindow::DeleteUnit()
{
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="元件") return;
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除元件?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
    {
        int Equipment_ID=ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
        SelectEquipment_ID=0;
        SelectSymbol_ID=0;
        QString StrUnitsInfo;
        QSqlQuery query=QSqlQuery(T_ProjectDatabase);
        QString temp="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID);
        query.exec(temp);
        if(query.next())
        {
            qDebug()<<"add info to RemovedUnitsInfo";
            //DT,ProjectStructure_ID,Type,Spec,Eqpt_Category,Name,Desc,PartCode,OrderNum,Factory,Remark,TVariable,TModel
            StrUnitsInfo+=query.value("DT").toString();
            StrUnitsInfo+=","+query.value("ProjectStructure_ID").toString();
            StrUnitsInfo+=","+query.value("Type").toString();
            StrUnitsInfo+=","+query.value("Spec").toString();
            StrUnitsInfo+=","+query.value("Eqpt_Category").toString();
            StrUnitsInfo+=","+query.value("Name").toString();
            StrUnitsInfo+=","+query.value("Desc").toString();
            StrUnitsInfo+=","+query.value("PartCode").toString();
            StrUnitsInfo+=","+query.value("OrderNum").toString();
            StrUnitsInfo+=","+query.value("Factory").toString();
            StrUnitsInfo+=","+query.value("Remark").toString();
            StrUnitsInfo+=","+query.value("TVariable").toString();
            StrUnitsInfo+=","+query.value("TModel").toString();
            RemovedUnitsInfo.append(StrUnitsInfo);
        }
        temp =  QString("DELETE FROM Equipment WHERE Equipment_ID="+QString::number(Equipment_ID));
        query.exec(temp);
        temp="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(Equipment_ID)+"'";
        query.exec(temp);
        QStringList ListPageID;
        while(query.next())
        {
            QString Symbol_ID=query.value("Symbol_ID").toString();
            //删除已绘制的符号
            if(query.value("Symbol_Handle").toString()!="") DeleteDwgSymbolByPageAndHandle(query.value("Page_ID").toString(),query.value("Symbol_Handle").toString());
            if(!ListPageID.contains(query.value("Page_ID").toString())) ListPageID.append(query.value("Page_ID").toString());
            QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM Symb2TermInfo WHERE Symbol_ID = '"+Symbol_ID+"'");
            querySymb2TermInfo.exec(temp);
        }
        //删除编组
        if(ListPageID.count()==1) DeleteGroup(ListPageID.at(0),QString::number(Equipment_ID));

        temp =  QString("DELETE FROM Symbol WHERE Equipment_ID= '"+QString::number(Equipment_ID)+"'");
        query.exec(temp);
    }
    LoadProjectUnits();
}

void MainWindow::ShowTerminalInDwgByTerminalID(QString TerminalID)
{
    QSqlQuery queryTerminalInstance=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM TerminalInstance WHERE Terminal_ID= '"+TerminalID+"'";
    queryTerminalInstance.exec(SqlStr);
    if(queryTerminalInstance.next())
    {
        QString Terminal_Handle=queryTerminalInstance.value("Handle").toString();
        if(Terminal_Handle=="") return;
        QString Page_ID=queryTerminalInstance.value("Page_ID").toString();
        QSqlQuery queryPage=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Page WHERE Page_ID= "+Page_ID;
        queryPage.exec(SqlStr);
        if(!queryPage.next()) return;
        qDebug()<<"Page_ID="<<Page_ID;

        //查看是否已经打开改图纸
        bool AlreadyOpened=false;
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                AlreadyOpened=true;
                break;
            }
        }
        if(!AlreadyOpened) OpenDwgPageByPageID(Page_ID.toInt());//打开对应的图纸

        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
            qDebug()<<"formMxdraw->Page_IDInDB="<<formMxdraw->Page_IDInDB;
            if(formMxdraw->Page_IDInDB==Page_ID.toInt())
            {
                ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
                formMxdraw->DataBaseTerminalInstanceID=queryTerminalInstance.value("TerminalInstanceID").toString();
                if(AlreadyOpened) formMxdraw->SetTerminalHighLight();
                else formMxdraw->FlagSetTerminalHighLight=true;
                break;
            }
        }
    }

}

void MainWindow::ShowTerminalInDwg()
{
    if(!ui->treeViewTerminal->currentIndex().isValid()) return;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    ShowTerminalInDwgByTerminalID(QString::number(ui->treeViewTerminal->currentIndex().data(Qt::UserRole).toInt()));
}

void MainWindow::ShowSpurInDwgBySymbolID(QString SymbolID)
{
    QSqlQuery querySymbol=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+SymbolID;
    querySymbol.exec(SqlStr);
    if(!querySymbol.next()) return;
    QString Symbol_Handle=querySymbol.value("Symbol_Handle").toString();
    if(Symbol_Handle=="") return;
    QString Page_ID=querySymbol.value("Page_ID").toString();
    QSqlQuery queryPage=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Page WHERE Page_ID= "+Page_ID;
    queryPage.exec(SqlStr);
    if(!queryPage.next()) return;
    qDebug()<<"Page_ID="<<Page_ID;

    //查看是否已经打开改图纸
    bool AlreadyOpened=false;
    QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            AlreadyOpened=true;
            break;
        }
    }
    if(!AlreadyOpened) OpenDwgPageByPageID(Page_ID.toInt());//打开对应的图纸

    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
        qDebug()<<"formMxdraw->Page_IDInDB="<<formMxdraw->Page_IDInDB;
        if(formMxdraw->Page_IDInDB==Page_ID.toInt())
        {
            ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
            formMxdraw->DataBaseSymbolID=SymbolID;
            if(AlreadyOpened) formMxdraw->SetSymbolSpurHighLight();
            else formMxdraw->FlagSetSymbolSpurHighLight=true;
            break;
        }
    }
}

void MainWindow::ShowSpurInDwg()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    ShowSpurInDwgBySymbolID(QString::number(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt()));

}

void MainWindow::ShowLineByUnitTargetInDwg()
{
    QStringList ListLineItemData=ui->treeViewLineByUnit->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;

    if(ListLineItemData.at(4)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(3);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(4)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(3);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowLineTargetInDwg()//转到目标
{
    QStringList ListLineItemData=ui->treeViewLineDT->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;

    if(ListLineItemData.at(4)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(3);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(4)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(3);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowLineByUnitSourceInDwg()
{
    QStringList ListLineItemData=ui->treeViewLineByUnit->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;
    if(ListLineItemData.at(2)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(1);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(2)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(1);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowLineSourceInDwg()//转到源
{
    QStringList ListLineItemData=ui->treeViewLineDT->currentIndex().data(Qt::UserRole).toStringList();
    qDebug()<<"ListLineItemData="<<ListLineItemData;
    if(ListLineItemData.count()!=5) return;
    if(ListLineItemData.at(2)=="0")
    {
        QSqlQuery querySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ListLineItemData.at(1);
        querySymb2TermInfo.exec(SqlStr);
        if(querySymb2TermInfo.next())
        {
            ShowSpurInDwgBySymbolID(querySymb2TermInfo.value("Symbol_ID").toString());
        }
    }
    if(ListLineItemData.at(2)=="1")
    {
        QSqlQuery queryTerminalTerm=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+ListLineItemData.at(1);
        queryTerminalTerm.exec(SqlStr);
        if(queryTerminalTerm.next())
        {
            ShowTerminalInDwgByTerminalID(queryTerminalTerm.value("Terminal_ID").toString());
        }
    }
}

void MainWindow::ShowtreeViewLineByUnitPopMenu(const QPoint &pos)
{
    if(!ui->treeViewLineByUnit->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewLineByUnit->indexAt(pos).data(Qt::WhatsThisRole).toString()!="功能子块") return;

    QAction actShowLineTarget("转到目标", this);
    tree_menu.addAction(&actShowLineTarget);
    connect(&actShowLineTarget,SIGNAL(triggered()),this,SLOT(ShowLineByUnitTargetInDwg()));
    QAction actShowLineSource("转到源", this);
    tree_menu.addAction(&actShowLineSource);
    connect(&actShowLineSource,SIGNAL(triggered()),this,SLOT(ShowLineByUnitSourceInDwg()));
    tree_menu.exec(QCursor::pos());
}

void MainWindow::ShowtreeViewLineDTPopMenu(const QPoint &pos)
{
    if(!ui->treeViewLineDT->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewLineDT->indexAt(pos).data(Qt::WhatsThisRole).toString()!="连线") return;

    QAction actShowLineTarget("转到目标", this);
    tree_menu.addAction(&actShowLineTarget);
    connect(&actShowLineTarget,SIGNAL(triggered()),this,SLOT(ShowLineTargetInDwg()));
    QAction actShowLineSource("转到源", this);
    tree_menu.addAction(&actShowLineSource);
    connect(&actShowLineSource,SIGNAL(triggered()),this,SLOT(ShowLineSourceInDwg()));
    tree_menu.exec(QCursor::pos());
}

void MainWindow::ShowtreeViewTerminalPopMenu(const QPoint &pos)
{
    if(!ui->treeViewTerminal->indexAt(pos).isValid()) return;
    bool CurPageValid=false;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(file.exists())
            {
                CurPageValid=true;
            }
        }
    }
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if((ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="项目")||(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="高层")||(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="位置"))
    {
        QAction actNewTerminalStrip("新建端子排", this);
        tree_menu.addAction(&actNewTerminalStrip);
        connect(&actNewTerminalStrip,SIGNAL(triggered()),this,SLOT(NewTerminalStrip()));
        QAction actPasteTerminal("粘贴端子排", this);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM TerminalStrip WHERE TerminalStrip_ID= "+QString::number(CopyTerminalStrip_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteTerminal.setEnabled(false);
        tree_menu.addAction(&actPasteTerminal);
        connect(&actPasteTerminal,SIGNAL(triggered()),this,SLOT(PasteTerminalStrip()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="端子排")
    {
        QAction actNewTerminal("新建端子", this);
        tree_menu.addAction(&actNewTerminal);
        connect(&actNewTerminal,SIGNAL(triggered()),this,SLOT(NewTerminal()));
        QAction actTerminalAttr("端子排属性", this);
        tree_menu.addAction(&actTerminalAttr);
        connect(&actTerminalAttr,SIGNAL(triggered()),this,SLOT(SlotTerminalStripAttr()));
        QAction actDeleteTerminal("删除端子排", this);
        tree_menu.addAction(&actDeleteTerminal);
        connect(&actDeleteTerminal,SIGNAL(triggered()),this,SLOT(DeleteTerminalStrip()));
        QAction actCopyTerminal("复制端子排", this);
        tree_menu.addAction(&actCopyTerminal);
        connect(&actCopyTerminal,SIGNAL(triggered()),this,SLOT(CopyTerminalStrip()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewTerminal->indexAt(pos).data(Qt::WhatsThisRole).toString()=="端子")
    {
        QAction actLoadTerminal("绘制端子", this);
        if(!CurPageValid) actLoadTerminal.setEnabled(false);
        tree_menu.addAction(&actLoadTerminal);
        connect(&actLoadTerminal,SIGNAL(triggered()),this,SLOT(SlotLoadTerminal()));
        QAction actNewTerminal("新建端子", this);
        tree_menu.addAction(&actNewTerminal);
        connect(&actNewTerminal,SIGNAL(triggered()),this,SLOT(NewTerminal()));
        QAction actTerminalAttr("端子属性", this);
        tree_menu.addAction(&actTerminalAttr);
        connect(&actTerminalAttr,SIGNAL(triggered()),this,SLOT(SlotTerminalAttr()));
        QAction actDeleteTerminal("删除端子", this);
        tree_menu.addAction(&actDeleteTerminal);
        connect(&actDeleteTerminal,SIGNAL(triggered()),this,SLOT(DeleteTerminal()));
        QAction actShowTerminalInDwg("转到图形", this);
        tree_menu.addAction(&actShowTerminalInDwg);
        connect(&actShowTerminalInDwg,SIGNAL(triggered()),this,SLOT(ShowTerminalInDwg()));
        QAction actDrawTerminalEqualDistance("等距绘制", this);
        if(!CurPageValid) actDrawTerminalEqualDistance.setEnabled(false);
        if(ui->treeViewTerminal->selectionModel()->selectedIndexes().count()<=1) actDrawTerminalEqualDistance.setEnabled(false);
        tree_menu.addAction(&actDrawTerminalEqualDistance);
        connect(&actDrawTerminalEqualDistance,SIGNAL(triggered()),this,SLOT(DrawTerminalEqualDistance()));
        tree_menu.exec(QCursor::pos());
    }
}

void MainWindow::ShowtreeViewUnitsPopMenu(const QPoint &pos)
{
    if(!ui->treeViewUnits->indexAt(pos).isValid()) return;
    bool CurPageValid=false;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(file.exists())
            {
                CurPageValid=true;
            }
        }
    }
    qDebug()<<"CurPageValid="<<CurPageValid;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if((ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="项目")||(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="高层")||(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="位置"))
    {
        QAction actNewUnit("新建元件", this);
        tree_menu.addAction(&actNewUnit);
        connect(&actNewUnit,SIGNAL(triggered()),this,SLOT(NewUnit()));
        QAction actPasteUnit("粘贴元件", this);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(CopyEquipment_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteUnit.setEnabled(false);
        tree_menu.addAction(&actPasteUnit);
        connect(&actPasteUnit,SIGNAL(triggered()),this,SLOT(PasteUnit()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="元件")
    {
        QAction actNewSpur("新建子块", this);
        tree_menu.addAction(&actNewSpur);
        connect(&actNewSpur,SIGNAL(triggered()),this,SLOT(SlotNewSpur()));
        QAction actNewSpurTemplate("新建子块(模板)", this);
        tree_menu.addAction(&actNewSpurTemplate);
        connect(&actNewSpurTemplate,SIGNAL(triggered()),this,SLOT(NewSpurTemplate()));
        QAction actUnitAttr("元件属性", this);
        tree_menu.addAction(&actUnitAttr);
        connect(&actUnitAttr,SIGNAL(triggered()),this,SLOT(ShowUnitAttr()));
        QAction actDeleteUnit("删除", this);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="元件")
            {
                actDeleteUnit.setEnabled(false);
                break;
            }
        }
        tree_menu.addAction(&actDeleteUnit);
        connect(&actDeleteUnit,SIGNAL(triggered()),this,SLOT(DeleteUnit()));
        QAction actCopyUnit("复制元件", this);
        tree_menu.addAction(&actCopyUnit);
        connect(&actCopyUnit,SIGNAL(triggered()),this,SLOT(CopyUnit()));

        QMenu LoadUnitTree_menu("整体放置");
        tree_menu.addMenu(&LoadUnitTree_menu);
        QAction actLoadUnitStamp("接线图章", this);
        LoadUnitTree_menu.addAction(&actLoadUnitStamp);
        connect(&actLoadUnitStamp,SIGNAL(triggered()),this,SLOT(LoadUnitStamp()));
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()!=1) actLoadUnitStamp.setEnabled(false);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+ui->treeViewUnits->indexAt(pos).data(Qt::UserRole).toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            QSqlQuery QuerySearchLib=QSqlQuery(T_LibDatabase);
            SqlStr="SELECT * FROM Equipment WHERE PartCode= '"+QuerySearch.value("PartCode").toString()+"'";
            QuerySearchLib.exec(SqlStr);
            if(QuerySearchLib.next())
            {
                if(QuerySearchLib.value("MultiLib").toString()=="") actLoadUnitStamp.setEnabled(false);
            }
        }
        QAction actLoadUnitAllTermsUp("全部向上", this);
        LoadUnitTree_menu.addAction(&actLoadUnitAllTermsUp);
        connect(&actLoadUnitAllTermsUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitAllTermsUp()));
        QAction actLoadUnitAllTermsDown("全部向下", this);
        LoadUnitTree_menu.addAction(&actLoadUnitAllTermsDown);
        connect(&actLoadUnitAllTermsDown,SIGNAL(triggered()),this,SLOT(LoadWholeUnitAllTermsDown()));
        QAction actLoadUnitOddTermsUp("奇数向上，偶数向下", this);
        LoadUnitTree_menu.addAction(&actLoadUnitOddTermsUp);
        connect(&actLoadUnitOddTermsUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitOddTermsUp()));
        QAction actLoadUnitEvenTermsUp("奇数向下，偶数向上", this);
        LoadUnitTree_menu.addAction(&actLoadUnitEvenTermsUp);
        connect(&actLoadUnitEvenTermsUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitEvenTermsUp()));
        QAction actLoadUnitFirstHalfUp("前半部分向上，后面向下", this);
        LoadUnitTree_menu.addAction(&actLoadUnitFirstHalfUp);
        connect(&actLoadUnitFirstHalfUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitFirstHalfUp()));
        QAction actLoadUnitLastHalfUp("前半部分向下，后面向上", this);
        LoadUnitTree_menu.addAction(&actLoadUnitLastHalfUp);
        connect(&actLoadUnitLastHalfUp,SIGNAL(triggered()),this,SLOT(LoadWholeUnitLastHalfUp()));

        //所有子块都是单端符号或无端口符号才可以整体放置元件；功能子块数量超过2个才可以整体放置元件 LuToDo 先注释掉了
        //if(ModelUnits->itemFromIndex(ui->treeViewUnits->indexAt(pos))->rowCount()<=1) LoadUnitTree_menu.setEnabled(false);
        QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
        QString sqlstr;
        for(int i=0;i<ModelUnits->itemFromIndex(ui->treeViewUnits->indexAt(pos))->rowCount();i++)
        {
            sqlstr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+ModelUnits->itemFromIndex(ui->treeViewUnits->indexAt(pos))->child(i,0)->data(Qt::UserRole).toString()+"'";
            QuerySymb2TermInfo.exec(sqlstr);
            int TermCount=0;
            while(QuerySymb2TermInfo.next()) TermCount++;
            if(TermCount>1)
            {
                LoadUnitTree_menu.setEnabled(false);
                break;
            }
        }

        QAction actNewUnit("新建元件", this);
        tree_menu.addAction(&actNewUnit);
        connect(&actNewUnit,SIGNAL(triggered()),this,SLOT(NewUnit()));
        QAction actPasteSpur("粘贴子块", this);
        SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(CopySymbol_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteSpur.setEnabled(false);
        tree_menu.addAction(&actPasteSpur);
        connect(&actPasteSpur,SIGNAL(triggered()),this,SLOT(PasteSpur()));

        tree_menu.addSeparator();

        QAction actAddComponentContainers(QString("为实体元件添加元件层容器"), this);
        tree_menu.addAction(&actAddComponentContainers);
        connect(&actAddComponentContainers, &QAction::triggered, this, &MainWindow::actionAddComponentContainers);

        QAction actRemoveComponentContainers(QString("删除元件层容器"), this);
        tree_menu.addAction(&actRemoveComponentContainers);
        connect(&actRemoveComponentContainers, &QAction::triggered, this, &MainWindow::actionRemoveComponentContainers);

        QAction actAttachToHigher(QString("将实体元件层添加到高层级容器"), this);
        tree_menu.addAction(&actAttachToHigher);
        connect(&actAttachToHigher, &QAction::triggered, this, &MainWindow::actionAttachComponentsToHigher);

        ContainerRepository repo(T_ProjectDatabase);
        repo.ensureTables();

        QMenu *levelMenu = tree_menu.addMenu(QString("层级：无"));
        QModelIndex contextIndex = ui->treeViewUnits->indexAt(pos);
        int equipmentId = contextIndex.data(Qt::UserRole).toInt();
        int componentContainerId = repo.componentContainerIdForEquipment(equipmentId);
        if (componentContainerId != 0) {
            QList<int> chainIds = repo.ancestorChainIds(componentContainerId);
            if (!chainIds.isEmpty()) {
                ContainerEntity topEntity = repo.getById(chainIds.first());
                if (topEntity.id() != 0)
                    levelMenu->setTitle(QString("层级：%1").arg(describeContainer(repo, topEntity)));

                for (int id : chainIds) {
                    ContainerEntity entity = repo.getById(id);
                    if (entity.id() == 0) continue;
                    QString description = describeContainer(repo, entity);
                    if (entity.type() == ContainerType::Component) {
                        QAction *componentInfo = levelMenu->addAction(description);
                        componentInfo->setEnabled(false);
                        continue;
                    }

                    QMenu *subMenu = levelMenu->addMenu(description);

                    QAction *renameAct = subMenu->addAction(QString("重命名当前容器"));
                    connect(renameAct, &QAction::triggered, this, [this, entityId = entity.id()]() {
                        ContainerRepository repoLocal(T_ProjectDatabase);
                        if (!repoLocal.ensureTables()) return;
                        ContainerEntity current = repoLocal.getById(entityId);
                        bool ok = false;
                        QString newName = QInputDialog::getText(this, tr("重命名容器"), tr("名称"), QLineEdit::Normal, current.name(), &ok);
                        if (!ok) return;
                        newName = newName.trimmed();
                        if (newName.isEmpty()) return;
                        current.setName(newName);
                        repoLocal.update(current);
                    });

                    QList<ContainerType> childTypes = childCandidateTypes(entity.type());
                    QAction *addChildAct = subMenu->addAction(QString("添加低层级容器"));
                    if (childTypes.isEmpty()) {
                        addChildAct->setEnabled(false);
                    } else {
                        connect(addChildAct, &QAction::triggered, this, [this, entityType = entity.type(), entityId = entity.id(), childTypes]() {
                            ContainerRepository repoLocal(T_ProjectDatabase);
                            if (!repoLocal.ensureTables()) return;
                            ContainerTreeDialog dialog(this);
                            dialog.setDatabase(T_ProjectDatabase);
                            dialog.setMode(ContainerTreeDialog::Mode::Select);
                            dialog.setAllowedTypes(childTypes);
                            if (dialog.exec() != QDialog::Accepted) return;
                            ContainerEntity selected = dialog.selectedEntity();
                            if (selected.id() == 0) return;
                            if (!ContainerRepository::canContain(entityType, selected.type())) {
                                QMessageBox::warning(this, tr("错误"), tr("所选容器层级不符合要求"));
                                return;
                            }
                            if (!repoLocal.attachToParent(selected.id(), entityId)) {
                                QMessageBox::warning(this, tr("错误"), tr("添加低层级容器失败"));
                            }
                        });
                    }

                    QAction *removeComponentAct = subMenu->addAction(QString("从中删除本元件容器"));
                    bool directParent = false;
                    if (componentContainerId != 0) {
                        ContainerEntity currentComponent = repo.getById(componentContainerId);
                        directParent = (currentComponent.parentId() == entity.id());
                    }
                    removeComponentAct->setEnabled(directParent);
                    if (directParent) {
                        connect(removeComponentAct, &QAction::triggered, this, [this, componentContainerId, parentId = entity.id()]() {
                            ContainerRepository repoLocal(T_ProjectDatabase);
                            if (!repoLocal.ensureTables()) return;
                            ContainerEntity comp = repoLocal.getById(componentContainerId);
                            if (comp.parentId() != parentId) return;
                            repoLocal.attachToParent(componentContainerId, 0);
                        });
                    }

                    QList<ContainerType> parentTypes = parentCandidateTypes(entity.type());
                    QAction *attachAct = subMenu->addAction(QString("将当前层级添加到高层级容器"));
                    if (parentTypes.isEmpty()) {
                        attachAct->setEnabled(false);
                    } else {
                        connect(attachAct, &QAction::triggered, this, [this, entityId = entity.id(), entityType = entity.type(), parentTypes]() {
                            ContainerRepository repoLocal(T_ProjectDatabase);
                            if (!repoLocal.ensureTables()) return;
                            ContainerTreeDialog dialog(this);
                            dialog.setDatabase(T_ProjectDatabase);
                            dialog.setMode(ContainerTreeDialog::Mode::Select);
                            dialog.setAllowedTypes(parentTypes);
                            if (dialog.exec() != QDialog::Accepted) return;
                            ContainerEntity target = dialog.selectedEntity();
                            if (target.id() == 0) return;
                            if (!ContainerRepository::canContain(target.type(), entityType)) {
                                QMessageBox::warning(this, tr("错误"), tr("所选容器层级不符合要求"));
                                return;
                            }
                            if (!repoLocal.attachToParent(entityId, target.id())) {
                                QMessageBox::warning(this, tr("错误"), tr("加入高层级容器失败"));
                            }
                        });
                    }
                }
            }
        }

        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewUnits->indexAt(pos).data(Qt::WhatsThisRole).toString()=="功能子块")
    {
        QAction actLoadSpur("绘制子块", this);
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()<=0) actLoadSpur.setEnabled(false);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            QString temp = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
            QuerySymbol.exec(temp);
            if(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")  {actLoadSpur.setEnabled(false);break;}
                if((QuerySymbol.value("FunDefine").toString()=="黑盒")||(QuerySymbol.value("FunDefine").toString()=="PLC 盒子"))
                {
                    if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()>1)
                    {
                        actLoadSpur.setEnabled(false);
                        break;
                    }
                }
                else
                {
                    if(QuerySymbol.value("Symbol").toString()=="")  {actLoadSpur.setEnabled(false);break;}
                }
            }
        }
        if(!CurPageValid) actLoadSpur.setEnabled(false);
        tree_menu.addAction(&actLoadSpur);
        connect(&actLoadSpur,SIGNAL(triggered()),this,SLOT(SlotLoadSpur()));
        QAction actNewSpur("新建子块", this);
        tree_menu.addAction(&actNewSpur);
        connect(&actNewSpur,SIGNAL(triggered()),this,SLOT(SlotNewSpur()));
        QAction actNewSpurTemplate("子块(模板)", this);
        tree_menu.addAction(&actNewSpurTemplate);
        connect(&actNewSpurTemplate,SIGNAL(triggered()),this,SLOT(NewSpurTemplate()));
        QAction actSpurAttr("子块属性", this);
        tree_menu.addAction(&actSpurAttr);
        connect(&actSpurAttr,SIGNAL(triggered()),this,SLOT(SlotSpurAttr()));
        QAction actDeleteSpur("删除子块", this);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            if(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()!="功能子块")
            {
                actDeleteSpur.setEnabled(false);
                break;
            }
        }
        tree_menu.addAction(&actDeleteSpur);
        connect(&actDeleteSpur,SIGNAL(triggered()),this,SLOT(DeleteSpur()));
        QAction actCopySpur("复制子块", this);
        tree_menu.addAction(&actCopySpur);
        connect(&actCopySpur,SIGNAL(triggered()),this,SLOT(CopySpur()));
        QAction actPasteSpur("粘贴子块", this);
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(CopySymbol_ID);
        QuerySearch.exec(SqlStr);
        if(!QuerySearch.next()) actPasteSpur.setEnabled(false);
        tree_menu.addAction(&actPasteSpur);
        connect(&actPasteSpur,SIGNAL(triggered()),this,SLOT(PasteSpur()));
        QAction actShowSpurInDwg("转到图形", this);
        tree_menu.addAction(&actShowSpurInDwg);
        connect(&actShowSpurInDwg,SIGNAL(triggered()),this,SLOT(ShowSpurInDwg()));
        QAction actDrawSpurEqualDistance("等距绘制", this);
        if(!CurPageValid) actDrawSpurEqualDistance.setEnabled(false);
        if(ui->treeViewUnits->selectionModel()->selectedIndexes().count()<=1) actDrawSpurEqualDistance.setEnabled(false);
        for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
        {
            SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QString::number(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
            QuerySymbol.exec(SqlStr);
            if(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")  {actDrawSpurEqualDistance.setEnabled(false);break;}
                if((QuerySymbol.value("FunDefine").toString()=="黑盒")||(QuerySymbol.value("FunDefine").toString()=="PLC 盒子"))  {actDrawSpurEqualDistance.setEnabled(false);break;}
            }
        }
        tree_menu.addAction(&actDrawSpurEqualDistance);
        connect(&actDrawSpurEqualDistance,SIGNAL(triggered()),this,SLOT(DrawSpurEqualDistance()));
        QAction actGetLinkRoad("获取信号链路", this);
        tree_menu.addAction(&actGetLinkRoad);
        connect(&actGetLinkRoad,SIGNAL(triggered()),this,SLOT(GetLinkRoad()));
        tree_menu.exec(QCursor::pos());
    }
}

void MainWindow::on_Btn_ContainerTree_clicked()
{
    ContainerTreeDialog dialog(this);
    dialog.setDatabase(T_ProjectDatabase);
    dialog.setModal(true);
    dialog.exec();
}

void MainWindow::actionAddComponentContainers()
{
    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("错误"), tr("数据库不可用"));
        return;
    }

    if (!ui->treeViewUnits->selectionModel()) return;
    const QModelIndexList indexes = ui->treeViewUnits->selectionModel()->selectedIndexes();
    QSet<int> equipmentIds;
    for (const QModelIndex &index : indexes) {
        if (index.column() != 0) continue;
        if (index.data(Qt::WhatsThisRole).toString() != "元件") continue;
        equipmentIds.insert(index.data(Qt::UserRole).toInt());
    }

    if (equipmentIds.isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("请选择需要处理的元件"));
        return;
    }

    int created = 0;
    int skipped = 0;
    int failed = 0;

    for (int equipmentId : equipmentIds) {
        int before = repo.componentContainerIdForEquipment(equipmentId);
        int cid = ensureComponentContainer(repo, T_ProjectDatabase, equipmentId);
        if (cid == 0) {
            ++failed;
            continue;
        }
        if (before == 0)
            ++created;
        else
            ++skipped;
    }

    QMessageBox::information(this, tr("完成"),
                             tr("新增%1，已存在%2，失败%3").arg(created).arg(skipped).arg(failed));
}

void MainWindow::actionRemoveComponentContainers()
{
    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("错误"), tr("数据库不可用"));
        return;
    }

    if (!ui->treeViewUnits->selectionModel()) return;
    const QModelIndexList indexes = ui->treeViewUnits->selectionModel()->selectedIndexes();
    QSet<int> equipmentIds;
    for (const QModelIndex &index : indexes) {
        if (index.column() != 0) continue;
        if (index.data(Qt::WhatsThisRole).toString() != "元件") continue;
        equipmentIds.insert(index.data(Qt::UserRole).toInt());
    }

    if (equipmentIds.isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("请选择需要处理的元件"));
        return;
    }

    int removed = 0;
    int skipped = 0;
    for (int equipmentId : equipmentIds) {
        int cid = repo.componentContainerIdForEquipment(equipmentId);
        if (cid == 0) {
            ++skipped;
            continue;
        }
        if (repo.deleteComponentContainerForEquipment(equipmentId))
            ++removed;
        else
            ++skipped;
    }

    QMessageBox::information(this, tr("完成"), tr("删除%1，跳过%2").arg(removed).arg(skipped));
}

void MainWindow::actionAttachComponentsToHigher()
{
    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables()) {
        QMessageBox::warning(this, tr("错误"), tr("数据库不可用"));
        return;
    }

    if (!ui->treeViewUnits->selectionModel()) return;
    const QModelIndexList indexes = ui->treeViewUnits->selectionModel()->selectedIndexes();
    QSet<int> containerIds;
    for (const QModelIndex &index : indexes) {
        if (index.column() != 0) continue;
        if (index.data(Qt::WhatsThisRole).toString() != "元件") continue;
        int equipmentId = index.data(Qt::UserRole).toInt();
        int cid = ensureComponentContainer(repo, T_ProjectDatabase, equipmentId);
        if (cid != 0) containerIds.insert(cid);
    }

    if (containerIds.isEmpty()) {
        QMessageBox::information(this, tr("提示"), tr("请选择需要处理的元件"));
        return;
    }

    QList<ContainerType> allowedParents = parentCandidateTypes(ContainerType::Component);
    ContainerTreeDialog dialog(this);
    dialog.setDatabase(T_ProjectDatabase);
    dialog.setMode(ContainerTreeDialog::Mode::Select);
    dialog.setAllowedTypes(allowedParents);
    if (dialog.exec() != QDialog::Accepted) return;

    ContainerEntity target = dialog.selectedEntity();
    if (target.id() == 0) return;
    if (!ContainerRepository::canContain(target.type(), ContainerType::Component)) {
        QMessageBox::warning(this, tr("错误"), tr("所选容器层级不符合要求"));
        return;
    }

    int attached = 0;
    int skipped = 0;
    for (int cid : containerIds) {
        if (repo.attachToParent(cid, target.id()))
            ++attached;
        else
            ++skipped;
    }

    QMessageBox::information(this, tr("完成"), tr("添加到高层级：%1，跳过：%2").arg(attached).arg(skipped));
}

void MainWindow::ShowtreeViewPagePopMenu(const QPoint &pos)
{
    if(!ui->treeViewPages->indexAt(pos).isValid()) return;
    QMenu tree_menu;
    tree_menu.clear();
    //根据点击节点确定菜单内容
    if(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="项目")
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actProjectAttr("项目属性", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>0) actProjectAttr.setEnabled(false);
        tree_menu.addAction(&actProjectAttr);
        connect(&actProjectAttr,SIGNAL(triggered()),this,SLOT(ProjectAttr()));
        QAction actAddExistPage("添加现有图纸", this);
        tree_menu.addAction(&actAddExistPage);
        connect(&actAddExistPage,SIGNAL(triggered()),this,SLOT(AddExistPage()));
        tree_menu.exec(QCursor::pos());
    }
    else if((ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="高层")||(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="位置"))
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actRename("重命名", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>0) actRename.setEnabled(false);
        tree_menu.addAction(&actRename);
        connect(&actRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actDelDwgPage("删除", this);
        tree_menu.addAction(&actDelDwgPage);
        connect(&actDelDwgPage,SIGNAL(triggered()),this,SLOT(actSlotDelete()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="图纸")
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actDwgPageAttr("页属性", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>0) actDwgPageAttr.setEnabled(false);
        tree_menu.addAction(&actDwgPageAttr);
        connect(&actDwgPageAttr,SIGNAL(triggered()),this,SLOT(DwgPageAttr()));
        QAction actDelDwgPage("删除", this);
        tree_menu.addAction(&actDelDwgPage);
        connect(&actDelDwgPage,SIGNAL(triggered()),this,SLOT(actSlotDelete()));
        tree_menu.exec(QCursor::pos());
    }
    else if(ui->treeViewPages->indexAt(pos).data(Qt::WhatsThisRole).toString()=="列表")
    {
        QAction actNewDwgPage("新建页", this);
        tree_menu.addAction(&actNewDwgPage);
        connect(&actNewDwgPage,SIGNAL(triggered()),this,SLOT(NewDwgPage()));
        QAction actLBRename("重命名", this);
        if(ui->treeViewPages->selectionModel()->selectedIndexes().count()>0) actLBRename.setEnabled(false);
        tree_menu.addAction(&actLBRename);
        connect(&actLBRename,SIGNAL(triggered()),this,SLOT(Rename()));
        QAction actDelLB("删除", this);
        tree_menu.addAction(&actDelLB);
        connect(&actDelLB,SIGNAL(triggered()),this,SLOT(actSlotDelete()));
        tree_menu.exec(QCursor::pos());
    }
}
void MainWindow::Rename()
{
    if(!ui->treeViewPages->currentIndex().isValid()) return;
    QDialog *dialogNameEdit =new QDialog();
    dialogNameEdit->setWindowTitle("重命名");
    dialogNameEdit->setMinimumSize(QSize(300,60));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNameEdit);
    QLineEdit *m_LineEdit = new QLineEdit(dialogNameEdit);
    m_LineEdit->setText(ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString());
    QHBoxLayout *layoutBtn = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNameEdit);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogNameEdit);
    pushbuttonCancel->setText("取消");
    layoutBtn->addWidget(pushbuttonOK);
    layoutBtn->addWidget(pushbuttonCancel);
    formlayoutNameEdit->addRow(m_LineEdit);
    formlayoutNameEdit->addRow(layoutBtn);
    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNameEdit,SLOT(accept()));

    if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        if (dialogNameEdit->exec()==QDialog::Accepted)
        {
            QSqlQuery query(T_ProjectDatabase);
            QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE Structure_ID= '3' AND Structure_INT= '"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString()+"'");
            query.prepare(tempSQL);
            query.bindValue(":Structure_INT",m_LineEdit->text());
            query.exec();
        }
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        if (dialogNameEdit->exec()==QDialog::Accepted)
        {
            if(ui->treeViewPages->currentIndex().parent().data(Qt::WhatsThisRole).toString()=="高层")
            {
                QSqlQuery query(T_ProjectDatabase);
                QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString()+"'");
                query.exec(sqlstr);
                while(query.next())
                {
                    QSqlQuery query2(T_ProjectDatabase);
                    sqlstr=QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+query.value("Parent_ID").toString());
                    query2.exec(sqlstr);
                    if(!query2.next()) continue;
                    if(query2.value("Structure_INT").toString()==ui->treeViewPages->currentIndex().parent().data(Qt::DisplayRole).toString())
                    {
                        QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE ProjectStructure_ID = "+query.value("ProjectStructure_ID").toString());
                        query.prepare(tempSQL);
                        query.bindValue(":Structure_INT",m_LineEdit->text());
                        query.exec();
                        break;
                    }
                }
            }
            else
            {
                QSqlQuery query(T_ProjectDatabase);
                QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE Structure_ID = '5' AND Structure_INT = '"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString()+"'");
                query.prepare(tempSQL);
                query.bindValue(":Structure_INT",m_LineEdit->text());
                query.exec();
            }
        }
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="列表")
    {
        if (dialogNameEdit->exec()==QDialog::Accepted)
        {
            QSqlQuery query(T_ProjectDatabase);
            QString tempSQL=QString("UPDATE ProjectStructure SET Structure_INT=:Structure_INT WHERE ProjectStructure_ID = "+QString::number(ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt()));
            query.prepare(tempSQL);
            query.bindValue(":Structure_INT",m_LineEdit->text());
            query.exec();
        }
    }
    LoadProjectPages();
}
void MainWindow::actSlotDelete()
{
    QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否确认删除?",
                                                            QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

    if(result!=QMessageBox::Yes)
    {
        return;
    }
    for(int i=0;i<ui->treeViewPages->selectionModel()->selectedIndexes().count();i++)
    {
        if(!ui->treeViewPages->selectionModel()->selectedIndexes().at(i).isValid()) continue;
        if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="图纸")
        {
            int Page_ID=ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
            SelectPage_ID=0;
            //删除对应的文件
            QString dwgfilename=GetPageNameByPageID(Page_ID);
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            //查看是否已经打开改图纸
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                }
            }
            QFile dwgfile(dwgfilepath);
            dwgfile.remove();

            QSqlQuery query=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM Page WHERE Page_ID="+QString::number(Page_ID));
            query.exec(temp);
            //同时更新图纸下所有的子块、端子、Connect、Wire、Link、Cable信息
            temp =  "DELETE FROM Connector WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            temp =  "DELETE FROM Link WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            temp =  "DELETE FROM Wires WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);

            temp="SELECT * FROM Symbol WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
            while(query.next())
            {
                QSqlQuery queryUpdate=QSqlQuery(T_ProjectDatabase);
                temp="UPDATE Symbol SET Page_ID=:Page_ID,Symbol_Handle=:Symbol_Handle,InsertionPoint=:InsertionPoint WHERE Symbol_ID = "+query.value("Symbol_ID").toString();
                queryUpdate.prepare(temp);
                queryUpdate.bindValue(":Page_ID","");
                queryUpdate.bindValue(":Symbol_Handle","");
                queryUpdate.bindValue(":InsertionPoint","");
                queryUpdate.exec();
                temp="UPDATE Symb2TermInfo SET Conn_Coordinate=:Conn_Coordinate WHERE Symbol_ID = '"+query.value("Symbol_ID").toString()+"'";
                queryUpdate.prepare(temp);
                queryUpdate.bindValue(":Conn_Coordinate","");
                queryUpdate.exec();
            }
            temp="DELETE FROM TerminalInstance WHERE Page_ID = '"+QString::number(Page_ID)+"'";
            query.exec(temp);
        }
        else if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="列表")
        {
            QSqlQuery query=QSqlQuery(T_ProjectDatabase);
            QString temp =  QString("DELETE FROM Page WHERE ProjectStructure_ID='"+QString::number(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt())+"'");
            query.exec(temp);
            temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt()));
            query.exec(temp);
        }
        else if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="位置")
        {
            QSqlQuery query(T_ProjectDatabase);
            if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).parent().data(Qt::WhatsThisRole).toString()=="高层")
            {
                QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::DisplayRole).toString()+"'");
                query.exec(sqlstr);
                while(query.next())
                {
                    QSqlQuery queryGaoceng(T_ProjectDatabase);
                    sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3' AND ProjectStructure_ID = "+query.value("Parent_ID").toString());
                    queryGaoceng.exec(sqlstr);
                    if(!queryGaoceng.next()) continue;
                    if(queryGaoceng.value("Structure_INT").toString()==ui->treeViewPages->selectionModel()->selectedIndexes().at(i).parent().data(Qt::DisplayRole).toString())
                    {
                        int ProjectStructure_ID=ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt();
                        QSqlQuery querydel(T_ProjectDatabase);
                        QString temp =  QString("DELETE FROM Page WHERE ProjectStructure_ID='"+QString::number(ProjectStructure_ID)+"'");
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(ProjectStructure_ID));//page
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(query.value("ProjectStructure_ID").toInt()));//位置
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryGaoceng.value("ProjectStructure_ID").toInt()));//高层
                        querydel.exec(temp);
                    }
                }
            }

        }
        else if(ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::WhatsThisRole).toString()=="高层")
        {
            QSqlQuery queryGaoceng(T_ProjectDatabase);
            QString sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '3' AND Structure_INT = '"+ui->treeViewPages->selectionModel()->selectedIndexes().at(i).data(Qt::DisplayRole).toString()+"'");
            queryGaoceng.exec(sqlstr);
            while(queryGaoceng.next())
            {
                QSqlQuery queryPos(T_ProjectDatabase);
                sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Parent_ID = '"+queryGaoceng.value("ProjectStructure_ID").toString()+"'");
                queryPos.exec(sqlstr);
                while(queryPos.next())
                {
                    QSqlQuery queryPage(T_ProjectDatabase);
                    sqlstr=QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6' AND Parent_ID = '"+queryPos.value("ProjectStructure_ID").toString()+"'");
                    queryPage.exec(sqlstr);
                    while(queryPage.next())
                    {
                        QSqlQuery querydel(T_ProjectDatabase);
                        QString temp =  QString("DELETE FROM Page WHERE ProjectStructure_ID='"+QString::number(queryPage.value("ProjectStructure_ID").toInt())+"'");
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryPage.value("ProjectStructure_ID").toInt()));//page
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryPos.value("ProjectStructure_ID").toInt()));//位置
                        querydel.exec(temp);
                        temp =  QString("DELETE FROM ProjectStructure WHERE ProjectStructure_ID="+QString::number(queryGaoceng.value("ProjectStructure_ID").toInt()));//高层
                        querydel.exec(temp);
                    }
                }
            }
        }
    }
    LoadProjectPages();
}
void MainWindow::DwgPageAttr()
{
    if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()!="图纸") return;
    DialogPageAttr *dlg=new DialogPageAttr(this);
    dlg->Mode=2;//modify page


    dlg->Page_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
    QString OriginalPageName=GetPageNameByPageID(dlg->Page_ID);
    dlg->LoadPageInfo();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        SelectPage_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        //更新treeview
        LoadProjectPages();
        if(OriginalPageName!=dlg->PageInitName)//重命名dwg文件
        {
            //查看是否已经打开改图纸，如打开则先关闭
            QString dwgfilename=OriginalPageName;
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            bool DwgOpened=false;
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    DwgOpened=true;
                    break;
                }
            }
            QFile File(dwgfilepath);
            File.rename(CurProjectPath+"/"+dlg->PageInitName+".dwg");
            if(DwgOpened) OpenDwgPageByPageID(dlg->Page_ID);//打开对应的图纸
        }
    }
    delete dlg;
}
QString MainWindow::CreateUnusedFileName(QString CurSelectPageName,QString ProjectStructure_ID)
{
    //在当前选中文件名的基础上加1，如果该文件存在，则新文件名为数字.a,.b,以此类推
    QString NumStr="";
    CurSelectPageName=CurSelectPageName.split(" ").at(0);
    for(int i=0;i<CurSelectPageName.count();i++)
    {
        if((CurSelectPageName.at(i)>='0')&&(CurSelectPageName.at(i)<='9')) NumStr+=CurSelectPageName.at(i);
    }
    int NewStr;
    if(NumStr!="")  NewStr=NumStr.toInt()+1;
    else
    {
        NewStr=1;
    }
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT * FROM Page WHERE ProjectStructure_ID = '"+ProjectStructure_ID+"'");
    QueryVar.exec(temp);
    bool Existed=false;
    while(QueryVar.next())
    {qDebug()<<"get value PageName";
        if(QueryVar.value("PageName").toString()==QString::number(NewStr))
        {
            Existed=true;
            break;
        }
    }
    if(Existed)
    {
        QueryVar.first();
        QueryVar.previous();
        Existed=false;
        while(QueryVar.next())
        {
            if(QueryVar.value("PageName").toString()==(QString::number(NewStr)+".a"))
            {
                Existed=true;break;
            }
        }
        if(!Existed) return  QString::number(NewStr)+".a";
        else
        {
            QueryVar.first();
            QueryVar.previous();
            Existed=false;
            while(QueryVar.next())
            {
                if(QueryVar.value("PageName").toString()==(QString::number(NewStr)+".b"))
                {
                    Existed=true;break;
                }
            }
            if(!Existed) return  QString::number(NewStr)+".b";
            else
            {
                QueryVar.first();
                QueryVar.previous();
                Existed=false;
                while(QueryVar.next())
                {
                    if(QueryVar.value("PageName").toString()==(QString::number(NewStr)+".c"))
                    {
                        Existed=true;break;
                    }
                }
                if(!Existed) return  QString::number(NewStr)+".c";
            }
        }
    }
    else
    {
        return  QString::number(NewStr);
    }
    return CurSelectPageName+".abc";
}

void MainWindow::AddExistPage()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("添加现有文件"));
    fileDialog.setDirectory(LocalProjectDefaultPath);
    fileDialog.setNameFilter(tr("dwg(*.dwg)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    QFileInfo SelectedFileInfo(fileNames.at(0));

    QString PageName=SelectedFileInfo.fileName();
    PageName=PageName.mid(0,PageName.count()-4);
    if(PageName.contains("·")) PageName=PageName.mid(PageName.lastIndexOf("·")+1,PageName.count()-PageName.lastIndexOf("·")-1);
    QString ProTag=GetCurIndexProTag(1);
    if(ProTag!="") PageName=ProTag+"·"+PageName;
    DialogPageAttr *dlg=new DialogPageAttr(this);
    dlg->Mode=1;//add page
    //根据节点确定dwg文件初始名称
    dlg->PageInitName=PageName;
    dlg->SetPageName();
    dlg->LoadPageInfo();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        QFile::copy(fileNames.at(0),CurProjectPath+"/"+dlg->PageInitName+".dwg");
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this,CurProjectPath+"/"+dlg->PageInitName+".dwg",dlg->Page_ID);
        formMxdraw->setWindowTitle(dlg->PageInitName);
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        //formMxdraw->InsertNodes();
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
        connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
        connect(formMxdraw,SIGNAL(SigalShowSpurAttr(int)),this,SLOT(ShowSpurAttr(int)));
        connect(formMxdraw,SIGNAL(SigalShowTerminalAttr(int,int)),this,SLOT(ShowTerminalAttr(int,int)));
        connect(formMxdraw,SIGNAL(UpdateCounterLink(int,QString)),this,SLOT(updateCounterLink(int,QString)));
        connect(formMxdraw,SIGNAL(SignalUpdateSpur(int)),this,SLOT(UpdateSpurBySymbol_ID(int)));
        connect(formMxdraw,SIGNAL(SignalUpdateTerminal(int)),this,SLOT(UpdateTerminalByTerminal_ID(int)));
        connect(formMxdraw,SIGNAL(SignalUpdateDwgBlkTagByPage_ID(int,QString,QString,QString)),this,SLOT(UpdateDwgBlkTagByPage_ID(int,QString,QString,QString)));
        SelectPage_ID=dlg->Page_ID;
        //更新treeview
        LoadProjectPages();
    }
    delete dlg;
}

//Mode=0:Add new  Mode=1:Add exist
QString MainWindow::GetCurIndexProTag(int Mode)
{
    qDebug()<<"GetCurIndexProTag,Mode="<<Mode;
    QString ProTag="";
    if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="图纸")
    {
        //如果选择的节点是图纸，则查看节点data中的Page_ID，检索数据库得到对应的page名称和ProjectStructure_ID，根据ProjectStructure_ID在ProjectStructure中检索对应的高层和位置信息
        int Page_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString temp = QString("SELECT * FROM Page WHERE Page_ID = "+QString::number(Page_ID));
        QueryVar.exec(temp);
        if(!QueryVar.next()) return "";
        QString ProjectStructure_ID=QueryVar.value("ProjectStructure_ID").toString();
        QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+ProjectStructure_ID);
        QueryPage.exec(temp);
        if(!QueryPage.next()) return "";

        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString());
        QueryPos.exec(temp);
        if(!QueryPos.next()) return "";
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) return "";
        if(QueryGaoceng.value("Structure_INT").toString()!="") ProTag+="="+QueryGaoceng.value("Structure_INT").toString();
        if(QueryPos.value("Structure_INT").toString()!="") ProTag+="+"+QueryPos.value("Structure_INT").toString();
        if(Mode==0)
        {
            if(QueryPage.value("Structure_INT").toString()!="") ProTag+="&"+QueryPage.value("Structure_INT").toString();
        }
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="列表")
    {
        //如果选择的节点是列表，则查看节点data中的ProjectStructure_ID，据此得到对应的高层和位置信息
        QSqlQuery QueryLB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        int ProjectStructure_ID=ui->treeViewPages->currentIndex().data(Qt::UserRole).toInt();
        QString temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QString::number(ProjectStructure_ID));
        QueryLB.exec(temp);
        if(!QueryLB.next()) return "";
        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryLB.value("Parent_ID").toString());
        QueryPos.exec(temp);
        if(!QueryPos.next()) return "";
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) return "";
        if(QueryGaoceng.value("Structure_INT").toString()!="") ProTag+="="+QueryGaoceng.value("Structure_INT").toString();
        if(QueryPos.value("Structure_INT").toString()!="") ProTag+="+"+QueryPos.value("Structure_INT").toString();
        if(Mode==0) if(QueryLB.value("Structure_INT").toString()!="") ProTag+="&"+QueryLB.value("Structure_INT").toString();
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="位置")
    {
        //如果选择的节点是位置，在该位置下创建图纸
        if(ui->treeViewPages->currentIndex().parent().data(Qt::WhatsThisRole).toString()=="高层")
        {
            ProTag+="="+ui->treeViewPages->currentIndex().parent().data(Qt::DisplayRole).toString();
        }
        ProTag+="+"+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString();
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="高层")
    {
        //如果选择的节点是高层，选择高层下第一个位置创建图纸
        ProTag+="="+ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString();
        if(ModelPages->itemFromIndex(ui->treeViewPages->currentIndex())->rowCount()>0)
        {
            if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="位置")
            {
                ProTag+="+"+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
            }
            else if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="列表")
            {
                if(Mode==0)  ProTag+="&"+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
            }
            else if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="图纸")
            {

            }
        }
    }
    else if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="项目")
    {
        if(ModelPages->itemFromIndex(ui->treeViewPages->currentIndex())->rowCount()>0)
        {
            if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="图纸")
            {}
            else if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="位置")
            {
                ProTag+="+"+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
            }
            else if(ui->treeViewPages->currentIndex().child(0,0).data(Qt::WhatsThisRole).toString()=="高层")
            {
                ProTag+="="+ui->treeViewPages->currentIndex().child(0,0).data(Qt::DisplayRole).toString();
                if(ModelPages->itemFromIndex(ui->treeViewPages->currentIndex().child(0,0))->rowCount()>0)
                {
                    if(ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::WhatsThisRole).toString()=="位置")
                    {
                        ProTag+="+"+ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::DisplayRole).toString();
                    }
                    else if(ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::WhatsThisRole).toString()=="列表")
                    {
                        if(Mode==0) ProTag+="&"+ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::DisplayRole).toString();
                    }
                    else if(ui->treeViewPages->currentIndex().child(0,0).child(0,0).data(Qt::WhatsThisRole).toString()=="图纸")
                    {
                    }
                }
            }
        }
    }
    return ProTag;
}

void MainWindow::NewDwgPage()
{
    //根据选择节点的位置确定新建图纸的名称
    QString PageName="";
    QString ProTag=GetCurIndexProTag(0);
    qDebug()<<"ProTag="<<ProTag;
    QString StrGaoceng="",StrPos="";
    if(ProTag.contains("="))
    {
        if(ProTag.contains("+")) StrGaoceng=ProTag.mid(ProTag.indexOf("=")+1,ProTag.indexOf("+")-ProTag.indexOf("=")-1);
        else if(ProTag.contains("&")) StrGaoceng=ProTag.mid(ProTag.indexOf("=")+1,ProTag.indexOf("&")-ProTag.indexOf("=")-1);
        else StrGaoceng=ProTag.mid(ProTag.indexOf("=")+1,ProTag.count()-ProTag.indexOf("=")-1);
    }
    if(ProTag.contains("+"))
    {
        if(ProTag.contains("&")) StrGaoceng=ProTag.mid(ProTag.indexOf("+")+1,ProTag.indexOf("&")-ProTag.indexOf("+")-1);
        else StrGaoceng=ProTag.mid(ProTag.indexOf("+")+1,ProTag.count()-ProTag.indexOf("+")-1);
    }
    QString ProjectStructure_ID=GetPageProjectStructure_IDByGaocengAndPos(StrGaoceng,StrPos,"");
    if(ui->treeViewPages->currentIndex().data(Qt::WhatsThisRole).toString()=="图纸")
        PageName=CreateUnusedFileName(ui->treeViewPages->currentIndex().data(Qt::DisplayRole).toString(),ProjectStructure_ID);
    else
        PageName=CreateUnusedFileName("",ProjectStructure_ID);
    if(ProTag!="") PageName=ProTag+"·"+PageName;

    DialogPageAttr *dlg=new DialogPageAttr(this);
    dlg->Mode=1;//add page

    //根据节点确定dwg文件初始名称
    dlg->PageInitName=PageName;
    dlg->SetPageName();
    dlg->LoadPageInfo();
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this,CurProjectPath+"/"+dlg->PageInitName+".dwg",dlg->Page_ID);
        connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
        connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
        formMxdraw->setWindowTitle(dlg->PageInitName);
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        //formMxdraw->InsertNodes();
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
        connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
        connect(formMxdraw,SIGNAL(SigalShowSpurAttr(int)),this,SLOT(ShowSpurAttr(int)));
        connect(formMxdraw,SIGNAL(SigalShowTerminalAttr(int,int)),this,SLOT(ShowTerminalAttr(int,int)));
        connect(formMxdraw,SIGNAL(UpdateCounterLink(int,QString)),this,SLOT(updateCounterLink(int,QString)));
        connect(formMxdraw,SIGNAL(SignalUpdateSpur(int)),this,SLOT(UpdateSpurBySymbol_ID(int)));
        connect(formMxdraw,SIGNAL(SignalUpdateTerminal(int)),this,SLOT(UpdateTerminalByTerminal_ID(int)));


        SelectPage_ID=dlg->Page_ID;
        //更新treeview
        LoadProjectPages();
    }
    delete dlg;
}

void MainWindow::InitNavigatorTree()
{
    ModelPages = new QStandardItemModel(ui->treeViewPages);
    ui->treeViewPages->header()->setVisible(false);
    ui->treeViewPages->setColumnWidth(0,50);
    ui->treeViewPages->setModel(ModelPages);

    ModelUnits = new QStandardItemModel(ui->treeViewUnits);
    ui->treeViewUnits->header()->setVisible(false);
    ui->treeViewUnits->setColumnWidth(0,50);
    ui->treeViewUnits->setModel(ModelUnits);

    ModelTerminals=new QStandardItemModel(ui->treeViewTerminal);
    ui->treeViewTerminal->header()->setVisible(false);
    ui->treeViewTerminal->setColumnWidth(0,50);
    ui->treeViewTerminal->setModel(ModelTerminals);

    ModelLineDT=new QStandardItemModel(ui->treeViewLineDT);
    ui->treeViewLineDT->header()->setVisible(false);
    ui->treeViewLineDT->setColumnWidth(0,50);
    ui->treeViewLineDT->setModel(ModelLineDT);

    ModelLineByUnits=new QStandardItemModel(ui->treeViewLineByUnit);
    ui->treeViewLineByUnit->header()->setVisible(false);
    ui->treeViewLineByUnit->setColumnWidth(0,50);
    ui->treeViewLineByUnit->setModel(ModelLineByUnits);
}

QString MainWindow::GetTerminalTermStrByTermID(QString TermID)
{
    QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+TermID.mid(0,TermID.indexOf("."));
    QueryTerminalTerm.exec(temp);
    if(QueryTerminalTerm.next())
    {
        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = "SELECT * FROM Terminal WHERE Terminal_ID = "+QueryTerminalTerm.value("Terminal_ID").toString();
        QueryTerminal.exec(temp);
        if(QueryTerminal.next())
        {
            QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            temp = "SELECT * FROM TerminalStrip WHERE TerminalStrip_ID = "+QueryTerminal.value("TerminalStrip_ID").toString();
            QueryTerminalStrip.exec(temp);
            if(QueryTerminalStrip.next())
            {
                return QueryTerminalStrip.value("DT").toString()+":"+QueryTerminal.value("Designation").toString()+TermID.mid(TermID.indexOf("."),TermID.count()-TermID.indexOf("."));
            }
        }
    }
    return "";
}

QString MainWindow::GetUnitTermStrByTermID(QString TermID)
{
    QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = "SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+TermID;
    QuerySymb2TermInfo.exec(temp);
    if(QuerySymb2TermInfo.next())
    {
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySymb2TermInfo.value("Symbol_ID").toString();
        QuerySymbol.exec(temp);
        if(QuerySymbol.next())
        {
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            temp = "SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
            QueryEquipment.exec(temp);
            if(QueryEquipment.next())
            {
                return GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString()+":"+QuerySymb2TermInfo.value("ConnNum").toString();
            }
        }
    }
    return "";
}
void MainWindow::ProduceDBJXB()
{
    //删除原JXB表
    QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
    QString SqlStr =  "DELETE FROM JXB ";
    QueryJXB.exec(SqlStr);
    //在ConnectLine表中检索连线
    QSqlQuery QueryConnectLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM ConnectLine WHERE Page_ID <> '' ORDER BY ConnectionNumber";
    QueryConnectLine.exec(SqlStr);
    while(QueryConnectLine.next())
    {
        QString Symb1_ID=QueryConnectLine.value("Symb1_ID").toString();
        QString Symb2_ID=QueryConnectLine.value("Symb2_ID").toString();
        if((Symb1_ID=="")||(Symb2_ID=="")) continue;
        if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) continue;
        if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) continue;
        //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表
        QString ConnectionNumber=QueryConnectLine.value("ConnectionNumber").toString();
        QString Symb1_Category=QueryConnectLine.value("Symb1_Category").toString();
        QString Symb2_Category=QueryConnectLine.value("Symb2_Category").toString();
        if((Symb1_Category=="1")&&(Symb2_Category=="1"))//同一个端子排的短接片要排除
        {
            QString TerminalStrip_ID1,TerminalStrip_ID2,Terminal_ID1,Terminal_ID2,ShortJumper1,ShortJumper2;
            QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb1_ID;
            QueryTerminalInstance.exec(SqlStr);
            if(QueryTerminalInstance.next())
            {
                TerminalStrip_ID1=QueryTerminalInstance.value("TerminalStrip_ID").toString();
                Terminal_ID1=QueryTerminalInstance.value("Terminal_ID").toString();
                QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+Terminal_ID1;
                QueryTerminal.exec(SqlStr);
                if(QueryTerminal.next()) ShortJumper1=QueryTerminal.value("ShortJumper").toString();
            }
            SqlStr = "SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb2_ID;
            QueryTerminalInstance.exec(SqlStr);
            if(QueryTerminalInstance.next())
            {
                TerminalStrip_ID2=QueryTerminalInstance.value("TerminalStrip_ID").toString();
                Terminal_ID2=QueryTerminalInstance.value("Terminal_ID").toString();
                QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+Terminal_ID2;
                QueryTerminal.exec(SqlStr);
                if(QueryTerminal.next()) ShortJumper2=QueryTerminal.value("ShortJumper").toString();
            }
            if((TerminalStrip_ID1==TerminalStrip_ID2)&&(ShortJumper1==ShortJumper2)) continue;//同一个端子排的短接片要排除
        }
        QString ProjectStructure_ID=GetProjectStructureIDByPageID(QueryConnectLine.value("Page_ID").toInt());
        bool CurLineIsUnValid=false;
        if(ConnectionNumber!="")//如果线号不为空则查看列表中是否已存在相同线号的导线，如果存在，则为无效导线
        {
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+ConnectionNumber+"' AND ProjectStructure_ID = '"+ProjectStructure_ID+"'";
            QuerySearch.exec(SqlStr);
            if(QuerySearch.next()) CurLineIsUnValid=true;
        }
        else//线号为空则查看列表中线号为空的连线，如果列表中导线两端连接点对象与当前连线的相同（Symb1_ID和Symb2_ID可互换），则当前导线为无效导线，反之则添加到列表
        {
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '' AND ProjectStructure_ID = '"+ProjectStructure_ID+"'";
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                QString SearchSymb1_ID=QuerySearch.value("Symb1_ID").toString();
                QString SearchSymb2_ID=QuerySearch.value("Symb2_ID").toString();
                QString SearchSymb1_Category=QuerySearch.value("Symb1_Category").toString();
                QString SearchSymb2_Category=QuerySearch.value("Symb2_Category").toString();
                if((SearchSymb1_ID==Symb1_ID)&&(SearchSymb2_ID==Symb2_ID)&&(SearchSymb1_Category==Symb1_Category)&&(SearchSymb2_Category==Symb2_Category))  CurLineIsUnValid=true;
                if((SearchSymb2_ID==Symb1_ID)&&(SearchSymb1_ID==Symb2_ID)&&(SearchSymb2_Category==Symb1_Category)&&(SearchSymb1_Category==Symb2_Category))  CurLineIsUnValid=true;
                if(CurLineIsUnValid) break;
            }
        }
        if(!CurLineIsUnValid)
        {
            SqlStr =  "INSERT INTO JXB (JXB_ID,ProjectStructure_ID,Page_ID,Cable_ID,ConnectionNumber,ConnectionNumber_Handle,Symb1_ID,Symb2_ID,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category,Symb1_Category,Symb2_Category)"
                      "VALUES (:JXB_ID,:ProjectStructure_ID,:Page_ID,:Cable_ID,:ConnectionNumber,:ConnectionNumber_Handle,:Symb1_ID,:Symb2_ID,:Wires_Type,:Wires_Color,:Wires_Diameter,:Wires_Category,:Symb1_Category,:Symb2_Category)";
            QueryJXB.prepare(SqlStr);
            QueryJXB.bindValue(":JXB_ID",GetMaxIDOfDB(T_ProjectDatabase,"JXB","JXB_ID"));
            QueryJXB.bindValue(":ProjectStructure_ID",ProjectStructure_ID);
            QueryJXB.bindValue(":Page_ID",QueryConnectLine.value("Page_ID").toString());
            QueryJXB.bindValue(":Cable_ID",QueryConnectLine.value("Cable_ID").toString());
            QueryJXB.bindValue(":ConnectionNumber",QueryConnectLine.value("ConnectionNumber").toString());
            QueryJXB.bindValue(":ConnectionNumber_Handle",QueryConnectLine.value("ConnectionNumber_Handle").toString());
            QueryJXB.bindValue(":Symb1_ID",QueryConnectLine.value("Symb1_ID").toString());
            QueryJXB.bindValue(":Symb2_ID",QueryConnectLine.value("Symb2_ID").toString());
            QueryJXB.bindValue(":Wires_Type",QueryConnectLine.value("Wires_Type").toString());
            QueryJXB.bindValue(":Wires_Color",QueryConnectLine.value("Wires_Color").toString());
            QueryJXB.bindValue(":Wires_Diameter",QueryConnectLine.value("Wires_Diameter").toString());
            QueryJXB.bindValue(":Wires_Category",QueryConnectLine.value("Wires_Category").toString());
            QueryJXB.bindValue(":Symb1_Category",QueryConnectLine.value("Symb1_Category").toString());
            QueryJXB.bindValue(":Symb2_Category",QueryConnectLine.value("Symb2_Category").toString());
            QueryJXB.exec();
        }
    }
}

void MainWindow::InsertTermToUnitStrip(QStandardItem *Item,QSqlQuery QueryJXBLine,QString Symb_ID,QString Symb_Category,int index)
{
    QString TermStr,StrSql;
    QString ConnectionNumber=QueryJXBLine.value("ConnectionNumber").toString();
    QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category;
    if(index==0) {Symb1_ID=Symb_ID;Symb1_Category=Symb_Category;}
    else {Symb2_ID=Symb_ID;Symb2_Category=Symb_Category;}
    if(Symb_Category=="0")
    {
        QSqlQuery QuerySearchTerm(T_ProjectDatabase);
        StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb_ID;
        QuerySearchTerm.exec(StrSql);
        if(QuerySearchTerm.next()) TermStr=QuerySearchTerm.value("ConnNum").toString();
    }
    else if(Symb_Category=="1")
    {
        QSqlQuery QuerySearchTerm(T_ProjectDatabase);
        StrSql="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+Symb_ID;
        QuerySearchTerm.exec(StrSql);
        if(QuerySearchTerm.next())
        {
            QSqlQuery QuerySearchTerminal(T_ProjectDatabase);
            StrSql="SELECT * FROM Terminal WHERE Terminal_ID= "+QuerySearchTerm.value("Terminal_ID").toString();
            QuerySearchTerminal.exec(StrSql);
            if(QuerySearchTerminal.next())
            {
                TermStr=QuerySearchTerminal.value("Designation").toString();
            }
        }
    }
    TermStr+="("+ConnectionNumber+")<->";
    if(index==0)//查找另一端的器件
    {
        Symb2_ID=QueryJXBLine.value("Symb2_ID").toString();
        Symb2_Category=QueryJXBLine.value("Symb2_Category").toString();
        if(Symb2_Category=="0") TermStr+=GetUnitTermStrByTermID(Symb2_ID);
        else if(Symb2_Category=="1") TermStr+=GetTerminalTermStrByTermID(Symb2_ID);
    }
    else if(index==1)//查找另一端的器件
    {
        Symb1_ID=QueryJXBLine.value("Symb1_ID").toString();
        Symb1_Category=QueryJXBLine.value("Symb1_Category").toString();
        if(Symb1_Category=="0") TermStr+=GetUnitTermStrByTermID(Symb1_ID);
        else if(Symb1_Category=="1") TermStr+=GetTerminalTermStrByTermID(Symb1_ID);
    }
    //判断Symb1_ID、Symb2_ID、Symb1_Category、Symb2_Category是否已存在
    for(int i=0;i<Item->rowCount();i++)
    {
        QStringList ListLineItemData=Item->data(Qt::UserRole).toStringList();
        if(ListLineItemData.count()==5)
        {
            if((ListLineItemData.at(1)==Symb1_ID)&&(ListLineItemData.at(2)==Symb1_Category)&&(ListLineItemData.at(3)==Symb2_ID)&&(ListLineItemData.at(4)==Symb2_Category))
                return;
        }
    }
    QStandardItem *TermItem=new QStandardItem(QIcon("C:/TBD/data/功能子块图标_已插入.png"),TermStr);
    TermItem->setData(QVariant("功能子块"),Qt::WhatsThisRole);

    QStringList ListLineItemData;
    ListLineItemData.clear();
    ListLineItemData.append(QueryJXBLine.value("JXB_ID").toString());
    if(index==0)
    {
        ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
    }
    else if(index==1)
    {
        ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
    }

    TermItem->setData(QVariant(ListLineItemData),Qt::UserRole);
    Item->appendRow(TermItem);
}
/*
QString MainWindow::GetLinkRoadBySymbol(int Symbol_ID)//获取信号链路(针对功能子块)
{
    QString FinalLinkRoad="";
    //获取功能子块下的端口ID提取信号链路
    QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QuerySymb2TermInfo.exec(StrSql);
    while(QuerySymb2TermInfo.next())
    {
       QList<QStringList> listFinalLinkRoad=GetLinkRoadByUnitStripID(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toInt());
       for(QStringList ListLinkRoad:listFinalLinkRoad)
       {
           FinalLinkRoad+="[";
           for(QString StrLinkRoad:ListLinkRoad)
             FinalLinkRoad+=StrLinkRoad+";";
           FinalLinkRoad.remove(FinalLinkRoad.count()-1,1);
           FinalLinkRoad+="]";
       }
    }
    //存储到数据库中
    QString SqlStr =  "UPDATE Symbol SET LinkRoad=:LinkRoad WHERE Symbol_ID= '"+QString::number(Symbol_ID)+"'";
    QSqlQuery querySymbol(T_ProjectDatabase);
    querySymbol.prepare(SqlStr);
    querySymbol.bindValue(":LinkRoad",FinalLinkRoad);
    querySymbol.exec();
    return FinalLinkRoad;
}


//KnownLineValidRoadCnt定义：器件ID，器件类型（0：元件，1：端子排，2：导线），子块数
QList<QStringList> MainWindow::GetLinkRoadByUnitStripID(int Symb2TermInfo_ID)//获取端口信号链路
{
    QList<QStringList> listFinalLinkRoad;
    QStringList listLinkRoad={QString::number(GetSymbolIDByTermID(0,Symb2TermInfo_ID))+",0,"+QString::number(GetLinesBySymb2TermInfo_ID(Symb2TermInfo_ID,0,"").count())};
    QStringList KnownLineValidRoadCnt=listLinkRoad;
    QString DT;
    int initSymb2TermInfo_ID=Symb2TermInfo_ID;
    int Category=0;
    while(1)
    {
        bool FindTerm=false;
        bool FindExecConn=false;
        bool FindSourceConn=false;
        int NodeSpurCount=0;
        QString StrLinkRoad="";//ID+类型 类型元件为0 端子排为1 导线为2
        //根据Symb2TermInfo_ID找到下一个端口，可以是连线的另一头，也可以是功能子块的另一头，优先找连线的另一头
        //====找连线的另一头====
        //查找端口对应的元件ID
        int UnitStripID=GetUnitStripIDByTermID(Category,Symb2TermInfo_ID,DT);
        if(ModelLineByUnits->rowCount()>0)
        {
            for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
            {
                for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
                {
                  for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                  {
                      if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toInt()!=0) continue;//必须是元件而不是端子排
                      if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt()!=UnitStripID) continue;
                      QStringList ListLineItemData;
                      //检索元件下的各个引脚连线，并且需要通过功能子块或T语言确定引脚之间的逻辑关系,暂时由功能子块确定引脚之间的逻辑关系
                      for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//元件引脚连线
                      {
                         QStandardItem *TermItem=ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0);
                         ListLineItemData=TermItem->data(Qt::UserRole).toStringList();
                         if(ListLineItemData.count()!=5) continue;
                         if(ListLineItemData.at(1).toInt()!=Symb2TermInfo_ID) continue;
                         //不能往回检索
                         bool LinkRepeated=false;
                         for(int n=0;n<listLinkRoad.count();n++)
                         {
                             if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(ListLineItemData.at(0)+",2")) {LinkRepeated=true;break;}
                         }
                         if(LinkRepeated) continue;

                         //判断是否是错误的路径
                         if(!CheckLinkRoad(ListLineItemData.at(0)+",2",KnownLineValidRoadCnt)) continue;
                         Symb2TermInfo_ID=ListLineItemData.at(3).toInt();
                         Category=ListLineItemData.at(4).toInt();
                         StrLinkRoad=ListLineItemData.at(0)+",2";
                         //如果是源端口则停止搜索
                         if(IsSourceConn(Symb2TermInfo_ID,Category))
                         {
                             FindSourceConn=true;
                             break;
                         }
                         FindTerm=true;
                         break;
                      }//for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//元件引脚连线
                      if(FindTerm||FindSourceConn) break;
                  }//for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                  if(FindTerm||FindSourceConn) break;
                }//for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
                if(FindTerm||FindSourceConn) break;
            }//for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层

        }//if(ModelLineByUnits->rowCount()>0)
        //====找连线的另一头END====
        //====找功能子块另一头=====
        if(!FindTerm)
        {
            QString SymbolID=QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID));
            //不能往回检索
            bool LinkRepeated=false;
            for(int n=0;n<listLinkRoad.count();n++)
            {
                if(listLinkRoad.at(n).mid(0,listLinkRoad.at(n).lastIndexOf(","))==(SymbolID+","+QString::number(Category))) {LinkRepeated=true;break;}
            }
            if(!LinkRepeated)
            {
                //查找功能子块另一端的端口之前必须检查功能子块
                if(CheckLinkRoad(SymbolID+","+QString::number(Category),KnownLineValidRoadCnt))
                {
                    if(GetUnitStripOtherSideTerm(Symb2TermInfo_ID,Category)>=0)
                    {
                        StrLinkRoad=QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID))+","+QString::number(Category);
                        if(IsExecConn(Symb2TermInfo_ID,Category)) FindExecConn=true;
                        else FindTerm=true;
                    }
                }
            }
        }
        //====找功能子块另一头END=====
        if(FindTerm||FindSourceConn||FindExecConn)
        {
            //更新KnownLineValidRoadCnt，listLinkRoad和ListNodeSpurCount
            //查看ListLineItemData.at(3)节点有几条子块,优先采用KnownLineValidRoadCnt中的结果
            bool FindedInKnownLineValidRoadCnt=false;
            for(QString StrKnownLine:KnownLineValidRoadCnt)
            {
                if(StrKnownLine.mid(0,StrKnownLine.lastIndexOf(","))==StrLinkRoad)
                {
                    //NodeSpurCount=StrKnownLine.split(",").at(2).toInt();
                    StrLinkRoad=StrKnownLine;
                    FindedInKnownLineValidRoadCnt=true;
                    break;
                }
            }
            if(!FindedInKnownLineValidRoadCnt)
            {
                NodeSpurCount=GetLinesBySymb2TermInfo_ID(Symb2TermInfo_ID,Category,"").count();
                StrLinkRoad+=","+QString::number(NodeSpurCount);
                KnownLineValidRoadCnt.append(StrLinkRoad);
            }
            listLinkRoad.append(StrLinkRoad);
            if(FindSourceConn) listLinkRoad.append(QString::number(GetSymbolIDByTermID(Category,Symb2TermInfo_ID))+","+QString::number(Category)+",0");
        }
        if(FindExecConn||FindSourceConn)
        {
            //当前的链路不是目标链路，因为没有找到源端口或检索到了终端端口，重新搜索
            Symb2TermInfo_ID=initSymb2TermInfo_ID;
            Category=0;
            UpdateKnownLineValidRoadCnt(listLinkRoad,KnownLineValidRoadCnt);
            if(FindSourceConn) listFinalLinkRoad.append(listLinkRoad);
            //else qDebug()<<"错误，找到终端端口";
//qDebug()<<"listLinkRoad="<<listLinkRoad<<",KnownLineValidRoadCnt="<<KnownLineValidRoadCnt;
            listLinkRoad.clear();
            listLinkRoad.append(QString::number(GetSymbolIDByTermID(0,initSymb2TermInfo_ID))+",0,"+QString::number(GetLinesBySymb2TermInfo_ID(initSymb2TermInfo_ID,0,"").count()));
        }
        else if(!FindTerm)
        {
            break;
        }
    }//end of while(1)
    //qDebug()<<"执行器链路检索完成："<<listFinalLinkRoad;
    return listFinalLinkRoad;
}*/



void MainWindow::InsertUnitTerminalToItem(QStandardItem *Item,QSqlQuery QueryJXBLine,int index)
{
    QString Symb_ID;
    if(index==0) Symb_ID=QueryJXBLine.value("Symb1_ID").toString();
    else if(index==1) Symb_ID=QueryJXBLine.value("Symb2_ID").toString();
    if(Symb_ID.contains(":C")||Symb_ID.contains(":G")||Symb_ID.contains(":1")||Symb_ID.contains(":2")||Symb_ID.contains(":3")) return;
    QString Symb_Category;
    if(index==0) Symb_Category=QueryJXBLine.value("Symb1_Category").toString();
    else if(index==1) Symb_Category=QueryJXBLine.value("Symb2_Category").toString();
    //qDebug()<<"ConnectLine_ID="<<QueryConnectLine.value("ConnectLine_ID").toInt();
    //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表

    //找到Symb_ID对应的器件
    QString DT;
    int UnitStripID=GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
    //查看当前的器件是否在列表中已经存在
    bool UnitStripExisted=false;
    for(int i=0;i<Item->rowCount();i++)
    {
        if((Item->child(i,0)->data(Qt::UserRole).toInt()==UnitStripID)&&(Item->child(i,0)->data(Qt::WhatsThisRole).toString()==Symb_Category))//已存在，添加Term到Item->child(i,0)
        {
            UnitStripExisted=true;
            /*
            //查看当前端口在Item->child(i,0)是否存在
            bool TermExisted=false;
            for(int j=0;j<Item->child(i,0)->rowCount();j++)
            {
                QStringList ListData=Item->child(i,0)->child(j,0)->data(Qt::UserRole).toStringList();
                if(ListData.count()==5)
                {
                    if(ListData.at(1)==Symb_ID)
                    {
                        TermExisted=true;
                        break;
                    }
                }
            }*/
            //if(!TermExisted)//添加Term到Item->child(i,0)
            {
                InsertTermToUnitStrip(Item->child(i,0),QueryJXBLine,Symb_ID,Symb_Category,index);
            }
            break;
        }//if(Item->child(i,0)->data(Qt::UserRole).toInt()==UnitStripID)
    }//for(int i=0;i<Item->rowCount();i++)
    if(!UnitStripExisted)//元件不存在，添加元件和端口
    {
        QStandardItem *UnitStripItem=new QStandardItem(QIcon("C:/TBD/data/端子排图标.png"),DT);
        UnitStripItem->setData(QVariant(Symb_Category),Qt::WhatsThisRole);
        UnitStripItem->setData(QVariant(UnitStripID),Qt::UserRole);
        Item->appendRow(UnitStripItem);
        InsertTermToUnitStrip(UnitStripItem,QueryJXBLine,Symb_ID,Symb_Category,index);
    }
}

void MainWindow::InsertLineToItem(QStandardItem *Item,QSqlQuery QueryJXBLine)
{
    QString Symb1_ID=QueryJXBLine.value("Symb1_ID").toString();
    QString Symb2_ID=QueryJXBLine.value("Symb2_ID").toString();
    if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) return;
    if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) return;
    QString Symb1_Category=QueryJXBLine.value("Symb1_Category").toString();
    QString Symb2_Category=QueryJXBLine.value("Symb2_Category").toString();
    //qDebug()<<"ConnectLine_ID="<<QueryConnectLine.value("ConnectLine_ID").toInt();
    //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表
    QString ConnectionNumber=QueryJXBLine.value("ConnectionNumber").toString();
    QStandardItem *ConnectionNumberNodeItem;
    bool AddConnectionNumberNode=true;
    if(ConnectionNumber=="")
    {
        for(int i=0;i<Item->rowCount();i++)
        {
            if(Item->child(i,0)->data(Qt::DisplayRole).toString()=="")
            {
                ConnectionNumberNodeItem=Item->child(i,0);
                AddConnectionNumberNode=false;
                break;
            }
        }
    }
    if(AddConnectionNumberNode)
    {
        ConnectionNumberNodeItem=new QStandardItem(QIcon("C:/TBD/data/线号图标.png"),ConnectionNumber);
        ConnectionNumberNodeItem->setData(QVariant("线号"),Qt::WhatsThisRole);
        ConnectionNumberNodeItem->setData(QVariant(QueryJXBLine.value("JXB_ID").toInt()),Qt::UserRole);
        Item->appendRow(ConnectionNumberNodeItem);
    }
    //在列表中添加导线
    //根据连接点对象是元件还是端子排分类
    QString Symb1Str,Symb2Str;
    if(Symb1_Category=="0")//元件
    {
        Symb1Str=GetUnitTermStrByTermID(Symb1_ID);
    }
    else if(Symb1_Category=="1")//端子排
    {
        Symb1Str=GetTerminalTermStrByTermID(Symb1_ID);
    }
    if(Symb2_Category=="0")//元件
    {
        Symb2Str=GetUnitTermStrByTermID(Symb2_ID);
    }
    else if(Symb2_Category=="1")//端子排
    {
        Symb2Str=GetTerminalTermStrByTermID(Symb2_ID);
    }
    QString LineStr=Symb1Str+"<->"+Symb2Str;
    if(ConnectionNumberNodeItem!=nullptr)
    {
        QStandardItem *LineItem=new QStandardItem(QIcon("C:/TBD/data/连线图标.png"),LineStr);
        LineItem->setData(QVariant("连线"),Qt::WhatsThisRole);
        QStringList ListLineItemData;
        ListLineItemData.clear();
        ListLineItemData.append(QueryJXBLine.value("JXB_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb1_Category").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_ID").toString());
        ListLineItemData.append(QueryJXBLine.value("Symb2_Category").toString());
        LineItem->setData(QVariant(ListLineItemData),Qt::UserRole);
        ConnectionNumberNodeItem->appendRow(LineItem);
    }
}

void MainWindow::LoadModelLineDT()
{
    //根据线号================
    ModelLineDT->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelLineDT->appendRow(fatherItem);

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    while(QueryJXB.next())
    {
        QString ProjectStructure_ID=QueryJXB.value("ProjectStructure_ID").toString();

        QString StrGaoceng,StrPos;
        QSqlQuery queryPos=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+ProjectStructure_ID;
        queryPos.exec(SqlStr);
        if(queryPos.next()) StrPos=queryPos.value("Structure_INT").toString();
        QSqlQuery queryGaoceng=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+queryPos.value("Parent_ID").toString();
        queryGaoceng.exec(SqlStr);
        if(queryGaoceng.next()) StrGaoceng=queryGaoceng.value("Structure_INT").toString();

        //查看ModelLineDT是否有该高层节点
        bool GaoCengExisted=false;
        QStandardItem *GaoCengNodeItem;
        for(int i=0;i<fatherItem->rowCount();i++)
        {
            if((fatherItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")&&(fatherItem->child(i,0)->data(Qt::DisplayRole).toString()==StrGaoceng))
            {
                GaoCengExisted=true;
                GaoCengNodeItem=fatherItem->child(i,0);
                break;
            }
        }
        if(!GaoCengExisted)
        {
            GaoCengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),StrGaoceng);
            GaoCengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
            fatherItem->appendRow(GaoCengNodeItem);
        }
        if(GaoCengNodeItem==nullptr) continue;
        bool PosExisted=false;
        QStandardItem *PosNodeItem;
        for(int i=0;i<GaoCengNodeItem->rowCount();i++)
        {
            if((GaoCengNodeItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")&&(GaoCengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==StrPos))
            {
                PosExisted=true;
                PosNodeItem=GaoCengNodeItem->child(i,0);
                break;
            }
        }
        if(!PosExisted)
        {
            PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),StrPos);
            PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
            GaoCengNodeItem->appendRow(PosNodeItem);
        }
        if(PosNodeItem==nullptr) continue;
        //在PosNodeItem下插入连线
        InsertLineToItem(PosNodeItem,QueryJXB);
    }
    if(ModelLineDT->rowCount()>0) ui->treeViewLineDT->expand(fatherItem->index());
}

void MainWindow::LoadModelLineByUnits()
{
    //根据元件=================
    ModelLineByUnits->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelLineByUnits->appendRow(fatherItem);

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(temp);
    while(QueryJXB.next())
    {
        QString StrGaoceng,StrPos;
        for(int index=0;index<2;index++)
        {
            if(index==0)
            {
                if(QueryJXB.value("Symb1_ID").toString()!="")
                {
                    GetUnitTermimalGaocengAndPos(QueryJXB.value("Symb1_Category").toInt(),QueryJXB.value("Symb1_ID").toInt(),StrGaoceng,StrPos);
                }
                else continue;
            }
            else if(index==1)
            {
                if(QueryJXB.value("Symb2_ID").toString()!="")
                {
                    GetUnitTermimalGaocengAndPos(QueryJXB.value("Symb2_Category").toInt(),QueryJXB.value("Symb2_ID").toInt(),StrGaoceng,StrPos);
                }
                else continue;
            }
            //qDebug()<<"StrGaoceng="<<StrGaoceng<<",StrPos="<<StrPos<<",index="<<index<<",ConnectionNumber="<<QueryJXB.value("ConnectionNumber").toString();
            //查看ModelLineByUnits是否有该高层节点
            bool GaoCengExisted=false;
            QStandardItem *GaoCengNodeItem;
            for(int i=0;i<fatherItem->rowCount();i++)
            {
                if((fatherItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")&&(fatherItem->child(i,0)->data(Qt::DisplayRole).toString()==StrGaoceng))
                {
                    GaoCengExisted=true;
                    GaoCengNodeItem=fatherItem->child(i,0);
                    break;
                }
            }
            if(!GaoCengExisted)
            {
                GaoCengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),StrGaoceng);
                GaoCengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
                fatherItem->appendRow(GaoCengNodeItem);
            }
            if(GaoCengNodeItem==nullptr) continue;
            bool PosExisted=false;
            QStandardItem *PosNodeItem;
            for(int i=0;i<GaoCengNodeItem->rowCount();i++)
            {
                if((GaoCengNodeItem->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")&&(GaoCengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==StrPos))
                {
                    PosExisted=true;
                    PosNodeItem=GaoCengNodeItem->child(i,0);
                    break;
                }
            }
            if(!PosExisted)
            {
                PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),StrPos);
                PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                GaoCengNodeItem->appendRow(PosNodeItem);
            }
            if(PosNodeItem==nullptr) continue;
            //在PosNodeItem下插入器件
            InsertUnitTerminalToItem(PosNodeItem,QueryJXB,index);
        }//for(int index=0;index<2;index++)
    }
    if(ModelLineByUnits->rowCount()>0) ui->treeViewLineByUnit->expand(fatherItem->index());

    QString OriginalLineGaoceng=ui->CbLineGaoceng->currentText();
    QString OriginalLinePos=ui->CbLinePos->currentText();
    ui->CbLineGaoceng->clear();
    ui->CbLineGaoceng->addItem("高层");
    ui->CbLinePos->clear();
    ui->CbLinePos->addItem("位置");
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)
    {
        ui->CbLineGaoceng->addItem(ModelLineByUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            bool Existed=false;
            for(int k=0;k<ui->CbLinePos->count();k++)
            {
                if(ui->CbLinePos->itemText(k)==ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbLinePos->addItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
            }
        }
    }
    ui->CbLineGaoceng->setCurrentText(OriginalLineGaoceng);
    ui->CbLinePos->setCurrentText(OriginalLinePos);

    //载入页
    QString OriginalPageName=ui->CbLinePage->currentText();
    ui->CbLinePage->clear();
    ui->CbLinePage->addItem("页");
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Page WHERE PageType = '原理图' ORDER BY ProjectStructure_ID";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        ui->CbLinePage->addItem(GetPageNameByPageID(QueryPage.value("Page_ID").toInt()));
    }
    ui->CbLinePage->setCurrentText(OriginalPageName);
    FilterLines();
}

void MainWindow::LoadProjectLines()
{
    LoadModelLineDT();
    LoadModelLineByUnits();
}

void MainWindow::LoadProjectTerminals()
{
    //记录当前展开的index
    QList<int> listGaocengExpendID,listPosExpendID,listTerminalStripExpendID;
    if(ModelTerminals->rowCount()>0)
    {
        for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//位置
        {
            if(ui->treeViewTerminal->isExpanded(ModelTerminals->item(0,0)->child(i,0)->index()))//高层
                listGaocengExpendID.append(ModelTerminals->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
            for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)//位置
            {
                if(ui->treeViewTerminal->isExpanded(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->index()))
                    listPosExpendID.append(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
                for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                {
                    if(ui->treeViewTerminal->isExpanded(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->index()))
                        listTerminalStripExpendID.append(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());
                }
            }
        }
    }

    ModelTerminals->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelTerminals->appendRow(fatherItem);
    ui->treeViewTerminal->expand(fatherItem->index());
    //在TerminalStrip表中检索元件
    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM TerminalStrip ORDER BY DT");
    QueryTerminalStrip.exec(temp);
    while(QueryTerminalStrip.next())
    {
        QString ProjectStructure_ID=QueryTerminalStrip.value("ProjectStructure_ID").toString();
        int TerminalStrip_ID=QueryTerminalStrip.value("TerminalStrip_ID").toInt();
        QString TerminalTag=QueryTerminalStrip.value("DT").toString();
        //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+ProjectStructure_ID);
        QueryPos.exec(temp);
        if(!QueryPos.next()) continue;
        QString PosStr=QueryPos.value("Structure_INT").toString();
        //查找对应的高层
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) continue;
        QString GaocengStr=QueryGaoceng.value("Structure_INT").toString();
        QString TerminalNodeStr;
        //UnitNodeStr+="="+GaocengStr;
        TerminalNodeStr=TerminalTag;
        //在treeViewUnits中查看位置是否存在，不存在则新增位置节点
        bool GaocengNodeExist=false;
        bool PosNodeExist=false;
        QStandardItem *PosNodeItem,*GaocengNodeItem;
        for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)
        {
            if(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==GaocengStr)
            {
                GaocengNodeExist=true;
                GaocengNodeItem=ModelTerminals->item(0,0)->child(i,0);
                break;
            }
        }
        if(!GaocengNodeExist) //新增高层节点
        {
            GaocengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),GaocengStr);
            GaocengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
            GaocengNodeItem->setData(QVariant(QueryGaoceng.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            fatherItem->appendRow(GaocengNodeItem);
        }
        if(GaocengNodeItem==nullptr) continue;
        for(int i=0;i<listGaocengExpendID.count();i++)
        {
            if(listGaocengExpendID.at(i)==QueryGaoceng.value("ProjectStructure_ID").toInt()) {ui->treeViewTerminal->expand(GaocengNodeItem->index());break;}
        }
        for(int i=0;i<GaocengNodeItem->rowCount();i++)//在高层节点下查找位置节点，不存在则新增位置节点
        {
            if(GaocengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==PosStr)
            {
                PosNodeExist=true;
                PosNodeItem=GaocengNodeItem->child(i,0);
                break;
            }
        }
        if(!PosNodeExist) //新增位置节点
        {
            PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),PosStr);
            PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
            PosNodeItem->setData(QVariant(QueryPos.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            GaocengNodeItem->appendRow(PosNodeItem);
        }
        if(PosNodeItem==nullptr) continue;
        for(int i=0;i<listPosExpendID.count();i++)
        {
            if(listPosExpendID.at(i)==QueryPos.value("ProjectStructure_ID").toInt()) {ui->treeViewTerminal->expand(PosNodeItem->index());break;}
        }
        //在位置节点下插入端子排
        QStandardItem *TerminalItem=new QStandardItem(QIcon("C:/TBD/data/端子排图标.png"),TerminalNodeStr);
        TerminalItem->setData(QVariant("端子排"),Qt::WhatsThisRole);
        TerminalItem->setData(QVariant(TerminalStrip_ID),Qt::UserRole);
        PosNodeItem->appendRow(TerminalItem);
        //在节点下插入所有的端子,在Symbol表中检索与元件关联的所有子块
        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QString::number(TerminalStrip_ID)+"' ORDER BY Terminal_ID");
        QueryTerminal.exec(temp);
        while(QueryTerminal.next())
        {
            QStandardItem *TerminalSpurItem;
            QString TerminalSpurStr=QueryTerminal.value("ShortJumper").toString()+QueryTerminal.value("Designation").toString();
            QSqlQuery QueryTerminalInstance = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            temp = "SELECT * FROM TerminalInstance WHERE Terminal_ID = '"+QueryTerminal.value("Terminal_ID").toString()+"'";
            QueryTerminalInstance.exec(temp);
            if(QueryTerminalInstance.next())
            {
                //TerminalSpurStr+="("+GetPageNameByPageID(QueryTerminal.value("Page_ID").toString().toInt())+")";
                TerminalSpurStr+="("+QueryTerminal.value("FunDefine").toString()+")";
                TerminalSpurItem=new QStandardItem(QIcon("C:/TBD/data/端子图标_已插入.png"),TerminalSpurStr);
            }
            else
            {
                TerminalSpurStr+="("+QueryTerminal.value("FunDefine").toString()+")";
                TerminalSpurItem=new QStandardItem(QIcon("C:/TBD/data/端子图标_未插入.png"),TerminalSpurStr);
            }
            TerminalSpurItem->setData(QVariant("端子"),Qt::WhatsThisRole);
            TerminalSpurItem->setData(QVariant(QueryTerminal.value("Terminal_ID").toInt()),Qt::UserRole);
            TerminalItem->appendRow(TerminalSpurItem);
            if(SelectTerminal_ID==QueryTerminal.value("Terminal_ID").toInt())
            {
                ui->treeViewTerminal->expand(TerminalItem->index());
                ui->treeViewTerminal->setCurrentIndex(TerminalSpurItem->index());
            }
        }
        if(SelectTerminalStrip_ID==TerminalStrip_ID)
        {
            ui->treeViewTerminal->expand(TerminalItem->index());
            ui->treeViewTerminal->setCurrentIndex(TerminalItem->index());
        }
        else
        {
            for(int i=0;i<listTerminalStripExpendID.count();i++)
            {
                if(listTerminalStripExpendID.at(i)==TerminalStrip_ID) {ui->treeViewTerminal->expand(TerminalItem->index());break;}
            }
        }
    }

    QString OriginalTerminalGaoceng=ui->CbTermGaoceng->currentText();
    QString OriginalTerminalPos=ui->CbTermPos->currentText();
    ui->CbTermGaoceng->clear();
    ui->CbTermGaoceng->addItem("高层");
    ui->CbTermPos->clear();
    ui->CbTermPos->addItem("位置");
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)
    {
        ui->CbTermGaoceng->addItem(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)
        {
            bool Existed=false;
            for(int k=0;k<ui->CbTermPos->count();k++)
            {
                if(ui->CbTermPos->itemText(k)==ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbTermPos->addItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
            }
        }
    }
    ui->CbTermGaoceng->setCurrentText(OriginalTerminalGaoceng);
    ui->CbTermPos->setCurrentText(OriginalTerminalPos);

    //载入页
    QString OriginalPageName=ui->CbUnitPage->currentText();
    ui->CbTermPage->clear();
    ui->CbTermPage->addItem("页");
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Page WHERE PageType = '原理图' ORDER BY ProjectStructure_ID";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        ui->CbTermPage->addItem(GetPageNameByPageID(QueryPage.value("Page_ID").toInt()));
    }
    ui->CbTermPage->setCurrentText(OriginalPageName);
    FilterTerminal();
}

void MainWindow::LoadProjectUnits()
{
    //记录当前展开的index
    QList<int> listGaocengExpendID,listPosExpendID,listEquipmentExpendID;
    if(ModelUnits->rowCount()>0)
    {
        for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//位置
        {
            if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->index()))//高层
                listGaocengExpendID.append(ModelUnits->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
            for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
            {
                if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->child(j,0)->index()))
                    listPosExpendID.append(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
                for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
                {
                    if(ui->treeViewUnits->isExpanded(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->index()))
                        listEquipmentExpendID.append(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());
                }
            }
        }
    }

    ModelUnits->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelUnits->appendRow(fatherItem);
    ui->treeViewUnits->expand(fatherItem->index());
    //在Equipment表中检索元件
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM Equipment ORDER BY DT");
    QueryEquipment.exec(temp);
    while(QueryEquipment.next())
    {
        QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
        int Equipment_ID=QueryEquipment.value("Equipment_ID").toInt();
        QString UnitTag=QueryEquipment.value("DT").toString();
        QString UnitType=QueryEquipment.value("Type").toString();
        QString UnitName=QueryEquipment.value("Name").toString();
        //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
        QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+ProjectStructure_ID);
        QueryPos.exec(temp);
        if(!QueryPos.next()) continue;
        QString PosStr=QueryPos.value("Structure_INT").toString();
        //查找对应的高层
        QSqlQuery QueryGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID="+QueryPos.value("Parent_ID").toString());
        QueryGaoceng.exec(temp);
        if(!QueryGaoceng.next()) continue;
        QString GaocengStr=QueryGaoceng.value("Structure_INT").toString();
        QString UnitNodeStr;
        //UnitNodeStr+="="+GaocengStr;
        UnitNodeStr=UnitTag;
        if((UnitType!="")||(UnitName!="")) UnitNodeStr+="(";
        UnitNodeStr+=UnitType;
        if(UnitType!="") UnitNodeStr+=",";
        UnitNodeStr+=UnitName;
        if((UnitType!="")||(UnitName!="")) UnitNodeStr+=")";
        //在treeViewUnits中查看位置是否存在，不存在则新增位置节点
        bool GaocengNodeExist=false;
        bool PosNodeExist=false;
        QStandardItem *PosNodeItem,*GaocengNodeItem;
        for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
        {
            if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==GaocengStr)
            {
                GaocengNodeExist=true;
                GaocengNodeItem=ModelUnits->item(0,0)->child(i,0);
                break;
            }
        }
        if(!GaocengNodeExist) //新增高层节点
        {
            GaocengNodeItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),GaocengStr);
            GaocengNodeItem->setData(QVariant("高层"),Qt::WhatsThisRole);
            GaocengNodeItem->setData(QVariant(QueryGaoceng.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            fatherItem->appendRow(GaocengNodeItem);
        }
        if(GaocengNodeItem==nullptr) continue;
        for(int i=0;i<listGaocengExpendID.count();i++)
        {
            if(listGaocengExpendID.at(i)==QueryGaoceng.value("ProjectStructure_ID").toInt()) {ui->treeViewUnits->expand(GaocengNodeItem->index());break;}
        }
        for(int i=0;i<GaocengNodeItem->rowCount();i++)//在高层节点下查找位置节点，不存在则新增位置节点
        {
            if(GaocengNodeItem->child(i,0)->data(Qt::DisplayRole).toString()==PosStr)
            {
                PosNodeExist=true;
                PosNodeItem=GaocengNodeItem->child(i,0);
                break;
            }
        }
        if(!PosNodeExist) //新增位置节点
        {
            PosNodeItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),PosStr);
            PosNodeItem->setData(QVariant("位置"),Qt::WhatsThisRole);
            PosNodeItem->setData(QVariant(QueryPos.value("ProjectStructure_ID").toInt()),Qt::UserRole);
            GaocengNodeItem->appendRow(PosNodeItem);
        }
        if(PosNodeItem==nullptr) continue;
        for(int i=0;i<listPosExpendID.count();i++)
        {
            if(listPosExpendID.at(i)==QueryPos.value("ProjectStructure_ID").toInt()) {ui->treeViewUnits->expand(PosNodeItem->index());break;}
        }
        //在位置节点下插入元件
        QStandardItem *UnitItem=new QStandardItem(QIcon("C:/TBD/data/元件图标.png"),UnitNodeStr);
        UnitItem->setData(QVariant("元件"),Qt::WhatsThisRole);
        UnitItem->setData(QVariant(Equipment_ID),Qt::UserRole);
        PosNodeItem->appendRow(UnitItem);
        //在元件节点下插入所有的功能子块,在Symbol表中检索与元件关联的所有子块
        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM Symbol WHERE Equipment_ID = '"+QString::number(Equipment_ID)+"'");
        QuerySymbol.exec(temp);
        //qDebug()<<"LoadProjectUnits Equipment_ID:"<<Equipment_ID;
        while(QuerySymbol.next())
        {
            QStandardItem *UnitSpurItem;
            QString UnitSpurStr;
            UnitSpurStr=GetUnitSpurStrBySymbol_ID(QuerySymbol);
            //根据Symbol_Handle是否存在确定功能子块图标和文字
            //qDebug()<<"Symbol:"<<QuerySymbol.value("Symbol").toString()<<"  Symbol_Handle:"<<QuerySymbol.value("Symbol_Handle").toString();
            if(QuerySymbol.value("Symbol").toString()==""&&(QuerySymbol.value("FunDefine").toString()!="黑盒")&&(QuerySymbol.value("FunDefine").toString()!="PLC 盒子"))
            {
                UnitSpurStr+="-"+QuerySymbol.value("FunDefine").toString();
                UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_不可插入.png"),UnitSpurStr);
            }
            else
            {
                if(QuerySymbol.value("Symbol_Handle").toString()!="")//
                {
                    //根据实际子块插入的位置
                    //得到子块实际放置的图纸位置名称
                    UnitSpurStr+="("+GetPageNameByPageID(QuerySymbol.value("Page_ID").toString().toInt())+")";
                    UnitSpurStr+=QuerySymbol.value("FunDefine").toString();
                    UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_已插入.png"),UnitSpurStr);
                }
                else
                {
                    UnitSpurStr+="-"+QuerySymbol.value("FunDefine").toString();
                    UnitSpurItem=new QStandardItem(QIcon("C:/TBD/data/逻辑支路图标_未插入.png"),UnitSpurStr);
                }
            }
            UnitSpurItem->setData(QVariant("功能子块"),Qt::WhatsThisRole);
            UnitSpurItem->setData(QVariant(QuerySymbol.value("Symbol_ID").toInt()),Qt::UserRole);
            UnitSpurItem->setFlags(UnitSpurItem->flags()|Qt::ItemIsDragEnabled);
            UnitItem->appendRow(UnitSpurItem);
            if(SelectSymbol_ID==QuerySymbol.value("Symbol_ID").toInt())
            {
                ui->treeViewUnits->expand(UnitItem->index());
                ui->treeViewUnits->setCurrentIndex(UnitSpurItem->index());
            }
        }
        if(SelectEquipment_ID==Equipment_ID)
        {
            ui->treeViewUnits->expand(UnitItem->index());
            ui->treeViewUnits->setCurrentIndex(UnitItem->index());
        }
        else
        {
            for(int i=0;i<listEquipmentExpendID.count();i++)
            {
                if(listEquipmentExpendID.at(i)==Equipment_ID) {ui->treeViewUnits->expand(UnitItem->index());break;}
            }
        }
    }

    LoadUnitTable();

    QString OriginalUnitGaoceng=ui->CbUnitGaoceng->currentText();
    QString OriginalUnitPos=ui->CbUnitPos->currentText();
    ui->CbUnitGaoceng->clear();
    ui->CbUnitGaoceng->addItem("高层");
    ui->CbUnitPos->clear();
    ui->CbUnitPos->addItem("位置");
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
    {
        ui->CbUnitGaoceng->addItem(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            bool Existed=false;
            for(int k=0;k<ui->CbUnitPos->count();k++)
            {
                if(ui->CbUnitPos->itemText(k)==ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbUnitPos->addItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
            }
        }
    }
    ui->CbUnitGaoceng->setCurrentText(OriginalUnitGaoceng);
    ui->CbUnitPos->setCurrentText(OriginalUnitPos);

    //载入页
    QString OriginalPageName=ui->CbUnitPage->currentText();
    ui->CbUnitPage->clear();
    ui->CbUnitPage->addItem("页");
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Page WHERE PageType = '原理图' ORDER BY ProjectStructure_ID";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        ui->CbUnitPage->addItem(GetPageNameByPageID(QueryPage.value("Page_ID").toInt()));
    }
    ui->CbUnitPage->setCurrentText(OriginalPageName);
    FilterUnit();
    LoadProjectSystemDescription();
}

void MainWindow::LoadUnitTable()
{
    ui->tableWidgetUnit->setRowCount(0);
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    //载入table
    if(!ui->CbUnitTogether->isChecked())//不汇总
    {
        for(int i=0;i<ModelUnits->rowCount();i++)
        {
            for(int j=0;j<ModelUnits->item(i,0)->rowCount();j++)
            {
                for(int k=0;k<ModelUnits->item(i,0)->child(j,0)->rowCount();k++)
                {
                    for(int m=0;m<ModelUnits->item(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                    {
                        int Equipment_ID = ModelUnits->item(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toInt();
                        QString SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(Equipment_ID);
                        QueryEquipment.exec(SqlStr);
                        if(QueryEquipment.next())
                        {
                            ui->tableWidgetUnit->setRowCount(ui->tableWidgetUnit->rowCount()+1);
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidgetUnit->rowCount())));//序号
                            ui->tableWidgetUnit->item(ui->tableWidgetUnit->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipment.value("Equipment_ID").toInt());
                            QString UnitTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,1,new QTableWidgetItem(UnitTag));//项目代号
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,2,new QTableWidgetItem(QueryEquipment.value("Type").toString()));//型号
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,3,new QTableWidgetItem(QueryEquipment.value("Name").toString()));//名称
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,4,new QTableWidgetItem("1"));//数量
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,5,new QTableWidgetItem(QueryEquipment.value("Factory").toString()));//厂家
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,6,new QTableWidgetItem(QueryEquipment.value("PartCode").toString()));//部件编号
                            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,7,new QTableWidgetItem(QueryEquipment.value("Remark").toString()));//元件备注
                        }
                    }
                }

            }
        }
    }
    else//汇总
    {
        QString StrSql;
        QStringList ListedPart;
        ListedPart.clear();
        StrSql="SELECT * FROM Equipment ORDER BY ProjectStructure_ID";
        QueryEquipment.exec(StrSql);
        while(QueryEquipment.next())
        {
            if(QueryEquipment.value("PartCode").toString()=="") continue;
            bool PartExisted=false;
            for(int i=0;i<ListedPart.count();i++)
            {
                if(ListedPart.at(i)==QueryEquipment.value("PartCode").toString())
                {
                    PartExisted=true;
                    break;
                }
            }
            if(PartExisted) continue;
            ListedPart.append(QueryEquipment.value("PartCode").toString());
            ui->tableWidgetUnit->setRowCount(ui->tableWidgetUnit->rowCount()+1);
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,0,new QTableWidgetItem(QString::number(ui->tableWidgetUnit->rowCount())));//序号
            ui->tableWidgetUnit->item(ui->tableWidgetUnit->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipment.value("Equipment_ID").toInt());
            QString UnitTag=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+QueryEquipment.value("DT").toString();
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,1,new QTableWidgetItem(UnitTag));//项目代号
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,2,new QTableWidgetItem(QueryEquipment.value("Type").toString()));//型号
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,3,new QTableWidgetItem(QueryEquipment.value("Name").toString()));//名称
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            StrSql="SELECT * FROM Equipment WHERE PartCode = '"+QueryEquipment.value("PartCode").toString()+"'";
            QuerySearch.exec(StrSql);
            if(QuerySearch.last())
                ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,4,new QTableWidgetItem(QString::number(QuerySearch.at()+1)));//数量
            else
                ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,4,new QTableWidgetItem("0"));//数量
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,5,new QTableWidgetItem(QueryEquipment.value("Factory").toString()));//厂家
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,6,new QTableWidgetItem(QueryEquipment.value("PartCode").toString()));//部件编号
            ui->tableWidgetUnit->setItem(ui->tableWidgetUnit->rowCount()-1,7,new QTableWidgetItem(QueryEquipment.value("Remark").toString()));//元件备注
        }
    }
}

void MainWindow::LoadProjectPages()
{
    //记录当前展开的index
    QList<int> listPagesExpend;
    if(ModelPages->rowCount()>0)
    {
        for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
        {
            if(ui->treeViewPages->isExpanded(ModelPages->item(0,0)->child(i,0)->index()))
            {
                if(StrIsNumber(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toString()))
                    listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt());
            }
            for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
            {
                if(ui->treeViewPages->isExpanded(ModelPages->item(0,0)->child(i,0)->child(j,0)->index()))
                {
                    if(StrIsNumber(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toString()))
                        listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt());
                }
                for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
                {
                    if(ui->treeViewPages->isExpanded(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->index()))
                    {
                        if(StrIsNumber(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toString()))
                            listPagesExpend.append(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt());
                    }
                }
            }
        }
    }

    ModelPages->clear();
    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString temp = QString("SELECT Structure_INT FROM ProjectStructure WHERE Structure_ID = '1'");
    QueryVar.exec(temp);
    if(!QueryVar.next()) return;
    QStandardItem *fatherItem;
    fatherItem= new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),QueryVar.value(0).toString());
    fatherItem->setData(QVariant("项目"),Qt::WhatsThisRole);
    ModelPages->appendRow(fatherItem);
    ui->treeViewPages->expand(fatherItem->index());
    QSqlQuery QueryVarPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    temp = QString("SELECT * FROM ProjectStructure WHERE Structure_ID = '6'");
    QueryVarPage.exec(temp);
    while(QueryVarPage.next())
    {
        //if(QueryVarPage.value("Structure_INT").toString()!="") continue;
        QString PosRecordID=QueryVarPage.value("Parent_ID").toString();
        QSqlQuery QueryVar2 = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+PosRecordID);
        QueryVar2.exec(temp);
        if(!QueryVar2.next()) return;
        QString GaoCengRecordID=QueryVar2.value("Parent_ID").toString();
        QSqlQuery QueryVar3 = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        temp = QString("SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+GaoCengRecordID);
        QueryVar3.exec(temp);
        if(!QueryVar3.next()) return;

        //查看高层节点是否存在，若不存在则新建,若存在则添加位置信息
        bool GaocengExist=false;
        //如果高层代号非空，则先检索高层代号节点是否存在；如果高层代号为空，则检索位置代号节点是否存在
        if(QueryVar3.value("Structure_INT").toString()!="")//高层代号非空，则先检索高层代号节点是否存在
        {
            for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==QueryVar3.value("Structure_INT").toString())//高层存在，添加位置信息
                {
                    bool PosExist=false;
                    //在高层代号非空的前提下，如果位置代号非空，则检索位置代号是否存在；
                    if(QueryVar2.value("Structure_INT").toString()!="")//位置信息非空
                    {
                        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
                        {
                            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()==QueryVar2.value("Structure_INT").toString())//位置信息存在
                            {
                                if(QueryVarPage.value("Structure_INT").toString()!="")
                                {
                                    AddIndexToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0),QueryVarPage,true,"列表");
                                }
                                else
                                    ModelPages->item(0,0)->child(i,0)->child(j,0)->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);

                                PosExist=true;
                                break;
                            }
                        }
                        if(!PosExist)//位置信息不存在
                        {
                            QStandardItem *SubSubFatherItem;
                            SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),QueryVar2.value("Structure_INT").toString());
                            SubSubFatherItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                            if(QueryVarPage.value("Structure_INT").toString()=="")
                            {
                                SubSubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                            }
                            else
                            {
                                AddIndexToIndex(SubSubFatherItem,QueryVarPage,true,"列表");
                            }
                            ModelPages->item(0,0)->child(i,0)->appendRow(SubSubFatherItem);

                        }
                    }
                    else//位置信息为空，直接添加列表图标
                    {
                        if(QueryVarPage.value("Structure_INT").toString()!="")
                        {
                            AddIndexToIndex(ModelPages->item(0,0)->child(i,0),QueryVarPage,true,"列表");
                        }
                        else
                        {
                            ModelPages->item(0,0)->child(i,0)->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                        }
                    }
                    GaocengExist=true;
                    break;
                }
            }
            if(!GaocengExist)//高层不存在,添加高层信息和位置信息
            {
                QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),QueryVar3.value("Structure_INT").toString());
                SubFatherItem->setData(QVariant("高层"),Qt::WhatsThisRole);
                ModelPages->item(0,0)->appendRow(SubFatherItem);
                if(QueryVar2.value("Structure_INT").toString()!="")//位置信息非空
                {
                    QStandardItem *SubSubFatherItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),QueryVar2.value("Structure_INT").toString());
                    SubSubFatherItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                    if(QueryVarPage.value("Structure_INT").toString()=="")//非表报
                    {
                        SubSubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                    }
                    else
                    {
                        AddIndexToIndex(SubSubFatherItem,QueryVarPage,true,"列表");
                    }
                    SubFatherItem->appendRow(SubSubFatherItem);
                }
                else//位置信息为空，直接添加列表节点
                {
                    if(QueryVarPage.value("Structure_INT").toString()=="")//非表报
                    {
                        SubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                    }
                    else
                    {
                        AddIndexToIndex(SubFatherItem,QueryVarPage,true,"列表");
                    }

                }
            }
        }
        else//高层代号为空，直接添加位置节点
        {
            bool PosExist=false;
            //在高层代号非空的前提下，如果位置代号非空，则检索位置代号是否存在；
            if(QueryVar2.value("Structure_INT").toString()!="")//位置信息非空
            {
                for(int j=0;j<ModelPages->item(0,0)->rowCount();j++)
                {
                    if(ModelPages->item(0,0)->child(j,0)->data(Qt::DisplayRole).toString()==QueryVar2.value("Structure_INT").toString())//位置信息存在
                    {
                        if(QueryVarPage.value("Structure_INT").toString()!="")
                        {
                            AddIndexToIndex(ModelPages->item(0,0)->child(j,0),QueryVarPage,true,"列表");
                        }
                        PosExist=true;
                        break;
                    }
                }
                if(!PosExist)//位置信息不存在
                {
                    QStandardItem *SubFatherItem;
                    SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),QueryVar2.value("Structure_INT").toString());
                    SubFatherItem->setData(QVariant("位置"),Qt::WhatsThisRole);
                    if(QueryVarPage.value("Structure_INT").toString()=="")
                    {
                        SubFatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                    }
                    else
                    {
                        AddIndexToIndex(SubFatherItem,QueryVarPage,true,"列表");
                    }
                    ModelPages->item(0,0)->appendRow(SubFatherItem);
                }
            }
            else//位置信息为空，直接添加列表图标
            {
                if(QueryVarPage.value("Structure_INT").toString()!="")
                {
                    AddIndexToIndex(ModelPages->item(0,0),QueryVarPage,true,"列表");
                }
                else
                {
                    fatherItem->setData(QVariant(QueryVarPage.value("ProjectStructure_ID").toInt()),Qt::UserRole);
                }
            }
        }
    }


    //从table Page载入Pages
    temp = QString("SELECT * FROM Page ORDER BY Page_ID ASC");
    QueryVar.exec(temp);
    while(QueryVar.next())
    {
        //在树节点中查找对应的位置节点
        bool Find=false;
        if(ModelPages->item(0,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
        {
            AddDwgFileToIndex(ModelPages->item(0,0),QueryVar,listPagesExpend);
            continue;
        }
        for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
        {
            //确认当前节点是是高层还是位置还是列表
            if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                {
                    AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0),QueryVar,listPagesExpend);
                    break;
                }
                for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
                {
                    //确认当前节点是位置还是列表
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="位置")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                        {
                            AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0),QueryVar,listPagesExpend);
                            Find=true;
                            break;
                        }
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount()<=0) continue;
                        for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
                        {
                            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()!="列表") continue;
                            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                            {
                                AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0),QueryVar,listPagesExpend);
                                Find=true;
                                break;
                            }
                        }
                    }
                    else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表")//当前节点是列表
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                        {
                            AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(j,0),QueryVar,listPagesExpend);
                            Find=true;
                            break;
                        }
                    }
                }
            }
            else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                {
                    AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0),QueryVar,listPagesExpend);
                    Find=true;
                    break;
                }
                if(ModelPages->item(0,0)->child(i,0)->rowCount()<=0) continue;
                for(int k=0;k<ModelPages->item(0,0)->child(i,0)->rowCount();k++)
                {
                    if(ModelPages->item(0,0)->child(i,0)->child(k,0)->data(Qt::WhatsThisRole).toString()!="列表") continue;
                    if(ModelPages->item(0,0)->child(i,0)->child(k,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                    {
                        AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0)->child(k,0),QueryVar,listPagesExpend);
                        Find=true;
                        break;
                    }
                }
            }
            else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="列表")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::UserRole).toInt()==QueryVar.value("ProjectStructure_ID").toInt())
                {
                    AddDwgFileToIndex(ModelPages->item(0,0)->child(i,0),QueryVar,listPagesExpend);
                    Find=true;
                    break;
                }
            }
            if(Find) break;
        }
    }
    //删除没有图纸的报表节点
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//列表
            {
                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()=="列表")
                {
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()<=0)
                    {
                        ModelPages->item(0,0)->child(i,0)->child(j,0)->removeRow(k);
                        k=k-1;
                        continue;
                    }
                }
            }
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount()<=0)
            {
                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()!="图纸")
                {
                    ModelPages->item(0,0)->child(i,0)->removeRow(j);
                    j=j-1;
                    continue;
                }
            }
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        if(ModelPages->item(0,0)->child(i,0)->rowCount()<=0)
        {
            if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()!="图纸")
            {
                ModelPages->item(0,0)->removeRow(i);i=i-1;continue;
            }
        }
    }
    ui->treeViewPages->expand(ModelPages->indexFromItem(fatherItem));
    QString OriginalPageGaoceng=ui->CbPageGaocengFilter->currentText();
    QString OriginalPagePos=ui->CbPagePosFilter->currentText();
    ui->CbPageGaocengFilter->clear();
    ui->CbPageGaocengFilter->addItem("高层");
    ui->CbPagePosFilter->clear();
    ui->CbPagePosFilter->addItem("位置");
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")
            ui->CbPageGaocengFilter->addItem(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")
        {
            //存在高层为空的图纸
            bool Existed=false;
            for(int k=0;k<ui->CbPageGaocengFilter->count();k++)
            {
                if(ui->CbPageGaocengFilter->itemText(k)=="")
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed) ui->CbPageGaocengFilter->addItem("");
            Existed=false;
            for(int k=0;k<ui->CbPagePosFilter->count();k++)
            {
                if(ui->CbPagePosFilter->itemText(k)==ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString())
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed)
            {
                ui->CbPagePosFilter->addItem(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString());
            }
        }
        else if((ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="图纸")||(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="列表"))
        {
            //存在高层和位置为空的图纸
            bool Existed=false;
            for(int k=0;k<ui->CbPageGaocengFilter->count();k++)
            {
                if(ui->CbPageGaocengFilter->itemText(k)=="")
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed) ui->CbPageGaocengFilter->addItem("");

            Existed=false;
            for(int k=0;k<ui->CbPagePosFilter->count();k++)
            {
                if(ui->CbPagePosFilter->itemText(k)=="")
                {
                    Existed=true;
                    break;
                }
            }
            if(!Existed) ui->CbPagePosFilter->addItem("");
        }
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="位置")
            {
                bool Existed=false;
                for(int k=0;k<ui->CbPagePosFilter->count();k++)
                {
                    if(ui->CbPagePosFilter->itemText(k)==ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString())
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed)
                {
                    ui->CbPagePosFilter->addItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString());
                }
            }
            else if((ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="图纸")||(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表"))
            {
                //存在高层和位置为空的图纸
                bool Existed=false;
                for(int k=0;k<ui->CbPageGaocengFilter->count();k++)
                {
                    if(ui->CbPageGaocengFilter->itemText(k)=="")
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed) ui->CbPageGaocengFilter->addItem("");

                Existed=false;
                for(int k=0;k<ui->CbPagePosFilter->count();k++)
                {
                    if(ui->CbPagePosFilter->itemText(k)=="")
                    {
                        Existed=true;
                        break;
                    }
                }
                if(!Existed) ui->CbPagePosFilter->addItem("");
            }
        }
    }
    ui->CbPageGaocengFilter->setCurrentText(OriginalPageGaoceng);
    ui->CbPagePosFilter->setCurrentText(OriginalPagePos);
    FilterPage();
}

void MainWindow::FilterTerminal()
{
    if(ModelTerminals->rowCount()<=0) return;

    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)
    {
        if(ui->CbTermGaoceng->currentText()!="高层")
        {
            if(ModelTerminals->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbTermGaoceng->currentText())
                ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),true);
            else
                ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),false);
        }
        else
            ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),false);

        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ui->CbTermPos->currentText()!="位置")
            {
                if(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbTermPos->currentText())
                    ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),true);
                else
                    ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),false);
            }
            else
                ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),false);

            for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                //元件
                if(ui->EdTermTagFilter->text()!="")
                {
                    if(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdTermTagFilter->text()))
                        ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),false);
                    else
                        ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),true);
                }
                else
                {
                    ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),false);
                }


                for(int m=0;m<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//功能子块
                {
                    if(ui->CbTermPage->currentText()!="页")
                    {
                        //查看当前功能子块是否在所筛选页面上
                        QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString();
                        QueryTerminal.exec(SqlStr);
                        if(QueryTerminal.next())
                        {
                            if(QueryTerminal.value("Page_ID").toString()!="")
                            {
                                if(GetPageNameByPageID(QueryTerminal.value("Page_ID").toInt())==ui->CbTermPage->currentText())
                                    ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                else
                                    ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                            }
                            else
                                ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                        }
                        else
                            ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                    }
                    else
                    {
                        ui->treeViewTerminal->setRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                    }
                }
            }
        }
    }

    //隐藏没有功能子块的节点
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
            {
                bool AllHide=true;
                for(int m=0;m<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewTerminal->isRowHidden(m,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewTerminal->setRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelTerminals->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewTerminal->isRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelTerminals->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewTerminal->setRowHidden(j,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelTerminals->item(0,0)->rowCount();i++)//高层
    {
        bool AllHide=true;
        for(int k=0;k<ModelTerminals->item(0,0)->child(i,0)->rowCount();k++)//位置
        {
            if(!ui->treeViewTerminal->isRowHidden(k,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelTerminals->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewTerminal->setRowHidden(i,ModelTerminals->indexFromItem(ModelTerminals->item(0,0)),true);
    }
}

void MainWindow::FilterLines()
{
    if(ModelLineByUnits->rowCount()<=0) return;

    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)
    {
        if(ui->CbLineGaoceng->currentText()!="高层")
        {
            if(ModelLineByUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbLineGaoceng->currentText())
                ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),true);
            else
                ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),false);
        }
        else
            ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),false);

        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ui->CbLinePos->currentText()!="位置")
            {
                if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbLinePos->currentText())
                    ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),true);
                else
                    ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),false);
            }
            else
                ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),false);

            for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                //元件
                if(ui->EdLineTagFilter->text()!="")
                {
                    if(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdLineTagFilter->text()))
                        ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),false);
                    else
                        ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),true);
                }
                else
                {
                    ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),false);
                }


                for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//功能子块
                {
                    if(ui->CbLinePage->currentText()!="页")
                    {
                        //查看当前功能子块是否在所筛选页面上

                        //可能是元件或端子
                        QStringList ListData=ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toStringList();
                        if(ListData.count()==5)
                        {
                            if(ListData.at(2)=="0")
                            {
                                QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+ListData.at(1);
                                QuerySymb2TermInfo.exec(SqlStr);
                                if(QuerySymb2TermInfo.next())
                                {
                                    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                    SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySymb2TermInfo.value("Symbol_ID").toString();
                                    QuerySymbol.exec(SqlStr);
                                    if(QuerySymbol.next())
                                    {
                                        if(QuerySymbol.value("Page_ID").toString()!="")
                                        {
                                            if(GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt())==ui->CbLinePage->currentText())
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                            else
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                        }
                                        else
                                            ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                    }
                                    else
                                        ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                }
                            }
                            else if(ListData.at(2)=="1")
                            {
                                QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                QString SqlStr="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID = "+ListData.at(1);
                                QueryTerminalTerm.exec(SqlStr);
                                if(QueryTerminalTerm.next())
                                {
                                    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                                    SqlStr="SELECT * FROM Terminal WHERE Terminal_ID = "+QueryTerminalTerm.value("Terminal_ID").toString();
                                    QueryTerminal.exec(SqlStr);
                                    if(QueryTerminal.next())
                                    {
                                        if(QueryTerminal.value("Page_ID").toString()!="")
                                        {
                                            if(GetPageNameByPageID(QueryTerminal.value("Page_ID").toInt())==ui->CbLinePage->currentText())
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                            else
                                                ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                        }
                                        else
                                            ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                    }
                                    else
                                        ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                                }
                            }
                        }
                    }
                    else
                    {
                        ui->treeViewLineByUnit->setRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                    }
                }
            }
        }
    }

    //隐藏没有功能子块的节点
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
            {
                bool AllHide=true;
                for(int m=0;m<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewLineByUnit->isRowHidden(m,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewLineByUnit->setRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewLineByUnit->isRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelLineByUnits->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewLineByUnit->setRowHidden(j,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelLineByUnits->item(0,0)->rowCount();i++)//高层
    {
        bool AllHide=true;
        for(int k=0;k<ModelLineByUnits->item(0,0)->child(i,0)->rowCount();k++)//位置
        {
            if(!ui->treeViewLineByUnit->isRowHidden(k,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelLineByUnits->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewLineByUnit->setRowHidden(i,ModelLineByUnits->indexFromItem(ModelLineByUnits->item(0,0)),true);
    }
}

void MainWindow::FilterUnit()
{
    if(ModelUnits->rowCount()<=0) return;

    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)
    {
        if(ui->CbUnitGaoceng->currentText()!="高层")
        {
            if(ModelUnits->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbUnitGaoceng->currentText())
                ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),true);
            else
                ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),false);
        }
        else
            ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),false);

        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ui->CbUnitPos->currentText()!="位置")
            {
                if(ModelUnits->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbUnitPos->currentText())
                    ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),true);
                else
                    ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),false);
            }
            else
                ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),false);

            for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                //元件
                if(ui->EdUnitTagSearch->text()!="")
                {
                    if(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdUnitTagSearch->text()))
                        ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),false);
                    else
                        ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),true);
                }
                else
                {
                    ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),false);
                }


                for(int m=0;m<ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)//功能子块
                {
                    if(ui->CbUnitPage->currentText()!="页")
                    {
                        //查看当前功能子块是否在所筛选页面上
                        QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::UserRole).toString();
                        QuerySymbol.exec(SqlStr);
                        if(QuerySymbol.next())
                        {
                            if(QuerySymbol.value("Page_ID").toString()!="")
                            {
                                if(GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt())==ui->CbUnitPage->currentText())
                                    ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                                else
                                    ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                            }
                            else
                                ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                        }
                        else
                            ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                    }
                    else
                    {
                        ui->treeViewUnits->setRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                    }
                }
            }
        }
    }

    //隐藏没有功能子块的节点
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//元件
            {
                bool AllHide=true;
                for(int m=0;m<ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewUnits->isRowHidden(m,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelUnits->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewUnits->setRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelUnits->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewUnits->isRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelUnits->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewUnits->setRowHidden(j,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelUnits->item(0,0)->rowCount();i++)//高层
    {
        bool AllHide=true;
        for(int k=0;k<ModelUnits->item(0,0)->child(i,0)->rowCount();k++)//位置
        {
            if(!ui->treeViewUnits->isRowHidden(k,ModelUnits->indexFromItem(ModelUnits->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelUnits->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewUnits->setRowHidden(i,ModelUnits->indexFromItem(ModelUnits->item(0,0)),true);
    }
}

void MainWindow::FilterPage()
{
    if(ModelPages->rowCount()<=0) return;

    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")
        {
            if(ui->CbPageGaocengFilter->currentText()!="高层")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbPageGaocengFilter->currentText())
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                else
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
            }
            else
                ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
        }
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="位置")
        {
            if(ui->CbPagePosFilter->currentText()!="位置")
            {
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()!=ui->CbPagePosFilter->currentText())
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                else
                {
                    if((ui->CbPageGaocengFilter->currentText()=="高层")||(ui->CbPageGaocengFilter->currentText()==""))
                        ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                    else
                        ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                }
            }
            else
            {
                if((ui->CbPageGaocengFilter->currentText()=="高层")||(ui->CbPageGaocengFilter->currentText()==""))
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                else
                    ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
        }
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="图纸")
        {
            bool TypeNotSame=false;
            if(ModelPages->item(0,0)->data(Qt::WhatsThisRole).toString()=="列表")
            {
                if(ModelPages->item(0,0)->data(Qt::DisplayRole).toString()==ui->CbPageTypeFilter->currentText()) TypeNotSame=false;
                else TypeNotSame=true;
            }
            else
            {
                if(ui->CbPageTypeFilter->currentText()=="原理图") TypeNotSame=false;
                else TypeNotSame=true;
            }
            if(ui->CbPageTypeFilter->currentText()!="类型"&&TypeNotSame)
            {
                ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
            else//需要显示出来
            {
                bool ShouldHide=false;
                if((ui->CbPageGaocengFilter->currentText()!="高层")&&(ui->CbPageGaocengFilter->currentText()!="")) ShouldHide=true;
                if((ui->CbPagePosFilter->currentText()!="位置")&&(ui->CbPagePosFilter->currentText()!="")) ShouldHide=true;
                if(!ShouldHide)
                {
                    if(ui->EdPageFilter->text()!="")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                            ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
                    }
                    else
                        ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                }
                else ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
        }
        else if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="列表")
        {
            if((ui->CbPageTypeFilter->currentText()!="类型")&&(ui->CbPageTypeFilter->currentText()!=ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()))
                ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            else
            {
                bool ShouldHide=false;
                if((ui->CbPageGaocengFilter->currentText()!="高层")&&(ui->CbPageGaocengFilter->currentText()!="")) ShouldHide=true;
                if((ui->CbPagePosFilter->currentText()!="位置")&&(ui->CbPagePosFilter->currentText()!="")) ShouldHide=true;
                if(!ShouldHide) ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),false);
                else ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
            }
        }

        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="位置")
            {
                if(ui->CbPagePosFilter->currentText()!="位置")
                {
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()!=ui->CbPagePosFilter->currentText())
                        ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    else
                        ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                }
                else
                    ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
            }
            else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="图纸")
            {
                //必须满足高层为空或者位置为空，非空的已经经过筛选
                bool TypeNotSame=false;
                if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="列表")
                {
                    if(ModelPages->item(0,0)->child(i,0)->data(Qt::DisplayRole).toString()==ui->CbPageTypeFilter->currentText()) TypeNotSame=false;
                    else TypeNotSame=true;
                }
                else
                {
                    if(ui->CbPageTypeFilter->currentText()=="原理图") TypeNotSame=false;
                    else TypeNotSame=true;
                }

                if((ui->CbPageTypeFilter->currentText()!="类型")&&TypeNotSame)
                    ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                else
                {
                    bool DwgNameOk=true;
                    if(ui->EdPageFilter->text()!="")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                            DwgNameOk=true;
                        else
                            DwgNameOk=false;
                    }
                    else DwgNameOk=true;

                    if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")//高层不为空，位置为空
                    {
                        if((ui->CbPagePosFilter->currentText()=="位置")||(ui->CbPagePosFilter->currentText()==""))
                        {
                            if(DwgNameOk)
                                ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                            else
                                ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                        }
                        else
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    }
                    else
                    {
                        if(DwgNameOk)
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    }
                }
            }
            else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表")
            {
                if((ui->CbPageTypeFilter->currentText()!="类型")&&(ui->CbPageTypeFilter->currentText()!=ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()))
                    ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                else
                {
                    if(ModelPages->item(0,0)->child(i,0)->data(Qt::WhatsThisRole).toString()=="高层")//高层不为空，位置为空
                    {
                        if((ui->CbPagePosFilter->currentText()=="位置")||(ui->CbPagePosFilter->currentText()==""))
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
                    }
                    else
                        ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),false);
                }
            }

            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()=="图纸")
                {
                    bool TypeNotSame=false;
                    if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::WhatsThisRole).toString()=="列表")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->data(Qt::DisplayRole).toString()==ui->CbPageTypeFilter->currentText()) TypeNotSame=false;
                        else TypeNotSame=true;
                    }
                    else
                    {
                        if(ui->CbPageTypeFilter->currentText()=="原理图") TypeNotSame=false;
                        else TypeNotSame=true;
                    }

                    bool DwgNameOk=true;
                    if(ui->EdPageFilter->text()!="")
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                            DwgNameOk=true;
                        else
                            DwgNameOk=false;
                    }
                    else DwgNameOk=true;

                    if((ui->CbPageTypeFilter->currentText()!="类型")&&TypeNotSame)
                        ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
                    else
                    {
                        if(DwgNameOk)
                            ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),false);
                        else
                            ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
                    }
                }
                else if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::WhatsThisRole).toString()=="列表")
                {
                    if((ui->CbPageTypeFilter->currentText()!="类型")&&(ui->CbPageTypeFilter->currentText()!=ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->data(Qt::DisplayRole).toString()))
                        ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
                    else
                        ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),false);
                    for(int m=0;m<ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                    {
                        if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::WhatsThisRole).toString()=="图纸")
                        {
                            bool DwgNameOk=true;
                            if(ui->EdPageFilter->text()!="")
                            {
                                if(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->child(m,0)->data(Qt::DisplayRole).toString().contains(ui->EdPageFilter->text()))
                                    DwgNameOk=true;
                                else
                                    DwgNameOk=false;
                            }
                            else DwgNameOk=true;

                            if(DwgNameOk) ui->treeViewPages->setRowHidden(m,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)),false);
                            else ui->treeViewPages->setRowHidden(m,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)),true);
                        }
                    }
                }
            }
        }
    }

    //隐藏没有图纸的节点
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)//高层
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)//位置
        {
            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)//列表
            {
                bool AllHide=true;
                for(int m=0;m<ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount();m++)
                {
                    if(!ui->treeViewPages->isRowHidden(m,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0))))
                        AllHide=false;
                }
                if(AllHide&&(ModelPages->item(0,0)->child(i,0)->child(j,0)->child(k,0)->rowCount()>0)) ui->treeViewPages->setRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0)),true);
            }
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        for(int j=0;j<ModelPages->item(0,0)->child(i,0)->rowCount();j++)
        {
            //ModelPages->item(0,0)->child(i,0)->child(j,0)下面所有的子节点均隐藏
            bool AllHide=true;
            for(int k=0;k<ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount();k++)
            {
                if(!ui->treeViewPages->isRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)->child(j,0))))
                    AllHide=false;
            }
            if(AllHide&&(ModelPages->item(0,0)->child(i,0)->child(j,0)->rowCount()>0)) ui->treeViewPages->setRowHidden(j,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0)),true);
        }
    }
    for(int i=0;i<ModelPages->item(0,0)->rowCount();i++)
    {
        bool AllHide=true;
        for(int k=0;k<ModelPages->item(0,0)->child(i,0)->rowCount();k++)
        {
            if(!ui->treeViewPages->isRowHidden(k,ModelPages->indexFromItem(ModelPages->item(0,0)->child(i,0))))
                AllHide=false;
        }
        if(AllHide&&(ModelPages->item(0,0)->child(i,0)->rowCount()>0)) ui->treeViewPages->setRowHidden(i,ModelPages->indexFromItem(ModelPages->item(0,0)),true);
    }
}

void MainWindow::AddIndexToIndex(QStandardItem *FatherItem,QSqlQuery query,bool AddProjectStructure_ID,QString Type)
{
    QStandardItem *SubItem;
    if(Type=="列表") SubItem=new QStandardItem(QIcon("C:/TBD/data/列表图标.png"),query.value("Structure_INT").toString());
    else if(Type=="位置") SubItem=new QStandardItem(QIcon("C:/TBD/data/位置图标.png"),query.value("Structure_INT").toString());
    else if(Type=="高层") SubItem=new QStandardItem(QIcon("C:/TBD/data/高层图标.png"),query.value("Structure_INT").toString());
    else if(Type=="项目") SubItem=new QStandardItem(QIcon("C:/TBD/data/项目图标.png"),query.value("Structure_INT").toString());

    if(AddProjectStructure_ID)  SubItem->setData(QVariant(query.value("ProjectStructure_ID").toInt()),Qt::UserRole);
    SubItem->setData(QVariant(Type),Qt::WhatsThisRole);
    FatherItem->appendRow(SubItem);
}
void MainWindow::AddDwgFileToIndex(QStandardItem *item,QSqlQuery query,QList<int> listPagesExpend)
{
    QStandardItem *SubFatherItem=new QStandardItem(QIcon("C:/TBD/data/dwg图标.png"),query.value("PageName").toString()+" "+query.value("Page_Desc").toString());
    //图纸名称：PageName.dwg
    SubFatherItem->setData(QVariant("图纸"),Qt::WhatsThisRole);
    SubFatherItem->setData(QVariant(query.value("Page_ID").toInt()),Qt::UserRole);
    //添加到报表前面去
    int InsertRowIndex=-1;
    for(int k=0;k<item->rowCount();k++)
    {
        if(item->child(k,0)->data(Qt::WhatsThisRole).toString()=="列表")
        {
            InsertRowIndex=k;
            break;
        }
    }
    if(InsertRowIndex>=0) item->insertRow(InsertRowIndex,SubFatherItem);
    else item->appendRow(SubFatherItem);

    for(int i=0;i<listPagesExpend.count();i++)
    {
        if(listPagesExpend.at(i)==query.value("ProjectStructure_ID").toInt())
        {
            ui->treeViewPages->expand(item->index());
            break;
        }
    }
    if(SelectPage_ID==query.value("Page_ID").toInt()) ui->treeViewPages->setCurrentIndex(SubFatherItem->index());
}
void MainWindow::on_BtnNavigatorShow_clicked()
{
    ui->widgetNavigator->setVisible(true);
}

void MainWindow::on_BtnCloseNavigator_clicked()
{
    ui->widgetNavigator->setVisible(false);
}

void MainWindow::on_BtnNewProject_clicked()
{
    //建立后缀名为.swPro的文本文件
    DialogNewProject *dlgNewProject=new DialogNewProject(this);
    dlgNewProject->move(QApplication::desktop()->screenGeometry().width()/2-dlgNewProject->width()/2,QApplication::desktop()->screenGeometry().height()/2-dlgNewProject->height()/2);
    dlgNewProject->setModal(true);
    dlgNewProject->show();
    dlgNewProject->exec();
    if(dlgNewProject->Canceled) return;
    //dlgNewProject->ProjectPath,ProjectName
    CurProjectName=dlgNewProject->ProjectName;
    CurProjectPath=dlgNewProject->ProjectPath;
    LoadProject();
    delete dlgNewProject;
}

QStringList MainWindow::selectSystemUnitStripLineInfo()
{
    QStringList ListUnitStrip;
    QStringList ListUnitStripLineInfo;
    //得到器件清单 和 连接列表
    QSqlQuery QueryJXB(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(SqlStr);
    while(QueryJXB.next())
    {
        for(int index=0;index<2;index++)
        {
            QString Symb_ID;
            if(index==0) Symb_ID=QueryJXB.value("Symb1_ID").toString();
            else if(index==1) Symb_ID=QueryJXB.value("Symb2_ID").toString();
            if(Symb_ID=="") continue;
            if(Symb_ID.contains(":C")||Symb_ID.contains(":G")||Symb_ID.contains(":1")||Symb_ID.contains(":2")||Symb_ID.contains(":3")) continue;
            QString Symb_Category;
            if(index==0) Symb_Category=QueryJXB.value("Symb1_Category").toString();
            else if(index==1) Symb_Category=QueryJXB.value("Symb2_Category").toString();
            //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表

            //找到Symb_ID对应的器件
            QString DT;
            int UnitStripID=GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
            bool UnitStripExisted=false;
            for(int i=0;i<ListUnitStrip.count();i++)//这里可能存在器件与端子排ID的重复
            {
                QString id=ListUnitStrip.at(i).split(",").at(0);
                QString category=ListUnitStrip.at(i).split(",").at(1);
                if((id==QString::number(UnitStripID))&&(category==Symb_Category)) UnitStripExisted=true;
            }
            if(!UnitStripExisted)
            {
                ListUnitStrip.append(QString::number(UnitStripID)+","+Symb_Category);
                QString UnitStripLineInfo;
                QSqlQuery QuerySearch(T_ProjectDatabase);
                if(Symb_Category=="0")
                {
                    SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(UnitStripID);
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        UnitStripLineInfo=QuerySearch.value("Name").toString()+" "+DT;
                        SqlStr="SELECT * FROM EquipmentDiagnosePara WHERE Equipment_ID= '"+QString::number(UnitStripID)+"'";
                        QuerySearch.exec(SqlStr);
                        QString StrParameter;
                        while(QuerySearch.next())
                        {
                            if(StrParameter!="") StrParameter+=",";
                            StrParameter+=QuerySearch.value("Name").toString()+"="+QuerySearch.value("CurValue").toString()+QuerySearch.value("Unit").toString();
                        }
                        UnitStripLineInfo+="("+StrParameter+")";
                    }
                }
                else if(Symb_Category=="1")
                {
                    UnitStripLineInfo="端子排 "+DT;
                    SqlStr="SELECT * FROM TerminalStripDiagnosePara WHERE TerminalStrip_ID= '"+QString::number(UnitStripID)+"'";
                    QuerySearch.exec(SqlStr);
                    QString StrParameter;
                    while(QuerySearch.next())
                    {
                        if(StrParameter!="") StrParameter+=",";
                        StrParameter+=QuerySearch.value("Name").toString()+"="+QuerySearch.value("CurValue").toString()+QuerySearch.value("Unit").toString();
                    }
                    UnitStripLineInfo+="("+StrParameter+")";
                }
                ListUnitStripLineInfo.append(UnitStripLineInfo);
            }
        }//for(int index=0;index<2;index++)
        ListUnitStrip.append(QueryJXB.value("JXB_ID").toString()+",2");//添加导线
        ListUnitStripLineInfo.append("导线 "+QueryJXB.value("ConnectionNumber").toString()+"(MaxCurrent=20A,Resistance=0)");
    }
    return ListUnitStripLineInfo;
}

QStringList MainWindow::selectSystemConnections()
{
    QStringList ListConnections;
    QSqlQuery QueryJXB(T_ProjectDatabase);//设置数据库选择模型
    QSqlQuery QuerySearch(T_ProjectDatabase);
    QString SqlStr = "SELECT * FROM JXB ORDER BY ConnectionNumber";
    QueryJXB.exec(SqlStr);
    while(QueryJXB.next())
    {
        for(int index=0;index<2;index++)
        {
            QString ConnectionStr="";
            QString Symb_ID;
            if(index==0) Symb_ID=QueryJXB.value("Symb1_ID").toString();
            else if(index==1) Symb_ID=QueryJXB.value("Symb2_ID").toString();
            if(Symb_ID.contains(":C")||Symb_ID.contains(":G")||Symb_ID.contains(":1")||Symb_ID.contains(":2")||Symb_ID.contains(":3")) continue;
            QString Symb_Category;
            if(index==0) Symb_Category=QueryJXB.value("Symb1_Category").toString();
            else if(index==1) Symb_Category=QueryJXB.value("Symb2_Category").toString();
            //根据导线两端的SymbolTerm类型来定义导线，线号相同（不为空）但是两端连接对象不同则只有第一根导线是有效的；线号相同（不为空）且两端连接对象相同的为同一根导线，反之则添加到列表

            //找到Symb_ID对应的器件
            QString DT;
            GetUnitStripIDByTermID(Symb_Category.toInt(),Symb_ID.toInt(),DT);
            QString TermStr;
            if(Symb_Category=="0")
            {
                QString StrSql="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+Symb_ID;
                QuerySearch.exec(StrSql);
                if(QuerySearch.next()) TermStr=QuerySearch.value("ConnNum").toString();
            }
            else if(Symb_Category=="1")
            {
                QString StrSql="SELECT * FROM TerminalTerm WHERE TerminalTerm_ID= "+Symb_ID;
                QuerySearch.exec(StrSql);
                if(QuerySearch.next()) TermStr=QuerySearch.value("ConnNum").toString();
            }
            ConnectionStr=QueryJXB.value("ConnectionNumber").toString()+"."+QString::number(index+1)+","+DT+"."+TermStr;
            //查找有没有其他连接到同一个节点的端口
            SqlStr="SELECT * FROM JXB WHERE Symb1_ID = '"+Symb_ID+"' AND Symb1_Category = '"+Symb_Category+"' AND JXB_ID <> "+QueryJXB.value("JXB_ID").toString();
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                ConnectionStr+=","+QuerySearch.value("ConnectionNumber").toString()+".1";
            }
            SqlStr="SELECT * FROM JXB WHERE Symb2_ID = '"+Symb_ID+"' AND Symb2_Category = '"+Symb_Category+"' AND JXB_ID <> "+QueryJXB.value("JXB_ID").toString();
            QuerySearch.exec(SqlStr);
            while(QuerySearch.next())
            {
                ConnectionStr+=","+QuerySearch.value("ConnectionNumber").toString()+".2";
            }
            ListConnections.append("connect"+QString::number(ConnectionStr.split(",").count())+"e("+ConnectionStr+")");
        }//for(int index=0;index<2;index++)
    }
    return ListConnections;
}

void MainWindow::LoadProjectSystemDescription()
{
    ui->textEditSystemDiscription->clear();
    QStringList ListEquipmentsInfo=selectSystemUnitStripLineInfo();
    QStringList ListSystemConnections=selectSystemConnections();
    QString SystemDescription="DEF BEGIN\n";
    for(QString EquipmentsInfo:ListEquipmentsInfo) SystemDescription+=EquipmentsInfo+"\n";
    SystemDescription+="DEF END\n\n";
    for(QString SystemConnections:ListSystemConnections) SystemDescription+=SystemConnections+"\n";
    ui->textEditSystemDiscription->setText(SystemDescription);
}

void MainWindow::LoadModel()
{
    //移除功能管理Tab中的QTreeWidget
    QLayout *layout = ui->widget_func->layout();
    if (layout != nullptr) {
        QLayoutItem *item;
        while ((item = layout->takeAt(0)) != nullptr) {
            delete item->widget(); // 删除控件
            delete item;           // 删除布局项
        }
    }
    qDebug()<<CurProjectPath+"/Model.db";
    //连接数据库
    database = new SQliteDatabase(CurProjectPath+"/Model.db");
    if(!database->connect()){
        QMessageBox::information(nullptr, "Tips", "数据库连接失败！",QMessageBox::Yes);
    }

    systemEntity = new SystemEntity(database);
    systemEntity->setMainWindow(this);
    systemEntity->setCurrentModel(&currentModel);

    //=========================open model============
    currentModelName = "QBT";
    currentModel = database->selectModelByName(currentModelName);
    QString systemDescription = currentModel.getSystemDescription();
    ui->textEditSystemDiscription->setText(systemDescription);
    //qDebug()<<"systemDescription="<<systemDescription;
    functionDescription = currentModel.getFunctionDiscription();
    //qDebug()<<"functionDescription="<<functionDescription;
    systemEntity->updateObsVarsMap(systemEntity->prepareModel(systemDescription));
    //QString savedObsCode= currentModel.getTestDiscription();
    //ui->textEditTestDiscription->setText(savedObsCode);

    pDlgSelectFunctionDialog = new SelectFunctionDialog(systemEntity, systemDescription,functionDescription,this);
    pDlgSelectFunctionDialog->hide();
    UpdateFuncTree();
}

void MainWindow::UpdateFuncTree()
{
    QLayout *layout = ui->widget_func->layout();
    if (layout == nullptr) {
        layout = new QVBoxLayout;
        ui->widget_func->setLayout(layout);
    }
    layout->addWidget(pDlgSelectFunctionDialog->GetTreeWidget());
}

void MainWindow::initializeMxModules()
{
    static bool initialized = false;
    if (initialized) {
        return;
    }

    QAxObject object("{4FF8F5E1-8D85-45CC-B58E-BE1CF4A5C3EC}");
    object.dynamicCall("InitMxDrawOcx(const QString&,const QString&,const QString&,const QString&,const QString&)", "",
                       QString::fromLocal8Bit("中国船舶重工集团公司第704研究所"),
                       QString::fromLocal8Bit("电液系统"), "0510-83078024",
                       "010ADE5E0DA2A305784A00001F22E8014E9A9FCF5957272AA51F7EA69E974AA5D173220AB9865714670FA0B2ED850000060A177AE70EC20BB6BE0000242ABDE1218C1C87E1F84B3CFA9D1A5FB7E0B8C0A8702F347CEEE340D84B85CBAB639EADA5C7717953A30000262A75D1DCB40BDD2D638097969BF91CB4EFC96862F3DB91F7D7292C97D270AD6EBC8EC0EFB13063444100001A22E98792BAD32A4231E8E85A70D588C1B7B782224023E9D27CD844ED721BC9F99D00000D120712AC0F10BFC62E976BEF515415B18F0000080AB8CA9D8405892A7C0000");

    const QStringList iniOptions = {
        "EnableUndo=Y",
        "DisplayPrecision=500",
        "EnablePropertyWindow=N",
        "NOSHOWBOORDER=Y",
        "DrawGridLine=Y",
        "EnableClipboard=Y",
        "EnableSingleSelection=Y",
        "EnableDeleteKey=N",
        "IsHighQualityTTf=Y",
        "ObjectModifyEvent=Y",
        "DynamicHighlight=Y",
        "ISDISABLEEDITTEXT=Y"
    };
    object.dynamicCall("IniSet(const QString&)", iniOptions.join(","));

    if (!GlobalBackAxWidget) {
        GlobalBackAxWidget = new QAxWidget("{74A777F8-7A8F-4E7C-AF47-7074828086E2}");
    }

    if (!pApp) {
        auto *mxApp = new MxDrawApplication();
        pApp = reinterpret_cast<IMxDrawApplication *>(mxApp);
    }

    if (!dlgLoadSymbol) {
        dlgLoadSymbol = new DialogLoadSymbol(this);
    }
    if (!dlgDialogSymbols) {
        dlgDialogSymbols = new DialogSymbols(this);
    }

    const QString dwgPath = "C:/TBD/SPS/SPS_CDP.dwg";
    const QString jpgPath = "C:/TBD/data/TempImage/SPS_CDP.jpg";
    const QFileInfo dwgInfo(dwgPath);
    const QFileInfo jpgInfo(jpgPath);
    if (dwgInfo.exists()) {
        if (!jpgInfo.exists() || dwgInfo.lastModified() > jpgInfo.lastModified()) {
            pApp->dynamicCall("DwgToJpg(QString,QString,int,int)", dwgPath, jpgPath, 150, 85);
        }
    } else {
        qWarning() << "DWG file not found:" << dwgPath;
    }

    initialized = true;
}

void MainWindow::initAfterShow()
{
    initializeMxModules();
    LoadLastOpenedProject();
}

void MainWindow::LoadProject()
{
    qDebug()<<"CurProjectName"<<CurProjectName;
    if(T_ProjectDatabase.isOpen()) T_ProjectDatabase.close();
    T_ProjectDatabase = QSqlDatabase::addDatabase("QSQLITE",CurProjectName);
    QFile  File(CurProjectPath+"/"+CurProjectName+".db");
    if(!File.exists()){
        QMessageBox::warning(nullptr, "错误", "数据库文件不存在",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return ;
    }
    else
        T_ProjectDatabase.setDatabaseName(CurProjectPath+"/"+CurProjectName+".db");
    if (!T_ProjectDatabase.open()){
        QMessageBox::warning(nullptr, "错误", "打开数据库失败",
                             QMessageBox::Ok,QMessageBox::NoButton);
        return ;
    }
    ui->LbProjectName->setText("项目导航器（"+CurProjectName+"）");
    LoadProjectPages();
    LoadProjectUnits();
    LoadProjectTerminals();
    LoadProjectLines();

    //更新历史工程记录
    QString StrDir=LocalDataBasePath;
    QFile HisProFilePath(StrDir+"/历史工程记录.dat");
    if(!HisProFilePath.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    QStringList ListHisFile;
    ListHisFile.append(CurProjectPath+"/"+CurProjectName+".swPro");
    QTextStream txtInput(&HisProFilePath);
    while(!txtInput.atEnd())
    {
        QString CurLineText=txtInput.readLine().toUtf8();
        if(CurLineText==(CurProjectPath+"/"+CurProjectName+".swPro")) continue;
        if(CurLineText=="") continue;
        ListHisFile.append(CurLineText);
    }
    HisProFilePath.close();
    qDebug()<<"ListHisFile="<<ListHisFile;
    if(!HisProFilePath.open(QIODevice::WriteOnly | QIODevice::Text| QIODevice::Truncate)) return;
    for(int i=0;i<ListHisFile.count();i++)
    {
        if(i==10) break;
        HisProFilePath.write((ListHisFile.at(i)+"\n").toLocal8Bit().data());//写入文件，支持QByteArray和 char * 类型数据写入
    }
    HisProFilePath.close();

    LoadModel();
}

void MainWindow::LoadLastOpenedProject()
{
    QString StrDir=LocalDataBasePath;
    QFile HisProFilePath(StrDir+"/历史工程记录.dat");
    if(!HisProFilePath.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    QTextStream txtInput(&HisProFilePath);
    CurProjectName=txtInput.readLine().toUtf8();//读取第一行
    HisProFilePath.close();

    //CurProjectName:C:/TBD/MyProjects/测试系统5/测试系统5.swPro
    QFile LastProFilePath(CurProjectName);
    if(!LastProFilePath.exists()) return;
    int Index=CurProjectName.lastIndexOf("/");
    CurProjectPath=CurProjectName.mid(0,Index);
    CurProjectName=CurProjectName.mid(Index+1,CurProjectName.lastIndexOf(".swPro")-Index-1);
    LoadProject();
}

void MainWindow::on_BtnOpenProject_clicked()
{
    /*
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
       ((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",((formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget())->dwgFileName);
    }*/
    if(ui->mdiArea->subWindowList().count()>0)
    {
        QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"是否关闭所有打开的图纸?",
                                                                QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

        if(result==QMessageBox::Yes)
        {
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                ui->mdiArea->subWindowList().at(i)->close();
            }
        }
    }
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("打开文件"));
    fileDialog.setDirectory(LocalProjectDefaultPath);
    fileDialog.setNameFilter(tr("swPro(*.swPro)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    QFile SelectedFilePath(fileNames.at(0));
    if(!SelectedFilePath.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    QTextStream txtInput(&SelectedFilePath);
    CurProjectName=txtInput.readLine().toUtf8();
    SelectedFilePath.close();

    int Index=fileNames.at(0).lastIndexOf("/");
    CurProjectPath=fileNames.at(0).mid(0,Index);

    LoadProject();
}
void MainWindow::CloseMdiWnd(int Mode)
{
    qDebug()<<"CloseMdiWnd,Mode="<<Mode;
    formaxwidget *dlg=(formaxwidget *)sender();

    dlg->mdisubwindow->close();
    //如果Mode=1,删除dwg文件，打开符号库
    if(Mode==1)
    {
        qDebug()<<"Mode=1,删除dwg文件，打开符号库,SymbolName="<<dlg->SymbolName;
        QString DwgFileName="C:/TBD/SYMB2LIB/"+dlg->SymbolName;
        qDebug()<<"delete file";
        QFile file(DwgFileName);
        if(file.exists()) file.remove();
    }
    //if(Mode==0||Mode==1) on_BtnSymbolBaseManage_clicked();
}

void MainWindow::OpenDwgPageByPageID(int PageID)
{
    QString dwgfilename=GetPageNameByPageID(PageID);
    QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
    QFile dwgfile(dwgfilepath);
    if(!dwgfile.exists()) return;
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
            return;
        }
    }
    //创建新的mdi
    formaxwidget *formMxdraw=new formaxwidget(this,dwgfilepath,PageID);
    formMxdraw->setWindowTitle(dwgfilename);
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
    connect(formMxdraw,SIGNAL(UpdateProjectUnits()),this,SLOT(LoadProjectUnits()));
    connect(formMxdraw,SIGNAL(UpdateProjectTerminals()),this,SLOT(LoadProjectTerminals()));
    connect(formMxdraw,SIGNAL(SigalShowSpurAttr(int)),this,SLOT(ShowSpurAttr(int)));
    connect(formMxdraw,SIGNAL(SigalShowTerminalAttr(int,int)),this,SLOT(ShowTerminalAttr(int,int)));
    connect(formMxdraw,SIGNAL(UpdateCounterLink(int,QString)),this,SLOT(updateCounterLink(int,QString)));
    connect(formMxdraw,SIGNAL(SignalUpdateSpur(int)),this,SLOT(UpdateSpurBySymbol_ID(int)));
    connect(formMxdraw,SIGNAL(SignalUpdateTerminal(int)),this,SLOT(UpdateTerminalByTerminal_ID(int)));
}

//单击鼠标左键预览图纸，双击鼠标左键打开图纸
void MainWindow::on_treeViewPages_doubleClicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    qDebug()<<index.data(Qt::WhatsThisRole).toString();
    qDebug()<<"UserRole="<<index.data(Qt::UserRole).toInt();
    if(index.data(Qt::WhatsThisRole).toString()!="图纸") return;
    int Page_ID=index.data(Qt::UserRole).toInt();
    OpenDwgPageByPageID(Page_ID);
}

void MainWindow::on_treeViewPages_clicked(const QModelIndex &index)
{
    if(!ui->widgetPreView->isVisible()) return;
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="图纸") return;
    int Page_ID=index.data(Qt::UserRole).toInt();
    QString dwgfilename=GetPageNameByPageID(Page_ID);

    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
    qDebug()<<"path="<<path;
    QFileInfo file(path);
    if(!file.exists()) return;
    ui->axWidgetPreview->dynamicCall("OpenDwgFile(QString)",path);
    ui->axWidgetPreview->dynamicCall("ZoomAll()");
}

void MainWindow::on_Btn_SymbolLoad_clicked()
{
    dlgLoadSymbol->Canceled=true;
    dlgLoadSymbol->move(this->width()-dlgLoadSymbol->width()-20,50);
    dlgLoadSymbol->show();
    //QApplication::processEvents();
    dlgLoadSymbol->exec();
    if(dlgLoadSymbol->Canceled) return;
    if(dlgLoadSymbol->RetCode!=3)  return;//载入当前符号

    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->SymbolLoad(dlgLoadSymbol->BlockFileName,dlgLoadSymbol->SymbolID);
    }
}

void MainWindow::UpdateSymbolLib(QString CurSelectSymb2Class_ID)
{
    dlgDialogSymbols->LoadModelFromDB(CurSelectSymb2Class_ID);
}

void MainWindow::SlotSetCurMdiActive()
{
    formaxwidget *formMxdraw=(formaxwidget *)sender();
    ui->mdiArea->setActiveSubWindow(formMxdraw->mdisubwindow);
}

void MainWindow::SlotNewSymbol(int Mode)//0:取消 1：选择有效
{
    //创建新的mdi
    if(Mode==0)
    {
        on_BtnSymbolBaseManage_clicked();
        return;
    }
    qDebug()<<"SlotNewSymbol";
    formaxwidget *formMxdraw=new formaxwidget(this);
    formMxdraw->setWindowTitle(dlgDialogSymbols->Symb2_Name);
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
    connect(formMxdraw,SIGNAL(SignalUpdateSymbolLib(QString)),this,SLOT(UpdateSymbolLib(QString)));
    connect(formMxdraw,SIGNAL(SignalSetCurMdiActive()),this,SLOT(SlotSetCurMdiActive()));
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    qDebug()<<"SymbolName="<<dlgDialogSymbols->Symb2_Name+".dwg";
    formMxdraw->SymbolName=dlgDialogSymbols->Symb2_Name+".dwg";
    formMxdraw->DataBaseSymbolID="";
    formMxdraw->SymbolType=dlgDialogSymbols->SymbolType;
    formMxdraw->FunctionDefineClass_ID=dlgDialogSymbols->FunctionDefineClass_ID;
    formMxdraw->EditSymbol();

    qDebug()<<"end SlotNewSymbol";
}

void MainWindow::on_BtnSymbolBaseManage_clicked()
{
    //connect(&dlgDialogSymbols,SIGNAL(SignalUpdateLib()),this,SLOT(UpdateSymbolLib()));
    dlgDialogSymbols->setModal(true);
    dlgDialogSymbols->Canceled=true;
    dlgDialogSymbols->RetCode=2;
    dlgDialogSymbols->show();
    dlgDialogSymbols->exec();
    if(dlgDialogSymbols->Canceled) return;
    qDebug()<<"dlgDialogSymbols->RetCode="<<dlgDialogSymbols->RetCode;
    if(dlgDialogSymbols->RetCode==1) //修改符号
    {
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this);
        formMxdraw->setWindowTitle(dlgDialogSymbols->BlockFileName);
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        formMxdraw->SymbolName=dlgDialogSymbols->BlockFileName;
        formMxdraw->DataBaseSymbolID=dlgDialogSymbols->SymbolID;
        qDebug()<<"DataBaseSymbolID="<<formMxdraw->DataBaseSymbolID;
        formMxdraw->SymbolType=dlgDialogSymbols->SymbolType;
        formMxdraw->EditSymbol();
    }
    else if(dlgDialogSymbols->RetCode==3) //增加库文件
    {
        //在现有的窗口中选择图形
        if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
        {
            formaxwidget *formMdi;
            formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
            if(formMdi!=nullptr)
            {
                connect(formMdi,SIGNAL(SignalSelectDone(int)),this,SLOT(SlotNewSymbol(int)));
                formMdi->NewSymbolDwgName=dlgDialogSymbols->Symb2_Name+".dwg";
                formMdi->SelectEntitys();
            }
        }
        else//没有打开的主窗口，直接新建
        {
            qDebug()<<"没有打开的主窗口，直接新建";
            QString SourceFileName="C:/TBD/data/SymbolTemplate.dwg";
            QString DestinationFileName="C:/TBD/SYMB2LIB/"+dlgDialogSymbols->Symb2_Name+".dwg";
            QFile::copy(SourceFileName,DestinationFileName);
            SlotNewSymbol(1);
        }
    }
}

void MainWindow::on_BtnLocalDB_clicked()
{

    dlgUnitManage->show();
    //dlgUnitManage->showMaximized();
    QApplication::processEvents();
}

void MainWindow::on_BtnShowHidePreViewWidget_clicked()
{
    if(ui->tabWidget_Navigator->currentIndex()==3) return;
    if(ShowPreViewWidget)
    {
        ShowPreViewWidget=false;
        ui->BtnShowHidePreViewWidget->setText("图形预览▲");
        ui->widgetPreView->setVisible(false);
    }
    else
    {
        ShowPreViewWidget=true;
        ui->BtnShowHidePreViewWidget->setText("图形预览▼");
        ui->widgetPreView->setVisible(true);
    }
}

void MainWindow::on_Btn_GeneratePageList_clicked()
{
    dlgGenerate.setWindowTitle("生成图纸目录");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(0);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        qDebug()<<"GetPageProjectStructure_IDByGaocengAndPos,"<<GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"图纸目录");
        StrSql= "SELECT * FROM Page WHERE PageType = '图纸目录' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"图纸目录")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '图纸目录'  AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"图纸目录")+"'";
        QueryPage.exec(StrSql);
    }
    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(0,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Page WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建图纸目录清单dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"TZML");
                SetCurLayer(GlobalBackAxWidget,"TZML");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"目录",10,0,0,2);//目录
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",59,264,"页名",7,0,1,2);//页名
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,271,99,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",174,264,"页描述",7,0,1,2);//页描述
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",249,271,249,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",282,264,"页类型",7,0,1,2);//页类型
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",315,271,315,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",349,264,"备注",7,0,1,2);//备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线6
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","图纸目录");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,GetPageNameByPageID(QueryPage.value("Page_ID").toInt()),3.5,0,0,2);//页名
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,Lasty,99,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",101,Lasty-3.5,QueryPage.value("Page_Desc").toString(),3.5,0,0,2);//页描述
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",249,Lasty,249,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",251,Lasty-3.5,QueryPage.value("PageType").toString(),3.5,0,0,2);//页类型
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",315,Lasty,315,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",317,Lasty-3.5,"",3.5,0,0,2);//备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    LoadProjectPages();
}

void MainWindow::on_Btn_GenerateUnitList_clicked()//元件列表
{
    dlgGenerate.setWindowTitle("生成元件列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(1);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '元件列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"元件列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '元件列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"元件列表")+"'";
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Equipment WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryEquipment.exec(StrSql);
        while(QueryEquipment.next())
        {
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"MXB");
                SetCurLayer(GlobalBackAxWidget,"MXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"元件列表",10,0,0,2);//元件列表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",44,264,"项目代号",7,0,1,2);//项目代号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",69,271,69,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",104,264,"型号",7,0,1,2);//型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",139,271,139,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",169,264,"名称",7,0,1,2);//名称
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,271,199,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",205,264,"数量",7,0,1,2);//数量
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",211,257,211,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",236,264,"厂家",7,0,1,2);//厂家
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",261,257,261,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",296,264,"部件编号",7,0,1,2);//部件编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,257,331,271);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",357,264,"元件备注",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线9
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","元件列表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
            QString UnitTag=QueryEquipment.value("DT").toString();
            QString UnitType=QueryEquipment.value("Type").toString();
            QString UnitName=QueryEquipment.value("Name").toString();
            //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
            QString UnitNameStr=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+UnitTag;

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,UnitNameStr,3.5,0,0,2);//项目代号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",69,Lasty,69,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",71,Lasty-3.5,UnitType,3.5,0,0,2);//型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",139,Lasty,139,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",141,Lasty-3.5,UnitName,3.5,0,0,2);//名称
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,Lasty,199,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",201,Lasty-3.5,"1",3.5,0,0,2);//数量
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",211,Lasty,211,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",213,Lasty-3.5,QueryEquipment.value("Factory").toString(),3.5,0,0,2);//厂家
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",261,Lasty,261,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",263,Lasty-3.5,QueryEquipment.value("PartCode").toString(),3.5,0,0,2);//部件编号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,Lasty,331,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",333,Lasty-3.5,QueryEquipment.value("Remark").toString(),3.5,0,0,2);//元件备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线9
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

//Mode=0:Page  Mode=1:连线、元件、端子等
QStringList MainWindow::GetAllIDFromProjectStructure(int Mode,QString StrGaoceng,QString StrPos,bool AllGaoceng,bool AllPos)
{
    //这里要区分是不是所有的高层或位置
    QStringList ListProjectStructure_ID;
    QString StrSql;
    QSqlQuery QueryPos = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    if(Mode==0)
    {
        StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '6'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            if(AllGaoceng)
            {
                if(AllPos)
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                }
                else
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE Structure_INT = '"+StrPos+"' AND ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                }
            }
            else
            {
                if(AllPos)
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next())
                    {
                        QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                        QuerySearchGaoceng.exec(StrSql);
                        if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                    }
                }
                else
                {
                    StrSql="SELECT * FROM ProjectStructure WHERE Structure_INT = '"+StrPos+"' AND ProjectStructure_ID = "+QueryPage.value("Parent_ID").toString();
                    QueryPos.exec(StrSql);
                    while(QueryPos.next())
                    {
                        QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                        QuerySearchGaoceng.exec(StrSql);
                        if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPage.value("ProjectStructure_ID").toString());
                    }
                }
            }
        }
    }
    else
    {
        if(AllGaoceng)
        {
            if(AllPos)
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5'";
                QueryPos.exec(StrSql);
                while(QueryPos.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
            }
            else
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+StrPos+"'";
                QueryPos.exec(StrSql);
                while(QueryPos.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
            }
        }
        else
        {
            if(AllPos)
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5'";
                QueryPos.exec(StrSql);
                while(QueryPos.next())
                {
                    QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                    QuerySearchGaoceng.exec(StrSql);
                    if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
                }
            }
            else
            {
                StrSql="SELECT * FROM ProjectStructure WHERE Structure_ID = '5' AND Structure_INT = '"+StrPos+"'";
                QueryPos.exec(StrSql);
                while(QueryPos.next())
                {
                    QSqlQuery QuerySearchGaoceng = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql="SELECT * FROM ProjectStructure WHERE ProjectStructure_ID = "+QueryPos.value("Parent_ID").toString()+" AND Structure_INT = '"+StrGaoceng+"'";
                    QuerySearchGaoceng.exec(StrSql);
                    if(QuerySearchGaoceng.next()) ListProjectStructure_ID.append(QueryPos.value("ProjectStructure_ID").toString());
                }
            }
        }
    }
    return ListProjectStructure_ID;
}
void MainWindow::on_Btn_GenerateConnectList_clicked()//连接列表
{
    dlgGenerate.setWindowTitle("生成连接列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(4);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '连接列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"连接列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '连接列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"连接列表")+"'";
        QueryPage.exec(StrSql);
    }
    qDebug()<<"SELECT * FROM JXB";
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM JXB WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        qDebug()<<"StrSql="<<StrSql;
        QueryJXB.exec(StrSql);
        while(QueryJXB.next())
        {
            if(CurRecordIndex>CurPageNum*32)
            {
                if(CurPageNum>0) GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                qDebug()<<"PageName="<<PageName;
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                CreateLayer(GlobalBackAxWidget,"JXB");
                SetCurLayer(GlobalBackAxWidget,"JXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"连接列表",10,0,0,2);//元件列表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",16,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",26,271,26,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",41,264,"连接代号",7,0,1,2);//项目代号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",56,271,56,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",81,264,"源",7,0,1,2);//型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",106,271,106,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",131,264,"目标",7,0,1,2);//名称
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",156,271,156,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",177,264,"型号",7,0,1,2);//数量
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",198,257,198,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",214,264,"颜色",7,0,1,2);//厂家
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",230,257,230,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",246,264,"截面积/直径",7,0,1,2);//部件编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",262,257,262,271);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",287,264,"源区图号",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",312,257,312,271);//竖线9
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",337,264,"目标区图号",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",362,257,362,271);//竖线10
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",372,264,"备注",7,0,1,2);//元件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",382,257,382,271);//竖线11
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","连接列表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString StrDT=QueryJXB.value("ConnectionNumber").toString();

            QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
            QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
            if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) continue;
            if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) continue;
            QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
            QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
            QString Symb1Str,Symb2Str;
            if(Symb1_Category=="0")//元件
                Symb1Str=GetUnitTermStrByTermID(Symb1_ID);
            else if(Symb1_Category=="1")//端子排
                Symb1Str=GetTerminalTermStrByTermID(Symb1_ID);
            if(Symb2_Category=="0")//元件
                Symb2Str=GetUnitTermStrByTermID(Symb2_ID);
            else if(Symb2_Category=="1")//端子排
                Symb2Str=GetTerminalTermStrByTermID(Symb2_ID);

            //根据源符号类型和目标符号类型进行检索确定区号
            QString SourcePageArea;
            QString DestinationPageArea;
            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            if(Symb1_Category=="0")//符号
            {
                StrSql = QString("SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+Symb1_ID);//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                SourcePageArea=QuerySearch.value("PageArea").toString();
            }
            else if(Symb1_Category=="1")//端子
            {
                StrSql = QString("SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb1_ID);//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Terminal WHERE Terminal_ID = "+QuerySearch.value("Terminal_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                SourcePageArea=QuerySearch.value("PageArea").toString();
            }
            if(Symb2_Category=="0")//符号
            {
                StrSql = QString("SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+Symb2_ID);//目标符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                DestinationPageArea=QuerySearch.value("PageArea").toString();
            }
            else if(Symb2_Category=="1")//端子
            {
                StrSql = QString("SELECT * FROM TerminalInstance WHERE TerminalInstanceID = "+Symb2_ID);//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                StrSql = QString("SELECT * FROM Terminal WHERE Terminal_ID = "+QuerySearch.value("Terminal_ID").toString());//源符号
                QuerySearch.exec(StrSql);
                if(!QuerySearch.next()) continue;
                DestinationPageArea=QuerySearch.value("PageArea").toString();
            }
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",26,Lasty,26,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",28,Lasty-3.5,StrDT,3.5,0,0,2);//连接代号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",56,Lasty,56,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",58,Lasty-3.5,Symb1Str,3.5,0,0,2);//源
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",106,Lasty,106,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",108,Lasty-3.5,Symb2Str,3.5,0,0,2);//目标
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",156,Lasty,156,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",158,Lasty-3.5,QueryJXB.value("Wires_Type").toString(),3.5,0,0,2);//型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",198,Lasty,198,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",200,Lasty-3.5,QueryJXB.value("Wires_Color").toString(),3.5,0,0,2);//颜色
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",230,Lasty,230,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",232,Lasty-3.5,QueryJXB.value("Wires_Diameter").toString(),3.5,0,0,2);//截面积/直径
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",262,Lasty,262,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",264,Lasty-3.5,SourcePageArea,3.5,0,0,2);//源区图号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",312,Lasty,312,Lasty-7);//竖线9
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",314,Lasty-3.5,DestinationPageArea,3.5,0,0,2);//目标区图号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",362,Lasty,362,Lasty-7);//竖线10
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",364,Lasty-3.5,"",3.5,0,0,2);//备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",382,Lasty,382,Lasty-7);//竖线11
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }

    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_Btn_GenerateTerminalList_clicked()//端子列表
{
    dlgGenerate.setWindowTitle("生成端子列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(3);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '端子列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"端子列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '端子列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"端子列表")+"'";
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryTerminalStrip = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM TerminalStrip WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryTerminalStrip.exec(StrSql);
        while(QueryTerminalStrip.next())
        {
            CurRecordIndex=1;
            QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            StrSql="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryTerminalStrip.value("TerminalStrip_ID").toString()+"'";
            QueryTerminal.exec(StrSql);
            int InitCurPageNum=CurPageNum;
            QStringList AddedTerminalID;
            AddedTerminalID.clear();
            while(QueryTerminal.next())
            {
                if(CurRecordIndex>(CurPageNum-InitCurPageNum)*32)
                {
                    PageName="";
                    if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                    if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                    if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                    PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                    //创建dwg文件
                    QFileInfo fileinfo(PageName);
                    if(fileinfo.exists())
                    {
                        QFile file(PageName);
                        file.remove();
                    }
                    QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                    QFile::copy(SourceFileName,PageName);
                    bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                    qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                    CreateLayer(GlobalBackAxWidget,"MXB");
                    SetCurLayer(GlobalBackAxWidget,"MXB");
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"端子列表",10,0,0,2);//端子列表
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,253,383,253);//横线2
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,253);//竖线1
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,271,383,253);//竖线2
                    QString TerminalStripTag=GetProjectStructureStrByProjectStructureID(QueryTerminalStrip.value("ProjectStructure_ID").toInt())+"-"+QueryTerminalStrip.value("DT").toString();
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",195,262,TerminalStripTag,7,0,1,2);//端子排项目代号
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,239,383,239);//横线3
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,253,7,239);//竖线1
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",22,246,"功能文本",7,0,1,2);//功能文本
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",37,253,37,239);//竖线2
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",60,246,"电缆编号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",83,253,83,239);//竖线3
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",108,246,"目标代号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",133,253,133,239);//竖线4
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",143,246,"连接点",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",153,253,153,239);//竖线5
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",164,246,"端子",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175,253,175,239);//竖线6
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",191,246,"短连接",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",207,253,207,239);//竖线7
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",232,246,"目标代号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",257,253,257,239);//竖线8
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",267,246,"连接点",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",277,253,277,239);//竖线9
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",300,246,"电缆编号",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",323,253,323,239);//竖线10
                    GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",353,246,"页/列",7,0,1,2);
                    GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,253,383,239);//竖线11
                    //GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                    int Page_ID=1;
                    QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                    QueryNewPage.exec(StrSql);
                    if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                    StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                      "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                    QueryNewPage.prepare(StrSql);
                    QueryNewPage.bindValue(":Page_ID",Page_ID);
                    QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                    QueryNewPage.bindValue(":Page_Desc","端子列表:"+TerminalStripTag);
                    QueryNewPage.bindValue(":PageType","端子列表");
                    QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                    QueryNewPage.bindValue(":Scale","1:1");
                    QueryNewPage.bindValue(":Border","A3:420x297");
                    QueryNewPage.bindValue(":Title","A3-zju.dwg");
                    QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                    QueryNewPage.exec();
                    Lasty=239;
                    CurPageNum++;
                }
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",22,Lasty-3.5,QueryTerminal.value("FunctionText").toString(),3.5,0,0,2);//功能文本

                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",37,Lasty,37,Lasty-7);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",83,Lasty,83,Lasty-7);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",133,Lasty,133,Lasty-7);//竖线4

                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",153,Lasty,153,Lasty-7);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",155,Lasty-3.5,QueryTerminal.value("Designation").toString(),3.5,0,0,2);//端子
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175,Lasty,175,Lasty-7);//竖线6
                //查看当前端子是否与上面的端子存在短接，存在则绘制短接线
                if(QueryTerminal.value("ShortJumper").toString()!="")
                {
                    qlonglong lID=GlobalBackAxWidget->dynamicCall("DrawCircle(double,double,double)",175+8*QueryTerminal.value("ShortJumper").toString().count(),Lasty-3.5,0.75).toLongLong();
                    IMxDrawCircle *LineCircle= (IMxDrawCircle*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
                    LineCircle->dynamicCall("setColorIndex(int)",McColor::mcYellow);
                    QSqlQuery QueryShortJump = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    double Internal=0;
                    for(int i=AddedTerminalID.count()-1;i>=0;i--)
                    {
                        Internal+=7;
                        StrSql = "SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryTerminalStrip.value("TerminalStrip_ID").toString()+"' AND ShortJumper = '"+QueryTerminal.value("ShortJumper").toString()+"' AND Terminal_ID = "+AddedTerminalID.at(i);
                        QueryShortJump.exec(StrSql);
                        if(QueryShortJump.next())
                        {
                            //绘制短接线
                            qlonglong lID=GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175+8*QueryTerminal.value("ShortJumper").toString().count(),Lasty-3.5+0.75,175+8*QueryTerminal.value("ShortJumper").toString().count(),Lasty-3.5+Internal-0.75).toLongLong();
                            IMxDrawLine *LineEnty= (IMxDrawLine*)GlobalBackAxWidget->querySubObject("ObjectIdToObject(const qlonglong)",lID);
                            LineEnty->dynamicCall("setColorIndex(int)",McColor::mcYellow);
                            break;
                        }
                    }
                }
                AddedTerminalID.append(QueryTerminal.value("Terminal_ID").toString());
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",185,Lasty-3.5,QueryTerminal.value("FunctionText").toString(),3.5,0,0,2);//短连接
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",207,Lasty,207,Lasty-7);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",257,Lasty,257,Lasty-7);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",277,Lasty,277,Lasty-7);//竖线9
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",323,Lasty,323,Lasty-7);//竖线10
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线11
                //从JXB中获取端子两端的连线，注意可能存在多根线接到同一个端子的情形
                int CurTerminalTermIndex=0;
                QSqlQuery QueryTerminalTerm = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql="SELECT * FROM TerminalTerm WHERE Terminal_ID = '"+QueryTerminal.value("Terminal_ID").toString()+"'";
                //qDebug()<<"StrSql="<<StrSql;
                QueryTerminalTerm.exec(StrSql);
                while(QueryTerminalTerm.next())
                {
                    // qDebug()<<"TerminalTerm_ID="<<QueryTerminalTerm.value("TerminalTerm_ID").toString();
                    CurTerminalTermIndex++;
                    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                    StrSql="SELECT * FROM JXB WHERE (Symb1_ID = '"+QueryTerminalTerm.value("TerminalTerm_ID").toString()+"' AND Symb1_Category = '1') OR (Symb2_ID = '"+QueryTerminalTerm.value("TerminalTerm_ID").toString()+"' AND Symb2_Category = '1')";
                    QueryJXB.exec(StrSql);
                    QString ConnectionNumber,SymbDT,ConnectTermNum;
                    while(QueryJXB.next())
                    {
                        if(QueryJXB.value("Symb1_ID").toString()==QueryTerminalTerm.value("TerminalTerm_ID").toString())
                        {
                            ConnectionNumber=QueryJXB.value("ConnectionNumber").toString();
                            QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
                            if(QueryJXB.value("Symb2_Category").toString()=="0")//元件
                            {
                                QString UnitTermStr=GetUnitTermStrByTermID(Symb2_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                            else if(QueryJXB.value("Symb2_Category").toString()=="1")//端子
                            {
                                QString UnitTermStr=GetTerminalTermStrByTermID(Symb2_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                        }
                        else if(QueryJXB.value("Symb2_ID").toString()==QueryTerminalTerm.value("TerminalTerm_ID").toString())
                        {
                            ConnectionNumber=QueryJXB.value("ConnectionNumber").toString();
                            QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
                            if(QueryJXB.value("Symb1_Category").toString()=="0")//元件
                            {
                                QString UnitTermStr=GetUnitTermStrByTermID(Symb1_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                            else if(QueryJXB.value("Symb1_Category").toString()=="1")//端子
                            {
                                QString UnitTermStr=GetTerminalTermStrByTermID(Symb1_ID);
                                SymbDT=UnitTermStr.mid(0,UnitTermStr.lastIndexOf(":"));
                                ConnectTermNum=UnitTermStr.mid(UnitTermStr.lastIndexOf(":")+1,UnitTermStr.count()-UnitTermStr.lastIndexOf(":")-1);
                            }
                        }
                        if((CurTerminalTermIndex>2)&&((CurTerminalTermIndex%2)==1))
                        {
                            Lasty=Lasty-7;
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",37,Lasty,37,Lasty-7);//竖线2
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",83,Lasty,83,Lasty-7);//竖线3
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",133,Lasty,133,Lasty-7);//竖线4
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",153,Lasty,153,Lasty-7);//竖线5
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",155,Lasty-3.5,QueryTerminal.value("Designation").toString(),3.5,0,0,2);//端子
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",175,Lasty,175,Lasty-7);//竖线6
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",207,Lasty,207,Lasty-7);//竖线7
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",257,Lasty,257,Lasty-7);//竖线8
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",277,Lasty,277,Lasty-7);//竖线9
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",323,Lasty,323,Lasty-7);//竖线10
                            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线11
                        }
                        if((CurTerminalTermIndex%2)==1)//表格左侧
                        {
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",39,Lasty-3.5,ConnectionNumber,3.5,0,0,2);//电缆编号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",85,Lasty-3.5,SymbDT,3.5,0,0,2);//目标代号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",135,Lasty-3.5,ConnectTermNum,3.5,0,0,2);//连接点
                        }
                        else
                        {
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",279,Lasty-3.5,ConnectionNumber,3.5,0,0,2);//电缆编号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",209,Lasty-3.5,SymbDT,3.5,0,0,2);//目标代号
                            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",259,Lasty-3.5,ConnectTermNum,3.5,0,0,2);//连接点
                        }
                    }
                }
                Lasty=Lasty-7;
                CurRecordIndex++;
            }//while(QueryTerminal.next())
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            //CurPageNum++;
        }//while(QueryTerminalStrip.next())
    }//for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_BtnLineConnect_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->LineConnect();
    }
}

void MainWindow::on_Btn_MultiLine_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->MultiLine();
    }
}

//重新生成连接
void MainWindow::on_Btn_RemakeConnectLine_clicked()
{
    //删除原连接Line表和ConnectLine表
    QSqlQuery QueryLine=QSqlQuery(T_ProjectDatabase);
    QString SqlStr =  "DELETE FROM Line ";
    QueryLine.exec(SqlStr);

    QSqlQuery QueryConnectLine=QSqlQuery(T_ProjectDatabase);
    SqlStr =  "DELETE FROM ConnectLine ";
    QueryConnectLine.exec(SqlStr);

    //先生成Line表，Line表中的Symb1_Category和Symb2_Category的0代表元件，1代表端子，2代表节点，3代表链接点
    //检索工程下所有dwg图纸的连线
    QSqlQuery QueryPage=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Page ORDER BY Page_ID ASC";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        QFile dwgfile(dwgfilepath);
        qDebug()<<"dwgfilepath="<<dwgfilepath;
        if(!dwgfile.exists()) continue;
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath);
        IMxDrawSelectionSet *ssLINE= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filterLINE=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
        filterLINE->AddStringEx("LINE",5020);
        filterLINE->AddStringEx("CONNECT", 8);
        ssLINE->dynamicCall("AllSelect(QVariant)",filterLINE->asVariant());
        int Cnt=ssLINE->dynamicCall("Count()").toInt();
        qDebug()<<"Cnt="<<Cnt;
        for(int LineIndex=0;LineIndex<Cnt;LineIndex++)
        {
            QString Symb1_ID="",Symb2_ID="",Symb1_Category="",Symb2_Category="",ConnectionNumber="",ConnectionNumber_Handle="",Wires_Handle="";
            QString Wires_Type="",Wires_Color="",Wires_Diameter="",Wires_Category="";

            IMxDrawLine *mLine= (IMxDrawLine *)ssLINE->querySubObject("Item(int)",LineIndex);
            if(EntyIsErased(GlobalBackAxWidget,(IMxDrawEntity *)mLine)) continue;//去除erase的实体
            //查看line的端点与Symb2TermInfo表、TerminalTerm表、Connector表、Link表是否有连接关系
            IMxDrawPoint *StartPt = (IMxDrawPoint *)mLine->querySubObject("StartPoint()");
            IMxDrawPoint *EndPt = (IMxDrawPoint *)mLine->querySubObject("EndPoint()");
            if((fabs(StartPt->x()-EndPt->x())<0.1)&&(fabs(StartPt->y()-EndPt->y())<0.1)) continue;
            for(int j=0;j<2;j++)
            {
                IMxDrawPoint *PtCross;
                if(j==0) PtCross=StartPt;
                else PtCross=EndPt;
                qDebug()<<"PtCrossx="<<PtCross->x()<<" PtCrossy="<<PtCross->y();
                QString Coordinate=QString::number(PtCross->x(),'f',0)+".000000,"+QString::number(PtCross->y(),'f',0)+".000000,0.000000";
                //Range&0x01:Symbol  Range&0x02:Terminal  Range&0x04:Connector  Range&0x08:Link
                QString StrTermConnect;
                if(GetLineDir(mLine)=="垂直")
                {
                    if((StartPt->y()>EndPt->y())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                    else if((StartPt->y()>EndPt->y())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                    else if((StartPt->y()<EndPt->y())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                    else if((StartPt->y()<EndPt->y())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                }
                else//水平
                {
                    if((StartPt->x()>EndPt->x())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                    else if((StartPt->x()>EndPt->x())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                    else if((StartPt->x()<EndPt->x())&&(j==0)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"右");
                    else if((StartPt->x()<EndPt->x())&&(j==1)) StrTermConnect=FindTermConnectInDB(QueryPage.value("Page_ID").toString(),Coordinate,15,"左");
                }

                qDebug()<<"Coordinate="<<Coordinate<<",StrTermConnect="<<StrTermConnect;
                if(StrTermConnect!="")
                {
                    QStringList ListStrTermConnect=StrTermConnect.split(",");
                    if(j==0)
                    {
                        Symb1_ID=ListStrTermConnect.at(0);//QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString();
                        Symb1_Category=ListStrTermConnect.at(1);
                    }
                    else
                    {
                        Symb2_ID=ListStrTermConnect.at(0);
                        Symb2_Category=ListStrTermConnect.at(1);
                    }
                }
            }//for(int j=0;j<2;j++)
            //insert记录到Line表
            QString StrSql =  "INSERT INTO Line (Line_ID,Page_ID,ConnectionNumber,ConnectionNumber_Handle,Wires_Handle,Symb1_ID,Symb2_ID,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category,Symb1_Category,Symb2_Category)"
                              "VALUES (:Line_ID,:Page_ID,:ConnectionNumber,:ConnectionNumber_Handle,:Wires_Handle,:Symb1_ID,:Symb2_ID,:Wires_Type,:Wires_Color,:Wires_Diameter,:Wires_Category,:Symb1_Category,:Symb2_Category)";
            QueryLine.prepare(StrSql);
            QueryLine.bindValue(":Line_ID",GetMaxIDOfDB(T_ProjectDatabase,"Line","Line_ID"));
            QueryLine.bindValue(":Page_ID",QueryPage.value("Page_ID").toString());

            //查看该连线是否有Wire定义（是否相交）
            //bool HasWireDefine=false;
            int Wires_ID=CheckLineCDPCross(mLine,QueryPage.value("Page_ID").toString());
            qDebug()<<"Wires_ID="<<Wires_ID;
            if(Wires_ID>0)
            {
                QSqlQuery QueryWires = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM Wires WHERE Wires_ID = "+QString::number(Wires_ID);
                QueryWires.exec(SqlStr);
                if(QueryWires.next())
                {
                    ConnectionNumber=QueryWires.value("ConnectionNumber").toString();
                    ConnectionNumber_Handle=QueryWires.value("Handle").toString();
                    Wires_Type=QueryWires.value("Type").toString();
                    Wires_Color=QueryWires.value("Color").toString();
                    Wires_Diameter=QueryWires.value("Diameters").toString();
                }
            }

            /*
           //创建选择集对象
           IMxDrawSelectionSet *ssWire= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
           //创建过滤对象
           //MxDrawResbuf* filterWire =new MxDrawResbuf();
           IMxDrawResbuf *filterWire=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
           filterWire->AddStringEx("INSERT",5020);
           filterWire->AddStringEx("LY_CDP",8);
           //McSelect::mcSelectionSetCrossing
           ssWire->dynamicCall("Select(int,QAxObject*,QAxObject*,QAxObject*)",McSelect::mcSelectionSetFence, ((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->asVariant(), ((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->asVariant(),filterWire->asVariant());
           qDebug()<<" LY_CDP ss.Count()="<<ssWire->Count();
           for (int WireIndex = 0; WireIndex < ssWire->Count(); WireIndex++)
           {
               IMxDrawEntity* entCross = (IMxDrawEntity *)ssWire->querySubObject("Item(int)",WireIndex);
               if(EntyIsErased(GlobalBackAxWidget,entCross)) return;
               if(entCross->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
               {
                   IMxDrawBlockReference *BlkWire=(IMxDrawBlockReference *)entCross;
                   if(BlkWire->dynamicCall("GetBlockName()").toString()=="SPS_CDP")
                   {
                       QSqlQuery QueryWires(T_ProjectDatabase);
                       QString StrSql="SELECT * FROM Wires WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"' AND Handle = '"+BlkWire->dynamicCall("handle()").toString()+"'";
                       QueryWires.exec(StrSql);
                       if(QueryWires.next())
                       {
                           HasWireDefine=true;
                           ConnectionNumber=QueryWires.value("ConnectionNumber").toString();
                           ConnectionNumber_Handle=QueryWires.value("Handle").toString();
                           Wires_Type=QueryWires.value("Type").toString();
                           Wires_Color=QueryWires.value("Color").toString();
                           Wires_Diameter=QueryWires.value("Diameters").toString();
                           break;
                       }
                   }
               }
           }
           */
            QueryLine.bindValue(":ConnectionNumber",ConnectionNumber);
            QueryLine.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
            QueryLine.bindValue(":Wires_Handle",mLine->dynamicCall("handle()").toString());
            QueryLine.bindValue(":Symb1_ID",Symb1_ID);
            QueryLine.bindValue(":Symb2_ID",Symb2_ID);
            QueryLine.bindValue(":Wires_Type",Wires_Type);
            QueryLine.bindValue(":Wires_Color",Wires_Color);
            QueryLine.bindValue(":Wires_Diameter",Wires_Diameter);
            QueryLine.bindValue(":Wires_Category",Wires_Category);
            QueryLine.bindValue(":Symb1_Category",Symb1_Category);
            QueryLine.bindValue(":Symb2_Category",Symb2_Category);
            QueryLine.exec();
        }//for(int i=0;i<Cnt;i++)
    }//while(QueryPage.next())

    //根据Line表生成ConnectLine表，将节点的"1"、"2"、"3"、"G"替换成"C"另一端的连接对象
    SqlStr =  "SELECT * FROM Line";
    QueryLine.exec(SqlStr);
    while(QueryLine.next())
    {
        QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category,Page_ID;;
        QString ConnectionNumber,ConnectionNumber_Handle,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category;
        Symb1_ID=QueryLine.value("Symb1_ID").toString();
        Symb2_ID=QueryLine.value("Symb2_ID").toString();
        Symb1_Category=QueryLine.value("Symb1_Category").toString();
        Symb2_Category=QueryLine.value("Symb2_Category").toString();
        ConnectionNumber=QueryLine.value("ConnectionNumber").toString();
        ConnectionNumber_Handle=QueryLine.value("ConnectionNumber_Handle").toString();
        Wires_Type=QueryLine.value("Wires_Type").toString();
        Wires_Color=QueryLine.value("Wires_Color").toString();
        Wires_Diameter=QueryLine.value("Wires_Diameter").toString();
        Wires_Category=QueryLine.value("Wires_Category").toString();
        Page_ID=QueryLine.value("Page_ID").toString();
        while(1)
        {
            bool LoopEnd=true;
            bool ShouldBreak=true;
            //如果是链接点则进行配对连接
            if((Symb1_Category=="3")||(Symb2_Category=="3"))
            {
                ShouldBreak=false;
                if(Symb1_Category=="3")
                {
                    QString Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Link WHERE Link_ID = "+Symb_ID+" AND CounterLink_ID <> ''";
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        QString CounterLink_ID=QuerySearch.value("CounterLink_ID").toString();

                        SqlStr = "SELECT * FROM Line WHERE Symb1_ID LIKE '"+CounterLink_ID+":%' AND Symb1_Category = '3'";
                        QuerySearch.exec(SqlStr);
                        bool FindedInLine=false;
                        if(QuerySearch.next())
                        {
                            FindedInLine=true;
                            Symb1_ID=QuerySearch.value("Symb2_ID").toString();
                            Symb1_Category=QuerySearch.value("Symb2_Category").toString();
                            if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                            {
                                ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                Wires_Type=QuerySearch.value("Wires_Type").toString();
                                Wires_Color=QuerySearch.value("Wires_Color").toString();
                                Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                Wires_Category=QuerySearch.value("Wires_Category").toString();
                                Page_ID=QueryLine.value("Page_ID").toString();
                            }
                            LoopEnd=false;
                        }

                        if(!FindedInLine)
                        {
                            SqlStr = "SELECT * FROM Line WHERE Symb2_ID LIKE '"+CounterLink_ID+":%' AND Symb2_Category = '3'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                FindedInLine=true;
                                Symb1_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb1_Category=QuerySearch.value("Symb1_Category").toString();
                                if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                                {
                                    ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                    ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                    Wires_Type=QuerySearch.value("Wires_Type").toString();
                                    Wires_Color=QuerySearch.value("Wires_Color").toString();
                                    Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                    Wires_Category=QuerySearch.value("Wires_Category").toString();
                                    Page_ID=QueryLine.value("Page_ID").toString();
                                }
                                LoopEnd=false;
                            }
                        }//end of if(!FindedInLine)


                        if(!FindedInLine)
                        {
                            //可能CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索
                            SqlStr = "SELECT * FROM Link WHERE Link_ID = "+CounterLink_ID;
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Coordinate_1=QuerySearch.value("Coordinate_1").toString();
                                QString LinkPage_ID=QuerySearch.value("Page_ID").toString();
                                SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                    QuerySearch.exec(SqlStr);
                                    if(QuerySearch.next())
                                    {
                                        if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                        {
                                            Symb1_ID=Symb2TermInfo_ID;
                                            Symb1_Category="0";
                                        }
                                    }
                                }
                                SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                    {
                                        Symb1_ID=TerminalInstanceID;
                                        Symb1_Category="1";
                                    }
                                }
                            }
                        }//end of if(!FindedInLine)
                    }
                }//end of if(Symb1_Category=="3")
                else if(Symb2_Category=="3")
                {
                    QString Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Link WHERE Link_ID = "+Symb_ID+" AND CounterLink_ID <> ''";
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        QString CounterLink_ID=QuerySearch.value("CounterLink_ID").toString();
                        SqlStr = "SELECT * FROM Line WHERE Symb1_ID LIKE '"+CounterLink_ID+":%' AND Symb1_Category = '3'";
                        QuerySearch.exec(SqlStr);
                        bool FindedInLine=false;
                        if(QuerySearch.next())
                        {
                            FindedInLine=true;
                            Symb2_ID=QuerySearch.value("Symb2_ID").toString();
                            Symb2_Category=QuerySearch.value("Symb2_Category").toString();
                            if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                            {
                                ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                Wires_Type=QuerySearch.value("Wires_Type").toString();
                                Wires_Color=QuerySearch.value("Wires_Color").toString();
                                Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                Wires_Category=QuerySearch.value("Wires_Category").toString();
                                Page_ID=QueryLine.value("Page_ID").toString();
                            }
                            LoopEnd=false;
                        }

                        if(!FindedInLine)
                        {
                            SqlStr = "SELECT * FROM Line WHERE Symb2_ID LIKE '"+CounterLink_ID+":%' AND Symb2_Category = '3'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                FindedInLine=true;
                                Symb2_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb2_Category=QuerySearch.value("Symb1_Category").toString();
                                if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                                {
                                    ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                    ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                    Wires_Type=QuerySearch.value("Wires_Type").toString();
                                    Wires_Color=QuerySearch.value("Wires_Color").toString();
                                    Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                    Wires_Category=QuerySearch.value("Wires_Category").toString();
                                    Page_ID=QueryLine.value("Page_ID").toString();
                                }
                                LoopEnd=false;
                            }
                        }//end of if(!FindedInLine)

                        if(!FindedInLine)
                        {
                            //可能CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索
                            SqlStr = "SELECT * FROM Link WHERE Link_ID = "+CounterLink_ID;
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Coordinate_1=QuerySearch.value("Coordinate_1").toString();
                                QString LinkPage_ID=QuerySearch.value("Page_ID").toString();
                                SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                    QuerySearch.exec(SqlStr);
                                    if(QuerySearch.next())
                                    {
                                        if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                        {
                                            Symb2_ID=Symb2TermInfo_ID;
                                            Symb2_Category="0";
                                        }
                                    }
                                }
                                SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+Coordinate_1+"'";
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                    //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                    if(QuerySearch.value("Page_ID").toString()==LinkPage_ID)
                                    {
                                        Symb2_ID=TerminalInstanceID;
                                        Symb2_Category="1";
                                    }
                                }
                            }
                        }//end of if(!FindedInLine)
                    }
                }//end of else if(Symb1_Category=="3")
            }//end of if((Symb1_Category=="3")||(Symb2_Category=="3"))
            else if((Symb1_Category=="2")||(Symb2_Category=="2"))
            {
                if(((Symb1_ID.contains(":1"))||(Symb1_ID.contains(":2"))||(Symb1_ID.contains(":3"))||(Symb1_ID.contains(":G")))&&(Symb1_Category=="2")) ShouldBreak=false;
                if(((Symb2_ID.contains(":1"))||(Symb2_ID.contains(":2"))||(Symb2_ID.contains(":3"))||(Symb2_ID.contains(":G")))&&(Symb2_Category=="2")) ShouldBreak=false;
                if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C")) ShouldBreak=false;
                if(ShouldBreak) break;
                int CaseID=0;
                if(((Symb1_ID.contains(":1"))||(Symb1_ID.contains(":2"))||(Symb1_ID.contains(":3"))||(Symb1_ID.contains(":G")))&&(Symb1_Category=="2")) CaseID=1;
                if(((Symb2_ID.contains(":1"))||(Symb2_ID.contains(":2"))||(Symb2_ID.contains(":3"))||(Symb2_ID.contains(":G")))&&(Symb2_Category=="2")) CaseID=2;
                if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C")) CaseID=3;
                if((CaseID==1)||(CaseID==2))
                {
                    QString Symb_ID;
                    if(CaseID==1) Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
                    else if(CaseID==2) Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Line WHERE (Symb1_ID = '"+Symb_ID+":C' AND Symb1_Category = '2') OR (Symb2_ID = '"+Symb_ID+":C' AND Symb2_Category = '2')";
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        if(QuerySearch.value("Symb1_ID").toString()==(Symb_ID+":C"))
                        {
                            if(CaseID==1)
                            {
                                Symb1_ID=QuerySearch.value("Symb2_ID").toString();
                                Symb1_Category=QuerySearch.value("Symb2_Category").toString();
                            }
                            else
                            {
                                Symb2_ID=QuerySearch.value("Symb2_ID").toString();
                                Symb2_Category=QuerySearch.value("Symb2_Category").toString();
                            }
                        }
                        else
                        {
                            if(CaseID==1)
                            {
                                Symb1_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb1_Category=QuerySearch.value("Symb1_Category").toString();
                            }
                            else
                            {
                                Symb2_ID=QuerySearch.value("Symb1_ID").toString();
                                Symb2_Category=QuerySearch.value("Symb1_Category").toString();
                            }
                        }
                        if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                        {
                            ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                            ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                            Wires_Type=QuerySearch.value("Wires_Type").toString();
                            Wires_Color=QuerySearch.value("Wires_Color").toString();
                            Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                            Wires_Category=QuerySearch.value("Wires_Category").toString();
                            Page_ID=QueryLine.value("Page_ID").toString();
                        }
                        LoopEnd=false;
                    }
                    else
                    {
                        qDebug()<<"CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索";
                        //可能CONNECT C直接和器件端口或端子连接，在Symb2TermInfo表和TerminalInstance表中进行检索
                        SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
                        qDebug()<<"SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
                        QuerySearch.exec(SqlStr);
                        if(QuerySearch.next())
                        {
                            QString C_Coordinate=QuerySearch.value("C_Coordinate").toString();
                            QString ConnectorPage_ID=QuerySearch.value("Page_ID").toString();
                            QString Connector_Name=QuerySearch.value("Connector_Name").toString();
                            SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+C_Coordinate+"'";
                            qDebug()<<"SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+C_Coordinate+"'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                qDebug()<<"SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    qDebug()<<"QuerySearch.value(Page_ID).toString()="<<QuerySearch.value("Page_ID").toString()<<",ConnectorPage_ID="<<ConnectorPage_ID;
                                    if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                    {
                                        if(CaseID==1)
                                        {
                                            Symb1_ID=Symb2TermInfo_ID;
                                            Symb1_Category="0";
                                        }
                                        else
                                        {
                                            Symb2_ID=Symb2TermInfo_ID;
                                            Symb2_Category="0";
                                        }
                                        LoopEnd=false;
                                    }
                                }
                            }
                            SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+C_Coordinate+"'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                {
                                    if(CaseID==1)
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb1_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb1_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb1_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb1_ID=TerminalInstanceID+".1";
                                        //Symb1_ID=TerminalInstanceID;
                                        Symb1_Category="1";
                                    }
                                    else
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb2_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb2_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb2_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb2_ID=TerminalInstanceID+".1";
                                        //Symb2_ID=TerminalInstanceID;
                                        Symb2_Category="1";
                                    }
                                    LoopEnd=false;
                                }
                            }
                        }
                    }//end of else
                }//end of if(CaseID>0)

                if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))//如果是CO节点则找CO节点1端口连线另一侧的连接
                {
                    QString Symb_ID;
                    if(Symb1_ID.contains(":C")) Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
                    else Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
                    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
                    SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
                    QuerySearch.exec(SqlStr);
                    if(QuerySearch.next())
                    {
                        if(QuerySearch.value("Connector_Name").toString().contains("SYMB2_M_PWF_CO"))
                        {
                            QString Coordinate_1=QuerySearch.value("Coordinate_1").toString();
                            QString ConnectorPage_ID=QuerySearch.value("Page_ID").toString();
                            QString Connector_Name=QuerySearch.value("Connector_Name").toString();
                            qDebug()<<"Coordinate_1="<<Coordinate_1<<",ConnectorPage_ID="<<ConnectorPage_ID<<",Connector_Name="<<Connector_Name;
                            SqlStr = "SELECT * FROM Line WHERE (Symb1_ID = '"+Symb_ID+":1' AND Symb1_Category = '2') OR (Symb2_ID = '"+Symb_ID+":1' AND Symb2_Category = '2')";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                if(QuerySearch.value("Symb1_ID").toString()==(Symb_ID+":1"))
                                {
                                    if(Symb1_ID.contains(":C"))
                                    {
                                        Symb1_ID=QuerySearch.value("Symb2_ID").toString();
                                        Symb1_Category=QuerySearch.value("Symb2_Category").toString();
                                    }
                                    else
                                    {
                                        Symb2_ID=QuerySearch.value("Symb2_ID").toString();
                                        Symb2_Category=QuerySearch.value("Symb2_Category").toString();
                                    }
                                }
                                else
                                {
                                    if(Symb1_ID.contains(":C"))
                                    {
                                        Symb1_ID=QuerySearch.value("Symb1_ID").toString();
                                        Symb1_Category=QuerySearch.value("Symb1_Category").toString();
                                    }
                                    else
                                    {
                                        Symb2_ID=QuerySearch.value("Symb1_ID").toString();
                                        Symb2_Category=QuerySearch.value("Symb1_Category").toString();
                                    }

                                }
                                if(QuerySearch.value("ConnectionNumber_Handle").toString()!="")
                                {
                                    ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
                                    ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
                                    Wires_Type=QuerySearch.value("Wires_Type").toString();
                                    Wires_Color=QuerySearch.value("Wires_Color").toString();
                                    Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
                                    Wires_Category=QuerySearch.value("Wires_Category").toString();
                                    Page_ID=QueryLine.value("Page_ID").toString();
                                }
                                LoopEnd=false;
                            }
                            //如果Symb1_ID或Symb2_ID包含:C且另一端与端口或端子直连，则更新Symb1_ID

                            SqlStr = "SELECT * FROM Symb2TermInfo WHERE Conn_Coordinate = '"+Coordinate_1+"'";
                            qDebug()<<"SqlStr="<<SqlStr;
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString Symb2TermInfo_ID=QuerySearch.value("Symb2TermInfo_ID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+QuerySearch.value("Symbol_ID").toString();
                                QuerySearch.exec(SqlStr);
                                if(QuerySearch.next())
                                {
                                    if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                    {
                                        if(Symb1_ID.contains(":C"))
                                        {
                                            Symb1_ID=Symb2TermInfo_ID;
                                            Symb1_Category="0";
                                        }
                                        else
                                        {
                                            Symb2_ID=Symb2TermInfo_ID;
                                            Symb2_Category="0";
                                        }
                                        LoopEnd=false;
                                    }
                                }
                            }
                            SqlStr = "SELECT * FROM TerminalInstance WHERE Coordinate = '"+Coordinate_1+"'";
                            QuerySearch.exec(SqlStr);
                            if(QuerySearch.next())
                            {
                                QString TerminalInstanceID=QuerySearch.value("TerminalInstanceID").toString();
                                //判断Symb2TermInfo对应的Page_ID是否满足ConnectorPage_ID
                                if(QuerySearch.value("Page_ID").toString()==ConnectorPage_ID)
                                {
                                    if(Symb1_ID.contains(":C"))
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb1_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb1_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb1_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb1_ID=TerminalInstanceID+".2";
                                        Symb1_Category="1";
                                    }
                                    else
                                    {
                                        if(Connector_Name=="SYMB2_M_PWF_CO1") Symb2_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO2") Symb2_ID=TerminalInstanceID+".2";
                                        if(Connector_Name=="SYMB2_M_PWF_CO3") Symb2_ID=TerminalInstanceID+".1";
                                        if(Connector_Name=="SYMB2_M_PWF_CO4") Symb2_ID=TerminalInstanceID+".2";
                                        Symb2_Category="1";
                                    }
                                    LoopEnd=false;
                                }
                            }
                        }
                    }
                }//end of if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))//如果是CO节点则找CO节点1端口连线另一侧的连接
            }//end of else if((Symb1_Category=="2")||(Symb2_Category=="2"))
            if(LoopEnd) break;
        }//while(1)

        QString StrSql =  "INSERT INTO ConnectLine (ConnectLine_ID,Page_ID,Cable_ID,Equipotential_Num,ConnectionNumber,ConnectionNumber_Handle,Symb1_ID,Symb2_ID,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category,Symb1_Category,Symb2_Category)"
                          "VALUES (:ConnectLine_ID,:Page_ID,:Cable_ID,:Equipotential_Num,:ConnectionNumber,:ConnectionNumber_Handle,:Symb1_ID,:Symb2_ID,:Wires_Type,:Wires_Color,:Wires_Diameter,:Wires_Category,:Symb1_Category,:Symb2_Category)";
        QueryConnectLine.prepare(StrSql);
        QueryConnectLine.bindValue(":ConnectLine_ID",GetMaxIDOfDB(T_ProjectDatabase,"ConnectLine","ConnectLine_ID"));
        QueryConnectLine.bindValue(":Page_ID",QueryLine.value("Page_ID").toString());
        QSqlQuery QuerySearchWire=QSqlQuery(T_ProjectDatabase);
        SqlStr = "SELECT * FROM Wires WHERE Handle = '"+ConnectionNumber_Handle+"' AND Page_ID = '"+Page_ID+"'";
        QuerySearchWire.exec(SqlStr);
        if(QuerySearchWire.next())  QueryConnectLine.bindValue(":Cable_ID",QuerySearchWire.value("Cable_ID").toString());
        else QueryConnectLine.bindValue(":Cable_ID","");
        QueryConnectLine.bindValue(":Equipotential_Num",QueryLine.value("Equipotential_Num").toString());
        QueryConnectLine.bindValue(":ConnectionNumber",ConnectionNumber);
        QueryConnectLine.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
        QueryConnectLine.bindValue(":Symb1_ID",Symb1_ID);
        QueryConnectLine.bindValue(":Symb2_ID",Symb2_ID);
        QueryConnectLine.bindValue(":Wires_Type",Wires_Type);
        QueryConnectLine.bindValue(":Wires_Color",Wires_Color);
        QueryConnectLine.bindValue(":Wires_Diameter",Wires_Diameter);
        QueryConnectLine.bindValue(":Wires_Category",Wires_Category);
        QueryConnectLine.bindValue(":Symb1_Category",Symb1_Category);
        QueryConnectLine.bindValue(":Symb2_Category",Symb2_Category);
        QueryConnectLine.exec();
    }//while(QueryLine.next())

    //如果某一个ConnectLine的两端都是"C"节点，则将他们连起来
    SqlStr="SELECT * FROM ConnectLine WHERE Symb1_ID LIKE '%:C' AND Symb2_ID LIKE '%:C'";
    QueryConnectLine.exec(SqlStr);
    while(QueryConnectLine.next())
    {
        qDebug()<<"Find 某一个ConnectLine的两端都是C节点，ConnectLine_ID="<<QueryConnectLine.value("ConnectLine_ID").toString();
        QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category,Page_ID;
        QString ConnectionNumber,ConnectionNumber_Handle,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category;
        QString ConnectLineSymb1_ID=QueryConnectLine.value("Symb1_ID").toString();
        QString ConnectLineSymb2_ID=QueryConnectLine.value("Symb2_ID").toString();
        Symb1_Category=QueryConnectLine.value("Symb1_Category").toString();
        Symb2_Category=QueryConnectLine.value("Symb2_Category").toString();
        ConnectionNumber=QueryConnectLine.value("ConnectionNumber").toString();
        ConnectionNumber_Handle=QueryConnectLine.value("ConnectionNumber_Handle").toString();
        Wires_Type=QueryConnectLine.value("Wires_Type").toString();
        Wires_Color=QueryConnectLine.value("Wires_Color").toString();
        Wires_Diameter=QueryConnectLine.value("Wires_Diameter").toString();
        Wires_Category=QueryConnectLine.value("Wires_Category").toString();
        Page_ID=QueryConnectLine.value("Page_ID").toString();

        QSqlQuery QuerySearch1=QSqlQuery(T_ProjectDatabase);
        QSqlQuery QuerySearch2=QSqlQuery(T_ProjectDatabase);
        SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+ConnectLineSymb1_ID+"' AND Symb1_Category = '2' AND Symb2_ID NOT LIKE '%:C') OR (Symb2_ID = '"+ConnectLineSymb1_ID+"' AND Symb2_Category = '2' AND Symb1_ID NOT LIKE '%:C')";
        QuerySearch1.exec(SqlStr);
        while(QuerySearch1.next())
        {
            SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+ConnectLineSymb2_ID+"' AND Symb1_Category = '2' AND Symb2_ID NOT LIKE '%:C') OR (Symb2_ID = '"+ConnectLineSymb2_ID+"' AND Symb2_Category = '2' AND Symb1_ID NOT LIKE '%:C')";
            QuerySearch2.exec(SqlStr);
            while(QuerySearch2.next())
            {
                if(ConnectLineSymb1_ID==QuerySearch1.value("Symb1_ID").toString())
                {
                    if(ConnectLineSymb2_ID==QuerySearch2.value("Symb1_ID").toString())
                    {
                        Symb1_ID=QuerySearch2.value("Symb2_ID").toString();
                        Symb1_Category=QuerySearch2.value("Symb2_Category").toString();
                        Symb2_ID=QuerySearch1.value("Symb2_ID").toString();
                        Symb2_Category=QuerySearch1.value("Symb2_Category").toString();
                    }
                    else if(ConnectLineSymb2_ID==QuerySearch2.value("Symb2_ID").toString())
                    {
                        Symb1_ID=QuerySearch2.value("Symb1_ID").toString();
                        Symb1_Category=QuerySearch2.value("Symb1_Category").toString();
                        Symb2_ID=QuerySearch1.value("Symb2_ID").toString();
                        Symb2_Category=QuerySearch1.value("Symb2_Category").toString();
                    }
                }
                else if(ConnectLineSymb1_ID==QuerySearch1.value("Symb2_ID").toString())
                {
                    if(ConnectLineSymb2_ID==QuerySearch2.value("Symb1_ID").toString())
                    {
                        Symb1_ID=QuerySearch1.value("Symb1_ID").toString();
                        Symb1_Category=QuerySearch1.value("Symb1_Category").toString();
                        Symb2_ID=QuerySearch2.value("Symb2_ID").toString();
                        Symb2_Category=QuerySearch2.value("Symb2_Category").toString();
                    }
                    else if(ConnectLineSymb2_ID==QuerySearch2.value("Symb2_ID").toString())
                    {
                        Symb1_ID=QuerySearch1.value("Symb1_ID").toString();
                        Symb1_Category=QuerySearch1.value("Symb1_Category").toString();
                        Symb2_ID=QuerySearch2.value("Symb1_ID").toString();
                        Symb2_Category=QuerySearch2.value("Symb1_Category").toString();
                    }
                }
                if(QuerySearch1.value("ConnectionNumber_Handle").toString()!="")
                {
                    ConnectionNumber=QuerySearch1.value("ConnectionNumber").toString();
                    ConnectionNumber_Handle=QuerySearch1.value("ConnectionNumber_Handle").toString();
                    Wires_Type=QuerySearch1.value("Wires_Type").toString();
                    Wires_Color=QuerySearch1.value("Wires_Color").toString();
                    Wires_Diameter=QuerySearch1.value("Wires_Diameter").toString();
                    Wires_Category=QuerySearch1.value("Wires_Category").toString();
                    Page_ID=QuerySearch1.value("Page_ID").toString();
                }
                else if(QuerySearch2.value("ConnectionNumber_Handle").toString()!="")
                {
                    ConnectionNumber=QuerySearch2.value("ConnectionNumber").toString();
                    ConnectionNumber_Handle=QuerySearch2.value("ConnectionNumber_Handle").toString();
                    Wires_Type=QuerySearch2.value("Wires_Type").toString();
                    Wires_Color=QuerySearch2.value("Wires_Color").toString();
                    Wires_Diameter=QuerySearch2.value("Wires_Diameter").toString();
                    Wires_Category=QuerySearch2.value("Wires_Category").toString();
                    Page_ID=QuerySearch2.value("Page_ID").toString();
                }
                //更新QuerySearch1
                QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                SqlStr="UPDATE ConnectLine SET Cable_ID=:Cable_ID,ConnectionNumber=:ConnectionNumber,ConnectionNumber_Handle=:ConnectionNumber_Handle,Symb1_ID=:Symb1_ID,"
                       "Symb2_ID=:Symb2_ID,Wires_Type=:Wires_Type,Wires_Color=:Wires_Color,Wires_Diameter=:Wires_Diameter,Wires_Category=:Wires_Category,"
                       "Symb1_Category=:Symb1_Category,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QuerySearch1.value("ConnectLine_ID").toString();
                QueryUpdate.prepare(SqlStr);
                QSqlQuery QuerySearchWire=QSqlQuery(T_ProjectDatabase);
                SqlStr = "SELECT * FROM Wires WHERE Handle = '"+ConnectionNumber_Handle+"' AND Page_ID = '"+Page_ID+"'";
                QuerySearchWire.exec(SqlStr);
                if(QuerySearchWire.next())  QueryUpdate.bindValue(":Cable_ID",QuerySearchWire.value("Cable_ID").toString());
                else QueryUpdate.bindValue(":Cable_ID","");
                QueryUpdate.bindValue(":ConnectionNumber",ConnectionNumber);
                QueryUpdate.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
                QueryUpdate.bindValue(":Symb1_ID",Symb1_ID);
                QueryUpdate.bindValue(":Symb2_ID",Symb2_ID);
                QueryUpdate.bindValue(":Wires_Type",Wires_Type);
                QueryUpdate.bindValue(":Wires_Color",Wires_Color);
                QueryUpdate.bindValue(":Wires_Diameter",Wires_Diameter);
                QueryUpdate.bindValue(":Wires_Category",Wires_Category);
                QueryUpdate.bindValue(":Symb1_Category",Symb1_Category);
                QueryUpdate.bindValue(":Symb2_Category",Symb2_Category);
                QueryUpdate.exec();
            }
        }
    }//while(QueryLine.next())

    //如果有2个CO节点直连，则将他们连起来
    QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
    SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%'";
    QueryConnector.exec(SqlStr);
    while(QueryConnector.next())
    {
        QString Connector_ID1,Connector_ID2;
        QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND C_Coordinate = '"+QueryConnector.value("C_Coordinate").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":1";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":1";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND C_Coordinate = '"+QueryConnector.value("Coordinate_1").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":C";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":1";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND Coordinate_1 = '"+QueryConnector.value("Coordinate_1").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":C";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":C";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
        SqlStr="SELECT * FROM Connector WHERE Connector_Name LIKE 'SYMB2_M_PWF_CO%' AND Page_ID = '"+QueryConnector.value("Page_ID").toString()+"' AND Coordinate_1 = '"+QueryConnector.value("C_Coordinate").toString()+"' AND Connector_ID <> "+QueryConnector.value("Connector_ID").toString();
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            Connector_ID1=QueryConnector.value("Connector_ID").toString()+":1";
            Connector_ID2=QuerySearch.value("Connector_ID").toString()+":C";
            UpdateConnectLine_CO_Connection(Connector_ID1,Connector_ID2);
        }
    }

    /*
   //如果某一个ConnectLine有一端是节点，且该处端点与元件端点或端子直连，则将他们连起来
   SqlStr="SELECT * FROM ConnectLine WHERE Symb1_Category = '2'";
   QueryConnectLine.exec(SqlStr);
   while(QueryConnectLine.next())
   {
       QString Symb1_ID=QueryConnectLine.value("Symb1_ID").toString();
       QString Symb_ID=Symb1_ID.mid(0,Symb1_ID.count()-2);
       QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
       SqlStr="SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
       QuerySearch.exec(SqlStr);
       if(QuerySearch.next())
       {
           QString TermConnectC,TermConnectG,TermConnect1,TermConnect2,TermConnect3;
           if(Symb1_ID.contains(":C"))
           {
               QStringList ListColumnName;
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":G' OR Symb2_ID = '"+Symb_ID+":G'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"G_Coordinate";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":1' OR Symb2_ID = '"+Symb_ID+":1'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_1";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":2' OR Symb2_ID = '"+Symb_ID+":2'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_2";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":3' OR Symb2_ID = '"+Symb_ID+":3'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_3";

               for(int i=0;i<ListColumnName.count();i++)
               {
qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value(ListColumnName.at(i)).toString();
                   //Range&0x01:Symbol  Range&0x02:Terminal  Range&0x04:Connector  Range&0x08:Link
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value(ListColumnName.at(i)).toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb1_ID=:Symb1_ID,Symb1_Category=:Symb1_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb1_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb1_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
           else
           {
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":C' OR Symb2_ID = '"+Symb_ID+":C'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next())
               {
qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value("C_Coordinate").toString();
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value("C_Coordinate").toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb1_ID=:Symb1_ID,Symb1_Category=:Symb1_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb1_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb1_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
       }
   }

   SqlStr="SELECT * FROM ConnectLine WHERE Symb2_Category = '2'";
   QueryConnectLine.exec(SqlStr);
   while(QueryConnectLine.next())
   {
       QString Symb2_ID=QueryConnectLine.value("Symb2_ID").toString();
       QString Symb_ID=Symb2_ID.mid(0,Symb2_ID.count()-2);
       QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
       SqlStr="SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID;
       QuerySearch.exec(SqlStr);
       if(QuerySearch.next())
       {
           QString TermConnectC,TermConnectG,TermConnect1,TermConnect2,TermConnect3;
           if(Symb2_ID.contains(":C"))
           {
               QStringList ListColumnName;
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":G' OR Symb2_ID = '"+Symb_ID+":G'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"G_Coordinate";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":1' OR Symb2_ID = '"+Symb_ID+":1'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_1";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":2' OR Symb2_ID = '"+Symb_ID+":2'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_2";

               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":3' OR Symb2_ID = '"+Symb_ID+":3'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next()) ListColumnName<<"Coordinate_3";

               for(int i=0;i<ListColumnName.count();i++)
               {
 qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value(ListColumnName.at(i)).toString();
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value(ListColumnName.at(i)).toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb2_ID=:Symb2_ID,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb2_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb2_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
           else
           {
               QSqlQuery QuerySearchLine=QSqlQuery(T_ProjectDatabase);
               SqlStr="SELECT * FROM Line WHERE Symb1_ID = '"+Symb_ID+":C' OR Symb2_ID = '"+Symb_ID+":C'";
               QuerySearchLine.exec(SqlStr);
               if(!QuerySearchLine.next())
               {
 qDebug()<<"FindTermConnect,Page_ID="<<QuerySearch.value("Page_ID").toString()<<",Coordinate="<<QuerySearch.value("C_Coordinate").toString();
                   QString StrTermConnect=FindTermConnectInDB(QuerySearch.value("Page_ID").toString(),QuerySearch.value("C_Coordinate").toString(),3);
qDebug()<<"StrTermConnect="<<StrTermConnect;
                   if(StrTermConnect!="")
                   {
                       QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
                       SqlStr="UPDATE ConnectLine SET Symb2_ID=:Symb2_ID,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QueryConnectLine.value("ConnectLine_ID").toString();
                       QueryUpdate.prepare(SqlStr);
                       QueryUpdate.bindValue(":Symb2_ID",StrTermConnect.split(",").at(0));
                       QueryUpdate.bindValue(":Symb2_Category",StrTermConnect.split(",").at(1));
                       QueryUpdate.exec();
                   }
               }
           }
       }
   }*/
    ProduceDBJXB();
    LoadProjectLines();
    LoadProjectSystemDescription();
}

//如果有2个CO节点直连，则将他们连起来
void MainWindow::UpdateConnectLine_CO_Connection(QString Connector_ID1,QString Connector_ID2)
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+Connector_ID1+"' AND Symb1_Category = '2') OR (Symb2_ID = '"+Connector_ID1+"' AND Symb2_Category = '2')";
    QuerySearch.exec(SqlStr);
    while(QuerySearch.next())
    {
        QSqlQuery QuerySearch2=QSqlQuery(T_ProjectDatabase);
        SqlStr = "SELECT * FROM ConnectLine WHERE (Symb1_ID = '"+Connector_ID2+"' AND Symb1_Category = '2') OR (Symb2_ID = '"+Connector_ID2+"' AND Symb2_Category = '2')";
        QuerySearch2.exec(SqlStr);
        while(QuerySearch2.next())
        {
            QString Symb1_ID,Symb2_ID,Symb1_Category,Symb2_Category,Page_ID;
            QString ConnectionNumber,ConnectionNumber_Handle,Wires_Type,Wires_Color,Wires_Diameter,Wires_Category;
            Symb1_ID=QuerySearch.value("Symb1_ID").toString();
            Symb2_ID=QuerySearch.value("Symb2_ID").toString();
            Symb1_Category=QuerySearch.value("Symb1_Category").toString();
            Symb2_Category=QuerySearch.value("Symb2_Category").toString();
            ConnectionNumber=QuerySearch.value("ConnectionNumber").toString();
            ConnectionNumber_Handle=QuerySearch.value("ConnectionNumber_Handle").toString();
            Wires_Type=QuerySearch.value("Wires_Type").toString();
            Wires_Color=QuerySearch.value("Wires_Color").toString();
            Wires_Diameter=QuerySearch.value("Wires_Diameter").toString();
            Wires_Category=QuerySearch.value("Wires_Category").toString();
            if((QuerySearch.value("Symb1_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb1_ID").toString()==Connector_ID2))
            {
                Symb1_ID=QuerySearch2.value("Symb2_ID").toString();
                Symb1_Category=QuerySearch2.value("Symb2_Category").toString();
            }
            if((QuerySearch.value("Symb1_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb2_ID").toString()==Connector_ID2))
            {
                Symb1_ID=QuerySearch2.value("Symb1_ID").toString();
                Symb1_Category=QuerySearch2.value("Symb1_Category").toString();
            }
            if((QuerySearch.value("Symb2_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb1_ID").toString()==Connector_ID2))
            {
                Symb2_ID=QuerySearch2.value("Symb2_ID").toString();
                Symb2_Category=QuerySearch2.value("Symb2_Category").toString();
            }
            if((QuerySearch.value("Symb2_ID").toString()==Connector_ID1)&&(QuerySearch2.value("Symb2_ID").toString()==Connector_ID2))
            {
                Symb2_ID=QuerySearch2.value("Symb1_ID").toString();
                Symb2_Category=QuerySearch2.value("Symb1_Category").toString();
            }
            if(QuerySearch2.value("ConnectionNumber_Handle").toString()!="")
            {
                ConnectionNumber=QuerySearch2.value("ConnectionNumber").toString();
                ConnectionNumber_Handle=QuerySearch2.value("ConnectionNumber_Handle").toString();
                Wires_Type=QuerySearch2.value("Wires_Type").toString();
                Wires_Color=QuerySearch2.value("Wires_Color").toString();
                Wires_Diameter=QuerySearch2.value("Wires_Diameter").toString();
                Wires_Category=QuerySearch2.value("Wires_Category").toString();
            }
            //更新QuerySearch1
            QSqlQuery QueryUpdate=QSqlQuery(T_ProjectDatabase);
            SqlStr="UPDATE ConnectLine SET ConnectionNumber=:ConnectionNumber,ConnectionNumber_Handle=:ConnectionNumber_Handle,Symb1_ID=:Symb1_ID,"
                   "Symb2_ID=:Symb2_ID,Wires_Type=:Wires_Type,Wires_Color=:Wires_Color,Wires_Diameter=:Wires_Diameter,Wires_Category=:Wires_Category,"
                   "Symb1_Category=:Symb1_Category,Symb2_Category=:Symb2_Category WHERE ConnectLine_ID = "+QuerySearch.value("ConnectLine_ID").toString();
            QueryUpdate.prepare(SqlStr);
            QueryUpdate.bindValue(":ConnectionNumber",ConnectionNumber);
            QueryUpdate.bindValue(":ConnectionNumber_Handle",ConnectionNumber_Handle);
            QueryUpdate.bindValue(":Symb1_ID",Symb1_ID);
            QueryUpdate.bindValue(":Symb2_ID",Symb2_ID);
            QueryUpdate.bindValue(":Wires_Type",Wires_Type);
            QueryUpdate.bindValue(":Wires_Color",Wires_Color);
            QueryUpdate.bindValue(":Wires_Diameter",Wires_Diameter);
            QueryUpdate.bindValue(":Wires_Category",Wires_Category);
            QueryUpdate.bindValue(":Symb1_Category",Symb1_Category);
            QueryUpdate.bindValue(":Symb2_Category",Symb2_Category);
            QueryUpdate.exec();
        }
    }
}

//Range&0x01:Symbol  Range&0x02:Terminal  Range&0x04:Connector  Range&0x08:Link
QString MainWindow::FindTermConnectInDB(QString Page_ID,QString Coordinate,unsigned char Range,QString LineDir)
{
    if(Coordinate=="") return "";
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    if(Range&0x01)//Symbol
    {
        SqlStr="SELECT * FROM Symbol WHERE Page_ID = '"+Page_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+QuerySearch.value("Symbol_ID").toString()+"' AND Conn_Coordinate = '"+Coordinate+"'";
            QuerySymb2TermInfo.exec(SqlStr);
            if(QuerySymb2TermInfo.next())
            {
                return QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()+",0";
            }
        }
    }
    if(Range&0x02)//Terminal
    {
        SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+Page_ID+"' AND Coordinate = '"+Coordinate+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            if(LineDir=="左")   return QuerySearch.value("TerminalInstanceID").toString()+"."+QuerySearch.value("LeftTerm").toString()+",1";
            else if(LineDir=="右")   return QuerySearch.value("TerminalInstanceID").toString()+"."+QuerySearch.value("RightTerm").toString()+",1";
        }
    }
    if(Range&0x04)//Connector
    {
        SqlStr="SELECT * FROM Connector WHERE Page_ID = '"+Page_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QStringList ListConnName={"C_Coordinate","G_Coordinate","Coordinate_1","Coordinate_2","Coordinate_3"};
            QStringList ListTermStr={":C",":G",":1",":2",":3"};
            for(int i=0;i<ListConnName.count();i++)
            {
                if(QuerySearch.value(ListConnName.at(i))==Coordinate) return QuerySearch.value("Connector_ID").toString()+ListTermStr.at(i)+",2";
            }
        }
    }
    if(Range&0x08)//Link
    {
        SqlStr="SELECT * FROM Link WHERE Page_ID = '"+Page_ID+"'";
        QuerySearch.exec(SqlStr);
        while(QuerySearch.next())
        {
            QStringList ListConnName={"C_Coordinate","Coordinate_1"};
            QStringList ListTermStr={":C",":1"};
            for(int i=0;i<ListConnName.count();i++)
            {
                if(QuerySearch.value(ListConnName.at(i))==Coordinate) return QuerySearch.value("Link_ID").toString()+ListTermStr.at(i)+",3";
            }
        }
    }
    return "";
}

void MainWindow::on_Btn_LineDefine_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->LineDefine();
    }
}

void MainWindow::on_Btn_CableDefine_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->CableDefine();
    }
}

void MainWindow::on_BtnNodeRightDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO1");
    }
}

void MainWindow::on_BtnNodeLeftDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO2");
    }
}

void MainWindow::on_BtnNodeRightUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO3");
    }
}

void MainWindow::on_BtnNodeLeftUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CO4");
    }
}

void MainWindow::on_BtnTNodeDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TLRU1");
    }
}

void MainWindow::on_BtnTNodeUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TLRO1");
    }
}

void MainWindow::on_BtnTNodeRight_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TOUR1");
    }
}

void MainWindow::on_BtnTNodeLeft_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_TOUL1");
    }
}

void MainWindow::on_BtnTNodeTX_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_BR1");
    }
}

void MainWindow::on_BtnTNodeCross_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_CR1");
    }
}

void MainWindow::on_BtnLinkRight_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点1");
    }
}

void MainWindow::on_BtnLinkUp_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点2");
    }
}

void MainWindow::on_BtnLinkLeft_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点3");
    }
}

void MainWindow::on_BtnLinkDown_clicked()
{
    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->NodeLoad("SYMB2_M_PWF_链接点4");
    }
}

//Mode=1:全部向上 Mode=2:全部向下 Mode=3：奇数向上，偶数向下 Mode=4：奇数向下，偶数向上  mode=5:前半部分向上，后面向下  Mode=6：前半部分向下，后面向上
void MainWindow::LoadWholeUnit(int Mode)
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                qDebug()<<"LoadUnit,ID="<<ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
                formMdi->LoadWholeUnit(ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt(),Mode);
            }
        }
    }
}

//整体放置，接线图章
void MainWindow::LoadUnitStamp()
{
    QSqlQuery QuerySearch=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID= "+ui->treeViewUnits->currentIndex().data(Qt::UserRole).toString();
    QuerySearch.exec(SqlStr);
    if(QuerySearch.next())
    {
        QSqlQuery QuerySearchLib=QSqlQuery(T_LibDatabase);
        SqlStr="SELECT * FROM Equipment WHERE PartCode= '"+QuerySearch.value("PartCode").toString()+"'";
        QuerySearchLib.exec(SqlStr);
        if(QuerySearchLib.next())
        {
            if(QuerySearchLib.value("MultiLib").toString()!="")
            {
                if(!ui->treeViewUnits->currentIndex().isValid()) return;
                if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="元件") return;
                if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
                {
                    formaxwidget *formMdi;
                    formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
                    if(formMdi!=nullptr)
                    {
                        //确定当前活动窗口的图纸是否为本项目图纸
                        QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
                        QFileInfo file(PageName);
                        if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
                        else
                        {
                            qDebug()<<"LoadUnitStamp,ID="<<ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
                            formMdi->UnitIdInDB=ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt();
                            formMdi->LoadUnitStamp(QuerySearchLib.value("MultiLib").toString());
                        }
                    }
                }
            }
        }
    }
}

//整体放置,全部向上
void MainWindow::LoadWholeUnitAllTermsUp()
{
    LoadWholeUnit(1);
}
//整体放置,全部向下
void MainWindow::LoadWholeUnitAllTermsDown()
{
    LoadWholeUnit(2);
}
//整体放置,奇数向上，偶数向下
void MainWindow::LoadWholeUnitOddTermsUp()
{
    LoadWholeUnit(3);
}
//整体放置,奇数向下，偶数向上
void MainWindow::LoadWholeUnitEvenTermsUp()
{
    LoadWholeUnit(4);
}
//整体放置,前半部分向上，后面向下
void MainWindow::LoadWholeUnitFirstHalfUp()
{
    LoadWholeUnit(5);
}
//整体放置,前半部分向下，后面向上
void MainWindow::LoadWholeUnitLastHalfUp()
{
    LoadWholeUnit(6);
}

void MainWindow::SlotLoadSpur()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListSymbol_ID;
                for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
                    ListSymbol_ID.append(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadSymbolSpur(ListSymbol_ID);//ui->treeViewUnits->currentIndex().data(Qt::UserRole).toInt());
            }
        }
    }
}

void MainWindow::DrawSpurEqualDistance()
{
    if(!ui->treeViewUnits->currentIndex().isValid()) return;
    if(ui->treeViewUnits->currentIndex().data(Qt::WhatsThisRole).toString()!="功能子块") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListSymbol_ID;
                for(int i=0;i<ui->treeViewUnits->selectionModel()->selectedIndexes().count();i++)
                    ListSymbol_ID.append(ui->treeViewUnits->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadEqualDistance(ListSymbol_ID,0);
            }
        }
    }
}

void MainWindow::DrawTerminalEqualDistance()//等距绘制端子
{
    if(!ui->treeViewTerminal->currentIndex().isValid()) return;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListTerminal_ID;
                for(int i=0;i<ui->treeViewTerminal->selectionModel()->selectedIndexes().count();i++)
                    ListTerminal_ID.append(ui->treeViewTerminal->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadEqualDistance(ListTerminal_ID,1);
            }
        }
    }
}

void MainWindow::SlotLoadTerminal()
{
    if(!ui->treeViewTerminal->currentIndex().isValid()) return;
    if(ui->treeViewTerminal->currentIndex().data(Qt::WhatsThisRole).toString()!="端子") return;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                QList<int> ListSymbol_ID;
                for(int i=0;i<ui->treeViewTerminal->selectionModel()->selectedIndexes().count();i++)
                    ListSymbol_ID.append(ui->treeViewTerminal->selectionModel()->selectedIndexes().at(i).data(Qt::UserRole).toInt());
                formMdi->LoadTerminal(ListSymbol_ID);
            }
        }
    }
}


void MainWindow::on_Btn_BlackBox_clicked()
{
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            if(!formMdi->IsDrawingMultiLib)
            {
                //确定当前活动窗口的图纸是否为本项目图纸
                QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
                QFileInfo file(PageName);
                if(!file.exists())
                {
                    QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
                    return;
                }
            }
            formMdi->DrawBlackBox();
        }
    }
}

void MainWindow::on_Btn_StructBox_clicked()
{
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            //确定当前活动窗口的图纸是否为本项目图纸
            QString PageName=CurProjectPath+"/"+formMdi->windowTitle()+".dwg";
            QFileInfo file(PageName);
            if(!file.exists()) QMessageBox::warning(nullptr, "提示", "该图纸不属于当前项目，请打开项目图纸！");
            else
            {
                formMdi->DrawStructBox();
            }
        }
    }
}

void MainWindow::on_BtnFuncManage_clicked()
{
    dlgFuncDefine->setModal(true);
    dlgFuncDefine->SetCurStackedWidgetIndex(1);
    dlgFuncDefine->show();
    dlgFuncDefine->exec();
}



void MainWindow::on_treeViewUnits_clicked(const QModelIndex &index)
{
    if(!ui->widgetPreView->isVisible()) return;
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="功能子块") return;
    QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Symbol WHERE Symbol_ID = "+index.data(Qt::UserRole).toString();
    QuerySymbol.exec(SqlStr);
    if(!QuerySymbol.next()) return;
    QString Path;
    if(QuerySymbol.value("Symbol").toString().contains("SPS_"))
        Path="C:/TBD/SPS/"+QuerySymbol.value("Symbol").toString()+".dwg";
    else
        Path="C:/TBD/SYMB2LIB/"+QuerySymbol.value("Symbol").toString()+".dwg";
    ui->axWidgetPreview->dynamicCall("OpenDwgFile(QString)",Path);
    ui->axWidgetPreview->dynamicCall("ZoomAll()");
}

void MainWindow::on_treeViewTerminal_clicked(const QModelIndex &index)
{
    if(!ui->widgetPreView->isVisible()) return;
    if(!index.isValid()) return;
    if(index.data(Qt::WhatsThisRole).toString()!="端子") return;
    QSqlQuery QueryTerminal = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Terminal WHERE Terminal_ID = "+index.data(Qt::UserRole).toString();
    QueryTerminal.exec(SqlStr);
    if(!QueryTerminal.next()) return;
    QString Path;
    if(QueryTerminal.value("Symbol").toString().contains("SPS_"))
        Path="C:/TBD/SPS/"+QueryTerminal.value("Symbol").toString()+".dwg";
    else
        Path="C:/TBD/SYMB2LIB/"+QueryTerminal.value("Symbol").toString()+".dwg";
    ui->axWidgetPreview->dynamicCall("OpenDwgFile(QString)",Path);
    ui->axWidgetPreview->dynamicCall("ZoomAll()");
}

void MainWindow::on_tabWidget_Navigator_currentChanged(int index)
{
    if(index==3)
    {
        ShowPreViewWidget=false;
        ui->BtnShowHidePreViewWidget->setText("图形预览▲");
        ui->widgetPreView->setVisible(false);
    }
}

void MainWindow::on_Btn_GeneratePartList_clicked()
{
    dlgGenerate.setWindowTitle("生成部件汇总表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(2);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '部件汇总表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"部件汇总表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '部件汇总表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"部件汇总表")+"'";
        qDebug()<<"StrSql="<<StrSql;
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    QStringList ListedPart;
    ListedPart.clear();
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Equipment WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' ORDER BY ProjectStructure_ID";
        QueryEquipment.exec(StrSql);
        while(QueryEquipment.next())
        {
            if(QueryEquipment.value("PartCode").toString()=="") continue;
            bool PartExisted=false;
            for(int i=0;i<ListedPart.count();i++)
            {
                if(ListedPart.at(i)==QueryEquipment.value("PartCode").toString())
                {
                    PartExisted=true;
                    break;
                }
            }
            if(PartExisted) continue;
            ListedPart.append(QueryEquipment.value("PartCode").toString());
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"MXB");
                SetCurLayer(GlobalBackAxWidget,"MXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"部件汇总表",10,0,0,2);//部件汇总表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",59,264,"部件编号",7,0,1,2);//部件编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,271,99,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",149,264,"型号",7,0,1,2);//型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,271,199,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",234,264,"名称",7,0,1,2);//名称
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",269,271,269,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",275,264,"数量",7,0,1,2);//数量
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",281,257,281,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",306,264,"厂家",7,0,1,2);//厂家
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,257,331,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",357,264,"部件备注",7,0,1,2);//部件备注
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线8
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","部件汇总表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
            QString UnitTag=QueryEquipment.value("DT").toString();
            QString UnitType=QueryEquipment.value("Type").toString();
            QString UnitName=QueryEquipment.value("Name").toString();
            //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置
            QString UnitNameStr=GetProjectStructureStrByProjectStructureID(QueryEquipment.value("ProjectStructure_ID").toInt())+"-"+UnitTag;

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,QueryEquipment.value("PartCode").toString(),3.5,0,0,2);//部件编号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",99,Lasty,99,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",101,Lasty-3.5,UnitType,3.5,0,0,2);//型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",199,Lasty,199,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",201,Lasty-3.5,UnitName,3.5,0,0,2);//名称
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",269,Lasty,269,Lasty-7);//竖线5

            QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            StrSql="SELECT * FROM Equipment WHERE PartCode = '"+QueryEquipment.value("PartCode").toString()+"'";
            QuerySearch.exec(StrSql);
            if(QuerySearch.last())
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",271,Lasty-3.5,QString::number(QuerySearch.at()+1),3.5,0,0,2);//数量
            else
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",271,Lasty-3.5,"0",3.5,0,0,2);//数量
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",281,Lasty,281,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",283,Lasty-3.5,QueryEquipment.value("Factory").toString(),3.5,0,0,2);//厂家
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",331,Lasty,331,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",333,Lasty-3.5,QueryEquipment.value("Remark").toString(),3.5,0,0,2);//部件备注
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_Btn_GenerateCableList_clicked()
{
    dlgGenerate.setWindowTitle("生成电缆列表");
    dlgGenerate.Canceled=true;
    dlgGenerate.LoadTable(5);
    dlgGenerate.setModal(true);
    dlgGenerate.show();
    dlgGenerate.exec();
    if(dlgGenerate.Canceled) return;

    //删除原Page记录
    QSqlQuery QueryPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString StrSql;
    if(dlgGenerate.ReplaceOriginalDwg)
    {
        StrSql= "SELECT * FROM Page WHERE PageType = '电缆列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"电缆列表")+"'";
        QueryPage.exec(StrSql);
        while(QueryPage.next())
        {
            QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
            QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
            for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
            {
                //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
                if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
                {
                    ui->mdiArea->subWindowList().at(i)->close();
                    break;
                }
            }
            QFile file(dwgfilepath);
            if(file.exists()) file.remove();
        }
        StrSql= "DELETE FROM Page WHERE PageType = '电缆列表' AND ProjectStructure_ID = '"+GetPageProjectStructure_IDByGaocengAndPos(dlgGenerate.StrGaoceng,dlgGenerate.StrPos,"电缆列表")+"'";
        QueryPage.exec(StrSql);
    }


    //根据当前图纸的Border表来绘制Text 目录
    double Lasty;
    int CurRecordIndex=1;
    int CurPageNum=0;
    QString PageName;
    QSqlQuery QueryWires = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QStringList ListProjectStructure_ID=GetAllIDFromProjectStructure(1,dlgGenerate.StrGaoceng,dlgGenerate.StrPos,dlgGenerate.AllGaoceng,dlgGenerate.AllPos);
    for(int indexID=0;indexID<ListProjectStructure_ID.count();indexID++)
    {
        StrSql="SELECT * FROM Wires WHERE ProjectStructure_ID = '"+ListProjectStructure_ID.at(indexID)+"' AND Cable_ID <> '' ORDER BY ProjectStructure_ID";
        QueryWires.exec(StrSql);
        while(QueryWires.next())
        {
            if(QueryWires.value("Cable_ID").toString()=="") continue;
            if(QueryWires.value("TextHandle").toString()!="") continue;
            if(CurRecordIndex>CurPageNum*32)
            {
                PageName="";
                if(dlgGenerate.StrGaoceng!="") PageName+="="+dlgGenerate.StrGaoceng;
                if(dlgGenerate.StrPos!="") PageName+="+"+dlgGenerate.StrPos;
                if(dlgGenerate.StrPage!="") PageName+="&"+dlgGenerate.StrPage;
                PageName=CurProjectPath+"/"+PageName+"·"+GetStrRemoveLastNum(dlgGenerate.InitPageName)+QString::number(GetStrLastNum(dlgGenerate.InitPageName)+CurPageNum)+".dwg";
                //创建dwg文件
                QFileInfo fileinfo(PageName);
                if(fileinfo.exists())
                {
                    QFile file(PageName);
                    file.remove();
                }
                QString SourceFileName="C:/TBD/TITLE/A3-zju.dwg";
                QFile::copy(SourceFileName,PageName);
                bool Ret=GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",PageName).toBool();
                qDebug()<<"DeleteDwgSymbolByPageAndHandle,OpenDwgFile "<<Ret;
                CreateLayer(GlobalBackAxWidget,"MXB");
                SetCurLayer(GlobalBackAxWidget,"MXB");
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",12,280,"电缆列表",10,0,0,2);//电缆列表
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,383,271);//横线1
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,257,383,257);//横线2
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,271,7,257);//竖线1
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,264,"序号",7,0,1,2);//序号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,271,19,257);//竖线2
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",56,264,"电缆编号",7,0,1,2);//电缆编号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",86,271,86,257);//竖线3
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",107,264,"电缆型号",7,0,1,2);//电缆型号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",128,271,128,257);//竖线4
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",150,264,"线芯结构",7,0,1,2);//线芯结构
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",172,271,172,257);//竖线5
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",202,264,"源",7,0,1,2);//源
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",232,257,232,271);//竖线6
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",262,264,"目标",7,0,1,2);//目标
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",292,257,292,271);//竖线7
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",317,264,"页号",7,0,1,2);//页号
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",342,257,342,271);//竖线8
                GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",362,264,"功能描述",7,0,1,2);//功能描述
                GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,257,383,271);//竖线9
                GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
                int Page_ID=1;
                QSqlQuery QueryNewPage = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                StrSql = QString("SELECT * FROM Page ORDER BY Page_ID DESC");
                QueryNewPage.exec(StrSql);
                if(QueryNewPage.next()) Page_ID=QueryNewPage.value("Page_ID").toInt()+1;
                StrSql =  QString("INSERT INTO Page (Page_ID,ProjectStructure_ID,Page_Desc,PageType,PageName,Scale,Border,Title,AlterTime)"
                                  "VALUES (:Page_ID,:ProjectStructure_ID,:Page_Desc,:PageType,:PageName,:Scale,:Border,:Title,:AlterTime)");
                QueryNewPage.prepare(StrSql);
                QueryNewPage.bindValue(":Page_ID",Page_ID);
                QueryNewPage.bindValue(":ProjectStructure_ID",QString::number(dlgGenerate.ProjectStructure_ID));
                QueryNewPage.bindValue(":Page_Desc","");
                QueryNewPage.bindValue(":PageType","电缆列表");
                QueryNewPage.bindValue(":PageName",QString::number(dlgGenerate.InitPageName.toInt()+CurPageNum));
                QueryNewPage.bindValue(":Scale","1:1");
                QueryNewPage.bindValue(":Border","A3:420x297");
                QueryNewPage.bindValue(":Title","A3-zju.dwg");
                QueryNewPage.bindValue(":AlterTime",QDateTime::currentDateTime().toString("yyyy-MM-dd hh:mm:ss"));
                QueryNewPage.exec();
                Lasty=257;
                CurPageNum++;
            }
            QString BHTag="";
            QSqlQuery QueryCable = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr="SELECT * FROM Cable WHERE Cable_ID = '"+QueryWires.value("Cable_ID").toString()+"'";
            QueryCable.exec(SqlStr);
            if(QueryCable.next())
            {
                BHTag= GetProjectStructureStrByProjectStructureID(QueryCable.value("ProjectStructure_ID").toInt())+"-"+QueryCable.value("CableNum").toString();
                if(QueryWires.value("Color").toString()!="") BHTag+="("+QueryWires.value("Color").toString()+")";
            }
            QString StrType=QueryCable.value("Type").toString();
            QString StrStructure=QueryCable.value("Structure").toString();

            QString StrSource,StrTarget;
            QSqlQuery QueryLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr="SELECT * FROM Line WHERE Wires_Handle = '"+QueryWires.value("Handle").toString()+"'";
            QueryLine.exec(SqlStr);
            if(QueryLine.next())
            {
                int Line_ID=QueryLine.value("Line_ID").toInt();
                QSqlQuery QueryConnectLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="SELECT * FROM ConnectLine WHERE ConnectLine_ID = "+QString::number(Line_ID);
                QueryConnectLine.exec(SqlStr);
                if(QueryConnectLine.next())
                {
                    if(QueryConnectLine.value("Symb1_Category").toString()=="0") StrSource=GetUnitTermStrByTermID(QueryConnectLine.value("Symb1_ID").toString());
                    if(QueryConnectLine.value("Symb1_Category").toString()=="1") StrSource=GetTerminalTermStrByTermID(QueryConnectLine.value("Symb1_ID").toString());
                    if(QueryConnectLine.value("Symb2_Category").toString()=="0") StrTarget=GetUnitTermStrByTermID(QueryConnectLine.value("Symb2_ID").toString());
                    if(QueryConnectLine.value("Symb2_Category").toString()=="1") StrTarget=GetTerminalTermStrByTermID(QueryConnectLine.value("Symb2_ID").toString());
                }
            }
            //根据ProjectStructure_ID在ProjectStructure表中查找元件所处位置

            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty-7,383,Lasty-7);//横线
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",7,Lasty,7,Lasty-7);//竖线1
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",13,Lasty-3.5,QString::number(CurRecordIndex),3.5,0,0,2);//序号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",19,Lasty,19,Lasty-7);//竖线2

            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",21,Lasty-3.5,BHTag,3.5,0,0,2);//电缆编号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",86,Lasty,86,Lasty-7);//竖线3
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",88,Lasty-3.5,StrType,3.5,0,0,2);//电缆型号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",128,Lasty,128,Lasty-7);//竖线4
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",130,Lasty-3.5,StrStructure,3.5,0,0,2);//线芯结构
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",172,Lasty,172,Lasty-7);//竖线5
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",174,Lasty-3.5,StrSource,3.5,0,0,2);//源
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",232,Lasty,232,Lasty-7);//竖线6
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",234,Lasty-3.5,StrTarget,3.5,0,0,2);//目标
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",292,Lasty,292,Lasty-7);//竖线7
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",294,Lasty-3.5,GetPageNameByPageID(QueryWires.value("Page_ID").toInt()),3.5,0,0,2);//页号
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",342,Lasty,342,Lasty-7);//竖线8
            GlobalBackAxWidget->dynamicCall("DrawText(double,double,const QString&,double,double,short,short)",344,Lasty-3.5,QueryCable.value("Desc").toString(),3.5,0,0,2);//功能描述
            GlobalBackAxWidget->dynamicCall("DrawLine(double,double,double,double)",383,Lasty,383,Lasty-7);//竖线9
            GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
            Lasty=Lasty-7;
            CurRecordIndex++;
        }
    }
    GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",PageName);
    LoadProjectPages();
}

void MainWindow::on_CbUnitTogether_clicked()
{
    LoadUnitTable();
}

void MainWindow::on_TabUnit_currentChanged(int index)
{
    if(index==0) ui->CbUnitTogether->setVisible(false);
    else ui->CbUnitTogether->setVisible(true);
}

void MainWindow::on_tableWidgetUnit_doubleClicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    int Equipment_ID=ui->tableWidgetUnit->item(index.row(),0)->data(Qt::UserRole).toInt();
    qDebug()<<"Equipment_ID="<<Equipment_ID;
    ShowUnitAttrByEquipment_ID(Equipment_ID);
}

void MainWindow::on_BtnPageFilter_clicked()
{
    FilterPage();
}

void MainWindow::on_CbPageGaocengFilter_currentIndexChanged(const QString &arg1)
{
    FilterPage();
}

void MainWindow::on_CbPagePosFilter_currentIndexChanged(const QString &arg1)
{
    FilterPage();
}

void MainWindow::on_CbPageTypeFilter_currentIndexChanged(const QString &arg1)
{
    FilterPage();
}

void MainWindow::on_EdPageFilter_editingFinished()
{
    FilterPage();
}

void MainWindow::on_BtnUnitFilter_clicked()
{
    FilterUnit();
}

void MainWindow::on_CbUnitGaoceng_currentIndexChanged(const QString &arg1)
{
    FilterUnit();
}

void MainWindow::on_CbUnitPos_currentIndexChanged(const QString &arg1)
{
    FilterUnit();
}

void MainWindow::on_CbUnitPage_currentIndexChanged(const QString &arg1)
{
    FilterUnit();
}

void MainWindow::on_EdUnitTagSearch_editingFinished()
{
    FilterUnit();
}

void MainWindow::on_BtnTermFilter_clicked()
{
    FilterTerminal();
}

void MainWindow::on_CbTermGaoceng_currentIndexChanged(const QString &arg1)
{
    FilterTerminal();
}

void MainWindow::on_CbTermPos_currentIndexChanged(const QString &arg1)
{
    FilterTerminal();
}

void MainWindow::on_CbTermPage_currentIndexChanged(const QString &arg1)
{
    FilterTerminal();
}

void MainWindow::on_EdTermTagFilter_editingFinished()
{
    FilterTerminal();
}

void MainWindow::on_tabWidgetLine_currentChanged(int index)
{
    ui->stackedWidgetLine->setCurrentIndex(index);
}

void MainWindow::on_BtnLineFilter_clicked()
{
    FilterLines();
}

void MainWindow::on_CbLineGaoceng_currentIndexChanged(const QString &arg1)
{
    FilterLines();
}

void MainWindow::on_CbLinePos_currentIndexChanged(const QString &arg1)
{
    FilterLines();
}

void MainWindow::on_CbLinePage_currentIndexChanged(const QString &arg1)
{
    FilterLines();
}

void MainWindow::on_EdLineTagFilter_editingFinished()
{
    FilterLines();
}

QString RecentPath="";
void MainWindow::on_BtnOpenPage_clicked()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("打开图纸"));
    if(RecentPath!="") fileDialog.setDirectory(RecentPath);
    else fileDialog.setDirectory(LocalProjectDefaultPath);
    fileDialog.setNameFilter(tr("dwg(*.dwg)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();

    QFileInfo fileinfo(fileNames.at(0));
    if(!fileinfo.exists()) return;
    QString dwgfilename=fileinfo.fileName();
    dwgfilename=dwgfilename.mid(0,dwgfilename.lastIndexOf(".dwg"));
    QString dwgfilepath=fileinfo.filePath();
    RecentPath=dwgfilepath;
    //查看是否已经打开改图纸
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
        {
            ui->mdiArea->setActiveSubWindow(ui->mdiArea->subWindowList().at(i));
            return;
        }
    }
    //创建新的mdi
    formaxwidget *formMxdraw=new formaxwidget(this,dwgfilepath);
    formMxdraw->setWindowTitle(dwgfilename);
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
}

//刷新终端功能子块链路
void MainWindow::on_BtnRefreshExecConn_clicked()
{
    QSqlQuery QuerySymbol(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Symbol WHERE ExecConn= TRUE";
    QuerySymbol.exec(StrSql);
    QString Gaoceng,Pos;
    ui->tableWidgetExecConn->setRowCount(0);
    while(QuerySymbol.next())
    {
        GetUnitTermimalGaocengAndPos(0,QuerySymbol.value("Symbol_ID").toInt(),Gaoceng,Pos);
        qDebug()<<"Equipment_ID="<<QuerySymbol.value("Equipment_ID").toInt()<<",Gaoceng="<<Gaoceng<<",Pos="<<Pos;
        if((ui->CbExecConnGaoceng->currentText()!="高层")||(ui->CbExecPos->currentText()!="位置"))
        {
            if((ui->CbExecConnGaoceng->currentText()!="高层")&&(ui->CbExecConnGaoceng->currentText()!=Gaoceng)) continue;
            if((ui->CbExecPos->currentText()!="位置")&&(ui->CbExecPos->currentText()!=Pos)) continue;
        }
        ui->tableWidgetExecConn->setRowCount(ui->tableWidgetExecConn->rowCount()+1);
        QTableWidgetItem *ItemExecConn=new QTableWidgetItem("");
        ItemExecConn->setCheckState(Qt::Unchecked);
        ItemExecConn->setData(Qt::UserRole,QuerySymbol.value("Symbol_ID").toInt());
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,0,ItemExecConn);//源端口
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,1,new QTableWidgetItem(Gaoceng));//高层
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,2,new QTableWidgetItem(Pos));//位置
        QSqlQuery QueryEquipment(T_ProjectDatabase);
        QString StrSql="SELECT * FROM Equipment WHERE Equipment_ID = "+QuerySymbol.value("Equipment_ID").toString();
        QueryEquipment.exec(StrSql);
        if(QueryEquipment.next())
        {
            ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,3,new QTableWidgetItem(QueryEquipment.value("DT").toString()));//元件名称
        }
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,4,new QTableWidgetItem(GetUnitSpurStrBySymbol_ID(QuerySymbol)));//功能子块名称
        ui->tableWidgetExecConn->setItem(ui->tableWidgetExecConn->rowCount()-1,5,new QTableWidgetItem(QuerySymbol.value("LinkRoad").toString()));//诊断链路
    }

}

void MainWindow::on_BtnShowLinkRoad_clicked()
{
    //创建新的mdi
    formaxwidget *formMxdraw=new formaxwidget(this);
    formMxdraw->setWindowTitle("诊断链路图");
    QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
    formMxdraw->mdisubwindow=mdisubwindow;
    connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
    QList<int> ListSymbolID;
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
            ListSymbolID.append(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toInt());
    }
    formMxdraw->DrawDiagnoseLinkRoad(ListSymbolID);
}

/*
void MainWindow::MakeListFinalLinkInfo()
{
    //QStringList ListFinalLinkInfo;
    ListFinalLinkInfo.clear();
    int Linkid=0;
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
        {
            Linkid++;
            QString StrLinkRoad=GetLinkRoadBySymbol(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toInt());
            ui->tableWidgetExecConn->item(i,5)->setText(StrLinkRoad);
            QStringList ListAllLinkRoad;
            while(1)
            {
                if(!(StrLinkRoad.contains("[")&&StrLinkRoad.contains("]"))) break;
                int index1=StrLinkRoad.indexOf("[");
                int index2=StrLinkRoad.indexOf("]");
                ListAllLinkRoad.append(StrLinkRoad.mid(index1+1,index2-index1-1));
                StrLinkRoad=StrLinkRoad.mid(index2+1,StrLinkRoad.count()-index2-1);
            }
//qDebug()<<"while(1) ListAllLinkRoad="<<ListAllLinkRoad;
            if(ListAllLinkRoad.count()==2)//正负两条链路
            {
                //将优先级高的链路放在ListAllLinkRoad前面
                for(int j=0;j<ListAllLinkRoad.count();j++)
                {
                    QString StrSourceConn=ListAllLinkRoad.at(j).split(";").last();
                    if((StrSourceConn.split(",").count()!=2)||(StrSourceConn.split(",").at(1)!="0"))
                    {
                        ListAllLinkRoad.removeAt(j);
                        continue;
                    }
                    int SourcePrior=GetSourcePriorBySymbolID(StrSourceConn.split(",").at(0));
                    if(SourcePrior<0)
                    {
                        ListAllLinkRoad.removeAt(j);
                        continue;
                    }
                    for(int k=j;k<ListAllLinkRoad.count();k++)
                    {
                        QString StrCompareSourceConn=ListAllLinkRoad.at(k).split(";").last();
                        if((StrCompareSourceConn.split(",").count()!=2)||(StrCompareSourceConn.split(",").at(1)!="0")) continue;
                        int CompareSourcePrior=GetSourcePriorBySymbolID(StrCompareSourceConn.split(",").at(0));
                        if(SourcePrior>CompareSourcePrior)//数字小的优先级高
                        {
                            //j k 互换
                            QString tmpStr=ListAllLinkRoad[j];
                            ListAllLinkRoad[j]=ListAllLinkRoad[k];
                            ListAllLinkRoad[k]=tmpStr;
                        }
                    }
                }//将优先级高的链路放在ListAllLinkRoad前面
//qDebug()<<"排序完成 ListAllLinkRoad="<<ListAllLinkRoad;
                //根据ListAllLinkRoad生成诊断文件CurProjectName.jmpl
                QStringList ListLinkRoad=ListAllLinkRoad.at(0).split(";");
                ListFinalLinkInfo.append(ListLinkRoad.at(ListLinkRoad.count()-1)+","+QString::number(Linkid)+",false,1,0");
                for(int k=ListLinkRoad.count()-2;k>=0;k--)
                {
                    //if((j>0)&&(k==(ListLinkRoad.count()-1))) continue;//源只统计一次
                    if(k==0) continue;//执行器只统计一次
                    //if((j!=(ListAllLinkRoad.count()-1))&&(k==0)) continue;//执行器只统计一次
                    ListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,1");
                }
                ListLinkRoad=ListAllLinkRoad.at(1).split(";");
                for(int k=ListLinkRoad.count()-1;k>0;k--)
                {
                    if(k==(ListLinkRoad.count()-1)) continue;//源只统计一次
                    ListFinalLinkInfo.append(ListLinkRoad.at(k)+","+QString::number(Linkid)+",false,1,2");
                }
                ListFinalLinkInfo.append(ListLinkRoad.at(0)+","+QString::number(Linkid)+",false,1,3");
            }//end of if(ListAllLinkRoad.count()==2)//正负两条链路
        }//end of if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
    }//end of for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
//qDebug()<<"ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateJmplInfo(ListFinalLinkInfo);//更新ListJmplInfo中相同功能子块出现的次数
//qDebug()<<"重新排序前a，ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateListFinalLinkInfoOrder(ListFinalLinkInfo);//根据功能子块出现的次数对每一条单链重新排序
    //return ListFinalLinkInfo;
}
*/

void MainWindow::RemakeLinkRoad(QStringList ListExecSpurID)
{
    ListFinalLinkInfo=MakeListFinalLinkInfo(ListExecSpurID);

    qDebug()<<"MakeListFinalLinkInfo，ListFinalLinkInfo="<<ListFinalLinkInfo;
    UpdateEquipmentTModelDiag(ListFinalLinkInfo);//镜像SymbolID对应的元件TModelDiag描述
    qDebug()<<"UpdateEquipmentTModelDiag，ListFinalLinkInfo="<<ListFinalLinkInfo;
    //根据链路生成诊断文件CurProjectName.jmpl CurProjectName.xmpl,CurProjectName.hrn CurProjectName.ini
    QString Strjmpl,Strhrn,Strini,StrSystemConnection;
    StrSystemDefine="\r\nclass Test {\r\n";

    QFile jmplfile(CurProjectPath+"/"+CurProjectName+".jmpl");
    jmplfile.remove();
    jmplfile.open(QIODevice::WriteOnly);

    //CurProjectName.jmpl
    QSqlQuery QueryEnumerations = QSqlQuery(T_LibDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Enumerations";
    QueryEnumerations.exec(SqlStr);
    while(QueryEnumerations.next())
    {
        Strjmpl+="\r\n";
        Strjmpl+="enum "+QueryEnumerations.value("EnumName").toString();
        Strjmpl+="{"+QueryEnumerations.value("EnumMember").toString()+"};";
    }
    Strjmpl+="\r\n\r\n";
    //器件T语言
    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
        ListFinalLinkInfo[i]=ListFinalLinkInfo.at(i).split(",").at(0)+","+ListFinalLinkInfo.at(i).split(",").at(1)+","+ListFinalLinkInfo.at(i).split(",").at(2)+",false,"+ListFinalLinkInfo.at(i).split(",").at(4)+","+ListFinalLinkInfo.at(i).split(",").at(5);
    }
    QString StrLastePort_out;
    QString LastLinkId="0";
    for(int i=0;i<ListFinalLinkInfo.count();i++)
    {
        bool FlagSpurIsNew=true;
        if(!CheckIfLinkSpurIsNew(ListFinalLinkInfo,i)) FlagSpurIsNew=false;
        //连接关系
        QString DT=GetComponentDTBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt());
        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),0);//用于获取链路信号
        QString StrTModelDiag=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),1);//用于诊断
        //获取当前功能子块的镜像号次
        int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),ListFinalLinkInfo.at(i).split(",").at(2));
        //if(ListFinalLinkInfo.at(i).split(",").at(4)!="1") DT=DT+"mirror"+QString::number(NumIndex);
        //从T语言中提取含有Symbol的Current变量名
        qDebug()<<"ListFinalLinkInfo.at(i).split().at(0)="<<ListFinalLinkInfo.at(i).split(",").at(0)<<",ListFinalLinkInfo.at(i).split().at(1)="<<ListFinalLinkInfo.at(i).split(",").at(1);
        QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),QString::number(NumIndex));
        qDebug()<<"TermNameList="<<TermNameList;
        if((ListFinalLinkInfo.at(i).split(",").at(2)==LastLinkId)&&FlagSpurIsNew)
            StrSystemConnection+="\r\n        "+StrLastePort_out+" = "+DT+"."+TermNameList.at(0)+";";
        StrLastePort_out=DT+"."+TermNameList.at(1);
        LastLinkId=ListFinalLinkInfo.at(i).split(",").at(2);

        if(!FlagSpurIsNew) continue;
        if(ListFinalLinkInfo.at(i).split(",").at(3)=="true") continue;

        //将器件实例化添加进StrSystemDefine，将连接关系添加进StrSystemConnection
        StrSystemDefine+="\r\n"+StrTModelDiag.mid(StrTModelDiag.indexOf("class")+5,StrTModelDiag.indexOf("{")-StrTModelDiag.indexOf("class")-5).remove(" ")+" "+DT+";";

        //添加器件class定义
        UpdateComponentString(Strjmpl,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),ListFinalLinkInfo.at(i).split(",").at(4));
        ListFinalLinkInfo[i]=ListFinalLinkInfo.at(i).split(",").at(0)+","+ListFinalLinkInfo.at(i).split(",").at(1)+","+ListFinalLinkInfo.at(i).split(",").at(2)+",true,"+ListFinalLinkInfo.at(i).split(",").at(4)+","+ListFinalLinkInfo.at(i).split(",").at(5);;
        for(int j=i;j<ListFinalLinkInfo.count();j++)
        {
            bool SkipFlag=false;
            if(ListFinalLinkInfo.at(i).split(",").at(1)=="2")
            {
                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(0)==ListFinalLinkInfo.at(i).split(",").at(0)))
                    SkipFlag=true;
            }
            else if(ListFinalLinkInfo.at(i).split(",").at(1)=="3")
            {
                if((ListFinalLinkInfo.at(j).split(",").at(1)=="3")&&(ListFinalLinkInfo.at(j).split(",").at(0)==ListFinalLinkInfo.at(i).split(",").at(0)))
                    SkipFlag=true;
            }
            else
            {
                if(ListFinalLinkInfo.at(j).split(",").at(1)!="2")
                {
                    int idj=GetUnitStripIDBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt());
                    int idi=GetUnitStripIDBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt());

                    if((idj==idi)&&(ListFinalLinkInfo.at(j).split(",").at(1)==ListFinalLinkInfo.at(i).split(",").at(1)))
                        SkipFlag=true;
                }
            }
            if(SkipFlag)
                ListFinalLinkInfo[j]=ListFinalLinkInfo.at(j).split(",").at(0)+","+ListFinalLinkInfo.at(j).split(",").at(1)+","+ListFinalLinkInfo.at(j).split(",").at(2)+",true,"+ListFinalLinkInfo.at(j).split(",").at(4)+","+ListFinalLinkInfo.at(j).split(",").at(5);;
        }
    }
    qDebug()<<"StrSystemDefine="<<StrSystemDefine;
    //根据StrSystemDefine将器件的Structure信息添加进Strhrn和Strini
    GetHrnAndIniInfoOfComponent(Strhrn,Strini,StrSystemDefine);
    qDebug()<<"Strjmpl="<<Strjmpl;
    qDebug()<<"StrSystemDefine="<<StrSystemDefine;
    qDebug()<<"StrSystemConnection="<<StrSystemConnection;
    jmplfile.write((Strjmpl+StrSystemDefine+"\r\n    {"+StrSystemConnection+"\r\n    }\r\n}").toLatin1().data());
    jmplfile.close();

    QFile hrnfile(CurProjectPath+"/test.hrn");
    hrnfile.remove();
    hrnfile.open(QIODevice::WriteOnly);
    hrnfile.write(Strhrn.toLatin1().data());
    hrnfile.close();

    QFile inifile(CurProjectPath+"/test.ini");
    inifile.remove();
    inifile.open(QIODevice::WriteOnly);
    inifile.write(Strini.toLatin1().data());
    inifile.close();

    //调用jmplcompiler生成.xmpl
    QProcess jmplcompiler;
    jmplcompiler.setWorkingDirectory(CurProjectPath);
    QString cmdstr="java -cp C:/TBD/data/l2compilerfull.jar gov.nasa.arc.skunkworks.io.jmpl.JmplCompiler Test test "+CurProjectPath+"/"+CurProjectName+".jmpl";
    jmplcompiler.start(cmdstr);
    jmplcompiler.waitForFinished(-1);

    //dlgFunctionManage->StrSystemDefine=this->StrSystemDefine;
}

void MainWindow::on_BtnRemakeLinkRoad_clicked()
{
    QStringList ListExecSpurID;
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->tableWidgetExecConn->item(i,0)->checkState()==Qt::Checked)
            ListExecSpurID.append(ui->tableWidgetExecConn->item(i,0)->data(Qt::UserRole).toString());
    }
    RemakeLinkRoad(ListExecSpurID);
}

void MainWindow::on_CbAllExecConn_clicked()
{
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        if(ui->CbAllExecConn->isChecked())
            ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Checked);
        else
            ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Unchecked);
    }
}

void MainWindow::UpdateXmplInfo(QString FunctionID)
{
    QStringList ListExecSpurID;
    QSqlQuery QueryFunction(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Function WHERE FunctionID = "+FunctionID;
    QueryFunction.exec(StrSql);
    if(!QueryFunction.next()) return;
    QStringList ExecsList=QueryFunction.value("ExecsList").toString().split(",");

    for(int i=0;i<ExecsList.count();i++)
    {
        QString StrSpur="";
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+ExecsList.at(i).mid(0,ExecsList.at(i).indexOf("."))+"'";
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(GetUnitSpurStrBySymbol_ID(QuerySymbol).split("￤").count()>1)
                {
                    if(ExecsList.at(i).mid(ExecsList.at(i).indexOf(".")+1,ExecsList.at(i).count()-ExecsList.at(i).indexOf(".")-1)==GetUnitSpurStrBySymbol_ID(QuerySymbol))
                    {
                        if(StrSpur!="") StrSpur+=",";
                        StrSpur+=QuerySymbol.value("Symbol_ID").toString();
                    }
                }
                else if(GetUnitSpurStrBySymbol_ID(QuerySymbol)!="")
                {
                    if(ExecsList.at(i).mid(ExecsList.at(i).indexOf(".")+1,ExecsList.at(i).count()-ExecsList.at(i).indexOf(".")-1).remove(" ").split("￤").contains(GetUnitSpurStrBySymbol_ID(QuerySymbol)))
                    {
                        if(StrSpur!="") StrSpur+=",";
                        StrSpur+=QuerySymbol.value("Symbol_ID").toString();
                    }
                }
            }
        }
        ListExecSpurID.append(StrSpur);
    }
    qDebug()<<"ListExecSpurID="<<ListExecSpurID;
    RemakeLinkRoad(ListExecSpurID);

    /*
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
       ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Unchecked);
    }

    QSqlQuery QueryFunction(T_ProjectDatabase);
    QString StrSql="SELECT * FROM Function WHERE FunctionID = "+FunctionID;
    QueryFunction.exec(StrSql);
    if(!QueryFunction.next()) return;
    QStringList ExecsList=QueryFunction.value("ExecsList").toString().split(",");
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        for(int j=0;j<ExecsList.count();j++)
        {
           if(ExecsList.at(j).contains(ui->tableWidgetExecConn->item(i,3)->text())&&ExecsList.at(j).contains(ui->tableWidgetExecConn->item(i,4)->text()))
              ui->tableWidgetExecConn->item(i,0)->setCheckState(Qt::Checked);
        }
    }
    on_BtnRemakeLinkRoad_clicked();*/
}

void MainWindow::StartDiagnose(QString SendCmdStr)
{
    QString modelfileName = CurProjectPath+"/test.xmpl";
    QFile file(modelfileName);
    if(file.exists())
    {
        modelfileName = modelfileName.left(modelfileName.lastIndexOf("."));
        QString program = "C:/TBD/data/l2test.exe";
        QStringList arguments;
        arguments<<modelfileName;//传递到exe的参数
        cmdDiagnose->start(program,arguments);
        cmdStarted = cmdDiagnose->waitForStarted(500);
    }

    QString jmplfileName = CurProjectPath+"/"+CurProjectName+".jmpl";
    QFile jmplfile(jmplfileName);
    if(!jmplfile.open(QIODevice::ReadOnly|QIODevice::Text))  return;
    if(jmplfile.exists())
    {
        qDebug()<<"GetGraphList";
        GetGraphList(jmplfile);
    }
    input_test_point.clear();
    qDebug()<<"GetGraphList ok";

    if(SendCmdStr!="") SendCmd(SendCmdStr,true);
}

void MainWindow::on_BtnStartDiagnose_clicked()
{
    //根据jmpl的系统描述筛选出执行器
    QFile Filejmpl(CurProjectPath+"/"+CurProjectName+".jmpl");
    if(!Filejmpl.open(QIODevice::ReadOnly)) return;
    QString StrJmpl= Filejmpl.readAll();
    StrJmpl=StrJmpl.mid(StrJmpl.indexOf("class Test {")+12,StrJmpl.count()-StrJmpl.indexOf("class Test {")-12);
    StrJmpl=StrJmpl.mid(0,StrJmpl.indexOf("{"));
    QStringList ListStrJmpl=StrJmpl.split(";");
    for(int i=0;i<ui->tableWidgetExecConn->rowCount();i++)
    {
        for(int j=0;j<ListStrJmpl.count();j++)
        {
            if(ListStrJmpl.at(j).contains(ui->tableWidgetExecConn->item(i,3)->text()))
                ui->tableWidgetExecConn ->item(i,0)->setCheckState(Qt::Checked);
        }
    }

    DiagnoseStepNumber=0;
    QsciEdit->clear();
    StartDiagnose("");
}

void MainWindow::GetGraphList(QFile& file)
{
    /*
    QTextStream in(&file);

    QString data = in.readAll();
    data = data.simplified();
    data = data.right(data.count() - data.lastIndexOf("class"));

//    qDebug()<<"data"<<data;

    QStringList data1 = data.split("{");

    //解析连接
    QString connect = data1[2];
    QStringList connect_data = connect.split(";");
    connect_data.removeLast();

//    qDebug()<<"connect";
    for(QString& temp_data : connect_data)
        temp_data.simplified();

    QVector<ArcData> connect_arc;

    QStringList module_data;
    QMultiMap<QString, QString>  port_data;     //用来处理模块内部连接
    QStringList keys;
    for(QString& temp_data : connect_data)
    {
        ArcData temp;
        QStringList temp_list = temp_data.split("=");

        temp.Tail = temp_list[0].simplified();
        temp.Head = temp_list[1].simplified();
        temp.Weight = 1;

        module_data.push_back(temp.Tail);
        module_data.push_back(temp.Head);

        QStringList tail = temp.Tail.split('.');
        QStringList head = temp.Head.split('.');
        QString tail_name = tail[0].simplified();
        QString tail_port = tail[1].simplified();
        QString head_name = head[0].simplified();
        QString head_port = head[1].simplified();

        if(!keys.contains(tail_name))
            keys.push_back(tail_name);
        if(!keys.contains(head_name))
            keys.push_back(head_name);

        if(!port_data.contains(tail_name, tail_port))
            port_data.insert(tail_name, tail_port);
        if(!port_data.contains(head_name, head_port))
            port_data.insert(head_name, head_port);

        connect_arc.push_back(temp);
    }

    //处理内部连接
    for(int i=0; i<keys.count(); i++)
    {
        QList<QString> values = port_data.values(keys[i]);

        if(values.count() == 1)
                continue;

        QVector<bool> visit(values.count(), false);
        for (int m = 0; m < values.size(); m++)
        {
            if(visit[m])    continue;
            visit[m] = true;

            for(int j=m; j<values.size(); j++)
            {
                if(m == j)  continue;

                QStringList m_last_data = values[m].split('_');
                QStringList j_last_data = values[j].split('_');
//                qDebug()<<"i_last_data"<<i_last_data;
//                qDebug()<<"j_last_data"<<j_last_data;
                if(m_last_data[1] == j_last_data[1] && m_last_data[2] == j_last_data[2])
                {
                    ArcData temp;
                    if(m_last_data[0].endsWith('In'))
                    {
                        temp.Tail = keys[i]+'.'+values[m];
                        temp.Head = keys[i]+'.'+values[j];
                        connect_arc.push_back(temp);
                    }
                    else
                    {
                        temp.Head = keys[i]+'.'+values[m];
                        temp.Tail = keys[i]+'.'+values[j];
                        temp.Weight = 1;
                    }

                    connect_arc.push_back(temp);

                    visit[j] = true;
                }
            }
        }
    }

    //根据数据库内的信息处理器件内部功能子块的关系，比如继电器的线圈子块控制着开关子块后面的器件
    QStringList inter_connect_port = GetInterLogicConnect();
    for(int i=0; i<inter_connect_port.count(); i = i+2)
    {
        ArcData temp;

        temp.Tail = inter_connect_port[i];
        temp.Head = inter_connect_port[i+1];
        temp.Weight = 1;

        connect_arc.push_back(temp);
    }
//    qDebug()<<"connect_arc";
//    for(int i=0; i<connect_arc.count(); i++)
//    {
//        qDebug()<<"tail"<<connect_arc[i].Tail
//               <<"head"<<connect_arc[i].Head;
//    }

    module_data.removeDuplicates();

    graph_list->Init(module_data, &connect_arc);

//    graph_list->DisplayNode();

    qDebug()<<"graph";
    QString temp_s = "SP01.ePort_out_p_n";
    graph_list->Display_DFS(&temp_s);

//    GetTestPoint();
    */
}



QList<TestPoint>  MainWindow::GetTestPoint()
{/*
    test_point.clear();

        QStringList candidate_port_name;


        for(int i=0; i<candidate_list.count(); i++)
            candidate_port_name.append(graph_list->GetModulePort(candidate_list[i].FaultSpur.split('.')[0]));

        candidate_port_name.removeDuplicates();
        for(int i=0; i<candidate_port_name.count(); i++)
            test_point.push_back(TestPoint(candidate_port_name[i], 0.0));


        for(int i=0; i<candidate_port_name.count(); i++)
        {
            QStringList front, back;
            graph_list->FindRepeat(candidate_port_name[i], candidate_port_name, front, back);

            test_point[i].calculate = CalculateRank(candidate_port_name[i], front, back);
            test_point[i].test_cost = GetTestCost(test_point[i].point_name);//(double)i/candidate_port_name.count();
  qDebug()<<"GetTestCost,point_name="<<test_point[i].point_name<<",test_cost="<<test_point[i].test_cost;
        }

        //排序前
    //    qDebug()<<"排序前";
    //    for(int i=0; i<test_pt.count(); i++)
    //        qDebug()<<test_pt[i].point_name << QString::number(test_pt[i].calculate);

        RemoveRepeatTestPoint(test_point);
        RemoveTestedPoint(test_point);
        qSort(test_point.begin(),test_point.end(),TestPoint::compareTestPointInformationEntropOnly);

    //    qDebug()<<"排序后";
    //    for(int i=0; i<test_pt.count(); i++)
    //        qDebug()<<test_pt[i].point_name << QString::number(test_pt[i].calculate);

        qDebug()<<"输出测点";
        for(int i=0; i<test_point.count(); i++)
            qDebug()<<test_point[i].point_name<<test_point[i].calculate;
*/
    return test_point;

}




double MainWindow::CalculateRank(const QString& port_name,const QStringList& front, const QStringList& back)
{
    //    if(front.empty())
    //        return INT_MAX;     //表示开头这点不可能

    //去除front里面重复的
    QStringList front_temp, back_temp;

    bool isInput = port_name.contains("In");    //判断是输出还是输入
    if(isInput)
        back_temp.push_back(port_name.split('.')[0]);
    else
        front_temp.push_back(port_name.split('.')[0]);

    for(int i=0; i<front.count(); i++)
    {
        if(!front_temp.contains(front[i].split('.')[0]))
            front_temp.push_back(front[i].split('.')[0]);
    }
    for(int i=0; i<back.count(); i++)
    {
        if(!back_temp.contains(back[i].split('.')[0]))
            back_temp.push_back(back[i].split('.')[0]);
    }


    QVector<double> front_prob, back_prob;

    for(int i=0; i<front_temp.count(); i++)
        front_prob.push_back(module_fault_prob[front_temp[i]]);

    for(int i=0; i<back_temp.count(); i++)
        back_prob.push_back(module_fault_prob[back_temp[i]]);

    //归一化处理
    double all_prob = 0.0;
    for(int i=0; i<front_prob.count(); i++)
        all_prob += front_prob[i];
    for(int i=0; i<back_prob.count(); i++)
        all_prob += back_prob[i];

    for(int i=0; i<front_prob.count(); i++)
        front_prob[i] = front_prob[i] / all_prob;
    for(int i=0; i<back_prob.count(); i++)
        back_prob[i] = back_prob[i] / all_prob;

    double work_well = 1.0;
    for(int i=0; i<front_prob.count(); i++)
    {
        work_well *= 1-front_prob[i];
    }

    double front_rank = 0.0, back_rank = 0.0;
    //计算如果成功后的熵
    for(int i=0; i<back_prob.count(); i++)
    {
        if(back_prob[i]<=0)    back_rank += 0;
        else
            back_rank += back_prob[i] * log(1/back_prob[i]);
    }
    back_rank = back_rank * work_well;
    //计算如果失败后的熵
    for(int i=0; i<front_prob.count(); i++)
    {
        if(front_prob[i]<=0)    front_rank += 0;
        else
            front_rank += front_prob[i] * log(1/front_prob[i]);
    }
    front_rank = front_rank *(1-work_well);

    qDebug()<<"输出概率"<<port_name << QString::number(front_rank) << QString::number(back_rank) <<QString::number(work_well);
    qDebug()<<"front";
    for(int i=0; i<front_temp.count(); i++)
        qDebug()<<front_temp[i]<<front_prob[i];
    qDebug()<<"back";
    for(int i=0; i<back_temp.count(); i++)
        qDebug()<<back_temp[i]<<back_prob[i];

    return front_rank + back_rank;
}



void MainWindow::RemoveRepeatTestPoint(QList<TestPoint>& test_pt)
{/*
    //    QVector<bool> is_have(test_pt.count(), true);

    //    qDebug()<<"输出原始的所有测地";
    //    for(int i=0; i<test_pt.count(); i++)
    //        qDebug()<<test_pt[i].point_name<<test_pt[i].calculate;

    //    for(int i=0; i<test_pt.count(); i++)
    //    {

    //        for(int j=0; j < test_pt.count(); j++)
    //        {
    //            if(abs(test_pt[i].calculate - test_pt[j].calculate) > 0.0001)
    //                continue;
    //            if(test_pt[i].point_name.split('.')[0] == test_pt[j].point_name.split('.')[0])    //同一个器件的端口不进行删除
    //                continue;

    //            bool is_connect = graph_list->isDirectConnect(test_pt[i].point_name, test_pt[j].point_name);
    //            if(is_connect)
    //            {
    //                //删除一条线的
    //                if(test_pt[i].point_name.startsWith('L'))
    //                    is_have[i] = false;
    //                else if(test_pt[j].point_name.startsWith('L'))
    //                    is_have[j] = false;
    //            }
    //        }

    //    }

    //    QList<TestPoint> ans;
    //    for(int i=0; i<is_have.count(); i++)
    //        if(is_have[i])
    //            ans.push_back(test_pt[i]);

    //    test_pt = ans;


        //上面是原来的版本，只考虑加入两个点直接连在一起，那么去掉一个点
        //但是有可能有好几个点连在一起，但是他们的信息熵是不一样的，所以这种情况就选择他们中间不是线的一点，然后信息熵选择他们中间最小的，然后重建一个测点

        QList<TestPoint> new_test_pt;
        QList<QSet<int>> all_connect;      //所有连接超过1的情况，先得到所有的，然后挑选不重复的

        for(int i=0; i<test_pt.count(); i++)
        {
            QSet<int> connect_test_pt;     //注意connect_test_pt保存测点在test_pt中的位置
            connect_test_pt.insert(i);

            for(int j=0; j < test_pt.count(); j++)
            {

                if(test_pt[i].point_name.split('.')[0] == test_pt[j].point_name.split('.')[0])    //同一个器件的端口不进行删除，注意j==i的情况包含在这里了
                    continue;

                bool is_connect = graph_list->isDirectConnect(test_pt[i].point_name, test_pt[j].point_name);
                if(is_connect)
                {
                    connect_test_pt.insert(j);
                }
            }

            if(connect_test_pt.count() == 1)
                continue;

            all_connect.push_back(connect_test_pt);
        }

        QVector<bool> is_delete(all_connect.count(), false);    //如果有共同的数字，那么合并到i处，那么j处的就要删掉
        for(int i=0; i<all_connect.count()-1; i++)
        {
            if(is_delete[i])    continue;

            bool all_is_find = false;
            while(!all_is_find)
            {
                all_is_find = true;
                for(int j=i+1; j<all_connect.count(); j++)
                {
                    if(is_delete[j])    continue;

                    bool is_connect = all_connect[i].intersects(all_connect[j]);        //只要all_connect[i]和all_connect[j]中有一个共同量，那么他们相连
                    if(is_connect)
                    {
                        all_connect[i].unite(all_connect[j]);
                        is_delete[j] = true;
                        all_is_find = false;
                    }
                }
            }

        }



        QVector<bool> is_single(test_pt.count(), false);    //在得到了所有连接的端口后，记录哪些端口是不在这些连接的端口里的，单独拿出来放入结果
        for(int m=0; m<all_connect.count(); m++)
        {
            if(is_delete[m])    continue;

            TestPoint temp_test_pt;
            for(QSet<int>::iterator it = all_connect[m].begin(); it!=all_connect[m].end(); it++)
            {
                is_single[*it] = true;
                if(it ==all_connect[m].begin() )
                {
                    temp_test_pt.point_name = test_pt[*it].point_name;
                    temp_test_pt.calculate = test_pt[*it].calculate;
                    temp_test_pt.test_cost = test_pt[*it].test_cost;
                    continue;
                }

                if(temp_test_pt.point_name.startsWith('L'))
                {
                    if(!test_pt[*it].point_name.startsWith("L"))
                        temp_test_pt.point_name = test_pt[*it].point_name;
                }

                if(temp_test_pt.calculate > test_pt[*it].calculate)
                    temp_test_pt.calculate = test_pt[*it].calculate;

                if(temp_test_pt.test_cost > test_pt[*it].test_cost)
                    temp_test_pt.test_cost = test_pt[*it].test_cost;

            }
            new_test_pt.append(temp_test_pt);
        }

        for(int i=0; i<is_single.count(); i++)
        {
            if(!is_single[i])
                new_test_pt.push_back(test_pt[i]);
        }

        qDebug()<<"整合后";
        for(int i=0; i<new_test_pt.count(); i++)
            qDebug()<<new_test_pt[i].point_name <<new_test_pt[i].calculate<<new_test_pt[i].test_cost;

        test_pt = new_test_pt;
        */
}

void MainWindow::RemoveTestedPoint(QList<TestPoint>& test_pt)
{/*
    QVector<bool> is_have(test_pt.count(), true);

    for(int i=0; i<test_pt.count()-1; i++)
    {

        if(input_test_point.find(test_pt[i].point_name) != input_test_point.end())
        {
            is_have[i] = false;
            continue;
        }

        QString module_name = test_pt[i].point_name.split('.')[0];      //加入是一个器件的两个端口，不删除
        for(QMap<QString, int>::iterator it=input_test_point.begin(); it != input_test_point.end(); it++)
        {
            if(module_name == it.key().split('.')[0])    //同一个器件的端口不进行删除
                continue;

            bool is_connect = graph_list->isDirectConnect(test_pt[i].point_name, it.key());
            if(is_connect)
                is_have[i] = false;
        }
    }

    QList<TestPoint> ans;
    for(int i=0; i<is_have.count(); i++)
        if(is_have[i])
            ans.push_back(test_pt[i]);

    test_pt = ans;
    */
}

QStringList MainWindow::GetInterLogicConnect()
{

    QStringList ans;
    return ans;
    QSqlQuery temp_connect = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT Symbol_ID,Equipment_ID, InterConnect from Symbol WHERE InterConnect IS NOT NULL AND InterConnect IS NOT ''";
    temp_connect.exec(SqlStr);
    while(temp_connect.next())
    {
        QString head, tail;

        QString id = temp_connect.value(0).toString();
        QString equip_id = temp_connect.value(1).toString();
        QString inter_connect = temp_connect.value(2).toString();

        QStringList head_port = GetTermNameListBySymbolID(id,"");
        QStringList tail_port = GetTermNameListBySymbolID(inter_connect,"");

        QSqlQuery module_name = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString sql_module_name = "SELECT DT, TModel from Equipment WHERE Equipment_ID = " + equip_id;
        module_name.exec(sql_module_name);

        if(module_name.next())
        {
            QString module = module_name.value(0).toString();
            QString T_model = module_name.value(1).toString();

            QString test_head1 = "ePort_out_" + head_port[0] + '_' + head_port[1];
            QString test_head2 = "ePort_out_" + head_port[1] + '_' + head_port[0];
            if(T_model.contains(test_head1))
                head = module + '.' + test_head1;
            else
                head = module + '.' + test_head2;

            QString test_tail1 = "ePort_in_" + tail_port[0] + '_' + tail_port[1];
            QString test_tail2 = "ePort_in_" + tail_port[1] + '_' + tail_port[0];
            if(T_model.contains(test_tail1))
                tail = module + '.' + test_tail1;
            else
                tail = module + '.' + test_tail2;

            //注意先尾部后头部；
            ans.push_back(tail);
            ans.push_back(head);
        }
    }

    return ans;

}


void MainWindow::SendCmd(QString SendCmdStr,bool print)
{
    ClearListRedEntity();
    ui->tableWidgetDiagResult->setRowCount(0);
    ui->tableWidgetTestPoint->setRowCount(0);
    cmdDiagnose->write(SendCmdStr.toLocal8Bit()+ '\n');
    if(print)
    {
        if(QsciEdit->text()!="") QsciEdit->append("\r\n");
        QsciEdit->append(SendCmdStr);
    }
    //张新宇
    candidate_list.clear();
    GetInputTestPoint(SendCmdStr);
}
void MainWindow::on_BtnSendCmd_clicked()
{
    QString Sendcmd=QsciEdit->text();
    while(Sendcmd.endsWith('\n')) Sendcmd.chop(1);
    SendCmd(Sendcmd.toLocal8Bit(),false);
}

void MainWindow::GetInputTestPoint(QString& cmd)
{
    QStringList data = cmd.split("\n");
    for(int i=0; i<data.count(); i++)
    {
        data[i] = data[i].simplified();
        if(data[i].startsWith("assign"))
            continue;

        data.removeAt(i);
        i--;
    }

    for(int i=0; i<data.count(); i++)
    {
        int start_pos = data[i].indexOf('.');
        int end_pos = data[i].indexOf('=');

        data[i] = data[i].mid(start_pos+1, end_pos-start_pos-1);
        data[i] = data[i].simplified();
    }

    for(int m=0; m<data.count(); m++)
    {
        if(input_test_point.find(data[m]) == input_test_point.end())
            input_test_point[data[m]] = 1;
    }

}

void MainWindow::on_BtnEndDiagnose_clicked()
{ 
    ClearListRedEntity();
    ClearDrawArrow();
    cmdDiagnose->waitForFinished(500);
    cmdDiagnose->close();
    ui->tableWidgetDiagResult->setRowCount(0);
    ui->tableWidgetDiagResult->setRowCount(1);
    ui->tableWidgetDiagResult->setItem(ui->tableWidgetDiagResult->rowCount()-1,0,new QTableWidgetItem("诊断未开始"));
    ui->tableWidgetTestPoint->setRowCount(0);
}

//Category=0:元件 Category=2：导线标号 3：导线 4：connector 5:黑盒Text
formaxwidget* MainWindow::GetOpenedDwgaxwidget(QString Symbol_Handle,int Category)
{
    QString Page_ID;
    if(Category==0)
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_Handle= '"+Symbol_Handle+"'";
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            if(QuerySymbol.value("Symbol_Handle").toString()=="") return nullptr;
            Page_ID=QuerySymbol.value("Page_ID").toString();
        }
    }
    else if(Category==2)
    {
        QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM JXB WHERE ConnectionNumber_Handle= '"+Symbol_Handle+"'";
        QueryJXB.exec(SqlStr);
        if(QueryJXB.next())
        {
            if(QueryJXB.value("ConnectionNumber_Handle").toString()=="") return nullptr;
            Page_ID=QueryJXB.value("Page_ID").toString();
        }
    }
    else if(Category==3)
    {
        QSqlQuery QueryLine=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Line WHERE Wires_Handle= '"+Symbol_Handle+"'";
        QueryLine.exec(SqlStr);
        if(QueryLine.next())
        {
            Page_ID=QueryLine.value("Page_ID").toString();
        }
    }
    else if(Category==4)
    {
        QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Connector WHERE Connector_Handle= '"+Symbol_Handle+"'";
        QueryConnector.exec(SqlStr);
        if(QueryConnector.next())
        {
            Page_ID=QueryConnector.value("Page_ID").toString();
        }
    }
    else if(Category==5)
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE DT_Handle= '"+Symbol_Handle+"'";
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next())
        {
            if(QuerySymbol.value("DT_Handle").toString()=="") return nullptr;
            Page_ID=QuerySymbol.value("Page_ID").toString();
        }
    }

    if(Page_ID!="")
    {
        QString dwgfilename=GetPageNameByPageID(Page_ID.toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) return nullptr;
        formaxwidget *formMxdraw;
        for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
        {
            //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
            if(ui->mdiArea->subWindowList().at(i)->windowTitle()==dwgfilename)
            {
                formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
                return formMxdraw;
            }
        }
    }
    return nullptr;
}

QString MainWindow::GetEquipment_IDByDT(QString DT)
{
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        return QueryEquipment.value("Equipment_ID").toString();
    }
    return "";
}

//根据OneComponentInfo.CurrentInOutName查找对应的TermID,格式为TermID,Category(0器件 1端子排 2导线),正负极(1正 2负),SymbolID/JXB_ID
QString MainWindow::GetValidTermIDString(QString OneComponentInfo,QString CurrentInOutName)
{
    qDebug()<<"GetValidTermIDString,OneComponentInfo="<<OneComponentInfo<<",CurrentInOutName="<<CurrentInOutName;
    QString DT=OneComponentInfo;
    QString ValidLocalTermID;
    if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr;
    SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        bool FlagFindLine=false;
        QString Equipment_ID=QueryEquipment.value("Equipment_ID").toString();
        QString TModel=QueryEquipment.value("TModel").toString();
        //QStringList ListTModel=TModelDiag.split(";");
        QString ValidSymbol_ID;
        QStringList ListTermID;
        QString TmpStr=CurrentInOutName;
        //在TModel中找到CurrentInOutName映射的端口号
        QStringList ListTermName=GetListTermNameByTModel(TModel,CurrentInOutName);//TmpStr.remove("ePort_out_").remove("ePort_in_").split("_");
        qDebug()<<"GetListTermNameByTModel,ListTermName="<<ListTermName;
        //根据ListTermName在Symbol中找到匹配的功能子块的ValidSymbol_ID
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+Equipment_ID+"'";
        QuerySymbol.exec(SqlStr);
        while(QuerySymbol.next())
        {
            //qDebug()<<"Symbol_ID="<<QuerySymbol.value("Symbol_ID").toString();
            ListTermID.clear();
            bool FlagFindSymbol=false;
            QString Symbol_ID=QuerySymbol.value("Symbol_ID").toString();
            int SymbolType=0;//普通：0 源：1 执行器：2
            if(QuerySymbol.value("SourceConn").toBool()) SymbolType=1;
            else if(QuerySymbol.value("ExecConn").toBool()) SymbolType=2;
            QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+Symbol_ID+"'";
            QuerySymb2TermInfo.exec(SqlStr);
            while(QuerySymb2TermInfo.next())
            {
                if(ListTermName.count()>0)
                {
                    if(ListTermName.contains(QuerySymb2TermInfo.value("ConnNum").toString()))
                    {
                        FlagFindSymbol=true;
                        ListTermID.append(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString());
                        break;
                    }
                }
            }
            if(!FlagFindSymbol) continue;
            //找到正确的ValidSymbol_ID,然后根据ListTermName来确定测试点端口号，同时ValidSymbol_ID必须在ListFinalLinkInfo中存在；如果功能子块是源或者执行器，则根据端口的连线在正极回路确定本地端口；
            ValidSymbol_ID=Symbol_ID;
            if(SymbolType==0)//普通传递功能子块
            {
                for(int i=0;i<ListFinalLinkInfo.count();i++)
                {
                    if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidSymbol_ID)&&(ListFinalLinkInfo.at(i).split(",").at(1)=="0"))
                    {
                        ValidLocalTermID=ListTermID.at(0)+",0,"+ListFinalLinkInfo.at(i).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                        FlagFindLine=true;
                        break;
                    }
                }
            }
            else//源或执行器
            {
                for(int i=0;i<ListFinalLinkInfo.count();i++)
                {
                    if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidSymbol_ID)&&(ListFinalLinkInfo.at(i).split(",").at(1)=="0"))
                    {
                        if(SymbolType==1)//源，检索单链往后传递的第一根正极导线
                        {
                            for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                            {
                                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(5)=="1"))
                                {
                                    //在JXB数据库中检索与ListFinalLinkInfo.at(j).split(",").at(0)导线相连的两个Symb2TermInfo_ID，其中一个必然连向ValidSymbol_ID
                                    QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
                                    SqlStr="SELECT * FROM JXB WHERE JXB_ID = "+ListFinalLinkInfo.at(j).split(",").at(0);
                                    QueryJXB.exec(SqlStr);
                                    if(QueryJXB.next())
                                    {
                                        QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
                                        QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
                                        QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
                                        QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
                                        if((Symb1_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb1_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb1_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                        if((Symb2_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb2_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb2_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                        }//end of if(SymbolType==1)//源，检索单链往后传递的第一根正极导线
                        else if(SymbolType==2)//执行器，检索单链往前传递的第一根正极导线
                        {
                            for(int j=i-1;j>=0;j--)
                            {
                                if((ListFinalLinkInfo.at(j).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(j).split(",").at(5)=="1"))
                                {
                                    //在JXB数据库中检索与ListFinalLinkInfo.at(j).split(",").at(0)导线相连的两个Symb2TermInfo_ID，其中一个必然连向ValidSymbol_ID
                                    QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
                                    SqlStr="SELECT * FROM JXB WHERE JXB_ID = "+ListFinalLinkInfo.at(j).split(",").at(0);
                                    QueryJXB.exec(SqlStr);
                                    if(QueryJXB.next())
                                    {
                                        QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
                                        QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
                                        QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
                                        QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
                                        if((Symb1_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb1_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb1_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                        if((Symb2_Category=="0")&&(QString::number(GetSymbolIDByTermID(0,Symb2_ID))==ValidSymbol_ID))
                                        {
                                            ValidLocalTermID=Symb2_ID+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }//end of for(int j=i-1;j>=0;j--)
                        }
                        else//普通功能子块
                        {
                            ValidLocalTermID=ListTermID.at(0)+",0,"+ListFinalLinkInfo.at(i).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                            FlagFindLine=true;
                            break;
                        }
                    }
                    if(FlagFindLine) break;
                }//end of for(int i=0;i<ListFinalLinkInfo.count();i++)
            }
            /*
            //绘制测试点箭头,根据ListFinalLinkInfo和JXB确定本地端口和相对端口
            //本地端口：查看与ValidSymbol_ID连接的功能子块，然后根据ListFinalLinkInfo的顺序确定端口
            //qDebug()<<"ValidSymbol_ID="<<ValidSymbol_ID<<",ListFinalLinkInfo="<<ListFinalLinkInfo;
            for(int i=0;i<ListTermID.count();i++)
            {
                //qDebug()<<"i="<<i;
                QSqlQuery QueryJXB=QSqlQuery(T_ProjectDatabase);
                SqlStr="SELECT * FROM JXB WHERE (Symb1_Category= '0' AND Symb1_ID = '"+ListTermID.at(i)+"') OR (Symb2_Category= '0' AND Symb2_ID = '"+ListTermID.at(i)+"')";
                QueryJXB.exec(SqlStr);
                while(QueryJXB.next())
                {
                    for(int j=0;j<ListFinalLinkInfo.count();j++)
                    {
                        if((ListFinalLinkInfo.at(j).split(",").at(0)==ValidSymbol_ID)&&(ListFinalLinkInfo.at(j).split(",").at(1)=="0"))
                        {
                            //qDebug()<<"find ,j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                            //如果是执行器，则执行器之前的那根导线为负极的线
                            if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")
                            {
                  //qDebug()<<"是执行器";
                                if(CurrentInOutName.contains("ePort_in"))
                                {
                  //qDebug()<<"JXB_ID="<<QueryJXB.value("JXB_ID").toString();
                                    for(int k=j-1;k>=0;k--)
                                    {
                                        if((QueryJXB.value("JXB_ID").toString()==ListFinalLinkInfo.at(k).split(",").at(0))&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)=="1"))
                                        {
                                            ValidLocalTermID=ListTermID.at(i)+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                                else if(CurrentInOutName.contains("ePort_out"))
                                {
                                    for(int k=j-1;k>=0;k--)
                                    {
                                        if((QueryJXB.value("JXB_ID").toString()==ListFinalLinkInfo.at(k).split(",").at(0))&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)=="1"))
                                        {
                                            if(i==0)  ValidLocalTermID=ListTermID.at(1)+",0,2,"+ValidSymbol_ID;
                                            else ValidLocalTermID=ListTermID.at(0)+",0,2,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="0")//是源
                            {
                                if(CurrentInOutName.contains("ePort_out"))
                                {
                                    for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                                    {
                                        if((QueryJXB.value("JXB_ID").toString()==ListFinalLinkInfo.at(k).split(",").at(0))&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)=="1"))
                                        {
                                            ValidLocalTermID=ListTermID.at(0)+",0,1,"+ValidSymbol_ID;
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                            }
                            else//不是执行器
                            {
                  //qDebug()<<"不是执行器";
                                if(CurrentInOutName.contains("ePort_in"))
                                {
                                    for(int k=j-1;k>=0;k--)
                                    {
               //qDebug()<<"k="<<k<<",ListFinalLinkInfo.at(k)="<<ListFinalLinkInfo.at(k);
                                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                                        if((ListFinalLinkInfo.at(k).split(",").at(0)==QueryJXB.value("JXB_ID").toString())&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5)))
                                        {
                                            qDebug()<<"find ,k="<<k;
                                            ValidLocalTermID=ListTermID.at(i)+",0,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }
                                else if(CurrentInOutName.contains("ePort_out"))
                                {
                                    for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                                    {
                                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                                        if((ListFinalLinkInfo.at(k).split(",").at(0)==QueryJXB.value("JXB_ID").toString())&&(ListFinalLinkInfo.at(k).split(",").at(1)=="2")&&(ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5)))
                                        {
                                            qDebug()<<"find ,k="<<k;
                                            ValidLocalTermID=ListTermID.at(i)+",0,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+ValidSymbol_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                                            FlagFindLine=true;
                                            break;
                                        }
                                    }
                                }//end of else if(CurrentInOutName.contains("ePort_out"))
                            }
                        }
                        if(FlagFindLine) break;
                    }//end of for(int j=0;j<ListFinalLinkInfo.count();j++)
                    if(FlagFindLine) break;
                }//end of while(QueryJXB.next())
                if(FlagFindLine) break;
            }//end of for(int i=0;i<ListTermID.count();i++)
            */
            if(FlagFindLine) break;
        }//end of while(QuerySymbol.next())
    }//end of if(QueryEquipment.next())

    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+DT+"'";
    QueryJXB.exec(SqlStr);
    if(QueryJXB.next())
    {
        bool FlagFindLocalTerm=false;
        //找到ListFinalLinkInfo中与当前导线的下一个器件或导线的
        QString JXB_ID=QueryJXB.value("JXB_ID").toString();
        QString Symb1_ID=QueryJXB.value("Symb1_ID").toString();
        QString Symb1_Category=QueryJXB.value("Symb1_Category").toString();
        QString Symb2_ID=QueryJXB.value("Symb2_ID").toString();
        QString Symb2_Category=QueryJXB.value("Symb2_Category").toString();
        //qDebug()<<"ValidJXB_ID="<<JXB_ID<<",Symb1_ID="<<Symb1_ID<<",Symb2_ID="<<Symb2_ID<<",ListFinalLinkInfo="<<ListFinalLinkInfo;
        for(int j=0;j<ListFinalLinkInfo.count();j++)
        {
            if((ListFinalLinkInfo.at(j).split(",").at(0)==JXB_ID)&&(ListFinalLinkInfo.at(j).split(",").at(1)=="2"))
            {
                //qDebug()<<"find ,j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                QString NextID,NextCategory;
                if(CurrentInOutName.contains("ePort_out"))
                {
                    for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                    {
                        //qDebug()<<"Cur k="<<k<<",ListFinalLinkInfo.at(k)="<<ListFinalLinkInfo.at(k);
                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                        //如果k是执行器了，那就选执行器
                        bool FlagIsExec=false;
                        if(ListFinalLinkInfo.at(k).split(",").at(5)=="3")
                            FlagIsExec=true;
                        if((ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5))||FlagIsExec)
                        {
                            //qDebug()<<"find ,k="<<k<<",NextID="<<ListFinalLinkInfo.at(k).split(",").at(0);
                            NextID=ListFinalLinkInfo.at(k).split(",").at(0);
                            NextCategory=ListFinalLinkInfo.at(k).split(",").at(1);
                            break;
                            //qDebug()<<"NextCategory="<<NextCategory;

                        }
                    }//end of for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                }//end of if(CurrentInOutName.contains("ePort_out"))
                else if(CurrentInOutName.contains("ePort_in"))
                {
                    for(int k=j-1;k>=0;k--)
                    {
                        //qDebug()<<"Cur k="<<k<<",ListFinalLinkInfo.at(k)="<<ListFinalLinkInfo.at(k);
                        if(ListFinalLinkInfo.at(k).split(",").at(2)!=ListFinalLinkInfo.at(j).split(",").at(2)) break;
                        //如果k是执行器了，那就选执行器
                        bool FlagIsExec=false;
                        bool FlagIsSource=false;
                        if(ListFinalLinkInfo.at(k).split(",").at(5)=="3")
                            FlagIsExec=true;
                        if(ListFinalLinkInfo.at(k).split(",").at(5)=="0")
                            FlagIsSource=true;
                        if((ListFinalLinkInfo.at(k).split(",").at(5)==ListFinalLinkInfo.at(j).split(",").at(5))||FlagIsExec||FlagIsSource)
                        {
                            //qDebug()<<"find ,k="<<k<<",NextID="<<ListFinalLinkInfo.at(k).split(",").at(0);
                            NextID=ListFinalLinkInfo.at(k).split(",").at(0);
                            NextCategory=ListFinalLinkInfo.at(k).split(",").at(1);
                            //qDebug()<<"NextCategory="<<NextCategory;
                            break;


                        }
                    }//end of for(int k=j+1;k<ListFinalLinkInfo.count();k++)
                }//end of else if(CurrentInOutName.contains("ePort_in"))

                if(NextCategory=="0")//与导线相连的是器件子块
                {
                    QStringList ListTermID;
                    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                    SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+NextID+"'";
                    QuerySymb2TermInfo.exec(SqlStr);
                    while(QuerySymb2TermInfo.next())
                    {
                        ListTermID.append(QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString());
                    }
                    //qDebug()<<"ListTermID="<<ListTermID;
                    if(ListTermID.count()==2)
                    {
                        if(ListTermID.at(0)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//功能子块ID,Category（器件为0，端子为1，导线为2）,正负级（正极为1，负极为2）
                        else if(ListTermID.at(1)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                        else if(ListTermID.at(0)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                        else if(ListTermID.at(1)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                        FlagFindLocalTerm=true;
                        break;
                    }
                    else if(ListTermID.count()==1)
                    {
                        int SymbolID=GetSymbolIDByTermID(0,Symb1_ID);
                        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                        SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+QString::number(SymbolID);
                        QuerySymbol.exec(SqlStr);
                        if(QuerySymbol.next())
                        {
                            if(QuerySymbol.value("SourceConn").toBool()) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                            else ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;
                            FlagFindLocalTerm=true;
                            break;
                        }
                    }
                }//end of if(NextCategory=="0")//与导线相连的是器件子块
                else if(NextCategory=="2")//与导线相连的是导线
                {
                    QStringList ListTermID;
                    QSqlQuery QueryJXB2=QSqlQuery(T_ProjectDatabase);
                    SqlStr="SELECT * FROM JXB WHERE JXB_ID= "+NextID;
                    QueryJXB2.exec(SqlStr);
                    if(QueryJXB2.next())
                    {
                        ListTermID.append(QueryJXB2.value("Symb1_ID").toString());
                        ListTermID.append(QueryJXB2.value("Symb2_ID").toString());
                    }
                    //qDebug()<<"ListTermID="<<ListTermID;
                    if(ListTermID.count()==2)
                    {
                        if(ListTermID.at(0)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb1_ID.toInt()));
                        else if(ListTermID.at(1)==Symb1_ID) ValidLocalTermID=Symb1_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb1_ID.toInt()));
                        else if(ListTermID.at(0)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb2_ID.toInt()));
                        else if(ListTermID.at(1)==Symb2_ID) ValidLocalTermID=Symb2_ID+",2,"+ListFinalLinkInfo.at(j).split(",").at(5)+","+JXB_ID;//QString::number(GetSymbolIDByTermID(0,Symb2_ID.toInt()));
                        FlagFindLocalTerm=true;
                        break;
                    }
                }
                if(FlagFindLocalTerm) break;
            }
        }//end of for(int j=0;j<ListFinalLinkInfo.count();j++)
    }//end of if(QueryJXB.next())
    qDebug()<<"Get ValidLocalTermID="<<ValidLocalTermID;
    return ValidLocalTermID;
}

QStringList MainWindow::GetTestPointTermID(QString OneComponentInfo,QString CurrentInOutName)
{
    //qDebug()<<"DrawTestPoint,OneComponentInfo="<<OneComponentInfo<<",CurrentInOutName="<<CurrentInOutName;
    //QStringList ListFinalLinkInfo=MakeListFinalLinkInfo();
    QString ValidLocalTermID=GetValidTermIDString(OneComponentInfo,CurrentInOutName);
    QString ValidRelativeTermID;
    //根据ValidLocalTermID查找相对测试点，正极则寻找相对地，负极则寻找相对正
    qDebug()<<"ValidLocalTermID="<<ValidLocalTermID;
    QString RelativePole;
    if(ValidLocalTermID.split(",").at(2)=="1") RelativePole="2";
    else RelativePole="1";
    bool FlagFind=false;
    for(int i=0;i<ListFinalLinkInfo.count();i++)//ListFinalLinkInfo:(SymbolID,Category,LinkID,Checked,Count,+-)
    {
        //找到测试点所在的ListFinalLinkInfo位置
        if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID.split(",").at(3))&&(ListFinalLinkInfo.at(i).split(",").at(1)==ValidLocalTermID.split(",").at(1)))
        {
            //当前选择的测试点是执行器，向前搜索
            if(ListFinalLinkInfo.at(i).split(",").at(5)=="3")
            {
                for(int j=i-1;j>=0;j--)
                {
                    if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                    if((ListFinalLinkInfo.at(j).split(",").at(5)==RelativePole)||(ListFinalLinkInfo.at(j).split(",").at(5)=="0"))
                    {
                        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                        int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                        QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                        ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[1]);
                        FlagFind=true;
                        break;
                    }
                }
            }
            else //if(ListFinalLinkInfo.at(i).split(",").at(5)=="0")//非执行器，向后搜索
            {
                for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                {
                    if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                    if((ListFinalLinkInfo.at(j).split(",").at(5)==RelativePole)||(ListFinalLinkInfo.at(j).split(",").at(5)=="3"))
                    {
                        QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                        int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                        QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                        ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0]);
                        FlagFind=true;
                        break;
                    }
                }
            }
        }
        if(FlagFind) break;
    }
    qDebug()<<"ValidRelativeTermID="<<ValidRelativeTermID;
    /*
    if(ValidLocalTermID.split(",").at(2)=="1")//寻找相对地
    {
        bool FlagFind=false;
        for(int i=0;i<ListFinalLinkInfo.count();i++)
        {
            if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID.split(",").at(3))&&(ListFinalLinkInfo.at(i).split(",").at(1)==ValidLocalTermID.split(",").at(1)))
            {
                //当前选择的测试点是执行器，向前搜索
                if(ListFinalLinkInfo.at(i).split(",").at(5)=="3")
                {
                    QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),0);
                    int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),ListFinalLinkInfo.at(i).split(",").at(2));
                    QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1),QString::number(NumIndex));
                    ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(i).split(",").at(0),ListFinalLinkInfo.at(i).split(",").at(1).toInt()),TermNameList[0].replace("ePort_in","ePort_out"));//currentIn
                    FlagFind=true;
                }
                else if(ListFinalLinkInfo.at(i).split(",").at(5)=="0")//当前选择的测试点是源
                {
                    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                    QString SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+ValidLocalTermID.split(",").at(0);
                    QuerySymb2TermInfo.exec(SqlStr);
                    if(QuerySymb2TermInfo.next())
                    {
                        QString ConnNum=QuerySymb2TermInfo.value("ConnNum").toString();
                        QString tmpStr=CurrentInOutName;
                        QString AnotherConnNum=tmpStr.remove("ePort_in").remove("ePort_out").remove(ConnNum).remove("_");
                        QString DT;
                        int Equipment_ID=GetUnitStripIDByTermID(0,ValidLocalTermID.split(",").at(0).toInt(),DT);
                        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                        SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+QString::number(Equipment_ID)+"'";
                        QuerySymbol.exec(SqlStr);
                        while(QuerySymbol.next())
                        {
                            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+QuerySymbol.value("Symbol_ID").toString()+"' AND ConnNum = '"+AnotherConnNum+"'";
                            QuerySymb2TermInfo.exec(SqlStr);
                            if(QuerySymb2TermInfo.next())
                            {
                                ValidRelativeTermID=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()+",0,2,"+QuerySymbol.value("Symbol_ID").toString();
                                FlagFind=true;
                            }
                        }
                    }
                }
                else//当前选择的测试点是器件或者导线
                {
                    if(CurrentInOutName.contains("ePort_in"))
                    {
                        for(int j=i-1;j>=0;j--)
                        {
                            //qDebug()<<"j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                            if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                            if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            {
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(1));//ePort_out
                                FlagFind=true;
                                break;
                            }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="0")//源
                            {
                                //源只能通过GetValidTermIDString找到源的正极，需要去找匹配的负极
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(1));//ePort_out
                                //查找与ValidRelativeTermID.split(",").at(0)匹配的n极
                                QString Str_n=TermNameList.at(1);
                                QStringList Listpn=Str_n.remove("ePort_out_").split("_");
                                bool FlagFindRelativeTermID=false;
                                QString Equipment_ID=GetEquipment_IDByDT(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()));
                                QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
                                QString SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+Equipment_ID+"'";
                                QuerySymbol.exec(SqlStr);
                                while(QuerySymbol.next())
                                {

                                    QString Symbol_ID=QuerySymbol.value("Symbol_ID").toString();
                                    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
                                    SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID= '"+Symbol_ID+"'";
                                    QuerySymb2TermInfo.exec(SqlStr);
                                    while(QuerySymb2TermInfo.next())
                                    {
                                        if(Listpn.contains(QuerySymb2TermInfo.value("ConnNum").toString())&&(ValidRelativeTermID.split(",").at(0)!=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()))
                                        {
                                            FlagFindRelativeTermID=true;
                                            ValidRelativeTermID=QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString()+",0,2,"+Symbol_ID;
                                            break;
                                        }
                                    }
                                    if(FlagFindRelativeTermID) break;
                                }//end of while(QuerySymbol.next())
                            }
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                            {
                                //因为执行器没有ePort_out_X_X,所以采用ePort_in_X_X的_X_X生成ePort_out_X_X
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0].replace("ePort_in","ePort_out"));
                                FlagFind=true;
                                break;
                            }
                        }
                    }//end of if(CurrentInOutName.contains("ePort_in"))
                    else
                    {
                        for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                        {
                            //qDebug()<<"j="<<j<<",ListFinalLinkInfo.at(j)="<<ListFinalLinkInfo.at(j);
                            if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                            if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            {
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(0));//currentIn
                                FlagFind=true;
                                break;
                            }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                            else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                            {
                                //因为执行器没有ePort_out_X_X,所以采用ePort_in_X_X的_X_X生成ePort_out_X_X
                                //从T语言中提取含有Symbol的Current变量名
                                QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                                int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                                QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                                ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0].replace("ePort_in","ePort_out"));
                                FlagFind=true;
                                break;
                            }
                        }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                    }
                }
            }//end of if(ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID)
            if(FlagFind) break;
        }//end of for(int i=0;i<ListFinalLinkInfo.count();i++)
    }//end of if(ValidLocalTermID.split(",").at(2)=="1")//寻找相对地
    else if(ValidLocalTermID.split(",").at(2)=="2")//寻找相对正
    {
        bool FlagFind=false;
        for(int i=0;i<ListFinalLinkInfo.count();i++)
        {
            if((ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID.split(",").at(3))&&(ListFinalLinkInfo.at(i).split(",").at(1)==ValidLocalTermID.split(",").at(1)))
            {
                if(CurrentInOutName.contains("ePort_in"))
                {
                    for(int j=i-1;j>=0;j--)
                    {
                        if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                        if((ListFinalLinkInfo.at(j).split(",").at(5)=="1")||(ListFinalLinkInfo.at(j).split(",").at(5)=="0"))
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(1));
                            FlagFind=true;
                            break;
                        }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                        else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0]);
                            //ValidRelativeTermID=GetValidTermIDString(ListFinalLinkInfo,GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0).toInt(),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),"ePort_in");
                            FlagFind=true;
                            break;
                        }
                    }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                }//end of if(CurrentInOutName.contains("ePort_in"))
                else
                {
                    for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                    {
                        if(ListFinalLinkInfo.at(j).split(",").at(2)!=ListFinalLinkInfo.at(i).split(",").at(2)) break;
                        if(ListFinalLinkInfo.at(j).split(",").at(5)=="1")
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList.at(0));
                            FlagFind=true;
                            break;
                        }//end of if(ListFinalLinkInfo.at(j).split(",").at(5)=="2")
                        else if(ListFinalLinkInfo.at(j).split(",").at(5)=="3")//执行器
                        {
                            //从T语言中提取含有Symbol的Current变量名
                            QString StrTModel=GetTModelOfComponent(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),0);
                            int NumIndex= GetMirrorIndex(ListFinalLinkInfo,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),ListFinalLinkInfo.at(j).split(",").at(2));
                            QStringList TermNameList=GetCurrentNameBySymbolID(StrTModel,ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1),QString::number(NumIndex));
                            ValidRelativeTermID=GetValidTermIDString(GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),TermNameList[0]);
                            //ValidRelativeTermID=GetValidTermIDString(ListFinalLinkInfo,GetComponentDTBySymbolID(ListFinalLinkInfo.at(j).split(",").at(0).toInt(),ListFinalLinkInfo.at(j).split(",").at(1).toInt()),"ePort_in");
                            FlagFind=true;
                            break;
                        }
                    }//end of for(int j=i+1;j<ListFinalLinkInfo.count();j++)
                }
            }//end of if(ListFinalLinkInfo.at(i).split(",").at(0)==ValidLocalTermID)
            if(FlagFind) break;
        }//end of for(int i=0;i<ListFinalLinkInfo.count();i++)
    }//end of if(ValidLocalTermID.split(",").at(2)=="1")//寻找相对地
    */
    return {ValidLocalTermID,ValidRelativeTermID};
}

void MainWindow::DrawTestPoint(QString OneComponentInfo,QString CurrentInOutName)
{
    QStringList ListValidTermID=GetTestPointTermID(OneComponentInfo,CurrentInOutName);
    //将两个TermID的位置发送给dlgDiagnoseUI
    DrawArrow(ListValidTermID);
    LoadTestPointInfo(OneComponentInfo,CurrentInOutName,ListValidTermID);
    LoadUserTestInfo();//自定义测试显示
}

//自定义测试显示
void MainWindow::LoadUserTestInfo()
{
    ListUserTest.clear();
    QSqlQuery QueryUserTest=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM UserTest WHERE FunctionID= '"+CurFunctionID+"'";
    QueryUserTest.exec(SqlStr);
    while(QueryUserTest.next())
    {
        QString Condition=QueryUserTest.value("Condition").toString();
        QStringList ListCondition=Condition.split(",");
        bool FlagBreak=false;
        for(QString StrOneCondition:ListCondition)//满足一个条件就可以
        {
            if(StrOneCondition.contains("="))//故障模式判断
            {
                for(CandidateData m_CandidateData:candidate_list)
                {
                    if((m_CandidateData.FaultSpur==StrOneCondition.split("=").at(0))&&(m_CandidateData.modeTransition==StrOneCondition.split("=").at(1)))
                    {
                        ListUserTest.append(QueryUserTest.value("Name").toString()+":"+QueryUserTest.value("Test").toString());
                        FlagBreak=true;
                        break;
                    }
                }
            }
            else//包含判断
            {
                for(CandidateData m_CandidateData:candidate_list)
                {
                    if(m_CandidateData.FaultSpur==StrOneCondition)
                    {
                        //将QueryUserTest.value("Test").toString()不全部在当前的观测中
                        QString Test=QueryUserTest.value("Test").toString();
                        QStringList ListTest=Test.split(",");
                        QString ValidTest;
                        qDebug()<<"ListTest="<<ListTest<<",ListAllObserve="<<ListAllObserve;
                        for(QString StrCurTest:ListTest)
                        {
                            bool FlagObserveExisted=false;
                            for(int i=0;i<ListAllObserve.count();i++)
                            {
                                if(ListAllObserve.at(i).contains(StrCurTest))
                                {
                                    FlagObserveExisted=true;
                                    break;
                                }
                            }
                            if(!FlagObserveExisted)
                            {
                                if(ValidTest!="") ValidTest+=",";
                                ValidTest+=StrCurTest;
                            }
                        }
                        if(ValidTest!="") ListUserTest.append(QueryUserTest.value("Name").toString()+":"+ValidTest);
                        FlagBreak=true;
                        break;
                    }
                }
            }
            if(FlagBreak) break;
        }//end of for(QString StrOneCondition:ListCondition)//满足一个条件就可以
    }//end of while(QueryUserTest.next())

    //刷新UI界面，按钮闪烁，点击按钮可查看自定义测试
    if(ListUserTest.count()>0)
    {
        ui->BtnUserTest->setEnabled(true);
    }
    else
    {
        ui->BtnUserTest->setEnabled(false);
    }
}

void MainWindow::DrawArrow(QStringList ListTermID)
{
    ClearDrawArrow();
    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    bool FirstIn=true;
    qDebug()<<"DrawArrow,ListTermID="<<ListTermID;
    if(ListTermID.count()==2)
    {
        if(ListTermID.at(0).split(",").at(2).toInt()>ListTermID.at(1).split(",").at(2).toInt())
        {
            ListTermID[0]=ListTermID.at(0).split(",").at(0)+","+ListTermID.at(0).split(",").at(1)+",2";
            ListTermID[1]=ListTermID.at(1).split(",").at(0)+","+ListTermID.at(1).split(",").at(1)+",1";
        }
        else
        {
            ListTermID[0]=ListTermID.at(0).split(",").at(0)+","+ListTermID.at(0).split(",").at(1)+",1";
            ListTermID[1]=ListTermID.at(1).split(",").at(0)+","+ListTermID.at(1).split(",").at(1)+",2";
        }
    }
    QStringList ListConn_Coordinate;
    for(int i=0;i<ListTermID.count();i++)
    {
        QString TermID=ListTermID.at(i).split(",").at(0);
        QString StrPolar=ListTermID.at(i).split(",").at(2);
        SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+TermID;
        QuerySymb2TermInfo.exec(SqlStr);
        if(QuerySymb2TermInfo.next())
        {
            QString ConnDirection=QuerySymb2TermInfo.value("ConnDirection").toString();
            QString Symbol_ID=QuerySymb2TermInfo.value("Symbol_ID").toString();
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Symbol_ID= "+Symbol_ID;
            QuerySymbol.exec(SqlStr);
            if(QuerySymbol.next())
            {
                if(FirstIn)
                {
                    FirstIn=false;
                    QString dwgfilename=GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt());
                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                    QFileInfo file(path);
                    if(!file.exists()) return;
                    if(CurDiagnoseDwgFilePath!=path)
                    {
                        CurDiagnoseDwgFilePath=path;
                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                    }
                    //ui->axWidgetDiagnose->dynamicCall("ZoomAll()");
                    //FlagSetTestPointHighLight=true;
                    //ClearDrawArrow();
                }
                DrawArrow(QuerySymb2TermInfo.value("Conn_Coordinate").toString(),StrPolar,ConnDirection);
                ListConn_Coordinate.append(QuerySymb2TermInfo.value("Conn_Coordinate").toString());
            }//end of if(QuerySymbol.next())
        }//end of if(QuerySymb2TermInfo.next())
    }//end of for(int i=0;i<ListTermID.count();i++)
    //ListConn_Coordinate适应屏幕显示
    if(ListConn_Coordinate.count()==2)
    {
        dCenterX=(ListConn_Coordinate.at(0).split(",").at(0).toDouble()+ListConn_Coordinate.at(1).split(",").at(0).toDouble())/2;
        dCenterY=(ListConn_Coordinate.at(0).split(",").at(1).toDouble()+ListConn_Coordinate.at(1).split(",").at(1).toDouble())/2;
        //connect(&TimerDelay,SIGNAL(timeout()), this, SLOT(timerSetTestPointHighLight()));
        QTimer::singleShot(100, this,SLOT(timerSetTestPointHighLight()));
        //TimerDelay.start(100);
        ui->axWidgetDiagnose->dynamicCall("ZoomCenter(double,double)",dCenterX,dCenterY);
    }
}

void MainWindow::timerSetTestPointHighLight()
{
    //TimerDelay.stop();
    ui->axWidgetDiagnose->dynamicCall("ZoomAll()");
    ui->axWidgetDiagnose->dynamicCall("ZoomScale(double)",0.2);
    ui->axWidgetDiagnose->dynamicCall("ZoomCenter(double,double)",dCenterX,dCenterY);
}

void MainWindow::DoSetTestPointHighLight()
{
}

void MainWindow::DrawArrow(QString Conn_Coordinate,QString Tag,QString ConnDirection)
{
    qDebug()<<"DrawArrow(),Conn_Coordinate="<<Conn_Coordinate<<",Tag="<<Tag;
    QString ArrowName,ArrowColor;
    //if(Tag=="1") ArrowColor="RED";//红
    //else ArrowColor="BLUE";//蓝
    ArrowColor="RED";//红

    if(ConnDirection=="向右") ArrowName="ARROW_"+ArrowColor+"_HOR";
    else if(ConnDirection=="向左") ArrowName="ARROW_"+ArrowColor+"_HOR";
    else if(ConnDirection=="向上") ArrowName="ARROW_"+ArrowColor+"_VER";
    else if(ConnDirection=="向下") ArrowName="ARROW_"+ArrowColor+"_VER";

    MyInsertBlock(ui->axWidgetDiagnose,"C:/TBD/SymbConnLib/"+ArrowName+".dwg",ArrowName);
    SetCurLayer(ui->axWidgetDiagnose,"ARROW");
    double Posx=Conn_Coordinate.split(",").at(0).toDouble();
    double Posy=Conn_Coordinate.split(",").at(1).toDouble();
    qlonglong lBlockID=ui->axWidgetDiagnose->dynamicCall("DrawBlockReference(double,double, QString,double,double)",Posx,Posy,ArrowName,1.0,0).toLongLong();
    IMxDrawBlockReference *blkEnty= (IMxDrawBlockReference*) ui->axWidgetDiagnose->querySubObject("ObjectIdToObject(const qlonglong)",lBlockID);
    if(Tag=="1") FindAttrDefAndAddAttrToBlock(ui->axWidgetDiagnose,blkEnty,"设备标识符(显示)","+");
    else FindAttrDefAndAddAttrToBlock(ui->axWidgetDiagnose,blkEnty,"设备标识符(显示)","-");
    // 准备闪烁颜色.
    MxDrawResbuf* colors = new MxDrawResbuf();
    //if(Tag=="1") colors->AddLong(255);
    //else colors->AddLong(0xFF0000);
    colors->AddLong(255);
    colors->AddLong(0);
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeColor(QVariant)",colors->asVariant());
    // 设置闪烁间隔的时间
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeTime(int)",500);
    // 开始闪烁
    ui->axWidgetDiagnose->dynamicCall("TwinkeEnt(QString)",blkEnty->ObjectID());

    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
}

//清除所有的箭头
void MainWindow::ClearDrawArrow()
{
    qDebug()<<"ClearDrawArrow()";
    IMxDrawSelectionSet *ss1= (IMxDrawSelectionSet *)ui->axWidgetDiagnose->querySubObject("NewSelectionSet()");
    IMxDrawResbuf *filter=(IMxDrawResbuf *)ui->axWidgetDiagnose->querySubObject("NewResbuf()");
    filter->AddStringEx("ARROW",8);  // 筛选图层
    ss1->dynamicCall("AllSelect(QVariant)",filter->asVariant());
    int Cnt=ss1->dynamicCall("Count()").toInt();
    for(int i=0;i<Cnt;i++)
    {
        IMxDrawEntity *Enty = (IMxDrawEntity*)ss1->querySubObject("Item(int)",i);
        Enty->dynamicCall("Erase()");
    }
    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
}

void MainWindow::SetDiagResultRed(QString StrFaultComponentInfo)
{
    QStringList ListFaultComponentInfo=StrFaultComponentInfo.split(" ");
    for(QString OneComponentInfo:ListFaultComponentInfo)
    {
        //映射到原理图上标红
        //这里可能是元件或者是子元件
        QString DT=OneComponentInfo.mid(0,OneComponentInfo.indexOf(":"));
        QString modeTransition=OneComponentInfo.mid(OneComponentInfo.indexOf(":")+1,OneComponentInfo.indexOf("(")-OneComponentInfo.indexOf(":")-1);
        if(DT=="") continue;
        if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));

        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr;
        SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
        QueryEquipment.exec(SqlStr);
        if(QueryEquipment.next())
        {
            QString Equipment_ID=QueryEquipment.value("Equipment_ID").toString();

            //qDebug()<<"Equipment_ID="<<Equipment_ID;
            QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
            SqlStr="SELECT * FROM Symbol WHERE Equipment_ID= '"+Equipment_ID+"'";
            QuerySymbol.exec(SqlStr);
            while(QuerySymbol.next())
            {
                if(QuerySymbol.value("Symbol_Handle").toString()=="") continue;

                QString dwgfilename=GetPageNameByPageID(QuerySymbol.value("Page_ID").toInt());
                QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                QFileInfo file(path);
                if(!file.exists()) return;
                if(CurDiagnoseDwgFilePath!=path)
                {
                    CurDiagnoseDwgFilePath=path;
                    ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                }
                SetEntityRed(QuerySymbol.value("Symbol_Handle").toString());
                ListRedEntity.append(QuerySymbol.value("Symbol_Handle").toString()+",0");
                if(QuerySymbol.value("DT_Handle").toString()!="")
                {
                    if(SetEntityRed(QuerySymbol.value("DT_Handle").toString()))
                    {
                        ListRedEntity.append(QuerySymbol.value("DT_Handle").toString()+",5");
                    }
                }
                /*
                formaxwidget *formMxdraw=GetOpenedDwgaxwidget(QuerySymbol.value("Symbol_Handle").toString(),0);
                if(formMxdraw==nullptr) continue;
 //qDebug()<<"Symbol_Handle="<<QuerySymbol.value("Symbol_Handle").toString();
                if(formMxdraw->SetEntityRed(QuerySymbol.value("Symbol_Handle").toString()))
                {
                    ListRedEntity.append(QuerySymbol.value("Symbol_Handle").toString()+",0");
                }
                //如果是黑盒，别忘了黑盒对应的标号
                if(QuerySymbol.value("DT_Handle").toString()!="")
                {
                    if(formMxdraw->SetEntityRed(QuerySymbol.value("DT_Handle").toString()))
                    {
                        ListRedEntity.append(QuerySymbol.value("DT_Handle").toString()+",5");
                    }
                }
*/
            }//end of while(QuerySymbol.next())
        }//end of if(QueryEquipment.next())

        QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+OneComponentInfo.mid(0,OneComponentInfo.indexOf(":"))+"'";
        QueryJXB.exec(SqlStr);
        if(QueryJXB.next())
        {
            QString ConnectionNumber_Handle=QueryJXB.value("ConnectionNumber_Handle").toString();

            QString dwgfilename=GetPageNameByPageID(QueryJXB.value("Page_ID").toInt());
            QString path=CurProjectPath+"/"+dwgfilename+".dwg";
            QFileInfo file(path);
            if(!file.exists()) return;
            if(CurDiagnoseDwgFilePath!=path)
            {
                CurDiagnoseDwgFilePath=path;
                ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
            }
            SetEntityRed(ConnectionNumber_Handle);
            ListRedEntity.append(ConnectionNumber_Handle+",2");
            /*
            formaxwidget *formMxdraw=GetOpenedDwgaxwidget(ConnectionNumber_Handle,2);
            if(formMxdraw==nullptr) continue;
            if(formMxdraw->SetEntityRed(ConnectionNumber_Handle))
            {
                ListRedEntity.append(ConnectionNumber_Handle+",2");
            }*/
            //找到所有ConnectionNumber相关导线
            QStringList ListFindedSymb_ID;
            QSqlQuery QueryConnectLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM ConnectLine WHERE ConnectionNumber = '"+OneComponentInfo.mid(0,OneComponentInfo.indexOf(":"))+"'";
            QueryConnectLine.exec(SqlStr);
            while(QueryConnectLine.next())
            {
                QString Symb1_ID=QueryConnectLine.value("Symb1_ID").toString();
                QString Symb2_ID=QueryConnectLine.value("Symb2_ID").toString();
                if((Symb1_ID=="")&&(Symb2_ID=="")) continue;
                if(Symb1_ID.contains(":C")||Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3")) continue;
                if(Symb2_ID.contains(":C")||Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3")) continue;
                QString ConnectLine_ID=QueryConnectLine.value("ConnectLine_ID").toString();
                QSqlQuery QueryLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                QSqlQuery QueryConnector = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr = "SELECT * FROM Line WHERE Line_ID = "+ConnectLine_ID;
                QueryLine.exec(SqlStr);
                if(QueryLine.next())
                {
                    QString dwgfilename=GetPageNameByPageID(QueryLine.value("Page_ID").toInt());
                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                    QFileInfo file(path);
                    if(!file.exists()) return;
                    if(CurDiagnoseDwgFilePath!=path)
                    {
                        CurDiagnoseDwgFilePath=path;
                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                    }
                    SetEntityRed(QueryLine.value("Wires_Handle").toString());
                    ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                    /*
                    formMxdraw=GetOpenedDwgaxwidget(QueryLine.value("Wires_Handle").toString(),3);
                    if(formMxdraw!=nullptr)
                    {
                        if(formMxdraw->SetEntityRed(QueryLine.value("Wires_Handle").toString()))
                           ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                    }*/
                    QStringList ListLineSearchID={ConnectLine_ID};
                    while(1)
                    {
                        if(ListLineSearchID.count()<1) break;
                        QueryLine = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                        SqlStr = "SELECT * FROM Line WHERE Line_ID = "+ListLineSearchID.at(0);
                        QueryLine.exec(SqlStr);
                        if(QueryLine.next())
                        {
                            ListLineSearchID.removeFirst();
                            Symb1_ID=QueryLine.value("Symb1_ID").toString();
                            Symb2_ID=QueryLine.value("Symb2_ID").toString();
                            bool GoOn=false;
                            QStringList ListSymb_ID;
                            if(Symb1_ID.contains(":G")||Symb1_ID.contains(":1")||Symb1_ID.contains(":2")||Symb1_ID.contains(":3"))
                            {
                                QString Symb_ID=Symb1_ID;
                                if(ListFindedSymb_ID.contains(Symb_ID)) continue;
                                ListFindedSymb_ID.append(Symb_ID);
                                Symb_ID=Symb_ID.mid(0,Symb_ID.count()-1)+"C";
                                ListSymb_ID.append(Symb_ID);
                                GoOn=true;
                            }
                            if(Symb2_ID.contains(":G")||Symb2_ID.contains(":1")||Symb2_ID.contains(":2")||Symb2_ID.contains(":3"))
                            {
                                QString Symb_ID=Symb2_ID;
                                if(ListFindedSymb_ID.contains(Symb_ID)) continue;
                                ListFindedSymb_ID.append(Symb_ID);
                                Symb_ID=Symb_ID.mid(0,Symb_ID.count()-1)+"C";
                                ListSymb_ID.append(Symb_ID);
                                GoOn=true;
                            }
                            if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))
                            {
                                for(int i=0;i<2;i++)
                                {
                                    QString Symb_ID;
                                    if(i==0)
                                    {
                                        if(Symb1_ID.contains(":C")) Symb_ID = Symb1_ID;
                                        else continue;
                                    }
                                    else
                                    {
                                        if(Symb2_ID.contains(":C")) Symb_ID = Symb2_ID;
                                        else continue;
                                    }
                                    SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID.mid(0,Symb_ID.count()-2);
                                    QueryConnector.exec(SqlStr);
                                    if(QueryConnector.next())
                                    {
                                        if(QueryConnector.value("Connector_Name").toString().contains("SYMB2_M_PWF_CO"))
                                        {
                                            if(ListFindedSymb_ID.contains(Symb_ID)) continue;
                                            ListFindedSymb_ID.append(Symb_ID);
                                            Symb_ID=Symb_ID.mid(0,Symb_ID.count()-1)+"1";
                                            ListSymb_ID.append(Symb_ID);
                                            GoOn=true;
                                        }
                                    }
                                }//end of for(int i=0;i<2;i++)
                            }//end of if(Symb1_ID.contains(":C")||Symb2_ID.contains(":C"))
                            if(!GoOn) continue;
                            for(QString Symb_ID:ListSymb_ID)
                            {
                                SqlStr = "SELECT * FROM Line WHERE (Symb1_ID = '"+Symb_ID+"') OR (Symb2_ID = '"+Symb_ID+"')";
                                QueryLine.exec(SqlStr);
                                if(QueryLine.next())
                                {
                                    QString dwgfilename=GetPageNameByPageID(QueryLine.value("Page_ID").toInt());
                                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                                    QFileInfo file(path);
                                    if(!file.exists()) return;
                                    if(CurDiagnoseDwgFilePath!=path)
                                    {
                                        CurDiagnoseDwgFilePath=path;
                                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                                    }
                                    SetEntityRed(QueryLine.value("Wires_Handle").toString());
                                    ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                                    /*
                                    formMxdraw=GetOpenedDwgaxwidget(QueryLine.value("Wires_Handle").toString(),3);
                                    if(formMxdraw!=nullptr)
                                    {
                                        if(formMxdraw->SetEntityRed(QueryLine.value("Wires_Handle").toString()))
                                            ListRedEntity.append(QueryLine.value("Wires_Handle").toString()+",3");
                                    }
                                    else qDebug()<<"formMxdraw=nullptr 2";*/
                                    ListLineSearchID.append(QueryLine.value("Line_ID").toString());
                                }

                                SqlStr = "SELECT * FROM Connector WHERE Connector_ID = "+Symb_ID.mid(0,Symb_ID.count()-2);
                                QueryConnector.exec(SqlStr);
                                if(QueryConnector.next())
                                {
                                    QString dwgfilename=GetPageNameByPageID(QueryConnector.value("Page_ID").toInt());
                                    QString path=CurProjectPath+"/"+dwgfilename+".dwg";
                                    QFileInfo file(path);
                                    if(!file.exists()) return;
                                    if(CurDiagnoseDwgFilePath!=path)
                                    {
                                        CurDiagnoseDwgFilePath=path;
                                        ui->axWidgetDiagnose->dynamicCall("OpenDwgFile(QString)",path);
                                    }
                                    SetEntityRed(QueryConnector.value("Connector_Handle").toString());
                                    ListRedEntity.append(QueryConnector.value("Connector_Handle").toString()+",4");
                                    /*
                                    formMxdraw=GetOpenedDwgaxwidget(QueryConnector.value("Connector_Handle").toString(),4);
                                    if(formMxdraw!=nullptr)
                                    {
                                        if(formMxdraw->SetEntityRed(QueryConnector.value("Connector_Handle").toString()))
                                          ListRedEntity.append(QueryConnector.value("Connector_Handle").toString()+",4");
                                    }*/
                                }
                            } //end of for(QString Symb_ID:ListSymb_ID)
                        }
                    }//end of while(1)
                    break;
                }
            }//end of while(QueryConnectLine.next())
        }//end of if(QueryJXB.next())
    }//end of for(QString OneComponentInfo:ListFaultComponentInfo)
}
void MainWindow::on_tableWidgetDiagResult_clicked(const QModelIndex &index)
{
    //清空ListRedEntity
    ClearListRedEntity();
    if(!index.isValid()) return;

    for(int selectedindex=0;selectedindex<ui->tableWidgetDiagResult->selectionModel()->selectedIndexes().count();selectedindex++)
    {
        int rowindex=ui->tableWidgetDiagResult->selectionModel()->selectedIndexes().at(selectedindex).row();
        QString StrFaultComponentInfo=ui->tableWidgetDiagResult->item(rowindex,0)->text();
        SetDiagResultRed(StrFaultComponentInfo);
    }//end of for(int selectedindex=0;selectedindex<ui->tableWidgetDiagResult->selectionModel()->selectedIndexes().count();selectedindex++)

}

void MainWindow::on_BtnSaveDwg_clicked()
{
    for(int i=0;i<ui->mdiArea->subWindowList().count();i++)
    {
        //if(ui->mdiArea->subWindowList().at(i)->windowTitle().contains("故障诊断")) continue;
        formaxwidget *formMxdraw=(formaxwidget *)ui->mdiArea->subWindowList().at(i)->widget();
        formMxdraw->GetAxWidget()->dynamicCall("SaveDwgFile(QString)",formMxdraw->dwgFileName);
    }
}

void MainWindow::on_tableWidgetTestPoint_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    ClearListRedEntity();
    QString testpointName=ui->tableWidgetTestPoint->item(index.row(),0)->text();
    DrawTestPoint(testpointName.mid(0,testpointName.indexOf(".")),testpointName.mid(testpointName.indexOf(".")+1,testpointName.count()-testpointName.indexOf(".")-1));//绘制正负测试点箭头
}

void MainWindow::on_BtnModifyFunction_clicked()
{
    if(pDlgSelectFunctionDialog->isHidden())
    {
        // 将functionTree控件从 MainWindow 中移除
        QLayout *mainWindowLayout = ui->widget_func->layout();
        if (mainWindowLayout != nullptr) {
            qDebug()<<"准备将functionTree控件从 MainWindow 中移除";
            mainWindowLayout->removeWidget(pDlgSelectFunctionDialog->GetTreeWidget());
            pDlgSelectFunctionDialog->GetTreeWidget()->setParent(nullptr);
        }

        //在对话框中显示functionTree控件
        pDlgSelectFunctionDialog->ShowSet();
        pDlgSelectFunctionDialog->move(this->width()/2 - pDlgSelectFunctionDialog->width()/2,
                                       this->height()/2 - pDlgSelectFunctionDialog->height()/2);
        pDlgSelectFunctionDialog->show();
        if(pDlgSelectFunctionDialog->exec() == QDialog::Accepted) {
            // Do something on accept
        }
        // 将 functionTree 再次添加回 MainWindow
        UpdateFuncTree();
    }
}
void MainWindow::UpdateFuncTable()
{

    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function";
    QueryFunction.exec(SqlStr);
    ui->tableWidgetFunction->setRowCount(0);
    while(QueryFunction.next())
    {
        ui->tableWidgetFunction->setRowCount(ui->tableWidgetFunction->rowCount()+1);
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,0,new QTableWidgetItem(QueryFunction.value("FunctionName").toString()));
        ui->tableWidgetFunction->item(ui->tableWidgetFunction->rowCount()-1,0)->setData(Qt::UserRole,QueryFunction.value("FunctionID").toString());
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,1,new QTableWidgetItem(QueryFunction.value("CmdValList").toString()));
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,2,new QTableWidgetItem(QueryFunction.value("ExecsList").toString()));
        ui->tableWidgetFunction->setItem(ui->tableWidgetFunction->rowCount()-1,3,new QTableWidgetItem(QueryFunction.value("Remark").toString()));
    }
}

void MainWindow::on_BtnDiagnose_clicked()
{
    ui->widgetNavigator->setVisible(false);
    ui->stackedWidget->setCurrentIndex(1);
    initDiagnoseUI();
    LoadAllFunction();
    LoadAllTools();
}

void MainWindow::initDiagnoseUI()
{
    ui->tableWidget_function_select->setStyleSheet("selection-background-color: rgb(85, 170, 255)");
    ui->tableWidget_function_select->setColumnWidth(0,140);//功能名称
    ui->tableWidget_function_select->setColumnWidth(1,400);//控制变量
    ui->tableWidget_function_select->setColumnWidth(2,400);//执行器名称
    ui->tableWidget_function_select->setColumnWidth(3,150);//备注
    ui->tableWidget_function_select->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_tool_select->setColumnWidth(0,400);//工具名称
    ui->tableWidget_tool_select->setFocusPolicy(Qt::NoFocus);
    LoadAllFunction();
    LoadAllTools();
}

void MainWindow::LoadAllFunction()
{
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function";
    QueryFunction.exec(SqlStr);

    ui->tableWidget_function_select->setRowCount(0);
    while(QueryFunction.next())
    {
        ui->tableWidget_function_select->setRowCount(ui->tableWidget_function_select->rowCount()+1);
        ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,0,new QTableWidgetItem(QueryFunction.value("FunctionName").toString()));
        ui->tableWidget_function_select->item(ui->tableWidget_function_select->rowCount()-1,0)->setData(Qt::UserRole,QueryFunction.value("FunctionID").toString());
        ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,1,new QTableWidgetItem(QueryFunction.value("CmdValList").toString()));
        ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,2,new QTableWidgetItem(QueryFunction.value("ExecsList").toString().remove(" ").replace(","," , ")));
        ui->tableWidget_function_select->setItem(ui->tableWidget_function_select->rowCount()-1,3,new QTableWidgetItem(QueryFunction.value("Remark").toString()));
    }
}

void MainWindow::LoadAllTools()
{
    ui->tableWidget_tool_select->setRowCount(0);
    ui->tableWidget_tool_select->setRowCount(ui->tableWidget_tool_select->rowCount()+1);
    ui->tableWidget_tool_select->setItem(ui->tableWidget_tool_select->rowCount()-1,0,new QTableWidgetItem("万用表"));
}

void MainWindow::SetStackIndex(int index)
{
    ui->stackedWidget_main->setCurrentIndex(index);
}

void MainWindow::init_symptom_list()//初始化征兆信号UI列表
{
    ui->tableWidget_known_symptom_select->setStyleSheet("selection-background-color: rgb(85, 170, 255)");
    ui->tableWidget_known_symptom_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_known_symptom_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_known_symptom_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);

    ui->tableWidget_known_symptom_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("观测对象名称") << tr("观测对象变量") << tr("观测值");
    ui->tableWidget_known_symptom_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_known_symptom_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);

    ui->tableWidget_known_symptom_select->setAlternatingRowColors(true);//使表格颜色交错功能为真

    //设置表头
    ui->tableWidget_known_symptom_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_known_symptom_select->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_known_symptom_select->setRowCount(0);
}

void MainWindow::AddOrModifyExec(int Mode,QString StrSelectedExec,QString StrExecState,QString StrExecStateVal)//Mode=1:add Mode=2:modify
{
    QDialog *dialogNewExec =new QDialog();
    if(Mode==1) dialogNewExec->setWindowTitle("新增观测变量");
    else if(Mode==2) dialogNewExec->setWindowTitle("修改观测变量");
    dialogNewExec->setMinimumSize(QSize(400,100));
    QFormLayout *formlayoutNameEdit = new QFormLayout(dialogNewExec);

    QVBoxLayout *layout = new QVBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogNewExec);
    pushbuttonOK->setText("确认");

    QCheckBox *CbOnlyExec=new QCheckBox(nullptr);
    CbOnlyExec->setText("只选择执行器");
    CbOnlyExec->setChecked(true);


    QHBoxLayout *linelayout1= new QHBoxLayout(nullptr);
    QLabel *m_label1 = new QLabel(dialogNewExec);
    m_label1->setText("观测对象");
    m_label1->setMaximumWidth(50);
    qxcombobox *m_QComboBox1 = new qxcombobox(dialogNewExec);
    linelayout1->addWidget(m_label1);
    linelayout1->addWidget(m_QComboBox1);
    m_QComboBox1->StrSystemDefine=StrSystemDefine;
    m_QComboBox1->CurFunctionID=CurFunctionID;
    connect(CbOnlyExec,SIGNAL(clicked(bool)),m_QComboBox1,SLOT(UpdateItems(bool)));

    QHBoxLayout *linelayout2= new QHBoxLayout(nullptr);
    QLabel *m_label2 = new QLabel(dialogNewExec);
    m_label2->setText("观测变量");
    m_label2->setMaximumWidth(50);
    qxcombobox *m_QComboBox2 = new qxcombobox(dialogNewExec);
    linelayout2->addWidget(m_label2);
    linelayout2->addWidget(m_QComboBox2);

    QHBoxLayout *linelayout3= new QHBoxLayout(nullptr);
    QLabel *m_label3 = new QLabel(dialogNewExec);
    m_label3->setText("观测值");
    m_label3->setMaximumWidth(50);
    qxcombobox *m_QComboBox3 = new qxcombobox(dialogNewExec);
    linelayout3->addWidget(m_label3);
    linelayout3->addWidget(m_QComboBox3);

    QVBoxLayout *layout3 = new QVBoxLayout(nullptr);
    layout3->addWidget(CbOnlyExec);
    layout3->addLayout(linelayout1);
    layout3->addLayout(linelayout2);
    layout3->addLayout(linelayout3);

    layout->addLayout(layout3);
    layout->addWidget(pushbuttonOK);
    formlayoutNameEdit->addRow(layout);

    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogNewExec,SLOT(accept()));
    QObject::connect(m_QComboBox1,SIGNAL(currentTextChanged(QString)),m_QComboBox2,SLOT(UpdateExecStateItems(QString)));
    QObject::connect(m_QComboBox2,SIGNAL(currentTextChanged(QString)),m_QComboBox3,SLOT(UpdateExecStateValueItems(QString)));
    for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
        m_QComboBox1->ExistedUnits.append(ui->tableWidget_known_symptom_select->item(i,0)->text());
    m_QComboBox1->Mode=Mode;




    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CurFunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
        QString tmpStr=StrSystemDefine;
        QStringList FunctionUnitList=tmpStr.remove("\r\n").split(";");
        for(int i=0;i<FunctionUnitList.count();i++)
        {
            FunctionUnitList[i]=FunctionUnitList.at(i).split(" ").last();
            if(FunctionUnitList[i]=="") FunctionUnitList.removeAt(i);
        }
        qDebug()<<"FunctionUnitList="<<FunctionUnitList;
        if(Mode==2)
        {
            bool SelectExecExist=false;
            for(int i=0;i<QueryFunction.value("ExecsList").toString().split(",").count();i++)
            {
                if(QueryFunction.value("ExecsList").toString().split(",").at(i).contains(StrSelectedExec))
                {
                    SelectExecExist=true;
                    break;
                }
            }
            if(!SelectExecExist) CbOnlyExec->setChecked(false);
        }

        QStringList ExecsList;
        if(CbOnlyExec->isChecked()) FunctionUnitList=QueryFunction.value("ExecsList").toString().split(",");

        //去除没有可观测变量的器件
        QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        for(QString StrFunctionUnit:FunctionUnitList)
        {
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+StrFunctionUnit+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
                bool NoObservable=true;
                for(QString StrStructure:ListStructure)
                {
                    if(StrStructure.split(",").at(2)=="Observable") NoObservable=false;
                }
                if(NoObservable) FunctionUnitList.removeAt(FunctionUnitList.indexOf(StrFunctionUnit));
            }
        }
        m_QComboBox1->clear();
        for(QString StrExec:FunctionUnitList)
        {
            bool skip=false;
            if(Mode==1)
            {
                for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
                {
                    if(StrExec.mid(0,StrExec.indexOf("."))==ui->tableWidget_known_symptom_select->item(i,0)->text())
                    {
                        skip=true;
                        break;
                    }
                }
            }
            if(!skip) m_QComboBox1->addItem(StrExec.mid(0,StrExec.indexOf(".")));
        }
    }
    if(Mode==2)
    {
        m_QComboBox1->setCurrentText(StrSelectedExec);
        m_QComboBox2->setCurrentText(StrExecState);
        m_QComboBox3->setCurrentText(StrExecStateVal);
    }
    if (dialogNewExec->exec()==QDialog::Accepted)
    {
        if(Mode==1)
        {
            ui->tableWidget_known_symptom_select->setRowCount(ui->tableWidget_known_symptom_select->rowCount()+1);
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,0,new QTableWidgetItem(m_QComboBox1->currentText()));
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,1,new QTableWidgetItem(m_QComboBox2->currentText()));
            ui->tableWidget_known_symptom_select->setItem(ui->tableWidget_known_symptom_select->rowCount()-1,2,new QTableWidgetItem(m_QComboBox3->currentText()));
        }
        else if(Mode==2)
        {
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),0)->setText(m_QComboBox1->currentText());
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),1)->setText(m_QComboBox2->currentText());
            ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),2)->setText(m_QComboBox3->currentText());
        }
    }
    else return;
}

QString MainWindow::GetTermJpgPath(QString Type,QString ConnNum)
{
    //获取所选文件类型过滤器
    QStringList filters;

    //文件过滤
    filters<<QString("*.jpg");

    //定义迭代器并设置过滤器
    QDirIterator dir_iterator("C:/TBD/data/TermImage/",
                              filters,
                              QDir::Files | QDir::NoSymLinks);
    while(dir_iterator.hasNext())
    {
        dir_iterator.next();
        QFileInfo file_info = dir_iterator.fileInfo();

        if(file_info.fileName().contains("_"+ConnNum)&&file_info.fileName().contains(Type))
            return file_info.filePath();
    }
    return "";
}

//TestPointName:DT
void MainWindow::LoadTestPointInfo(QString TestPointName,QString CurrentInOutName,QStringList ListTermStr)
{
    qDebug()<<"LoadTestPointInfo,TestPointName="<<TestPointName<<",CurrentInOutName="<<CurrentInOutName<<",ListTermStr="<<ListTermStr;
    CurTestPointName=TestPointName+"."+CurrentInOutName;
    QString DT=TestPointName;
    if(DT.contains(".")) DT=DT.mid(0,DT.indexOf("."));
    QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
    QueryEquipment.exec(SqlStr);
    if(QueryEquipment.next())
    {
        QString Name=QueryEquipment.value("Name").toString()+DT;
        CurTestUnit.Name=QueryEquipment.value("Name").toString();
        CurTestUnit.DT=DT;
        CurTestUnit.Equipment_ID=QueryEquipment.value("Equipment_ID").toInt();
        CurTestUnit.CurrentInOutName=CurrentInOutName;
        CurTestUnit.TModel=QueryEquipment.value("TModel").toString();
        ui->label_diagnosis_TestWord->setText("测试："+Name);
        ui->label_test_procedure->setText("检测电压");
    }
    QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+DT+"'";
    QueryJXB.exec(SqlStr);
    if(QueryJXB.next())
    {
        CurTestUnit.Name="导线";
        CurTestUnit.DT=DT;
        CurTestUnit.Equipment_ID=QueryJXB.value("JXB_ID").toInt();
        CurTestUnit.CurrentInOutName=CurrentInOutName;

        QSqlQuery QueryFunctionDefineClass(T_LibDatabase);
        QString StrSql="SELECT * FROM FunctionDefineClass WHERE Level =1 AND FunctionDefineName = '导线新'";
        QueryFunctionDefineClass.exec(StrSql);
        if(QueryFunctionDefineClass.next())
            CurTestUnit.TModel=QueryFunctionDefineClass.value("TModel").toString();

        QString Name="导线"+DT;
        ui->label_diagnosis_TestWord->setText("测试："+Name);
        ui->label_test_procedure->setText("检测电压");
    }

    ui->tabWidget_testpointPic->clear();
    AddTestPicture("工具图","万用表.png","C:/TBD/data/ToolImage/万用表.png");

    QString test_description;
    for(int i=0;i<ListTermStr.count();i++)
    {
        if(i>0) test_description+="\r\n";
        //if(ListTermStr.at(i).split(",").at(1)=="0")//器件
        {
            QSqlQuery QuerySymb2TermInfo = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            SqlStr = "SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID = "+ListTermStr.at(i).split(",").at(0);
            QuerySymb2TermInfo.exec(SqlStr);
            if(QuerySymb2TermInfo.next())
            {
                QString pointDT,pointName;
                int UnitStripID=GetUnitStripIDByTermID(0,ListTermStr.at(i).split(",").at(0).toInt(),pointDT);
                SqlStr = "SELECT * FROM Equipment WHERE Equipment_ID = "+QString::number(UnitStripID);
                QueryEquipment.exec(SqlStr);
                if(QueryEquipment.next())
                {
                    pointName=QueryEquipment.value("Name").toString();
                    QString PolarStr=(i==0)?"正极":"负极";
                    test_description+="万用表"+PolarStr+":"+pointName+pointDT+"."+QuerySymb2TermInfo.value("ConnNum").toString();
                    //查找测试点jpg图片
                    QString Tabname=QueryEquipment.value("DT").toString()+"."+QuerySymb2TermInfo.value("ConnNum").toString();
                    QString jpgPath=GetTermJpgPath(QueryEquipment.value("Type").toString(),QuerySymb2TermInfo.value("ConnNum").toString());
                    if(jpgPath!="") AddTestPicture(Tabname,jpgPath.mid(jpgPath.lastIndexOf("/")+1,jpgPath.count()-jpgPath.lastIndexOf("/")-1),jpgPath);
                }
            }
        }
    }
    ui->label_test_description_1->setText(test_description);
    ui->EdInputVal1->setText("");
    SetStackIndex(2);
    qDebug()<<"LoadTestPointInfo over";
}

void MainWindow::OpenPic(int ID)
{
    QXlabel *m_Label=(QXlabel*)sender();
    QPixmap photo(m_Label->PicPath);
    picture_Label->setPixmap(photo);
    picture_Label->setScaledContents(true);
    dlg_showPicture->setWindowTitle(m_Label->PicName);
    //dlg_showPicture->setWindowFlags( Qt::MSWindowsFixedSizeDialogHint);

    dlg_showPicture->show();
    QScreen *screen = QGuiApplication::primaryScreen ();
    QRect screenRect =  screen->availableVirtualGeometry();
    int screenWidth = screenRect.width();
    int screenHeight = screenRect.height();
    dlg_showPicture->move(screenWidth/2- dlg_showPicture->width()/2,screenHeight/2- dlg_showPicture->height()/2);
}

void MainWindow::AddTestPicture(QString Tabname,QString PicName,QString Path)
{
    QWidget* widget = new QWidget(nullptr);
    QVBoxLayout * layout = new QVBoxLayout(widget);//铺满布局

    ui->tabWidget_testpointPic->addTab(widget,Tabname);

    QWidget* widgetPic = new QWidget(widget);
    QXlabel* pLabel = new QXlabel(widgetPic);
    pLabel->PicPath=Path;
    pLabel->PicName=PicName;
    connect(pLabel,SIGNAL(doubleClicked(int)),this,SLOT(OpenPic(int)));
    widgetPic->setSizePolicy(QSizePolicy::Preferred,QSizePolicy::Preferred);//铺满布局
    //pLabel->setScaledContents(true);
    //pLabel->setFrameShape(QFrame::Panel);
    //pLabel->setFrameShadow(QFrame::Sunken);
    //pLabel->setLineWidth(3);
    //pLabel->setSizePolicy(QSizePolicy::Fixed,QSizePolicy::Fixed);

    layout->addWidget(widgetPic);

    QLabel* name_Label = new QLabel(widget);
    name_Label->setMaximumHeight(20);

    name_Label->setStyleSheet("font: 75 10pt '微软雅黑';");
    name_Label->setAlignment(Qt::AlignHCenter);

    QString picture_name = PicName;
    //picture_name.remove(".jpg").remove(".JPG").remove(".png").remove(".PNG");
    name_Label->setText(picture_name);
    layout->addWidget(name_Label);

    QPixmap photo(Path);
    //pLabel->resize(photo.width()-40,photo.height());

    pLabel->setScaledContents(true);
    int wLabel=376-12;
    int hLabel=321-20-18-75;
    //pLabel->setScaledContents(false);
    int wPhoto=photo.width();
    int hPhoto=photo.height();
    int Finalw,Finalh;
    if((wPhoto>=wLabel)&&(hPhoto>=hLabel))
    {
        if((wPhoto/hPhoto)>(wLabel/hLabel))
        {
            Finalw=wLabel;
            Finalh=wLabel*hPhoto/wPhoto;
        }
        else
        {
            Finalh=hLabel;
            Finalw=hLabel*wPhoto/hPhoto;
        }
    }
    else if((wPhoto>=wLabel)&&(hPhoto<=hLabel))
    {
        Finalw=wLabel;
        Finalh=wLabel*hPhoto/wPhoto;
    }
    else if((wPhoto<=wLabel)&&(hPhoto>=hLabel))
    {
        Finalh=hLabel;
        Finalw=hLabel*wPhoto/hPhoto;
    }
    else
    {
        Finalw=wPhoto;
        Finalh=hPhoto;
    }
    //qDebug()<<"wLabel="<<wLabel<<",hLabel="<<hLabel<<",wPhoto="<<wPhoto<<",hPhoto="<<hPhoto<<",Finalw="<<Finalw<<",Finalh="<<Finalh;
    //pLabel->resize(Finalw,Finalh);
    pLabel->move(0,0);
    //qDebug()<<"pLabel->width()="<<pLabel->width()<<",pLabel->height()="<<pLabel->height();
    pLabel->setPixmap(photo.scaled(Finalw,Finalh));//(photo.scaled(w,h,Qt::KeepAspectRatio,Qt::SmoothTransformation));
    //qDebug()<<"pLabel->width()="<<pLabel->width()<<",pLabel->height()="<<pLabel->height();
}

void MainWindow::on_toolButton_start_diagnosis_clicked()
{
    if(ui->tableWidget_function_select->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", " 请选择系统功能！");
        return;
    }
    //根据用户选择的功能生成xmpl
    CurFunctionID=ui->tableWidget_function_select->item(ui->tableWidget_function_select->currentRow(),0)->data(Qt::UserRole).toString();
    UpdateXmplInfo(CurFunctionID);
    init_symptom_list();
    SetStackIndex(1);
    ui->label_diagnosis_TestWord->setText("请选择一个或多个观测现象，并单击下一步");
    ui->LbFunction->setText("当前诊断功能:"+ui->tableWidget_function_select->item(ui->tableWidget_function_select->currentRow(),0)->text());
}

//解析当前测试模块的阈值信息
void MainWindow::on_btm_CalTestResult_clicked()
{
    if(!StrIsDouble(ui->EdInputVal1->text()))
    {
        QMessageBox::warning(nullptr, "提示", " 请输入正确的电压数值！");
        return;
    }
    QString SendCmdStr="assign test.";
    if(ui->CbTestType->currentText()=="电压")
    {
        QString StrVal=GetRangeValByTModel(CurTestUnit.TModel,CurTestUnit.CurrentInOutName,ui->EdInputVal1->text(),"电压");
        if(StrVal!="")
        {
            SendCmdStr+=CurTestPointName+".U="+StrVal;
            SendCmdStr+="\r\nfc";
            SendCmd(SendCmdStr,true);
        }
        //if(ui->EdInputVal1->text().toDouble()<3) SendCmdStr+=CurTestPointName+".U=none";
        //else if(ui->EdInputVal1->text().toDouble()<16) SendCmdStr+=CurTestPointName+".U=low";
        //else if(ui->EdInputVal1->text().toDouble()<26) SendCmdStr+=CurTestPointName+".U=middle";
        //else if(ui->EdInputVal1->text().toDouble()<30) SendCmdStr+=CurTestPointName+".U=high";
        //else SendCmdStr+=CurTestPointName+".U=infinite";
        //SendCmdStr+="\r\nfc";
        //SendCmd(SendCmdStr,true);
    }
    else if(ui->CbTestType->currentText()=="电流")
    {
        QString StrVal=GetRangeValByTModel(CurTestUnit.TModel,CurTestUnit.CurrentInOutName,ui->EdInputVal1->text(),"电流");
        if(StrVal!="")
        {
            SendCmdStr+=CurTestPointName+".I="+StrVal;
            SendCmdStr+="\r\nfc";
            SendCmd(SendCmdStr,true);
        }
    }
    else if(ui->CbTestType->currentText()=="电阻")
    {
        QString StrVal=GetRangeValByTModel(CurTestUnit.TModel,CurTestUnit.CurrentInOutName,ui->EdInputVal1->text(),"电阻");
        if(StrVal!="")
        {
            SendCmdStr+=CurTestPointName+".R="+StrVal;
            SendCmdStr+="\r\nfc";
            SendCmd(SendCmdStr,true);
        }
    }
}

void MainWindow::on_toolButton_known_symptom_select_next_clicked()
{
    if(ui->tableWidget_known_symptom_select->rowCount()<1)
    {
        QMessageBox::warning(nullptr, "提示", " 请选择观测现象！");
        return;
    }
    ListSkipTestPoint.clear();
    QString CmdValList;
    QSqlQuery QueryFunction = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr = "SELECT * FROM Function WHERE FunctionID = "+CurFunctionID;
    QueryFunction.exec(SqlStr);
    if(QueryFunction.next())
    {
        CmdValList=QueryFunction.value("CmdValList").toString();
    }
    QString SendCmdStr;
    for(QString StrCmdVal:CmdValList.split(","))
    {
        if(SendCmdStr!="") SendCmdStr+="\r\n";
        SendCmdStr+="progress test."+StrCmdVal;
    }
    ListAllObserve.clear();
    for(int i=0;i<ui->tableWidget_known_symptom_select->rowCount();i++)
    {
        QString CurObserve=ui->tableWidget_known_symptom_select->item(i,0)->text()+"."+ui->tableWidget_known_symptom_select->item(i,1)->text()+"="+ui->tableWidget_known_symptom_select->item(i,2)->text();
        ListAllObserve.append(CurObserve);
        if(SendCmdStr!="") SendCmdStr+="\r\n";
        SendCmdStr+="assign test."+CurObserve;
    }
    DiagnoseInitStr=SendCmdStr;
    if(ui->tableWidget_known_symptom_select->rowCount()>0) SendCmdStr+="\r\nfc";
    qDebug()<<"SendCmdStr="<<SendCmdStr;
    StartDiagnose(SendCmdStr);


    //SetStackIndex(2);
}

//张新宇写
double MainWindow::CalculateInformation(QString& module_name)
{
    double all_prob = 0.0;
    double all_work_well_prob = 1.0;
    double module_name_prob = 1.0;
    bool is_have = false;


    if(module_fault_prob.isEmpty())
    {
        qDebug()<<"module_fault_prob为空，输出错误";
        return INT_MAX;
    }

    //归一化
    QVector<double> prob;
    for(auto it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
        all_prob+=it.value();

    for(auto it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
    {
        if(it.key() == module_name)
        {
            is_have = true;
            module_name_prob = it.value()/all_prob;
        }
        else
            prob.append(it.value()/all_prob);
    }

    if(!is_have)      //如果自定义测点不在module_fault_prob里面
        qDebug()<<"自定义测试"<<module_name<<"没有找到概率";

    for(int i=0; i<prob.count(); i++)
    {
        all_work_well_prob *= (1-prob[i]);
    }


    //如果自定义测试成功，那么信息熵为0，不进行计算

    //如果自定义测试没有成功
    //如果输入的自定义测试器件不在module_fault_prob里，那么默认这个器件对系统的信息熵没有影响
    //如果输入的自定义测试器件在在module_fault_prob里，那么考虑这个器件对系统的信息熵的影响
    double faild_prob;
    if(is_have)
        faild_prob = 1-(module_name_prob * all_work_well_prob);
    else
        faild_prob = 1;


    double information = 1.0;
    for(int i=0; i<prob.size(); i++)
        information += prob[i] * log(1/prob[i]);

    qDebug()<<"输出module_fault_prob";
    for(auto it = module_fault_prob.begin(); it!=module_fault_prob.end(); it++)
        qDebug()<<it.key()<<it.value();

    qDebug()<<"输出归一化prob";
    for(auto it = prob.begin(); it!=prob.end(); it++)
        qDebug()<<*it;

    qDebug()<<"输出faild_prob "<< faild_prob<<" module_name_prob "<<module_name_prob<<" all_work_well_prob "<<all_work_well_prob;

    qDebug()<<"输出Information "<<information << "输出Information*faild_prob" << faild_prob * information;
    return faild_prob * information;
}

void MainWindow::CalculateCustomInformation(QString& base,QStringList& list)
{
    this->base = base;
    this->list = list;
    this->depth = 0;
    custom_process = new QProcess();
    connect(custom_process , SIGNAL(readyReadStandardOutput()) , this , SLOT(on_custom_read()));
    information = 0.0;

    StartCustomProcess();


}

void MainWindow::StartCustomProcess()
{
    if(depth >= list.count())
    {
        delete custom_process;
        custom_process = nullptr;
        return ;
    }

    qDebug()<<"process start "<<base<<" depth "<<depth<<" "<<list[depth];
    QString modelfileName = CurProjectPath+"/test.xmpl";
    QFile file(modelfileName);
    if(file.exists())
    {


        modelfileName = modelfileName.left(modelfileName.lastIndexOf("."));
        QString program = "C:/TBD/data/l2test.exe";
        QStringList arguments;
        arguments<<modelfileName;//传递到exe的参数
        custom_process->start(program,arguments);
        custom_process->setCurrentReadChannel(QProcess::StandardOutput);
        custom_process->waitForStarted(500);

        custom_process->write((base + '\n' + list[depth] + '\n').toLocal8Bit());

        custom_process->waitForBytesWritten(200);
    }
}

void MainWindow::on_custom_read()
{

    QList<QString> temp_candidate_name_list;
    custom_process->waitForReadyRead(200);
    QString output = custom_process->readAllStandardOutput().data();

    qDebug()<<"my_out\n"<<output;

    if(!output.contains("Candidate")) return;

    QList<CandidateData> temp_candidate_list;

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
            if(!data.FaultSpur.split('.')[0].isEmpty())
                temp_candidate_name_list.append(data.FaultSpur.split('.')[0]);

            data.FaultProbability = 1 / qPow(2, data.PriorVal.toInt());

            bool is_have = false;
            for(CandidateData& temp_data : temp_candidate_list)
            {
                if(temp_data.FaultSpur == data.FaultSpur
                        && temp_data.modeTransition == data.modeTransition
                        && temp_data.PriorVal == data.PriorVal)

                {
                    is_have = true;
                    break;
                }
            }

            if(!is_have)
                temp_candidate_list.append(data);
        }
    }
    if(temp_candidate_name_list.isEmpty())
        return;

    temp_candidate_name_list.removeDuplicates();

    //更新故障概率
    custom_module_fault_prob.clear();
    for(CandidateData& data : temp_candidate_list)
    {
        if(custom_module_fault_prob.find(data.FaultSpur.split('.')[0]) == custom_module_fault_prob.end())
        {
            custom_module_fault_prob[data.FaultSpur.split('.')[0]] = data.FaultProbability;
        }
        else
        {
            custom_module_fault_prob[data.FaultSpur.split('.')[0]] = custom_module_fault_prob[data.FaultSpur.split('.')[0]] + data.FaultProbability - data.FaultProbability * custom_module_fault_prob[data.FaultSpur.split('.')[0]];
        }

    }

    qDebug()<<"temp_candidate_name_list\n"<<temp_candidate_name_list;


    //计算达到这个结果的概率
    //对原来的module_fault_prob归一化
    QMap<QString, double> temp_module_prob = module_fault_prob;
    double all_prob = 0.0;
    for(auto it =temp_module_prob.begin(); it!=temp_module_prob.end();it++)
        all_prob += it.value();

    qDebug()<<"all_prob "<<all_prob;
    for(auto it =temp_module_prob.begin(); it!=temp_module_prob.end();it++)
    {
        *it = it.value() / all_prob;
        qDebug()<<it.value();
    }

    double result_prob = 1.0;
    for(auto it_old = temp_module_prob.begin(); it_old != temp_module_prob.end(); it_old++)
    {
        auto it_new = custom_module_fault_prob.find(it_old.key());

        if(it_new == custom_module_fault_prob.end())
        {
            result_prob *= 1-it_old.value();
        }
    }
    qDebug()<<"result_prob "<<result_prob;

    //计算新的信息熵
    double information_temp = 0.0;
    //custom_module_fault_prob归一化
    double custom_all_prob = 0.0;
    for(auto it =custom_module_fault_prob.begin(); it!=custom_module_fault_prob.end();it++)
        custom_all_prob += it.value();

    qDebug()<<"custom_all_prob "<<custom_all_prob;
    for(auto it =custom_module_fault_prob.begin(); it!=custom_module_fault_prob.end();it++)
    {
        *it = it.value() / custom_all_prob;
        qDebug()<<it.value();
    }


    for(int i=0; i<temp_candidate_name_list.count(); i++)
    {
        auto it_new = custom_module_fault_prob.find(temp_candidate_name_list[i]);

        information_temp += it_new.value() * log(1/it_new.value());
    }

    information +=  information_temp * result_prob;

    qDebug()<<"information "<<information;
    qDebug()<<"information_temp "<<information_temp;

    qDebug()<<"log test"<<log(3);
    depth++;

    custom_process->close();
    custom_process->waitForFinished();

    StartCustomProcess();
}


void MainWindow::on_toolButton_known_symptom_delete_clicked()
{
    if(ui->tableWidget_known_symptom_select->currentRow()<0) return;
    ui->tableWidget_known_symptom_select->removeRow(ui->tableWidget_known_symptom_select->currentRow());
}

void MainWindow::on_toolButton_not_exit_symptom_modify_clicked()
{
    if(ui->tableWidget_known_symptom_select->currentRow()<0) return;
    AddOrModifyExec(2,ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),0)->text(),ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),1)->text(),ui->tableWidget_known_symptom_select->item(ui->tableWidget_known_symptom_select->currentRow(),2)->text());
}

void MainWindow::on_toolButton_known_symptom_add_clicked()
{
    AddOrModifyExec(1,"","","");
}

void MainWindow::on_BtnEndDiagnose_2_clicked()
{
    FinishDiagnose();
}

void MainWindow::on_BtnEndDiagnose_3_clicked()
{
    FinishDiagnose();
}

void MainWindow::on_toolButton_resule_OK_next_clicked()
{
    FinishDiagnose();
}

void MainWindow::on_toolButton_all_result_next_clicked()
{
    FinishDiagnose();
}

void MainWindow::FinishDiagnose()
{
    SetStackIndex(0);
    ui->label_diagnosis_TestWord->setText("请选择系统功能");
    ui->LbFunction->setText("当前诊断功能:无");
    on_BtnEndDiagnose_clicked();
    ui->stackedWidget->setCurrentIndex(0);
    ListSkipTestPoint.clear();
    QsciEdit->clear();
    ui->EdInputVal1->setText("");
}

void MainWindow::on_BtnShowMdi_clicked()
{
    ui->stackedWidget->setCurrentIndex(0);
}

//获取推荐的测点（跳过人为选择跳过的测点）
void MainWindow::GetRecommendedTestPoint()
{
    //ListSkipTestPoint.append(CurTestPointName);
    if((test_point.count()>0)&&(ui->tableWidgetDiagResult->rowCount()>1))
    {
        int RecommendedTestPointIndex=-1;
        for(int i=0;i<test_point.count();i++)
        {
            bool needSkip=false;
            for(int j=0;j<ListSkipTestPoint.count();j++)
            {
                if(test_point.at(i).point_name==ListSkipTestPoint.at(j))
                {
                    needSkip=true;
                    break;
                }
            }
            //if(test_point.at(i).calculate<0.00000001) continue;
            if(!needSkip)
            {
                RecommendedTestPointIndex=i;
                break;
            }
        }
        if(RecommendedTestPointIndex>=0)
        {
            ui->tableWidgetTestPoint->setCurrentIndex(ui->tableWidgetTestPoint->model()->index(RecommendedTestPointIndex,0));
            on_tableWidgetTestPoint_clicked(ui->tableWidgetTestPoint->model()->index(RecommendedTestPointIndex,0));
            ClearListRedEntity();
            for(int i=0;i<ui->tableWidgetDiagResult->rowCount();i++)
            {
                SetDiagResultRed(ui->tableWidgetDiagResult->item(i,0)->text());
            }
        }
    }
}

void MainWindow::on_toolButton_skip_this_test_clicked()
{
    qDebug()<<"CurTestPointName="<<CurTestPointName<<",ListSkipTestPoint="<<ListSkipTestPoint;
    //判断是否还有其他测试点
    for(int i=0;i<test_point.count();i++)
    {
        bool needSkip=false;
        if(test_point.at(i).point_name==CurTestPointName) continue;
        for(int j=0;j<ListSkipTestPoint.count();j++)
        {
            if(test_point.at(i).point_name==ListSkipTestPoint.at(j))
            {
                needSkip=true;
                break;
            }
        }
        qDebug()<<"test_point="<<test_point.at(i).point_name<<",needSkip="<<needSkip;
        if(!needSkip)
        {
            QsciEdit->append("\r\n//skip "+CurTestPointName);
            ListSkipTestPoint.append(CurTestPointName);
            ui->tableWidgetTestPoint->setCurrentIndex(ui->tableWidgetTestPoint->model()->index(i,0));
            on_tableWidgetTestPoint_clicked(ui->tableWidgetTestPoint->model()->index(i,0));
            return;
        }
    }
    QMessageBox::warning(nullptr, "提示", "没有其他测试点或其他测试点已全部跳过");
}

void MainWindow::on_toolButton_slelct_other_test_clicked()
{
    /*
    QList<QString> list_test;
    for(int i=0;i<test_point.count();i++)
    {
       list_test.append(test_point.at(i).point_name+","+QString::number(test_point.at(i).calculate)+","+QString::number(test_point.at(i).test_cost));
    }*/
    Dialog_select_another_test *dlg=new Dialog_select_another_test(this,&test_point);
    //dlg->InitTable(1);
    dlg->SetTestPreference(TestPointPreference);
    dlg->showNormal();
    dlg->setWindowTitle("候选测试点");
    dlg->setModal(true);

    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        QString test_name = dlg->get_test_name();
        SelectTestPoint(test_name);
    }
    delete dlg; //删除对话框
}

void MainWindow::SelectTestPoint(QString TestPointName)
{
    qDebug()<<"SelectTestPoint TestPointName="<<TestPointName;
    for(int i=0;i<test_point.count();i++)
    {
        if(test_point.at(i).point_name==TestPointName)
        {
            QsciEdit->append("\r\n//select "+TestPointName);
            on_tableWidgetTestPoint_clicked(ui->tableWidgetTestPoint->model()->index(i,0));
            break;
        }
    }
}

void MainWindow::on_axWidgetDiagnose_CommandEnded(const QString &sCmdName)
{
    qDebug()<<"axWidgetDiagnose sCmdName="<<sCmdName;
    if((sCmdName=="MXOCXSYS_ImpMxDrawXCommand")||(sCmdName=="MXOCXSYS_CommandInImp"))
    {
        if(FlagSetTestPointHighLight) ui->axWidgetDiagnose->dynamicCall("DoCommand(const int&)",100);
        FlagSetTestPointHighLight=false;
    }
}

void MainWindow::on_axWidgetDiagnose_ImplementCommandEvent(int iCommandId)
{
    qDebug()<<"axWidgetDiagnose on_axWidgetDiagnose_ImplementCommandEvent,iCommandId="<<iCommandId;
    if (iCommandId == 100)   DoSetTestPointHighLight();
}

//根据QsciEdit重新诊断   还需要考虑跳过和选择其他测试点的情况
void MainWindow::on_BtnLastStep_clicked()
{
    QString StrQsciEdit=QsciEdit->text();
    QString StrStepDiagnose=StrQsciEdit.remove(DiagnoseInitStr);
    //找到上一步执行的指令是什么，可能还没执行任何指令，也可能执行fc，也可能是skip或select
    StrStepDiagnose.remove("\r\nfc");
    QString StrLastCmd=StrStepDiagnose.mid(StrStepDiagnose.lastIndexOf("\r\n"),StrStepDiagnose.count()-StrStepDiagnose.lastIndexOf("\r\n")-1);
    if((!StrStepDiagnose.contains("="))&&(!StrStepDiagnose.contains("//skip"))&&(!StrStepDiagnose.contains("//select")))//上一步为选择观测现象
    {
        on_BtnEndDiagnose_clicked();
        QsciEdit->clear();
        ui->label_diagnosis_TestWord->setText("请选择一个或多个观测现象，并单击下一步");
        SetStackIndex(1);
        return;
    }
    else if(StrLastCmd.contains("="))
    {
        //去除所有的"\r\nfc"，然后去除最后一行，再加上"\r\nfc"
        StrQsciEdit=QsciEdit->text();
        StrQsciEdit.remove("\r\nfc");
        StrQsciEdit=StrQsciEdit.mid(0,StrQsciEdit.lastIndexOf("\r\n"));
        StrQsciEdit+="\r\nfc";
        qDebug()<<"//fc,ReDiagnose StrQsciEdit="<<StrQsciEdit;
        //on_BtnEndDiagnose_clicked();
        QsciEdit->clear();
        ReDiagnose(StrQsciEdit);
    }
    else if(StrLastCmd.contains("//skip"))
    {
        StrQsciEdit=QsciEdit->text();
        StrQsciEdit=StrQsciEdit.mid(0,StrQsciEdit.lastIndexOf("\r\n"));
        qDebug()<<"//skip,ReDiagnose StrQsciEdit="<<StrQsciEdit;
        //on_BtnEndDiagnose_clicked();
        QString SkipPointName=StrLastCmd.mid(StrLastCmd.indexOf("//skip")+7,StrLastCmd.count()-StrLastCmd.indexOf("//skip")-7);
        qDebug()<<"SkipPointName="<<SkipPointName;
        ListSkipTestPoint.removeAt(ListSkipTestPoint.indexOf(SkipPointName));
        QsciEdit->clear();
        ReDiagnose(StrQsciEdit);
    }
    else if(StrLastCmd.contains("//select"))
    {
        StrQsciEdit=QsciEdit->text();
        StrQsciEdit=StrQsciEdit.mid(0,StrQsciEdit.lastIndexOf("\r\n"));
        qDebug()<<"//select,ReDiagnose StrQsciEdit="<<StrQsciEdit;
        //on_BtnEndDiagnose_clicked();
        QsciEdit->clear();
        ReDiagnose(StrQsciEdit);
    }
}

void MainWindow::ReDiagnose(QString StrDiagnose)
{
    //如果StrDiagnose的最后一句是"//select"
    QString LastStr=StrDiagnose.mid(StrDiagnose.lastIndexOf("\r\n"),StrDiagnose.count()-StrDiagnose.lastIndexOf("\r\n")-1);
    qDebug()<<"ReDiagnose,LastStr="<<LastStr;
    if(LastStr.contains("//select"))
    {
        QsciEdit->append(StrDiagnose);
        QString TestPointName=LastStr.mid(LastStr.indexOf("//select ")+9,LastStr.count()-LastStr.indexOf("//select ")-9);
        SelectTestPoint(TestPointName);
    }
    else
    {
        ListSkipTestPoint.clear();
        QStringList ListStrDiagnose=StrDiagnose.split("\r\n");
        for(QString tmpStr:ListStrDiagnose)
        {
            if(tmpStr.contains("//skip ")) ListSkipTestPoint.append(tmpStr.mid(tmpStr.indexOf("//skip ")+7,tmpStr.count()-tmpStr.indexOf("//skip ")-7));
        }
        on_BtnEndDiagnose_clicked();
        StartDiagnose(StrDiagnose);
    }
}

void MainWindow::on_toolButton_known_symptom_select_last_clicked()
{
    ui->label_diagnosis_TestWord->setText("请选择系统功能");
    ui->LbFunction->setText("当前诊断功能:无");
    SetStackIndex(0);
}

void MainWindow::on_BtnLastStep_2_clicked()
{
    on_BtnLastStep_clicked();
}

//清空ListRedEntity
void MainWindow::ClearListRedEntity()
{
    for(QString RedEntityHandle:ListRedEntity)
    {
        IMxDrawEntity *Enty=(IMxDrawEntity *)(ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",RedEntityHandle.split(",").at(0)));
        if(Enty==nullptr) continue;

        if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
        {
            IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
            for (int  j = 0; j < blkEnty->dynamicCall("AttributeCount()").toInt(); j++)
            {
                // 得到块引用中所有的属性
                IMxDrawAttribute *attrib = (IMxDrawAttribute *)blkEnty->querySubObject("AttributeItem(int)",j);
                //qDebug()<<"tag="<<attrib->dynamicCall("Tag()").toString();
                if((attrib->dynamicCall("Tag()").toString()=="设备标识符(显示)")||(attrib->dynamicCall("Tag()").toString()=="连接代号"))
                {
                    if(blkEnty->dynamicCall("GetBlockName()").toString()=="SPS_CDP")
                        attrib->dynamicCall("setColorIndex(int)",McColor::mcGreen);
                    else
                        attrib->dynamicCall("setColorIndex(int)",McColor::mcCyan);
                    break;
                }
            }
            blkEnty->dynamicCall("AssertWriteEnabled()");
        }
        else if(Enty->dynamicCall("ObjectName()").toString()=="McDbMText")
        {
            Enty->dynamicCall("setColorIndex(int)",McColor::mcCyan);
        }
        //formaxwidget *formMxdraw=GetOpenedDwgaxwidget(RedEntityHandle.split(",").at(0),RedEntityHandle.split(",").at(1).toInt());
        //if(formMxdraw==nullptr) continue;
        /*
        IMxDrawEntity *Enty=(IMxDrawEntity *)(ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",RedEntityHandle.split(",").at(0)));
        ui->axWidgetDiagnose->dynamicCall("StopTwinkeEnt (QString)",Enty->ObjectID());
        ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
        */
    }
    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
    ListRedEntity.clear();
}

//诊断可视化用，将块变红色
bool MainWindow::SetEntityRed(QString Handle)
{
    //qDebug()<<"SetEntityRed,Handle="<<Handle;
    IMxDrawEntity *Enty=(IMxDrawEntity *)ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",Handle);
    if(Enty==nullptr) return false;
    //Enty->dynamicCall("setColorIndex(int)",McColor::mcRed);

    if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
    {
        IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
        for (int  j = 0; j < blkEnty->dynamicCall("AttributeCount()").toInt(); j++)
        {
            // 得到块引用中所有的属性
            IMxDrawAttribute *attrib = (IMxDrawAttribute *)blkEnty->querySubObject("AttributeItem(int)",j);
            //qDebug()<<"attrib->dynamicCall(Tag()).toString()"<<attrib->dynamicCall("Tag()").toString();
            if((attrib->dynamicCall("Tag()").toString()=="设备标识符(显示)")||(attrib->dynamicCall("Tag()").toString()=="连接代号"))
            {
                attrib->dynamicCall("setColorIndex(int)",McColor::mcRed);
                break;
            }
        }
        blkEnty->dynamicCall("AssertWriteEnabled()");
    }
    else if(Enty->dynamicCall("ObjectName()").toString()=="McDbMText")
    {
        Enty->dynamicCall("setColorIndex(int)",McColor::mcRed);
    }
    ui->axWidgetDiagnose->dynamicCall("UpdateDisplay()");
    /*
qDebug()<<"SetEntityRed,Handle="<<Handle;
    int OriginalColor=0xFFFFFF;
    IMxDrawEntity *Enty=(IMxDrawEntity *)ui->axWidgetDiagnose->querySubObject("HandleToObject(const QString)",Handle);
    if(Enty==nullptr) return false;
    if(Enty->dynamicCall("ObjectName()").toString()=="McDbBlockReference")
    {
        IMxDrawBlockReference* blkEnty=(IMxDrawBlockReference*)Enty;
        if(blkEnty->dynamicCall("GetBlockName()").toString()=="SPS_CDP") OriginalColor=0x00FF00;//导线定义 绿色
        else OriginalColor=0xFFFFFF;//白色
    }
    else OriginalColor=0x00FF00;//导线 绿色

    OriginalColor=0x00FF00;//导线 绿色
//qDebug()<<"OriginalColor="<<OriginalColor;
    // 准备闪烁颜色.
    MxDrawResbuf* colors = new MxDrawResbuf();
    colors->AddLong(255);
    colors->AddLong(0);
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeColor(QVariant)",colors->asVariant());
    // 设置闪烁间隔的时间
    ui->axWidgetDiagnose->dynamicCall("SetTwinkeTime(int)",500);
    // 开始闪烁
    ui->axWidgetDiagnose->dynamicCall("TwinkeEnt(QString)",Enty->ObjectID());
*/
    return true;
}

void MainWindow::on_BtnFlurUnits_clicked()
{
    FlurWndIsActive=true;
    qDebug()<<"on_BtnFlurUnits_clicked()";
    QList<QString> list_test;
    for(int i=0;i<ui->tableWidgetDiagResult->rowCount();i++)
    {
        list_test.append(ui->tableWidgetDiagResult->item(i,0)->text());
    }
    DialogFlurUnit *dlg=new DialogFlurUnit(this,&list_test);
    dlg->InitTable(2);
    dlg->showNormal();
    dlg->setWindowTitle("模糊组");
    dlg->setModal(true);

    dlg->exec();// 以模态方式显示对话框
    FlurWndIsActive=false;
    if (dlg->RetCode>0) //诊断完成被按下
    {
        SetStackIndex(6);
        ui->label_diagnosis_TestWord->setText("诊断结束");
        QString StrResult;
        for(int i=0;i<dlg->RetDiagnoseList.count();i++)
        {
            if(StrResult!="") StrResult+=" , ";
            StrResult+=dlg->RetDiagnoseList.at(i);
        }

        ui->tableWidget_DiagResult->setRowCount(0);
        QStringList ListFaultInfo=StrResult.split(",");
        for(int i=0;i<ListFaultInfo.count();i++)
        {
            ui->tableWidget_DiagResult->setRowCount(ui->tableWidget_DiagResult->rowCount()+1);
            QString DT,Gaoceng,Pos,Name,SubDT,Daihao,ModeType,RepairPlan,RepairResource;
            Daihao=ListFaultInfo.at(i).mid(0,ListFaultInfo.at(i).indexOf(":")).remove(" ");
            if(Daihao.contains("."))
            {
                DT=Daihao.mid(0,Daihao.indexOf("."));
                SubDT=Daihao.mid(Daihao.indexOf(".")+1,Daihao.count()-Daihao.indexOf(".")-1);
            }
            else DT=Daihao;

            ModeType=ListFaultInfo.at(i).mid(ListFaultInfo.at(i).indexOf(":")+1,ListFaultInfo.at(i).indexOf("(")-ListFaultInfo.at(i).indexOf(":")-1);
            QSqlQuery QueryEquipment = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString SqlStr = "SELECT * FROM Equipment WHERE DT = '"+DT+"'";
            QueryEquipment.exec(SqlStr);
            if(QueryEquipment.next())
            {
                GetUnitTermimalGaocengAndPos(0,QueryEquipment.value("Equipment_ID").toInt(),Gaoceng,Pos);
                Name=QueryEquipment.value("Name").toString();
                QStringList ListRepairInfo=QueryEquipment.value("RepairInfo").toString().split("￤￤");
                for(int j=0;j<ListRepairInfo.count();j++)
                {
                    if(SubDT!="")
                    {
                        if(ListRepairInfo.at(j).split("￤").at(0).contains(SubDT)&&(ListRepairInfo.at(j).split("￤").at(1)==ModeType))
                        {
                            RepairPlan=ListRepairInfo.at(j).split("￤").at(2);
                            RepairResource=ListRepairInfo.at(j).split("￤").at(3);
                            break;
                        }
                    }
                    else
                    {
                        if((ListRepairInfo.at(j).split("￤").at(0)=="mode")&&(ListRepairInfo.at(j).split("￤").at(1)==ModeType))
                        {
                            RepairPlan=ListRepairInfo.at(j).split("￤").at(2);
                            RepairResource=ListRepairInfo.at(j).split("￤").at(3);
                            break;
                        }
                    }
                }
            }
            else//导线
            {
                Name="导线";
                QSqlQuery QueryJXB = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                QString SqlStr = "SELECT * FROM JXB WHERE ConnectionNumber = '"+DT+"'";
                QueryJXB.exec(SqlStr);
                if(QueryJXB.next())
                {
                    GetPageGaocengAndPos(QueryJXB.value("Page_ID").toInt(),Gaoceng,Pos);
                    if(ModeType=="loose")
                    {
                        RepairPlan="紧固导线";
                        RepairResource="十字螺丝刀";
                    }
                    else if(ModeType=="broken")
                    {
                        RepairPlan="更换导线";
                        RepairResource="导线,十字螺丝刀";
                    }
                }
            }
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,0,new QTableWidgetItem(Gaoceng+"-"+Pos));//位置
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,1,new QTableWidgetItem(Name));//名称
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,2,new QTableWidgetItem(Daihao));//代号
            ModeType.replace("loose","接触不良");
            ModeType.replace("tripped","接触不良");
            ModeType.replace("blown","器件失效");
            ModeType.replace("broken","器件失效");
            ModeType.replace("unknownFault","未知故障");
            ModeType.replace("malFunction","器件失效");
            ModeType.replace("stuckOpen","卡滞");
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,3,new QTableWidgetItem(ModeType));//故障模式
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,4,new QTableWidgetItem(RepairPlan));//维修方法
            ui->tableWidget_DiagResult->setItem(ui->tableWidget_DiagResult->rowCount()-1,5,new QTableWidgetItem(RepairResource));//所需资源
        }
        ui->tableWidget_DiagResult->resizeRowsToContents();
        StrResult.replace("KA_cd1","触点");
        StrResult.replace("KA_xq1","线圈");
        StrResult.replace("loose","接触不良");
        StrResult.replace("tripped","接触不良");
        StrResult.replace("blown","器件失效");
        StrResult.replace("broken","器件失效");
        StrResult.replace("unknownFault","未知故障");
        StrResult.replace("malFunction","器件失效");
        StrResult.replace("stuckOpen","卡滞");
        ui->label_result_2->setText("故障器件："+StrResult);
    }
    delete dlg; //删除对话框
}

//获取测试点的测试代价 testpointName:HL01.ePort_in_1_2
double MainWindow::GetTestCost(QString testpointName)
{
    double RetTestCost=0;
    QStringList ListTermID=GetTestPointTermID(testpointName.mid(0,testpointName.indexOf(".")),testpointName.mid(testpointName.indexOf(".")+1,testpointName.count()-testpointName.indexOf(".")-1));
    QSqlQuery QuerySymb2TermInfo=QSqlQuery(T_ProjectDatabase);
    QString SqlStr;
    for(int i=0;i<ListTermID.count();i++)
    {
        QString TermID=ListTermID.at(i).split(",").at(0);
        SqlStr="SELECT * FROM Symb2TermInfo WHERE Symb2TermInfo_ID= "+TermID;
        QuerySymb2TermInfo.exec(SqlStr);
        if(QuerySymb2TermInfo.next())
        {
            QString TestCost=QuerySymb2TermInfo.value("TestCost").toString().remove(" ");
            if(StrIsDouble(TestCost)) RetTestCost+=TestCost.toDouble();
        }//end of if(QuerySymb2TermInfo.next())
    }//end of for(int i=0;i<ListTermID.count();i++)

    return RetTestCost;
}

void MainWindow::on_BtnSetTestPreference_clicked()
{
    DialogSetTestPreference *dlg =new DialogSetTestPreference(this);
    dlg->SetPreference(TestPointPreference);
    dlg->show();
    dlg->setModal(true);
    dlg->exec();
    if(!dlg->Canceled) TestPointPreference=dlg->TestPointPreference;
    delete dlg;
}

void MainWindow::on_BtnUserTest_clicked()
{
    qDebug()<<"ListUserTest="<<ListUserTest;
    DialogDiagUserTest *dlg=new DialogDiagUserTest();
    dlg->setWindowTitle("自定义测试选择");
    dlg->LoadTestList(ListUserTest);
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        qDebug()<<"dlg->CmdStr="<<dlg->CmdStr;
        dlg->CmdStr+="\r\nfc";
        SendCmd(dlg->CmdStr,true);
    }
    delete dlg;
}

//自动上端子
void MainWindow::on_Btn_SetTerminal_clicked()
{
    DialogAddTerminal *dlg=new DialogAddTerminal();
    dlg->setWindowTitle("上端子");
    dlg->setModal(true);
    dlg->show();
    dlg->exec();
    if(!dlg->Canceled)
    {
        //绘制端子
        formaxwidget *formMdi;
        if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
        {
            formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
            if(formMdi==nullptr) return;

            QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
            QString tempSQL="SELECT * FROM TerminalStrip WHERE DT = '"+dlg->DT+"'";
            QueryVar.exec(tempSQL);
            if(QueryVar.next())
            {
                tempSQL="SELECT * FROM Terminal WHERE TerminalStrip_ID = '"+QueryVar.value("TerminalStrip_ID").toString()+"' AND Designation = '"+QString::number(dlg->Designation)+"'";
                QueryVar.exec(tempSQL);
                if(QueryVar.next())
                {
                    //formMdi->AddTerminalTag=dlg->DT;
                    //formMdi->AddTerminalDesignation=dlg->Designation;
                    formMdi->TerminalAdd(QueryVar.value("Terminal_ID").toString());
                }
            }
        }
    }
    delete dlg;
}

void MainWindow::on_BtnDataAnalyse_clicked()
{
//    DialogTestReport *dlg=new DialogTestReport();
//    dlg->setWindowTitle("系统统计信息");
//    dlg->setModal(true);
//    Sleep(1200);
//    dlg->show();
//    dlg->exec();
//    delete dlg;

    // 创建对话框并设置样式
    QDialog *waitDialog = new QDialog(this, Qt::FramelessWindowHint | Qt::Dialog);
    waitDialog->setStyleSheet("background-color: #D3D3D3; color: black;font: 75 12pt;"); // 设置灰底黑字的样式
    waitDialog->setFixedSize(400, 100); // 设置对话框的大小

    // 创建布局和标签
    QVBoxLayout *layout = new QVBoxLayout(waitDialog);
    QLabel *label = new QLabel("正在分析计算测试性评价指标，请稍候...");
    //label->setFont(QFont("Arial", 10)); // 设置字体大小
    label->setAlignment(Qt::AlignCenter); // 文本居中
    layout->addWidget(label);
    waitDialog->setLayout(layout);

    // 设置对话框为模态
    waitDialog->setWindowModality(Qt::WindowModal);

    // 显示对话框
    waitDialog->show();

    // 设置计时器在1200毫秒后触发
    int waitTime = 200;
    if(CurProjectName=="双电机拖曳收放装置") waitTime=1200;
    else if(CurProjectName=="收放存储装置") waitTime=975;
    else if(CurProjectName=="尾轴密封试验装置") waitTime=240;
    QTimer::singleShot(waitTime, this, [this, waitDialog]() {
        // 关闭等待对话框
        waitDialog->accept();
        // 删除对话框
        waitDialog->deleteLater();
        // 显示报告对话框
        CurComponentCount = ui->tableWidgetUnit->rowCount(); // 获取行数
        DialogTestReport *dlg = new DialogTestReport(); // 通过构造函数传递行数
        dlg->setWindowTitle("系统统计信息");
        dlg->setModal(true);
        dlg->exec();
        delete dlg;
    });
}


void MainWindow::on_BtnMultiLibManage_clicked()
{
    DialogMultiLib *dlg=new DialogMultiLib(this);
    dlg->setWindowTitle("多端元件库");
    dlg->setModal(true);
    dlg->show();
    dlg->exec();

    if(dlg->Canceled) return;
    if(dlg->RetCode==1) //修改符号
    {
        //创建新的mdi
        formaxwidget *formMxdraw=new formaxwidget(this);
        formMxdraw->setWindowTitle(dlg->OpenFilePath);
        connect(formMxdraw,SIGNAL(SignalCloseMdiWnd(int)),this,SLOT(CloseMdiWnd(int)));
        QMdiSubWindow *mdisubwindow= ui->mdiArea->addSubWindow (formMxdraw) ;
        formMxdraw->mdisubwindow=mdisubwindow;
        formMxdraw->IsDrawingMultiLib=true;
        formMxdraw->EditMultiLib(dlg->OpenFilePath);
    }
    else if(dlgDialogSymbols->RetCode==3) //增加库文件
    {
        //在现有的窗口中选择图形
        if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
        {
            formaxwidget *formMdi;
            formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
            if(formMdi!=nullptr)
            {
                connect(formMdi,SIGNAL(SignalSelectDone(int)),this,SLOT(SlotNewSymbol(int)));
                formMdi->NewSymbolDwgName=dlgDialogSymbols->Symb2_Name+".dwg";
                formMdi->SelectEntitys();
            }
        }
        else//没有打开的主窗口，直接新建
        {
            qDebug()<<"没有打开的主窗口，直接新建";
            QString SourceFileName="C:/TBD/data/SymbolTemplate.dwg";
            QString DestinationFileName="C:/TBD/SYMB2LIB/"+dlgDialogSymbols->Symb2_Name+".dwg";
            QFile::copy(SourceFileName,DestinationFileName);
            SlotNewSymbol(1);
        }
    }

    delete dlg;
}

void MainWindow::on_BtnSetCentrePoint_clicked()
{
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formaxwidget *formMdi;
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi!=nullptr)
        {
            if(formMdi->IsDrawingMultiLib)
                formMdi->GetAxWidget()->dynamicCall("DoCommand(const int&)",104);
        }
    }
}

void MainWindow::on_mdiArea_subWindowActivated(QMdiSubWindow *arg1)
{
    if(arg1==nullptr) return;
    bool IsMultiLib=false;
    if(arg1->windowTitle().contains(".dwg"))
    {
        formaxwidget *formMdi=(formaxwidget*)arg1;
        if(formMdi->IsDrawingMultiLib) IsMultiLib=true;
    }
    if(IsMultiLib)
    {
        ui->BtnSetCentrePoint->setEnabled(true);
        ui->Btn_MultiLine->setEnabled(false);
        ui->Btn_SetTerminal->setEnabled(false);
        ui->Btn_BlackBox->setEnabled(true);
        ui->Btn_StructBox->setEnabled(false);
        ui->Btn_TypicalDwg->setEnabled(false);
        ui->Btn_LineDefine->setEnabled(false);
        ui->Btn_CableDefine->setEnabled(false);
    }
    else
    {
        ui->BtnSetCentrePoint->setEnabled(false);
        ui->Btn_MultiLine->setEnabled(true);
        ui->Btn_SetTerminal->setEnabled(true);
        ui->Btn_BlackBox->setEnabled(true);
        ui->Btn_StructBox->setEnabled(true);
        ui->Btn_TypicalDwg->setEnabled(true);
        ui->Btn_LineDefine->setEnabled(true);
        ui->Btn_CableDefine->setEnabled(true);
    }
}

//放置文字
void MainWindow::on_BtnPutText_clicked()
{
    QDialog *dialogTextStr =new QDialog();
    dialogTextStr->setWindowTitle("请输入插入的文字内容");
    dialogTextStr->setMinimumSize(QSize(300,60));
    QFormLayout *formlayoutDesignation = new QFormLayout(dialogTextStr);
    QLineEdit *m_LineEdit = new QLineEdit(dialogTextStr);

    QHBoxLayout *layoutBtn = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogTextStr);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogTextStr);
    pushbuttonCancel->setText("取消");
    layoutBtn->addWidget(pushbuttonOK);
    layoutBtn->addWidget(pushbuttonCancel);
    formlayoutDesignation->addRow(m_LineEdit);
    formlayoutDesignation->addRow(layoutBtn);
    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogTextStr,SLOT(accept()));
    if (dialogTextStr->exec()!=QDialog::Accepted) return;

    formaxwidget *formMdi;
    if (ui->mdiArea->subWindowList().count()>0) //如果有打开的主窗口，获取活动窗口
    {
        formMdi=(formaxwidget*)ui->mdiArea->activeSubWindow()->widget();
        if(formMdi==nullptr) return;
        formMdi->LoadText(m_LineEdit->text());
    }
}

void MainWindow::on_BtnClearDB_clicked()
{
    QSqlQuery QueryPage=QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Page ORDER BY Page_ID ASC";
    QueryPage.exec(SqlStr);
    while(QueryPage.next())
    {
        QString dwgfilename=GetPageNameByPageID(QueryPage.value("Page_ID").toInt());
        QString dwgfilepath=CurProjectPath+"/"+dwgfilename+".dwg";
        QFile dwgfile(dwgfilepath);
        if(!dwgfile.exists()) continue;
        GlobalBackAxWidget->dynamicCall("OpenDwgFile(QString)",dwgfilepath);
        QSqlQuery QueryTerminalInstance=QSqlQuery(T_ProjectDatabase);
        QSqlQuery QueryDELETE=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM TerminalInstance WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"'";
        QueryTerminalInstance.exec(SqlStr);
        while(QueryTerminalInstance.next())
        {
            IMxDrawEntity *BlkSearch=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryTerminalInstance.value("Handle").toString());
            qDebug()<<"QueryTerminalInstance.value(Handle).toString()="<<QueryTerminalInstance.value("Handle").toString();
            if((BlkSearch==nullptr)||EntyIsErased(GlobalBackAxWidget,BlkSearch))
            {
                qDebug()<<"delete "<<QueryTerminalInstance.value("Handle").toString();
                SqlStr =  "DELETE FROM TerminalInstance WHERE TerminalInstanceID = "+QueryTerminalInstance.value("TerminalInstanceID").toString();
                QueryDELETE.exec(SqlStr);
            }
        }

        QSqlQuery QueryConnector=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Connector WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"'";
        QueryConnector.exec(SqlStr);
        while(QueryConnector.next())
        {
            IMxDrawEntity *BlkSearch=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryConnector.value("Connector_Handle").toString());
            if((BlkSearch==nullptr)||EntyIsErased(GlobalBackAxWidget,BlkSearch))
            {
                SqlStr =  "DELETE FROM Connector WHERE Connector_ID = "+QueryConnector.value("Connector_ID").toString();
                QueryDELETE.exec(SqlStr);
            }
        }

        QSqlQuery QueryWires=QSqlQuery(T_ProjectDatabase);
        SqlStr="SELECT * FROM Wires WHERE Page_ID = '"+QueryPage.value("Page_ID").toString()+"'";
        QueryWires.exec(SqlStr);
        while(QueryWires.next())
        {
            IMxDrawEntity *BlkSearch=(IMxDrawEntity *)GlobalBackAxWidget->querySubObject("HandleToObject(const QString)",QueryWires.value("Handle").toString());
            if((BlkSearch==nullptr)||EntyIsErased(GlobalBackAxWidget,BlkSearch))
            {
                SqlStr =  "DELETE FROM Wires WHERE Wires_ID = "+QueryWires.value("Wires_ID").toString();
                QueryDELETE.exec(SqlStr);
            }
        }
        //清除重叠的连线
        IMxDrawSelectionSet *ssLINE= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
        IMxDrawResbuf *filterLINE=(IMxDrawResbuf *)GlobalBackAxWidget->querySubObject("NewResbuf()");
        filterLINE->AddStringEx("LINE",5020);
        filterLINE->AddStringEx("CONNECT", 8);
        ssLINE->dynamicCall("AllSelect(QVariant)",filterLINE->asVariant());
        int Cnt=ssLINE->dynamicCall("Count()").toInt();
        for(int LineIndex=0;LineIndex<Cnt;LineIndex++)
        {
            IMxDrawLine *mLine= (IMxDrawLine *)ssLINE->querySubObject("Item(int)",LineIndex);
            if(EntyIsErased(GlobalBackAxWidget,(IMxDrawEntity *)mLine)) continue;//去除erase的实体
            IMxDrawSelectionSet *ss= (IMxDrawSelectionSet *)GlobalBackAxWidget->querySubObject("NewSelectionSet()");
            //创建过滤对象
            MxDrawResbuf* filter =new MxDrawResbuf();
            filter->AddStringEx("LINE",5020);
            filter->AddStringEx("CONNECT", 8);
            for(int k=0;k<2;k++)
            {
                if(k==0) ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->asVariant(),filter->asVariant());
                if(k==1) ss->dynamicCall("SelectAtPoint(QAxObject*,QAxObject*)",((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->asVariant(),filter->asVariant());
                qDebug()<<"ss.Count()="<<ss->Count();
                for (int i = 0; i < ss->Count(); i++)
                {
                    IMxDrawLine* mLineCross = (IMxDrawLine *)ss->querySubObject("Item(int)",i);
                    if(EntyIsErased(GlobalBackAxWidget,(IMxDrawEntity *)mLineCross)) continue;//去除erase的实体
                    if(mLineCross->dynamicCall("handle()").toString()==mLine->dynamicCall("handle()").toString()) continue;//排除自身
                    //mLineCross是mLine的子线段（被包含）
                    double mLineStartx=((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->x();
                    double mLineStarty=((IMxDrawPoint *)mLine->querySubObject("StartPoint()"))->y();
                    double mLineEndx=((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->x();
                    double mLineEndy=((IMxDrawPoint *)mLine->querySubObject("EndPoint()"))->y();
                    double mLineCrossStartx=((IMxDrawPoint *)mLineCross->querySubObject("StartPoint()"))->x();
                    double mLineCrossStarty=((IMxDrawPoint *)mLineCross->querySubObject("StartPoint()"))->y();
                    double mLineCrossEndx=((IMxDrawPoint *)mLineCross->querySubObject("EndPoint()"))->x();
                    double mLineCrossEndy=((IMxDrawPoint *)mLineCross->querySubObject("EndPoint()"))->y();
                    bool ShouldErase=false;

                    if((GetLineDir(mLine)=="水平")&&(GetLineDir(mLineCross)=="水平"))
                    {
                        if(mLineStartx<mLineEndx)
                        {
                            if((mLineStartx<=mLineCrossStartx)&&(mLineStartx<=mLineCrossEndx)&&(mLineEndx>=mLineCrossStartx)&&(mLineEndx>=mLineCrossEndx)) ShouldErase=true;
                        }
                        else
                        {
                            if((mLineStartx>=mLineCrossStartx)&&(mLineStartx>=mLineCrossEndx)&&(mLineEndx<=mLineCrossStartx)&&(mLineEndx<=mLineCrossEndx)) ShouldErase=true;
                        }
                    }
                    else if((GetLineDir(mLine)=="垂直")&&(GetLineDir(mLineCross)=="垂直"))
                    {
                        if(mLineStarty<mLineEndy)
                        {
                            if((mLineStarty<=mLineCrossStarty)&&(mLineStarty<=mLineCrossEndy)&&(mLineEndy>=mLineCrossStarty)&&(mLineEndy>=mLineCrossEndy)) ShouldErase=true;
                        }
                        else
                        {
                            if((mLineStarty>=mLineCrossStarty)&&(mLineStarty>=mLineCrossEndy)&&(mLineEndy<=mLineCrossStarty)&&(mLineEndy<=mLineCrossEndy)) ShouldErase=true;
                        }
                    }
                    if(ShouldErase) mLineCross->dynamicCall("Erase()");
                }
            }//end of for(int k=0;k<2;k++)
        }//for(int LineIndex=0;LineIndex<Cnt;LineIndex++)
        GlobalBackAxWidget->dynamicCall("SaveDwgFile(QString)",dwgfilepath);
    }
}


void MainWindow::on_CbTestType_currentIndexChanged(const QString &arg1)
{
    if(ui->CbTestType->currentText()=="电压") ui->LbDW->setText("V");
    else if(ui->CbTestType->currentText()=="电流") ui->LbDW->setText("A");
    else if(ui->CbTestType->currentText()=="电阻") ui->LbDW->setText("R");
}
