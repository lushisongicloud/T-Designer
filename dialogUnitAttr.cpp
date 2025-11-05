#include "dialogUnitAttr.h"
#include "ui_dialogUnitAttr.h"
#include "BO/function/tmodelvalidator.h"
#include "BO/function/tmodelcheckservice.h"
#include "BO/function/tmodelhelper.h"
#include "widget/portconfigpanel.h"
#include "widget/portconfigeditdialog.h"
#include "widget/containerhierarchyutils.h"
#include "BO/containerrepository.h"
#include "widget/tmodelcompiledisplaydialog.h"
#include <algorithm>
#include <QJsonDocument>
#include <QJsonArray>
#include <QJsonObject>
#include <QJsonValue>
#include <QMap>
#include <QMenu>
#include <QMessageBox>
#include <QRegularExpression>
extern int SelectEquipment_ID;
extern int SelectSymbol_ID;
extern QStringList RemovedUnitsInfo;
extern QSqlDatabase T_ProjectDatabase;
DialogUnitAttr::DialogUnitAttr(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::DialogUnitAttr)
{
    ui->setupUi(this);
    ui->tableWidgetUnitAttr->setRowCount(6);
    ui->tableWidgetUnitAttr->setColumnWidth(0,100);//属性名
    ui->tableWidgetUnitAttr->setColumnWidth(1,600);//数值

    ui->tableWidgetUnitAttr->setItem(0,0,new QTableWidgetItem("元件描述"));
    ui->tableWidgetUnitAttr->setItem(0,1,new QTableWidgetItem(""));
    ui->tableWidgetUnitAttr->setItem(1,0,new QTableWidgetItem("元件备注"));
    ui->tableWidgetUnitAttr->setItem(1,1,new QTableWidgetItem(""));
    ui->tableWidgetUnitAttr->setItem(2,0,new QTableWidgetItem("技术参数"));
    ui->tableWidgetUnitAttr->setItem(2,1,new QTableWidgetItem(""));
    ui->tableWidgetUnitAttr->setItem(3,0,new QTableWidgetItem("功能文本"));
    ui->tableWidgetUnitAttr->setItem(3,1,new QTableWidgetItem(""));
    ui->tableWidgetUnitAttr->setItem(4,0,new QTableWidgetItem("铭牌文本"));
    ui->tableWidgetUnitAttr->setItem(4,1,new QTableWidgetItem(""));
    ui->tableWidgetUnitAttr->setItem(5,0,new QTableWidgetItem("装配地点"));
    ui->tableWidgetUnitAttr->setItem(5,1,new QTableWidgetItem(""));

    ui->tableWidgetSpur->setColumnWidth(0,100);//编号
    ui->tableWidgetSpur->setColumnWidth(1,100);//子块代号
    //ui->tableWidgetSpur->setColumnHidden(4,true);

    // 修改tableWidgetStructure为常量表，4列：常量名、值、单位、备注
    ui->tableWidgetStructure->setColumnCount(4);
    ui->tableWidgetStructure->setHorizontalHeaderLabels({"常量名", "值", "单位", "备注"});
    ui->tableWidgetStructure->setColumnWidth(0,100);//常量名
    ui->tableWidgetStructure->setColumnWidth(1,100);//值
    ui->tableWidgetStructure->setColumnWidth(2,100);//单位
    ui->tableWidgetStructure->horizontalHeader()->setStretchLastSection(true);//最后一列自适应
    ui->tableWidgetStructure->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableWidgetStructure->setSelectionMode(QAbstractItemView::ExtendedSelection);
    ui->tableWidgetStructure->setEditTriggers(QAbstractItemView::DoubleClicked | QAbstractItemView::EditKeyPressed);
    
    // 设置右键菜单
    ui->tableWidgetStructure->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->tableWidgetStructure, SIGNAL(customContextMenuRequested(QPoint)), 
            this, SLOT(showConstantsContextMenu(QPoint)));

    ui->tableRepairInfo->setColumnWidth(0,200);//故障模式
    ui->tableRepairInfo->setColumnWidth(1,100);//故障概率
    ui->tableRepairInfo->setColumnWidth(2,300);//解决方案
    ui->tableRepairInfo->setColumnWidth(3,240);//所需资源
    
    // 设置tableRepairInfo右键菜单
    ui->tableRepairInfo->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->tableRepairInfo, SIGNAL(customContextMenuRequested(QPoint)), 
            this, SLOT(showRepairInfoContextMenu(QPoint)));

    ui->tableTerm->setColumnWidth(0,60);
    ui->tableTerm->setColumnWidth(1,40);
    ui->tableTerm->setColumnWidth(2,80);
    ui->tableTerm->setColumnWidth(3,80);
    ui->tableTerm->setColumnWidth(4,60);
    ui->tableTerm->setColumnWidth(5,50);

    Canceled=true;
    UnitTypeChanged=false;
    UnitProSetUpdated=false;
    UnitTagChanged=false;
    InitTEdit();
    const int tab5Index = ui->tabWidget->indexOf(ui->tab_5);
    const int tab3Index = ui->tabWidget->indexOf(ui->tab_3);
    if (tab5Index != -1) {
        ui->tabWidget->removeTab(tab5Index);
    }
    if (tab3Index != -1) {
        ui->tabWidget->removeTab(tab3Index);
    }
    dlgUnitManage=new DialogUnitManage(this);
    ui->tabWidget->setCurrentIndex(0);

    m_scene.setBackgroundBrush(Qt::gray);
    ui->graphicsView->setScene(&m_scene);
    QPixmap pix("");
    m_dialogTag=new dialogTag(ui->frameTag);
    connect(m_dialogTag,SIGNAL(DrawTag(int,QColor)),this,SLOT(SlotDrawTagWrapper(int,QColor)));
    connect(m_dialogTag,SIGNAL(ChangeColor(QColor)),this,SLOT(SlotChangeColorWrapper(QColor)));
    ui->tableWidgetUnitPic->setColumnWidth(0,200);

    m_scene_term.setBackgroundBrush(Qt::gray);
    ui->graphicsView_Term->setScene(&m_scene_term);
    m_dialogTermTag=new dialogTag(ui->frameTag_Term);
    connect(m_dialogTermTag,SIGNAL(DrawTag(int,QColor)),this,SLOT(SlotDrawTermTagWrapper(int,QColor)));
    connect(m_dialogTermTag,SIGNAL(ChangeColor(QColor)),this,SLOT(SlotChangeTermColorWrapper(QColor)));

    // m_portConfigPanel = ui->portConfigPanel;  // 已移除独立的PortConfigPanel控件
    // if (m_portConfigPanel) {
    //     m_portConfigPanel->setDatabase(T_ProjectDatabase);
    //     loadPortConfig(0);
    // }

    // 设置 tableTerm 右键菜单
    ui->tableTerm->setContextMenuPolicy(Qt::CustomContextMenu);
    connect(ui->tableTerm, SIGNAL(customContextMenuRequested(QPoint)), this, SLOT(showTableTermContextMenu(QPoint)));
}

DialogUnitAttr::~DialogUnitAttr()
{
    delete ui;
}
void DialogUnitAttr::closeEvent(QCloseEvent *event) {
    ui->tabWidget->setCurrentIndex(0);//默认回到主属性页
    m_scene.SetBackGroundImage(QPixmap(""));//清空图片
    m_scene_term.SetBackGroundImage(QPixmap(""));//清空图片
    QDialog::closeEvent(event);
}
void DialogUnitAttr::ReloadLib()
{
    dlgUnitManage->LoadDBGroup();
}

void DialogUnitAttr::InitUIInfo()
{
    ui->LbProTag->setText("");
    ui->EdUnitTag->setText("");
    ui->CbPartCode->setCurrentText("");
    ui->LbType->setText("");
    ui->LbName->setText("");
    ui->LbFactory->setText("");
    ui->LbOrderNum->setText("");
    ui->tableWidgetUnitAttr->item(0,1)->setText("");
    ui->tableWidgetUnitAttr->item(1,1)->setText("");
    QsciEdit->setText("");
    ui->tableWidgetSpur->setRowCount(0);
    ui->tableWidgetStructure->setRowCount(0);
    loadPortConfig(0);
}

void DialogUnitAttr::UpdateUIInfo(QSqlQuery QueryEquipment)//dataFunc 从工程数据库中加载信息到界面
{
    QString ProjectStructure_ID=QueryEquipment.value("ProjectStructure_ID").toString();
    NewProjectStructure_ID=ProjectStructure_ID.toInt();
    // qDebug()<<"NewProjectStructure_ID="<<NewProjectStructure_ID;
    StrProTag=GetProjectStructureStrByProjectStructureID(NewProjectStructure_ID);
    //qDebug()<<"StrProTag="<<StrProTag;
    QString UnitTag=QueryEquipment.value("DT").toString();
    QString curSupplier = QueryEquipment.value("Factory").toString();
    ui->LbProTag->setText(StrProTag+"-"+UnitTag);
    ui->EdUnitTag->setText(UnitTag);
    ui->CbPartCode->setCurrentText(QueryEquipment.value("PartCode").toString());
    ui->LbType->setText(QueryEquipment.value("Type").toString());
    ui->LbName->setText(QueryEquipment.value("Name").toString());
    ui->LbFactory->setText(curSupplier);
    ui->LbOrderNum->setText(QueryEquipment.value("OrderNum").toString());
    ui->EdMTBF->setText(QueryEquipment.value("MTBF").toString());
    ui->tableWidgetUnitAttr->item(0,1)->setText(QueryEquipment.value("Desc").toString());
    ui->tableWidgetUnitAttr->item(1,1)->setText(QueryEquipment.value("SymbRemark").toString());

    //Lu ToDo 照片及标注信息加载
    //ui->tableWidgetUnitPic 第1列为“图片”，第2列为“已标注”
    fillUnitPicTable(QueryEquipment.value("Picture").toString(),QueryEquipment.value("Factory").toString());

    loadPortConfig(QueryEquipment.value("Equipment_ID").toInt());

    QsciEdit->setText(QueryEquipment.value("TModel").toString());
    
    // 加载常量数据（从Structure字段）
    loadConstants(QueryEquipment.value("Structure").toString());
    
    //维修信息 - 使用新格式加载（故障模式、故障概率、解决方案、所需资源）
    TModelHelper::loadRepairInfoToTable(ui->tableRepairInfo, QueryEquipment.value("RepairInfo").toString());
    
    if(ui->tableRepairInfo->rowCount()>0)
    {
        ui->tableRepairInfo->setCurrentIndex(ui->tableRepairInfo->model()->index(0,0));
        on_tableRepairInfo_clicked(ui->tableRepairInfo->model()->index(0,0));
    }

    //自动生成变量定义代码
    //(declare-fun %FU%.1.i () Real)
    QString VariableText="";

    QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM Symbol WHERE Equipment_ID = '"+QueryEquipment.value("Equipment_ID").toString()+"'";
    QuerySymbol.exec(SqlStr);
    ui->tableWidgetSpur->setRowCount(0);
    ui->tableTerm->setRowCount(0);
    QStringList ListInterConnectInfo;
    while(QuerySymbol.next())
    {
        if((QuerySymbol.value("FuncType").toString()=="虚拟端口-观测布尔量")||(QuerySymbol.value("FuncType").toString()=="虚拟端口-观测实数量"))
        {
            if(VariableText!="") VariableText+="\n";
            QString UnitText="";
            if(QuerySymbol.value("FuncType").toString()=="虚拟端口-观测布尔量") UnitText="Bool";
            else if(QuerySymbol.value("FuncType").toString()=="虚拟端口-观测实数量") UnitText="Real";
            VariableText+="(declare-fun %"+UnitTag+"%."+QuerySymbol.value("FunDefine").toString()+" () "+UnitText+")";
        }
        ui->tableWidgetSpur->setRowCount(ui->tableWidgetSpur->rowCount()+1);

        //Lu ToDo 根据Symbol_ID查询并加载Symb2TermInfo（端子信息）
        QString Symbol_ID=QuerySymbol.value("Symbol_ID").toString();
        QSqlQuery QuerySymb2TermInfo= QSqlQuery(T_ProjectDatabase);
        SqlStr=QString("SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+Symbol_ID+"'");
        QuerySymb2TermInfo.exec(SqlStr);
        QString spurDT = QuerySymbol.value("Show_DT").toString();
        QString SpurDescStr;
        QStringList StrListTestCost,StrListConnNum;
        while(QuerySymb2TermInfo.next())
        {
            QString StrConnNum = QuerySymb2TermInfo.value("ConnNum").toString();
            QString StrTestCost = QuerySymb2TermInfo.value("TestCost").toString();

            if(StrConnNum.isEmpty())StrConnNum = "?";
            StrListConnNum.append(StrConnNum);
            if(!StrTestCost.isEmpty())StrListTestCost.append(StrTestCost);//后期应优化，如何处理好功能子块与端子的测试代价

            if((QuerySymbol.value("FuncType").toString()=="接线端口")||(QuerySymbol.value("FuncType").toString()==""))
            {
                if(VariableText!="") VariableText+="\n";
                VariableText+="(declare-fun %"+UnitTag+"%."+QuerySymb2TermInfo.value("ConnNum").toString()+".i () Real)\n";
                VariableText+="(declare-fun %"+ui->EdUnitTag->text()+"%."+QuerySymb2TermInfo.value("ConnNum").toString()+".u () Real)";
            }

            //端子配置ui->tableTerm
            //0）子块代号 1）端号 2）描述 3）变量 4）测试代价 5）是否标注 6）图片路径
            ui->tableTerm->setRowCount(ui->tableTerm->rowCount()+1);

            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,0,new QTableWidgetItem(spurDT));
            ui->tableTerm->item(ui->tableTerm->rowCount()-1,0)->setData(Qt::UserRole,QuerySymbol.value("Symbol_ID").toString());
            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,1,new QTableWidgetItem(QuerySymb2TermInfo.value("ConnNum").toString()));
            ui->tableTerm->item(ui->tableTerm->rowCount()-1,1)->setData(Qt::UserRole,QuerySymb2TermInfo.value("Symb2TermInfo_ID").toString());
            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,2,new QTableWidgetItem(QuerySymb2TermInfo.value("ConnDesc").toString()));
            
            // 获取端口配置的变量
            QString variables = getPortVariables(spurDT, QuerySymb2TermInfo.value("ConnNum").toString());
            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,3,new QTableWidgetItem(variables));
            
            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,4,new QTableWidgetItem(QuerySymb2TermInfo.value("TestCost").toString()));

            QMap<QString, QString> imagePaths; // 文件名与路径的映射
            QMap<QString, QString> tagInfos;   // 文件名与标注信息的映射

            // 定义要搜索的目录
            QStringList searchDirs = {
                CurProjectPath + QString(PROJECT_PIC_PATH),
                QString(PIC_BASE_PATH) + "/" + curSupplier,
                QString(PIC_BASE_PATH)
            };
            QString strPicRecord = QuerySymb2TermInfo.value("TermPicPath").toString();
            if(!strPicRecord.isNull() && !strPicRecord.isEmpty()){
                processPictureInfo(strPicRecord, curSupplier, searchDirs,
                                   imagePaths, tagInfos);
            }

            // 解析并填充 "是否标注" 和 "图片路径" 列
            QString fileName;
            if (!imagePaths.isEmpty()) {
                fileName = imagePaths.keys().first(); // 取第一个文件名
            }
            QString absoluteImagePath = imagePaths.value(fileName);
            QString strTagInfo = tagInfos.value(fileName);
            // 5）是否标注
            QString annotated = (!strTagInfo.isEmpty() && !absoluteImagePath.isEmpty()) ? "是" : "否";
            ui->tableTerm->setItem(ui->tableTerm->rowCount() - 1, 5, new QTableWidgetItem(annotated));
            ui->tableTerm->item(ui->tableTerm->rowCount() - 1, 5)->setData(Qt::UserRole, strTagInfo);
            // 6）图片路径
            ui->tableTerm->setItem(ui->tableTerm->rowCount() - 1, 6, new QTableWidgetItem(absoluteImagePath));
        }

        SpurDescStr=QuerySymbol.value("Show_DT").toString();
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,0,new QTableWidgetItem(StrListConnNum.join("￤")));
        ui->tableWidgetSpur->item(ui->tableWidgetSpur->rowCount()-1,0)->setFlags(ui->tableWidgetSpur->item(ui->tableWidgetSpur->rowCount()-1,0)->flags()&(~Qt::ItemIsEditable));
        ui->tableWidgetSpur->item(ui->tableWidgetSpur->rowCount()-1,0)->setData(Qt::UserRole,QVariant(QuerySymbol.value("Symbol_ID").toString()));
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,1,new QTableWidgetItem(SpurDescStr));

        QTableWidgetItem *ItemSourceConn=new QTableWidgetItem(QuerySymbol.value("SourcePrior").toString());//优先级
        if(QuerySymbol.value("SourceConn").toBool()) ItemSourceConn->setCheckState(Qt::Checked);
        else
        {
            if((QuerySymbol.value("FuncType").toString()=="")||(QuerySymbol.value("FuncType").toString()=="接线端口"))
                ItemSourceConn->setCheckState(Qt::Unchecked);
        }
        //ItemSourceConn->setFlags(ItemSourceConn->flags()&(~Qt::ItemIsEditable));

        QTableWidgetItem *ItemExecConn=new QTableWidgetItem("");
        if(QuerySymbol.value("ExecConn").toBool()) ItemExecConn->setCheckState(Qt::Checked);
        else
        {
            if((QuerySymbol.value("FuncType").toString()=="")||(QuerySymbol.value("FuncType").toString()=="接线端口"))
                ItemExecConn->setCheckState(Qt::Unchecked);
        }
        ItemExecConn->setFlags(ItemExecConn->flags()&(~Qt::ItemIsEditable));
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,2,ItemSourceConn);//源端口
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,3,ItemExecConn);//终端端口
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,4,new QTableWidgetItem(StrListTestCost.join("￤")));
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,5,new QTableWidgetItem(""));//受控
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,6,new QTableWidgetItem(QuerySymbol.value("Symbol_Desc").toString()));//受控
        if(QuerySymbol.value("InterConnect").toString()!="")
        {
            ListInterConnectInfo.append(QString::number(ui->tableWidgetSpur->rowCount()-1)+":"+QuerySymbol.value("InterConnect").toString());
        }
    }//end of while(QuerySymbol.next())

    if(ui->tableTerm->rowCount()>0)
    {
        ui->tableTerm->setCurrentIndex(ui->tableTerm->model()->index(0,0));
        on_tableTerm_clicked(ui->tableTerm->currentIndex());
    }

    for(int i=0;i<ListInterConnectInfo.count();i++)
    {
        QString StrInterConnectInfo=ListInterConnectInfo.at(i).split(":").at(1);//(13,14);(16,17)
        QStringList ListCoupleSpur=StrInterConnectInfo.split(";");//(13,14)
        QString StrTable;
        for(QString StrInterSpur:ListCoupleSpur)
        {
            if(StrTable!="") StrTable+=";";
            StrTable+="(";
            for(QString StrSpur:StrInterSpur.remove("(").remove(")").split(",")) //ListInterSpur.append(StrSpur);
            {
                if(!StrTable.endsWith("(")) StrTable+=",";
                for(int j=0;j<ui->tableWidgetSpur->rowCount();j++)
                {
                    if(StrSpur==ui->tableWidgetSpur->item(j,0)->data(Qt::UserRole).toString())
                    {
                        StrTable+=QString::number(j+1);
                    }
                }
            }
            StrTable+=")";
        }
        ui->tableWidgetSpur->item(ListInterConnectInfo.at(i).split(":").at(0).toInt(),5)->setText(StrTable);
    }
    //QsciEditVariable->setText(VariableText);
    if(ui->tableWidgetSpur->rowCount()>0)
    {
        QuerySymbol.first();
        ui->tableWidgetSpur->setCurrentItem(ui->tableWidgetSpur->item(0,0));
        ui->LbSpurFuncName->setText(QuerySymbol.value("FunDefine").toString());
        QString Symbol=QuerySymbol.value("Symbol").toString();
        if(Symbol.contains("SPS_"))  UnitSymbolsView("C:/TBD/SPS/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
        else if(Symbol.contains("ES2_")) UnitSymbolsView("C:/TBD/SYMB2LIB/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
    }


}
//Mode=1:add  Mode=2:modify
void DialogUnitAttr::LoadInfo(int Mode,int Equipment_ID)
{
    AttrMode=Mode;
    if(Mode==1) {ui->LbProTag->setText(StrProTag);return;}
    CurEquipment_ID=QString::number(Equipment_ID);

    QSqlQueryModel *model = new QSqlQueryModel(this);
    model->setQuery("SELECT PartCode FROM Equipment", T_ProjectDatabase);

    if (model->lastError().isValid()) {
        qDebug() << "Error executing SQL query:" << model->lastError().text();
    } else {
        ui->CbPartCode->setModel(model);
        ui->CbPartCode->setModelColumn(0); // 设置模型列，假设PartCode是第一列
    }

    QSqlQuery QueryEquipment= QSqlQuery(T_ProjectDatabase);
    QString SqlStr=QString("SELECT * FROM Equipment WHERE Equipment_ID= "+QString::number(Equipment_ID));
    QueryEquipment.exec(SqlStr);
    if(!QueryEquipment.next()) return;
    LoadDiagnoseParameter();
    UpdateUIInfo(QueryEquipment);
}

//载入CurEquipment_ID元件诊断参数，元件变量定义及元件约束定义
void DialogUnitAttr::LoadDiagnoseParameter()
{
    QSqlQuery QueryEquipmentDiagnosePara= QSqlQuery(T_ProjectDatabase);
    QString SqlStr="SELECT * FROM EquipmentDiagnosePara WHERE Equipment_ID= '"+CurEquipment_ID+"'";
    QueryEquipmentDiagnosePara.exec(SqlStr);
    if(!QueryEquipmentDiagnosePara.next()) return;
    ui->tableUnitDiagnosePara->setRowCount(0);
    ui->tableUnitDiagnosePara->setRowCount(ui->tableUnitDiagnosePara->rowCount()+1);
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,0,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("Name").toString()));//名称
    ui->tableUnitDiagnosePara->item(ui->tableUnitDiagnosePara->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipmentDiagnosePara.value("DiagnoseParaID").toString());
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,1,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("Unit").toString()));//单位
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,2,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("CurValue").toString()));//当前值
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,3,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("DefaultValue").toString()));//默认值
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,4,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("Remark").toString()));//备注
}

void DialogUnitAttr::on_BtnProSet_clicked()
{
    dlgPageNameSet.LoadTable(ui->LbProTag->text(),2);//Mode=1:Page项目代号  Mode=2:Unit项目代号
    dlgPageNameSet.HideEdPageName();
    dlgPageNameSet.setModal(true);
    dlgPageNameSet.show();
    dlgPageNameSet.exec();
    if(!dlgPageNameSet.Canceled)
    {
        UnitProSetUpdated=true;
        StrProTag=dlgPageNameSet.ReturnUnitPro;
        qDebug()<<"StrProTag="<<StrProTag;
        ui->LbProTag->setText(StrProTag+"-"+ui->EdUnitTag->text());
    }
}
void DialogUnitAttr::InitTEdit()
{
    //设置字体
    QFont font("Courier", 10, QFont::Normal);
    QFontMetrics fontmetrics = QFontMetrics(font);
    QscilexerCppAttach *textLexer = new QscilexerCppAttach;
    textLexer->setColor(QColor(Qt:: yellow),QsciLexerCPP::CommentLine);    //设置自带的注释行为绿色
    textLexer->setColor(QColor(Qt::red),QsciLexerCPP::KeywordSet2);
    int line,col;
    /*
    QsciEditVariable = new QsciScintilla();
    ui->TEditLayout_Variable->addWidget(QsciEditVariable);
    ui->frame_EditVariable->setLayout(ui->TEditLayout_Variable);

    //connect(QsciEdit, SIGNAL(textChanged()),this, SLOT(ModelWasModified()));
    //setCurrentFile("");

    QsciEditVariable->setFont(font);
    QsciEditVariable->setMarginsFont(font);

    //设置左侧行号栏宽度等
    QsciEditVariable->setMarginWidth(0, fontmetrics.width("000"));
    QsciEditVariable->setMarginLineNumbers(0, true);
    QsciEditVariable->setBraceMatching(QsciScintilla::SloppyBraceMatch);
    QsciEditVariable->setTabWidth(4);
    //设置括号等自动补全
    QsciEditVariable->setAutoIndent(true);
    //初始设置c++解析器
    //textEdit->setLexer(new QsciLexerCPP(this));

    QsciEditVariable->setLexer(textLexer);
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

    QsciEditVariable->setAutoCompletionSource(QsciScintilla::AcsAll);   //设置源，自动补全所有地方出现的
    QsciEditVariable->setAutoCompletionCaseSensitivity(true);   //设置自动补全大小写敏感
    QsciEditVariable->setAutoCompletionThreshold(2);    //设置每输入2个字符就会出现自动补全的提示

    QsciEditVariable->setCaretLineVisible(true);
    //设置光标所在行背景色
    QsciEditVariable->setCaretLineBackgroundColor(Qt::lightGray);

    // ui->textEdit->setCursorPosition(2,2);
    //int markerDefine(MarkerSymbol sym, int markerNumber = -1);
    QsciEditVariable->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
    //得到光标位置

    QsciEditVariable->getCursorPosition(&line,&col);

    //设置显示字体
    QsciEditVariable->setFont(QFont("Courier New"));
    //设置编码方式
    QsciEditVariable->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
*/


    QsciEdit = new QsciScintilla();
    ui->TEditLayout->addWidget(QsciEdit);
    ui->frame_Edit_Description->setLayout(ui->TEditLayout);
    //connect(QsciEdit, SIGNAL(textChanged()),this, SLOT(ModelWasModified()));
    //setCurrentFile("");
    //设置字体
    QsciEdit->setFont(font);
    QsciEdit->setMarginsFont(font);
    //设置左侧行号栏宽度等
    QsciEdit->setMarginWidth(0, fontmetrics.width("000"));
    QsciEdit->setMarginLineNumbers(0, true);
    QsciEdit->setBraceMatching(QsciScintilla::SloppyBraceMatch);
    QsciEdit->setTabWidth(4);
    //设置括号等自动补全
    QsciEdit->setAutoIndent(true);
    //初始设置c++解析器
    //textEdit->setLexer(new QsciLexerCPP(this));
    QscilexerCppAttach *textLexer2 = new QscilexerCppAttach;
    textLexer->setColor(QColor(Qt:: green),QsciLexerCPP::CommentLine);    //设置自带的注释行为绿色
    textLexer->setColor(QColor(Qt::red),QsciLexerCPP::KeywordSet2);
    QsciEdit->setLexer(textLexer2);
    //设置自动补全

    QsciAPIs *apis2 = new QsciAPIs(textLexer);
    apis2->add(QString("PORT_DEF_BEGIN"));
    apis2->add(QString("PORT_DEF_END"));
    apis2->add(QString("DEF"));
    apis2->add(QString("PORT"));
    apis2->add(QString("METER"));
    apis2->add(QString("METER_PIC"));
    apis2->add(QString("METER_MODE"));


    apis2->prepare();


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
    QsciEdit->getCursorPosition(&line,&col);

    //设置显示字体
    QsciEdit->setFont(QFont("Courier New"));
    //设置编码方式
    QsciEdit->SendScintilla(QsciScintilla::SCI_SETCODEPAGE,QsciScintilla::SC_CP_UTF8);//设置编码为UTF-8
}
void DialogUnitAttr::on_tableWidgetSpur_clicked(const QModelIndex &index)
{
    if(ui->tableWidgetSpur->currentRow()<0) return;
    if(!index.isValid()) return;
    if(!UnitTypeChanged) //未重新设定过元件型号，使用T_ProjectDatabase中的Equipment表和Symbol表
    {
        QSqlQuery QuerySymbol=QSqlQuery(T_ProjectDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+ui->tableWidgetSpur->item(index.row(),0)->data(Qt::UserRole).toString();
        qDebug()<<"SqlStr="<<SqlStr;
        QuerySymbol.exec(SqlStr);
        if(!QuerySymbol.next()) return;
        ui->LbSpurFuncName->setText(QuerySymbol.value("FunDefine").toString());
        QString Symbol=QuerySymbol.value("Symbol").toString();
        if(Symbol=="")
        {
            QPixmap p=QPixmap("");
            ui->LbSpurJpg->setPixmap(p);
        }
        if(Symbol.contains("SPS_"))  UnitSymbolsView("C:/TBD/SPS/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
        else if(Symbol.contains("ES2_")) UnitSymbolsView("C:/TBD/SYMB2LIB/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
    }
    else//重新设定过元件型号，使用T_LibDatabase中的EquipmentTemplate表和
    {
        QSqlQuery QueryEquipmentTemplate=QSqlQuery(T_LibDatabase);
        QString SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+index.data(Qt::UserRole).toString();
        QueryEquipmentTemplate.exec(SqlStr);
        if(!QueryEquipmentTemplate.next()) return;
        QString FunDefine=QueryEquipmentTemplate.value("FunDefine").toString();
        QSqlQuery QueryFunctionDefineClass=QSqlQuery(T_LibDatabase);
        SqlStr="SELECT * FROM FunctionDefineClass WHERE FunctionDefineCode = '"+FunDefine+"'";
        QueryFunctionDefineClass.exec(SqlStr);
        if(!QueryFunctionDefineClass.next()) return;
        ui->LbSpurFuncName->setText(QueryFunctionDefineClass.value("FunctionDefineName").toString());
        QString Symbol;
        if(QueryEquipmentTemplate.value("Symbol").toString()!="") Symbol=QueryEquipmentTemplate.value("Symbol").toString();
        else Symbol=QueryFunctionDefineClass.value("DefaultSymbol").toString();
        if(Symbol.contains("SPS_"))  UnitSymbolsView("C:/TBD/SPS/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
        else if(Symbol.contains("ES2_")) UnitSymbolsView("C:/TBD/SYMB2LIB/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
    }
}

void DialogUnitAttr::on_BtnOk_clicked()//dataFunc 将界面上的器件信息保存到工程库
{
    if(ui->EdUnitTag->text()=="")
    {
        QMessageBox::warning(nullptr, "提示", " 元件代号不能为空");
        return;
    }
    for(int i=0;i<ui->tableUnitDiagnosePara->rowCount();i++)
    {
        if(ui->tableUnitDiagnosePara->item(i,0)->text()=="")
        {
            QMessageBox::information(this, "提示信息","诊断参数名称不能为空!", QMessageBox::Yes);
            return;
        }
        if(ui->tableUnitDiagnosePara->item(i,2)->text()=="")
        {
            QMessageBox::information(this, "提示信息","诊断参数当前值不能为空!", QMessageBox::Yes);
            return;
        }
        if(!StrIsDouble(ui->tableUnitDiagnosePara->item(i,2)->text()))
        {
            QMessageBox::information(this, "提示信息","诊断参数当前值必须为数值!", QMessageBox::Yes);
            return;
        }
        if(ui->tableUnitDiagnosePara->item(i,3)->text()=="")
        {
            QMessageBox::information(this, "提示信息","诊断参数默认值不能为空!", QMessageBox::Yes);
            return;
        }
        if(!StrIsDouble(ui->tableUnitDiagnosePara->item(i,3)->text()))
        {
            QMessageBox::information(this, "提示信息","诊断参数默认值必须为数值!", QMessageBox::Yes);
            return;
        }
    }

    ListSymbolSpurInfo.clear();
    for(int i=0;i<ui->tableWidgetSpur->rowCount();i++)
    {
        QString SymbolSpurInfo;
        if(ui->tableWidgetSpur->item(i,2)->checkState()==Qt::Checked) SymbolSpurInfo+="Checked";
        else SymbolSpurInfo+="Unchecked";
        SymbolSpurInfo+=","+ui->tableWidgetSpur->item(i,2)->text();
        if(ui->tableWidgetSpur->item(i,3)->checkState()==Qt::Checked) SymbolSpurInfo+=",Checked";
        else SymbolSpurInfo+=",Unchecked";
        SymbolSpurInfo+=","+ui->tableWidgetSpur->item(i,4)->text();
        SymbolSpurInfo+=","+ui->tableWidgetSpur->item(i,5)->text();
        ListSymbolSpurInfo.append(SymbolSpurInfo);
    }
    qDebug()<<"ListSymbolSpurInfo="<<ListSymbolSpurInfo;

    QString GaocengStr,PosStr;
    QString TmpStr=ui->LbProTag->text();
    int indexGaoceng=TmpStr.indexOf("=");
    int indexPos=TmpStr.indexOf("+");
    int indexUnit=TmpStr.indexOf("-");
    if(indexGaoceng>=0) GaocengStr=TmpStr.mid(indexGaoceng+1,indexPos-indexGaoceng-1);
    if(indexPos>=0) PosStr=TmpStr.mid(indexPos+1,indexUnit-indexPos-1);
    NewProjectStructure_ID=InsertRecordToProjectStructure(0,GaocengStr,PosStr,"");


    if(AttrMode==1)//Mode1 新增
    {
        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM Equipment WHERE DT = '"+ui->EdUnitTag->text()+"' AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"'";
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            QMessageBox::warning(nullptr, "提示", " 该元件已存在，请修改项目代号或元件代号！");
            return;
        }
    }
    else//Mode2 修改
    {
        //如果是修改元件：如果元件标号被修改，则查看Equipment表中是否存在相同标号的元件，如果存在则合并元件
        QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM Equipment WHERE DT = '"+ui->EdUnitTag->text()+"' AND ProjectStructure_ID = '"+QString::number(NewProjectStructure_ID)+"' AND Equipment_ID <> "+CurEquipment_ID;
        qDebug()<<"SqlStr="<<SqlStr;
        QuerySearch.exec(SqlStr);
        if(QuerySearch.next())
        {
            //元件标号被修改，存在相同标号的元件,询问是否合并元件
            QMessageBox::StandardButton result=QMessageBox::warning(nullptr,QString::fromLocal8Bit("Warning"),"该元件已存在，是否合并功能子块?",
                                                                    QMessageBox::Yes|QMessageBox::No,QMessageBox::NoButton);

            if(result==QMessageBox::Yes)
            {
                //删除原Equipment表中的记录，将原元件关联的Symbol关联到新的Equipment表记录
                QString CombineEquipment_ID=QuerySearch.value("Equipment_ID").toString();

                QString StrUnitsInfo;
                QSqlQuery query=QSqlQuery(T_ProjectDatabase);
                QString temp="SELECT * FROM Equipment WHERE Equipment_ID= "+CurEquipment_ID;
                query.exec(temp);
                if(query.next())
                {
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

                SqlStr="DELETE FROM Equipment WHERE Equipment_ID = "+CurEquipment_ID;
                QuerySearch.exec(SqlStr);
                QSqlQuery QuerySymbol = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
                SqlStr="UPDATE Symbol SET Equipment_ID=:Equipment_ID WHERE Equipment_ID = '"+CurEquipment_ID+"'";
                QuerySymbol.prepare(SqlStr);
                QuerySymbol.bindValue(":Equipment_ID",CombineEquipment_ID);
                QuerySymbol.exec();
                CurEquipment_ID=CombineEquipment_ID;
                UnitTagChanged=true;
            }
            else return;
        }
    }

    Canceled=false;

    //更新器件信息,区分是新增还是修改
    //Lu ToDo
    if(AttrMode==1)//新增器件（直接添加功能子块）
    {
        //找到当前最大的Equipment_ID
        int MaxEquipment_ID=GetMaxIDOfDB(T_ProjectDatabase,"Equipment","Equipment_ID");
        //更新T_ProjectDatabase数据库的Equipment表
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString tempSQL = QString("INSERT INTO Equipment (Equipment_ID,DT,ProjectStructure_ID,Type,Eqpt_Category,Name,Desc,PartCode,SymbRemark,OrderNum,Factory,TVariable,TModel,Structure,RepairInfo,Picture,MTBF)"
                                  "VALUES (:Equipment_ID,:DT,:ProjectStructure_ID,:Type,:Eqpt_Category,:Name,:Desc,:PartCode,:SymbRemark,:OrderNum,:Factory,:TVariable,:TModel,:Structure,:RepairInfo,:Picture,:MTBF)");
        QueryVar.prepare(tempSQL);
        QueryVar.bindValue(":Equipment_ID",MaxEquipment_ID);
        QueryVar.bindValue(":DT",ui->EdUnitTag->text());
        QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
        QueryVar.bindValue(":Type",ui->LbType->text());
        QueryVar.bindValue(":Eqpt_Category","普通元件");//普通元件还是PLC元件
        QueryVar.bindValue(":Name",ui->LbName->text());
        QueryVar.bindValue(":Desc",ui->tableWidgetUnitAttr->item(0,1)->text());
        QueryVar.bindValue(":PartCode",ui->CbPartCode->currentText());
        QueryVar.bindValue(":SymbRemark",ui->tableWidgetUnitAttr->item(1,1)->text());
        QueryVar.bindValue(":OrderNum",ui->LbOrderNum->text());
        QueryVar.bindValue(":Factory",ui->LbFactory->text());
        QueryVar.bindValue(":TVariable","");//QsciEditVariable->text());
        QueryVar.bindValue(":TModel",QsciEdit->text());
        QueryVar.bindValue(":MTBF",ui->EdMTBF->text());
        QString StrPic;
        for(int i=0;i<ui->tableWidgetUnitPic->rowCount();i++)
        {
            if(i!=0) StrPic+="||";
            StrPic+=ui->tableWidgetUnitPic->item(i,0)->data(Qt::UserRole).toString();
        }
        QueryVar.bindValue(":Picture",StrPic);
        
        // 保存常量数据到Structure字段
        QString StrStructure = saveConstants();
        QueryVar.bindValue(":Structure",StrStructure);
        
        // 保存维修信息 - 使用新格式（故障模式、故障概率、解决方案、所需资源）
        QString StrRepairInfo = TModelHelper::saveRepairInfoFromTable(ui->tableRepairInfo);
        QueryVar.bindValue(":RepairInfo",StrRepairInfo);
        QueryVar.exec();

        //更新T_ProjectDatabase数据库的Symbol表和Symb2TermInfo表
        AddSymbTblAndSymb2TermInfoTbl(LibEquipment_ID,QString::number(MaxEquipment_ID),"",ListSymbolSpurInfo);
        // 复制端口配置与宏族（库 -> 工程）
        copyPortConfigAndMacrosFromLibrary(LibEquipment_ID, MaxEquipment_ID);
        SelectEquipment_ID=MaxEquipment_ID;
        SelectSymbol_ID=0;
        CurEquipment_ID=QString::number(MaxEquipment_ID);
        emit(UpdateProjectUnits());
    }
    else if(AttrMode==2)//修改器件信息
    {
        QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
        QString SqlStr="SELECT * FROM Equipment WHERE Equipment_ID = "+CurEquipment_ID;
        QueryVar.exec(SqlStr);
        if(QueryVar.next())
        {
            if(QueryVar.value("DT").toString()!=ui->EdUnitTag->text()) UnitTagChanged=true;
        }
        qDebug()<<"UnitTagChanged="<<UnitTagChanged;
        SqlStr="UPDATE Equipment SET DT=:DT,ProjectStructure_ID=:ProjectStructure_ID,Type=:Type,Eqpt_Category=:Eqpt_Category,Name=:Name,Desc=:Desc,PartCode=:PartCode,OrderNum=:OrderNum,Factory=:Factory,TVariable=:TVariable,TModel=:TModel,Structure=:Structure,RepairInfo=:RepairInfo,MTBF=:MTBF"
               " WHERE Equipment_ID = "+CurEquipment_ID;
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":DT",ui->EdUnitTag->text());
        QueryVar.bindValue(":ProjectStructure_ID",QString::number(NewProjectStructure_ID));
        QueryVar.bindValue(":Type",ui->LbType->text());
        QueryVar.bindValue(":Eqpt_Category","普通元件");//普通元件还是PLC元件
        QueryVar.bindValue(":Name",ui->LbName->text());
        QueryVar.bindValue(":Desc",ui->tableWidgetUnitAttr->item(0,1)->text());
        QueryVar.bindValue(":PartCode",ui->CbPartCode->currentText());
        QueryVar.bindValue(":SymbRemark",ui->tableWidgetUnitAttr->item(1,1)->text());
        QueryVar.bindValue(":OrderNum",ui->LbOrderNum->text());
        QueryVar.bindValue(":Factory",ui->LbFactory->text());
        QueryVar.bindValue(":TVariable","");//QsciEditVariable->text());
        QueryVar.bindValue(":TModel",QsciEdit->text());
        QueryVar.bindValue(":MTBF",ui->EdMTBF->text());
        
        // 保存常量数据到Structure字段
        QString StrStructure = saveConstants();
        QueryVar.bindValue(":Structure",StrStructure);
        
        // 保存维修信息 - 使用新格式（故障模式、故障概率、解决方案、所需资源）
        QString StrRepairInfo = TModelHelper::saveRepairInfoFromTable(ui->tableRepairInfo);
        QueryVar.bindValue(":RepairInfo",StrRepairInfo);
        QueryVar.exec();

        for(int i=0;i<ui->tableWidgetSpur->rowCount();i++)
{
            SqlStr="UPDATE Symbol SET Show_DT=:Show_DT,SourceConn=:SourceConn,ExecConn=:ExecConn,SourcePrior=:SourcePrior,InterConnect=:InterConnect, Symbol_Desc=:Symbol_Desc WHERE Symbol_ID= "+ui->tableWidgetSpur->item(i,0)->data(Qt::UserRole).toString();
            QueryVar.prepare(SqlStr);
            QueryVar.bindValue(":Show_DT",ui->tableWidgetSpur->item(i,1)->text());
            if(ui->tableWidgetSpur->item(i,2)->checkState()==Qt::Checked)
                QueryVar.bindValue(":SourceConn",true);
            else
                QueryVar.bindValue(":SourceConn",false);

            if(ui->tableWidgetSpur->item(i,3)->checkState()==Qt::Checked)
                QueryVar.bindValue(":ExecConn",true);
            else
                QueryVar.bindValue(":ExecConn",false);

            QueryVar.bindValue(":SourcePrior",ui->tableWidgetSpur->item(i,2)->text());
            qDebug()<<"ui->tableWidgetSpur->item(i,5)->text()="<<ui->tableWidgetSpur->item(i,5)->text();
            QStringList ListInterConnect=ui->tableWidgetSpur->item(i,5)->text().split(";");
            QString InterConnect;
            if(ui->tableWidgetSpur->item(i,5)->text()!="")
            {
                for(QString StrInterConnect:ListInterConnect)//(1,2);(3,4)
                {
                    StrInterConnect.remove("(").remove(")");
                    QStringList ListCoupleSpur=StrInterConnect.split(",");
                    if(InterConnect!="") InterConnect+=";";
                    InterConnect+="(";
                    for(QString StrOneSpur:ListCoupleSpur)
                    {
                        if(StrIsNumber(StrOneSpur))
                        {
                            int RowVal=StrOneSpur.toInt();
                            if(RowVal<=ui->tableWidgetSpur->rowCount())
                            {
                                if(!InterConnect.endsWith("(")) InterConnect+=",";
                                InterConnect+=ui->tableWidgetSpur->item(RowVal-1,0)->data(Qt::UserRole).toString();
                            }
                        }
                    }
                    InterConnect+=")";
                }
            }
            QueryVar.bindValue(":InterConnect",InterConnect);
            QueryVar.bindValue(":Symbol_Desc",ui->tableWidgetSpur->item(i,6)->text());
            QueryVar.exec();

            //目前单独在"端子"选项卡中进行保存
            //            QSqlQuery QuerySearch(T_ProjectDatabase);
            //            SqlStr="SELECT * FROM Symb2TermInfo WHERE Symbol_ID = '"+ui->tableWidgetSpur->item(i,0)->data(Qt::UserRole).toString()+"'";
            //            QuerySearch.exec(SqlStr);
            //            int Symb2TermIndex=0;
            //            while(QuerySearch.next())
            //            {
            //                if(Symb2TermIndex>=ui->tableWidgetSpur->item(i,4)->text().split("￤").count()) break;
            //                QSqlQuery QuerySymb2TermInfo(T_ProjectDatabase);
            //                SqlStr="UPDATE Symb2TermInfo SET TestCost=:TestCost,TermPicPath=:TermPicPath,TagType=:TagType,TagPos=:TagPos,TagEdge=:TagEdge,TagColor=:TagColor WHERE Symb2TermInfo_ID = "+QuerySearch.value("Symb2TermInfo_ID").toString();
            //                QuerySymb2TermInfo.prepare(SqlStr);
            //                QString StrTestCost=ui->tableWidgetSpur->item(i,4)->text().split("￤").at(Symb2TermIndex);
            //                QuerySymb2TermInfo.bindValue(":TestCost",StrTestCost.remove(" "));
            //                QuerySymb2TermInfo.exec();
            //                Symb2TermIndex++;
            //            }//while(QuerySearch.next())
        }
        // 如果重新设定过型号，需同步端口配置/宏族
        if(UnitTypeChanged) {
            copyPortConfigAndMacrosFromLibrary(LibEquipment_ID, CurEquipment_ID.toInt());
        }
    }

    qDebug()<<"DELETE FROM EquipmentDiagnosePara";
    m_componentContainerId = resolveContainerId(CurEquipment_ID.toInt(), true);
    // if (m_portConfigPanel) {  // 已移除独立的PortConfigPanel控件
    //     m_portConfigPanel->setContainerId(m_componentContainerId);
    //     if (!savePortConfig())
    //         return;
    // }

    QSqlQuery QueryVar = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr="DELETE FROM EquipmentDiagnosePara WHERE Equipment_ID='"+CurEquipment_ID+"'";
    QueryVar.exec(SqlStr);
    for(int i=0;i<ui->tableUnitDiagnosePara->rowCount();i++)
    {
        qDebug()<<"INSERT INTO EquipmentDiagnosePara";
        int DiagnoseParaID=GetMaxIDOfDB(T_ProjectDatabase,"EquipmentDiagnosePara","DiagnoseParaID");
        SqlStr = "INSERT INTO EquipmentDiagnosePara (DiagnoseParaID,Equipment_ID,Name,Unit,CurValue,DefaultValue,Remark)"
                 " VALUES (:DiagnoseParaID,:Equipment_ID,:Name,:Unit,:CurValue,:DefaultValue,:Remark)";
        qDebug()<<"SqlStr="<<SqlStr<<"DiagnoseParaID="<<DiagnoseParaID;
        QueryVar.prepare(SqlStr);
        QueryVar.bindValue(":DiagnoseParaID",DiagnoseParaID);
        QueryVar.bindValue(":Equipment_ID",CurEquipment_ID);
        QueryVar.bindValue(":Name",ui->tableUnitDiagnosePara->item(i,0)->text());
        QueryVar.bindValue(":Unit",ui->tableUnitDiagnosePara->item(i,1)->text());
        QueryVar.bindValue(":CurValue",ui->tableUnitDiagnosePara->item(i,2)->text());
        QueryVar.bindValue(":DefaultValue",ui->tableUnitDiagnosePara->item(i,3)->text());
        QueryVar.bindValue(":Remark",ui->tableUnitDiagnosePara->item(i,4)->text());
        QueryVar.exec();
    }

    //更新端子配置表中的子块代号
    QSqlQuery QuerySymbol= QSqlQuery(T_ProjectDatabase);
    for(int i=0;i<ui->tableTerm->rowCount();i++)
    {
        SqlStr="SELECT * FROM Symbol WHERE Symbol_ID = "+ui->tableTerm->item(i,0)->data(Qt::UserRole).toString();
        QuerySymbol.exec(SqlStr);
        if(QuerySymbol.next()) ui->tableTerm->item(i,0)->setText(QuerySymbol.value("Show_DT").toString());
    }
    close();
}

//根据数据库中记录填写tableWidgetUnitPic表格
//ui->tableWidgetUnitPic共两列：
//1）图片:显示信息[如果在磁盘中找到了图片，则显示图片的绝对路径；如果没找到图片，则显示图片名];UserRole Data：[图片的绝对路径（在磁盘中找到了对应文件）；""（在磁盘中未找到图片）]
//2）标注信息:显示信息[“是”（strTagInfo有效）；“否”（strTagInfo无效）];UserRole Data[strTagInfo]
int DialogUnitAttr::resolveContainerId(int equipmentId, bool createIfMissing)
{
    if (equipmentId <= 0)
        return 0;

    QSqlQuery ddl(T_ProjectDatabase);
    ddl.exec(QStringLiteral("CREATE TABLE IF NOT EXISTS equipment_containers (equipment_id INTEGER PRIMARY KEY, container_id INTEGER)"));
    ddl.exec(QStringLiteral("CREATE INDEX IF NOT EXISTS idx_eq_containers_container ON equipment_containers(container_id)"));

    ContainerRepository repo(T_ProjectDatabase);
    if (!repo.ensureTables())
        return 0;

    int containerId = repo.componentContainerIdForEquipment(equipmentId);
    if (containerId == 0 && createIfMissing) {
        containerId = ContainerHierarchy::ensureComponentContainer(repo, T_ProjectDatabase, equipmentId);
    }
    return containerId;
}

void DialogUnitAttr::loadPortConfig(int equipmentId)
{
    // 已移除独立的PortConfigPanel控件，端口配置通过tableTerm右键菜单编辑
    // if (!m_portConfigPanel)
    //     return;
    m_componentContainerId = resolveContainerId(equipmentId, true);
    // m_portConfigPanel->setContainerId(m_componentContainerId);
    // m_portConfigPanel->load();
}

bool DialogUnitAttr::savePortConfig()
{
    // 已移除独立的PortConfigPanel控件，端口配置通过tableTerm右键菜单保存
    // if (!m_portConfigPanel)
    //     return true;
    if (m_componentContainerId <= 0)
        return true;

    // QString error;
    // if (!m_portConfigPanel->validate(&error)) {
    //     QMessageBox::warning(this, tr("提示"), error);
    //     return false;
    // }
    // if (!m_portConfigPanel->save()) {
    //     QMessageBox::warning(this, tr("提示"), tr("端口配置保存失败"));
    //     return false;
    // }
    return true;
}

// 复制库中元件的端口配置与连接宏到工程数据库
// 触发时机：
// 1) 新增元件（AttrMode==1）并从器件库选择了型号
// 2) 修改元件（AttrMode==2 且 UnitTypeChanged==true）重新选择了型号
// 说明：库与工程的 equipment_id 不同，需重新分配 container_id，并克隆全部 port_config / port_connect_macro 条目
bool DialogUnitAttr::copyPortConfigAndMacrosFromLibrary(const QString &libEquipmentIdStr, int projectEquipmentId)
{
    int libEquipmentId = libEquipmentIdStr.toInt();
    if (libEquipmentId <= 0 || projectEquipmentId <= 0) {
        qDebug() << "[copyPortConfig] 参数非法" << libEquipmentId << projectEquipmentId;
        return false;
    }

    // 获取库侧 container_id
    {
        QSqlQuery ddl(T_LibDatabase);
        ddl.exec(QStringLiteral("CREATE TABLE IF NOT EXISTS equipment_containers (equipment_id INTEGER PRIMARY KEY, container_id INTEGER)"));
        ddl.exec(QStringLiteral("CREATE INDEX IF NOT EXISTS idx_eq_containers_container ON equipment_containers(container_id)"));
    }
    ContainerRepository repoLib(T_LibDatabase);
    if (!repoLib.ensureTables()) {
        qWarning() << "[copyPortConfig] ensureTables(lib) 失败";
        return false;
    }
    int libContainerId = repoLib.componentContainerIdForEquipment(libEquipmentId);
    if (libContainerId == 0) {
        // 若库侧尚未生成，尝试生成（理论上库中应已有）
        libContainerId = ContainerHierarchy::ensureComponentContainer(repoLib, T_LibDatabase, libEquipmentId);
    }
    if (libContainerId == 0) {
        qWarning() << "[copyPortConfig] 未获得库侧 container_id";
        return false;
    }

    // 获取工程侧 container_id
    int projectContainerId = resolveContainerId(projectEquipmentId, true);
    if (projectContainerId <= 0) {
        qWarning() << "[copyPortConfig] 未获得工程侧 container_id";
        return false;
    }

    // 确保工程侧存在 port_config / port_connect_macro 表
    {
        QSqlQuery ddlProj(T_ProjectDatabase);
        ddlProj.exec(QStringLiteral("CREATE TABLE IF NOT EXISTS port_config ("
                                    " port_config_id INTEGER PRIMARY KEY AUTOINCREMENT,"
                                    " container_id INTEGER NOT NULL,"
                                    " function_block TEXT NOT NULL,"
                                    " port_name TEXT NOT NULL,"
                                    " port_type TEXT NOT NULL,"
                                    " direction TEXT NOT NULL DEFAULT 'bidirectional',"
                                    " variable_profile TEXT NOT NULL DEFAULT 'default',"
                                    " variables_json TEXT NOT NULL,"
                                    " connect_macro TEXT,"
                                    " custom_metadata TEXT,"
                                    " updated_at TEXT DEFAULT CURRENT_TIMESTAMP)"));
        ddlProj.exec(QStringLiteral("CREATE TABLE IF NOT EXISTS port_connect_macro ("
                                    " macro_id INTEGER PRIMARY KEY AUTOINCREMENT,"
                                    " container_id INTEGER NOT NULL,"
                                    " macro_name TEXT NOT NULL,"
                                    " domain TEXT NOT NULL,"
                                    " arity INTEGER NOT NULL,"
                                    " expansion_template TEXT NOT NULL,"
                                    " description TEXT,"
                                    " metadata_json TEXT,"
                                    " updated_at TEXT DEFAULT CURRENT_TIMESTAMP)"));
        ddlProj.exec(QStringLiteral("CREATE UNIQUE INDEX IF NOT EXISTS idx_port_config_unique ON port_config(container_id, function_block, port_name)"));
        ddlProj.exec(QStringLiteral("CREATE UNIQUE INDEX IF NOT EXISTS idx_connect_macro_unique ON port_connect_macro(container_id, macro_name)"));
    }

    QSqlQuery selLibCfg(T_LibDatabase);
    selLibCfg.prepare(QStringLiteral("SELECT function_block, port_name, port_type, direction, variable_profile, variables_json, connect_macro, custom_metadata "
                                     "FROM port_config WHERE container_id = ?"));
    selLibCfg.addBindValue(libContainerId);
    if (!selLibCfg.exec()) {
        qWarning() << "[copyPortConfig] 读取库侧 port_config 失败:" << selLibCfg.lastError();
        return false;
    }

    // 清理工程侧旧配置（若重新选择型号）
    QSqlQuery delProj(T_ProjectDatabase);
    delProj.prepare(QStringLiteral("DELETE FROM port_config WHERE container_id = ?"));
    delProj.addBindValue(projectContainerId);
    if (!delProj.exec()) {
        qWarning() << "[copyPortConfig] 删除旧工程 port_config 失败:" << delProj.lastError();
        return false;
    }

    QSqlQuery insProjCfg(T_ProjectDatabase);
    insProjCfg.prepare(QStringLiteral("INSERT INTO port_config(container_id,function_block,port_name,port_type,direction,variable_profile,variables_json,connect_macro,custom_metadata)"
                                      " VALUES(?,?,?,?,?,?,?,?,?)"));
    int copiedPorts = 0;
    while (selLibCfg.next()) {
        insProjCfg.addBindValue(projectContainerId);
        insProjCfg.addBindValue(selLibCfg.value(0));
        insProjCfg.addBindValue(selLibCfg.value(1));
        insProjCfg.addBindValue(selLibCfg.value(2));
        insProjCfg.addBindValue(selLibCfg.value(3));
        insProjCfg.addBindValue(selLibCfg.value(4));
        insProjCfg.addBindValue(selLibCfg.value(5));
        insProjCfg.addBindValue(selLibCfg.value(6));
        insProjCfg.addBindValue(selLibCfg.value(7));
        if (!insProjCfg.exec()) {
            qWarning() << "[copyPortConfig] 插入工程 port_config 失败:" << insProjCfg.lastError();
        } else {
            ++copiedPorts;
        }
    }

    // 拷贝连接宏（包含自定义与内置映射；内置宏族若后续改为全局，可在此处过滤）
    QSqlQuery selLibMacro(T_LibDatabase);
    selLibMacro.prepare(QStringLiteral("SELECT macro_name, domain, arity, expansion_template, description, metadata_json FROM port_connect_macro WHERE container_id = ?"));
    selLibMacro.addBindValue(libContainerId);
    if (!selLibMacro.exec()) {
        qWarning() << "[copyPortConfig] 读取库侧 port_connect_macro 失败:" << selLibMacro.lastError();
    } else {
        // 删除工程侧旧宏
        QSqlQuery delMacro(T_ProjectDatabase);
        delMacro.prepare(QStringLiteral("DELETE FROM port_connect_macro WHERE container_id = ?"));
        delMacro.addBindValue(projectContainerId);
        delMacro.exec();

        QSqlQuery insProjMacro(T_ProjectDatabase);
        insProjMacro.prepare(QStringLiteral("INSERT INTO port_connect_macro(container_id,macro_name,domain,arity,expansion_template,description,metadata_json) VALUES(?,?,?,?,?,?,?)"));
        int copiedMacros = 0;
        while (selLibMacro.next()) {
            insProjMacro.addBindValue(projectContainerId);
            insProjMacro.addBindValue(selLibMacro.value(0));
            insProjMacro.addBindValue(selLibMacro.value(1));
            insProjMacro.addBindValue(selLibMacro.value(2));
            insProjMacro.addBindValue(selLibMacro.value(3));
            insProjMacro.addBindValue(selLibMacro.value(4));
            insProjMacro.addBindValue(selLibMacro.value(5));
            if (!insProjMacro.exec()) {
                qWarning() << "[copyPortConfig] 插入工程 port_connect_macro 失败:" << insProjMacro.lastError();
            } else {
                ++copiedMacros;
            }
        }
        qDebug() << "[copyPortConfig] 已复制端口" << copiedPorts << "条, 宏" << copiedMacros << "条";
    }
    return true;
}

void DialogUnitAttr::fillUnitPicTable(const QString &picture, const QString &supplier) {
    ui->tableWidgetUnitPic->setRowCount(0);
    if(picture.isEmpty())return;
    QMap<QString, QString> imagePaths; // 文件名与路径的映射
    QMap<QString, QString> tagInfos;   // 文件名与标注信息的映射

    // 定义要搜索的目录
    QStringList searchDirs = {
        CurProjectPath + QString(PROJECT_PIC_PATH),
        QString(PIC_BASE_PATH) + "/" + supplier,
        QString(PIC_BASE_PATH)
    };

    processPictureInfo(picture, supplier, searchDirs,
                       imagePaths, tagInfos);

    // 填充表格
    for (const QString &fileName : imagePaths.keys()) {
        QString absoluteImagePath = imagePaths[fileName];
        QString strTagInfo = tagInfos[fileName];

        int currentRow = ui->tableWidgetUnitPic->rowCount();
        ui->tableWidgetUnitPic->insertRow(currentRow);

        // 设置图片路径或文件名
        QTableWidgetItem *itemPic = new QTableWidgetItem(absoluteImagePath.isEmpty() ? fileName : absoluteImagePath);
        itemPic->setData(Qt::UserRole, absoluteImagePath);
        ui->tableWidgetUnitPic->setItem(currentRow, 0, itemPic);

        // 设置是否已标注
        QString annotated = isTagInfoValid(strTagInfo) ? "是" : "否";

        QTableWidgetItem *itemAnnotated = new QTableWidgetItem(annotated);
        itemAnnotated->setData(Qt::UserRole, strTagInfo);
        ui->tableWidgetUnitPic->setItem(currentRow, 1, itemAnnotated);
    }

    // 默认显示第一条
    if (ui->tableWidgetUnitPic->rowCount() > 0) {
        ui->tableWidgetUnitPic->setCurrentIndex(ui->tableWidgetUnitPic->model()->index(0, 0));
        on_tableWidgetUnitPic_clicked(ui->tableWidgetUnitPic->currentIndex());
    } else {
        m_scene.clear();
    }
}

void DialogUnitAttr::on_BtnUnitChoose_clicked() //dataFunc 从器件库中载入器件信息到界面
{
    //DialogUnitManage *dlg=new DialogUnitManage(this);
    dlgUnitManage->setModal(true);
    dlgUnitManage->SetStackWidget(0);
    dlgUnitManage->show();
    dlgUnitManage->exec();
    if(dlgUnitManage->Canceled) return;
    LibEquipment_ID=dlgUnitManage->CurEquipment_ID;//在弹出对话框的器件库中选择器件，返回器件的Equipment_ID

    //=====根据选择的器件的Equipment_ID，在器件库数据库中查询相关信息，并加载到界面中来=====
    QSqlQuery QueryEquipment= QSqlQuery(T_LibDatabase);
    QString SqlStr=QString("SELECT * FROM Equipment WHERE Equipment_ID='"+LibEquipment_ID+"'");
    QueryEquipment.exec(SqlStr);
    if(!QueryEquipment.next()) return;
    if(QueryEquipment.value("PartCode").toString()==ui->CbPartCode->currentText()) return;
    UnitTypeChanged=true;
    ui->CbPartCode->setCurrentText(QueryEquipment.value("PartCode").toString());
    ui->LbType->setText(QueryEquipment.value("Type").toString());
    ui->LbName->setText(QueryEquipment.value("Name").toString());
    ui->LbFactory->setText(QueryEquipment.value("Supplier").toString());
    ui->LbOrderNum->setText(QueryEquipment.value("OrderNum").toString());
    ui->tableWidgetUnitAttr->item(0,1)->setText(QueryEquipment.value("Desc").toString());
    ui->EdMTBF->setText(QueryEquipment.value("MTBF").toString());
    QsciEdit->setText(QueryEquipment.value("TModel").toString());
    on_BtnCompile_clicked();
    QStringList ListStructure=QueryEquipment.value("Structure").toString().split(";");
    if(ListStructure.count()==ui->tableWidgetStructure->rowCount())
    {
        for(int i=0;i<ListStructure.count();i++)
        {
            if(ui->tableWidgetStructure->item(i,0)->text()!=ListStructure.at(i).split(",").at(0)) continue;
            ((QComboBox *)ui->tableWidgetStructure->cellWidget(i,2))->setCurrentText(ListStructure.at(i).split(",").at(1));
            ((QComboBox *)ui->tableWidgetStructure->cellWidget(i,3))->setCurrentText(ListStructure.at(i).split(",").at(2));
        }
    }

    //Lu ToDo 照片及标注信息加载
    //ui->tableWidgetUnitPic有两列：图片;已标注
    //其中第1列显示图片路径（如果找到了图片则显示绝对路径，没找到则显示图片文件名）；第1列的Qt::UserRole的Data存储图片绝对路径（没找到图片则为空）
    //第2列显示“是”或“否”表示是否已标注，第2列的Qt::UserRole的Data存储StrTagInfo
    //图片先在QDir projectPicDir(CurProjectPath + PROJECT_PIC_PATH)目录下查找，剩下没找到的在QDir BasePicDir(QString(PIC_BASE_PATH) + "/" + supplier)下查找，剩下没找到的在QDir BasePicDir(QString(PIC_BASE_PATH))下查找,还没找到的，则在第1列只显示图片文件名，也不显示图片。
    fillUnitPicTable(QueryEquipment.value("Picture").toString(),QueryEquipment.value("Supplier").toString());

    //维修信息
    ui->tableRepairInfo->setRowCount(0);
    for(int i=0;i<ui->tableWidgetStructure->rowCount();i++)
    {
        if(ui->tableWidgetStructure->item(i,1)->text()=="ModeType")
        {
            QComboBox *CbModeTypeBox= ((QComboBox *)ui->tableWidgetStructure->cellWidget(i,2));
            for(int j=0;j<CbModeTypeBox->count();j++)
            {
                if((CbModeTypeBox->itemText(j)=="nominal")||(CbModeTypeBox->itemText(j)=="undefined")||(CbModeTypeBox->itemText(j)=="default")) continue;
                if((CbModeTypeBox->itemText(j)=="on")||(CbModeTypeBox->itemText(j)=="off")||(CbModeTypeBox->itemText(j)=="open")||(CbModeTypeBox->itemText(j)=="close")) continue;
                ui->tableRepairInfo->setRowCount(ui->tableRepairInfo->rowCount()+1);
                ui->tableRepairInfo->setItem(ui->tableRepairInfo->rowCount()-1,0,new QTableWidgetItem(ui->tableWidgetStructure->item(i,0)->text()));
                ui->tableRepairInfo->setItem(ui->tableRepairInfo->rowCount()-1,1,new QTableWidgetItem(CbModeTypeBox->itemText(j)));
                ui->tableRepairInfo->setItem(ui->tableRepairInfo->rowCount()-1,2,new QTableWidgetItem(""));
                ui->tableRepairInfo->setItem(ui->tableRepairInfo->rowCount()-1,3,new QTableWidgetItem(""));
            }
        }
    }
    QStringList ListRepairInfo=QueryEquipment.value("RepairInfo").toString().split("￤￤");
    if(ListRepairInfo.count()==ui->tableRepairInfo->rowCount())
    {
        for(int i=0;i<ListRepairInfo.count();i++)
        {
            if(ListRepairInfo.at(i).split("￤").count()==4)
            {
                if(ui->tableRepairInfo->item(i,0)->text()!=ListRepairInfo.at(i).split("￤").at(0)) continue;
                if(ui->tableRepairInfo->item(i,1)->text()!=ListRepairInfo.at(i).split("￤").at(1)) continue;
                ui->tableRepairInfo->item(i,2)->setText(ListRepairInfo.at(i).split("￤").at(2));
                ui->tableRepairInfo->item(i,3)->setText(ListRepairInfo.at(i).split("￤").at(3));
            }
        }
    }
    //维修信息=====结束

    //器件实例化参数加载
    ui->tableUnitDiagnosePara->setRowCount(0);
    QSqlQuery QueryEquipmentDiagnosePara= QSqlQuery(T_LibDatabase);
    SqlStr="SELECT * FROM EquipmentDiagnosePara WHERE Equipment_ID= '"+LibEquipment_ID+"'";
    QueryEquipmentDiagnosePara.exec(SqlStr);
    while(QueryEquipmentDiagnosePara.next())
    {
        ui->tableUnitDiagnosePara->setRowCount(ui->tableUnitDiagnosePara->rowCount()+1);
        ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,0,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("Name").toString()));//名称
        ui->tableUnitDiagnosePara->item(ui->tableUnitDiagnosePara->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipmentDiagnosePara.value("DiagnoseParaID").toString());
        ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,1,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("Unit").toString()));//单位
        ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,2,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("DefaultValue").toString()));//当前值
        ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,3,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("DefaultValue").toString()));//默认值
        ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,4,new QTableWidgetItem(QueryEquipmentDiagnosePara.value("Remark").toString()));//备注
    }
    //器件实例化参数加载=====结束

    QSqlQuery QueryEquipmentTemplate= QSqlQuery(T_LibDatabase);
    SqlStr=QString("SELECT * FROM EquipmentTemplate WHERE Equipment_ID = '"+LibEquipment_ID+"'");
    QueryEquipmentTemplate.exec(SqlStr);
    ui->tableWidgetSpur->setRowCount(0);
    ui->tableTerm->setRowCount(0);
    QString VariableText="";
    QStringList ListInterConnectInfo;
    while(QueryEquipmentTemplate.next())
    {
        if((QueryEquipmentTemplate.value("FuncType").toString()=="虚拟端口-观测布尔量")||(QueryEquipmentTemplate.value("FuncType").toString()=="虚拟端口-观测实数量"))
        {
            if(VariableText!="") VariableText+="\n";
            QString UnitText="";
            if(QueryEquipmentTemplate.value("FuncType").toString()=="虚拟端口-观测布尔量") UnitText="Bool";
            else if(QueryEquipmentTemplate.value("FuncType").toString()=="虚拟端口-观测实数量") UnitText="Real";
            VariableText+="(declare-fun %"+ui->EdUnitTag->text()+"%."+QueryEquipmentTemplate.value("FunDefine").toString()+" () "+UnitText+")";
        }
        ui->tableWidgetSpur->setRowCount(ui->tableWidgetSpur->rowCount()+1);
        QString UnitSpurStr,SpurDescStr;
        UnitSpurStr=QueryEquipmentTemplate.value("ConnNum").toString();
        SpurDescStr=QueryEquipmentTemplate.value("SpurDT").toString();
        //￤分割
        if((QueryEquipmentTemplate.value("FuncType").toString()=="接线端口")||(QueryEquipmentTemplate.value("FuncType").toString()==""))
        {
            if(UnitSpurStr!="")
            {
                QStringList ListTermConn=UnitSpurStr.split("￤");
                for(QString TermConn:ListTermConn)
                {
                    if(VariableText!="") VariableText+="\n";
                    VariableText+="(declare-fun %"+ui->EdUnitTag->text()+"%."+TermConn+".i () Real)\n";
                    VariableText+="(declare-fun %"+ui->EdUnitTag->text()+"%."+TermConn+".u () Real)";
                }
            }

        }
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,0,new QTableWidgetItem(UnitSpurStr));
        ui->tableWidgetSpur->item(ui->tableWidgetSpur->rowCount()-1,0)->setData(Qt::UserRole,QVariant(QueryEquipmentTemplate.value("EquipmentTemplate_ID").toString()));
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,1,new QTableWidgetItem(SpurDescStr));
        QTableWidgetItem *ItemSourceConn=new QTableWidgetItem(QueryEquipmentTemplate.value("SourcePrior").toString());//优先级
        if(QueryEquipmentTemplate.value("SourceConn").toBool()) ItemSourceConn->setCheckState(Qt::Checked);
        else
        {
            if((QueryEquipmentTemplate.value("FuncType").toString()=="")||(QueryEquipmentTemplate.value("FuncType").toString()=="接线端口"))
                ItemSourceConn->setCheckState(Qt::Unchecked);
        }
        //ItemSourceConn->setFlags(ItemSourceConn->flags()&(~Qt::ItemIsEditable));

        QTableWidgetItem *ItemExecConn=new QTableWidgetItem("");
        if(QueryEquipmentTemplate.value("ExecConn").toBool()) ItemExecConn->setCheckState(Qt::Checked);
        else
        {
            if((QueryEquipmentTemplate.value("FuncType").toString()=="")||(QueryEquipmentTemplate.value("FuncType").toString()=="接线端口"))
                ItemExecConn->setCheckState(Qt::Unchecked);
        }
        ItemExecConn->setFlags(ItemExecConn->flags()&(~Qt::ItemIsEditable));
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,2,ItemSourceConn);//源端口
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,3,ItemExecConn);//终端端口
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,4,new QTableWidgetItem(QueryEquipmentTemplate.value("TestCost").toString()));
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,5,new QTableWidgetItem(""));//受控
        ui->tableWidgetSpur->setItem(ui->tableWidgetSpur->rowCount()-1,5,new QTableWidgetItem(QueryEquipmentTemplate.value("ConnDesc").toString()));//描述

        if(QueryEquipmentTemplate.value("InterConnect").toString()!="")
        {
            ListInterConnectInfo.append(QString::number(ui->tableWidgetSpur->rowCount()-1)+":"+QueryEquipmentTemplate.value("InterConnect").toString());
        }
        qDebug()<<"跳过端子配置";
        //更新端子配置
//        QSqlQuery QueryTermInfo= QSqlQuery(T_LibDatabase);
//        SqlStr=QString("SELECT * FROM TermInfo WHERE EquipmentTemplate_ID = '"+QueryEquipmentTemplate.value("EquipmentTemplate_ID").toString()+"'");
//        QueryTermInfo.exec(SqlStr);
//        while(QueryTermInfo.next())
//        {
//            ui->tableTerm->setRowCount(ui->tableTerm->rowCount()+1);
//            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,0,new QTableWidgetItem(QueryEquipmentTemplate.value("SpurDT").toString()));
//            ui->tableTerm->item(ui->tableTerm->rowCount()-1,0)->setData(Qt::UserRole,QueryEquipmentTemplate.value("EquipmentTemplate_ID").toString());
//            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,1,new QTableWidgetItem(QueryTermInfo.value("TermNum").toString()));
//            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,2,new QTableWidgetItem(QueryTermInfo.value("TestCost").toString()));
//            ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,3,new QTableWidgetItem(QueryTermInfo.value("TermPicPath").toString()));
//            if(QueryTermInfo.value("TagType").toString()!="")
//            {
//                ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,4,new QTableWidgetItem("是"));
//                ui->tableTerm->item(ui->tableTerm->rowCount()-1,4)->setData(Qt::UserRole,QueryTermInfo.value("TagType").toString()+"|"+QueryTermInfo.value("TagColor").toString()+"|"+QueryTermInfo.value("TagPos").toString()+"|"+QueryTermInfo.value("TagEdge").toString());
//            }
//            else
//                ui->tableTerm->setItem(ui->tableTerm->rowCount()-1,4,new QTableWidgetItem("否"));
//        }
    }
    qDebug()<<"ListInterConnectInfo="<<ListInterConnectInfo;
    for(int i=0;i<ListInterConnectInfo.count();i++)
    {
        QString StrInterConnectInfo=ListInterConnectInfo.at(i).split(":").at(1);
        for(int j=0;j<ui->tableWidgetSpur->rowCount();j++)
        {
            if(StrInterConnectInfo.split(",").contains(ui->tableWidgetSpur->item(j,0)->data(Qt::UserRole).toString()))
            {
                if(ui->tableWidgetSpur->item(ListInterConnectInfo.at(i).split(":").at(0).toInt(),5)->text()!="")
                    ui->tableWidgetSpur->item(ListInterConnectInfo.at(i).split(":").at(0).toInt(),5)->setText(ui->tableWidgetSpur->item(ListInterConnectInfo.at(i).split(":").at(0).toInt(),5)->text()+",");
                ui->tableWidgetSpur->item(ListInterConnectInfo.at(i).split(":").at(0).toInt(),5)->setText(ui->tableWidgetSpur->item(ListInterConnectInfo.at(i).split(":").at(0).toInt(),5)->text()+QString::number(j+1));
            }
        }
    }

    //QsciEditVariable->setText(VariableText);
    if(ui->tableWidgetSpur->rowCount()>0)
    {
        QueryEquipmentTemplate.first();
        ui->tableWidgetSpur->setCurrentItem(ui->tableWidgetSpur->item(0,0));
        QString FunDefine=QueryEquipmentTemplate.value("FunDefine").toString();
        QSqlQuery QueryFunctionDefineClass= QSqlQuery(T_LibDatabase);
        SqlStr=QString("SELECT * FROM FunctionDefineClass WHERE FunctionDefineCode = '"+FunDefine+"'");
        QueryFunctionDefineClass.exec(SqlStr);
        if(QueryFunctionDefineClass.next())
        {
            ui->LbSpurFuncName->setText(QueryFunctionDefineClass.value("FunctionDefineName").toString());
            QString Symbol=QueryFunctionDefineClass.value("DefaultSymbol").toString();
            if(Symbol.contains("SPS_"))  UnitSymbolsView("C:/TBD/SPS/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
            else if(Symbol.contains("ES2_")) UnitSymbolsView("C:/TBD/SYMB2LIB/"+Symbol+".dwg","C:/TBD/data/TempImage/"+Symbol+".jpg",ui->LbSpurJpg,true);
        }
    }
}

void DialogUnitAttr::on_EdUnitTag_textChanged(const QString &arg1)
{
    if(ui->EdUnitTag->text()!="") ui->LbProTag->setText(StrProTag+"-"+ui->EdUnitTag->text());
    //查找数据库中是否有相同的代号
    QSqlQuery QuerySearch = QSqlQuery(T_ProjectDatabase);//设置数据库选择模型
    QString SqlStr="SELECT * FROM Equipment WHERE DT = '"+ui->EdUnitTag->text()+"'";
    QuerySearch.exec(SqlStr);
    if(QuerySearch.next())
    {
        UpdateUIInfo(QuerySearch);
    }
}

void DialogUnitAttr::on_BtnCancel_clicked()
{
    Canceled=true;
    close();
}

void DialogUnitAttr::on_BtnAddPara_clicked()
{
    ui->tableUnitDiagnosePara->setRowCount(ui->tableUnitDiagnosePara->rowCount()+1);
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,0,new QTableWidgetItem(""));//名称
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,1,new QTableWidgetItem(""));//单位
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,2,new QTableWidgetItem("0"));//当前值
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,3,new QTableWidgetItem("0"));//默认值
    ui->tableUnitDiagnosePara->setItem(ui->tableUnitDiagnosePara->rowCount()-1,4,new QTableWidgetItem(""));//备注
}

void DialogUnitAttr::on_BtnDeletePara_clicked()
{
    if(ui->tableUnitDiagnosePara->currentRow()<0) return;
    ui->tableUnitDiagnosePara->removeRow(ui->tableUnitDiagnosePara->currentRow());
}

void DialogUnitAttr::on_BtnCompile_clicked()
{
    // 解析T语言模型
    TModelParser parser;
    QString tmodelText = QsciEdit->text();
    
    if (!parser.parse(tmodelText)) {
        QMessageBox::warning(this, "解析失败", "T语言模型解析失败");
        return;
    }
    
    // 收集常量映射
    QMap<QString, QString> constants;
    for (int i = 0; i < ui->tableWidgetStructure->rowCount(); i++) {
        QString name = ui->tableWidgetStructure->item(i, 0) ? ui->tableWidgetStructure->item(i, 0)->text().trimmed() : "";
        QString value = ui->tableWidgetStructure->item(i, 1) ? ui->tableWidgetStructure->item(i, 1)->text().trimmed() : "";
        
        if (!name.isEmpty()) {
            constants[name] = value;
        }
    }
    
    // 获取器件名称（用于替换%Name%）
    QString componentName = ui->EdUnitTag->text().trimmed();
    if (componentName.isEmpty()) {
        componentName = "COMPONENT";  // 默认名称
    }
    
    // 编译
    QString portVars, internalVars, normalMode;
    QList<TModelParser::FailureMode> failureModes;
    
    if (!parser.compile(componentName, constants, portVars, internalVars, normalMode, failureModes)) {
        QMessageBox::warning(this, "编译失败", "T语言模型编译失败");
        return;
    }
    
    // 显示编译结果
    TModelCompileDisplayDialog *displayDialog = new TModelCompileDisplayDialog(this);
    displayDialog->setCompileResult(portVars, internalVars, normalMode, failureModes);
    displayDialog->exec();
    delete displayDialog;
    
    // 自动从T语言模型中获取故障模式
    int addedCount = TModelHelper::autoFillFaultModesFromTModel(ui->tableRepairInfo, tmodelText);
    if (addedCount > 0) {
        qDebug() << "自动添加了" << addedCount << "个故障模式";
    }
}

void DialogUnitAttr::on_BtnValidateTModel_clicked()
{
    const QString rawModelText = QsciEdit->text();
    QString componentName = ui->EdUnitTag->text().trimmed();
    if (componentName.isEmpty()) {
        componentName = QStringLiteral("COMPONENT");
    }

    // 准备校验上下文
    TModelValidationContext context;
    context.componentName = componentName;

    QMap<QString, QString> placeholderValues;
    auto addPlaceholderValue = [&](const QString &name, const QString &value) {
        const QString trimmedName = name.trimmed();
        const QString trimmedValue = value.trimmed();
        if (trimmedName.isEmpty() || trimmedValue.isEmpty())
            return;
        placeholderValues.insert(trimmedName, trimmedValue);
    };

    // 收集常量表格中的常量定义
    for (int row = 0; row < ui->tableWidgetStructure->rowCount(); ++row) {
        QTableWidgetItem *nameItem = ui->tableWidgetStructure->item(row, 0);
        QTableWidgetItem *valueItem = ui->tableWidgetStructure->item(row, 1);
        if (!nameItem)
            continue;
        QString name = nameItem->text().trimmed();
        QString value = valueItem ? valueItem->text().trimmed() : QString();
        if (!name.isEmpty()) {
            context.constants[name] = value;
        }
        addPlaceholderValue(nameItem->text(), valueItem ? valueItem->text() : QString());
    }

    for (int row = 0; row < ui->tableUnitDiagnosePara->rowCount(); ++row) {
        QTableWidgetItem *nameItem = ui->tableUnitDiagnosePara->item(row, 0);
        if (!nameItem)
            continue;
        const QString currentValue = ui->tableUnitDiagnosePara->item(row, 2)
                ? ui->tableUnitDiagnosePara->item(row, 2)->text()
                : QString();
        QString value = currentValue.trimmed();
        if (value.isEmpty()) {
            const QString defaultValue = ui->tableUnitDiagnosePara->item(row, 3)
                    ? ui->tableUnitDiagnosePara->item(row, 3)->text()
                    : QString();
            value = defaultValue.trimmed();
        }
        addPlaceholderValue(nameItem->text(), value);
    }
    
    // 收集维修信息表格中的故障模式概率
    for (int row = 0; row < ui->tableRepairInfo->rowCount(); ++row) {
        QString faultMode = ui->tableRepairInfo->item(row, 0) ? 
            ui->tableRepairInfo->item(row, 0)->text().trimmed() : "";
        QString probability = ui->tableRepairInfo->item(row, 1) ? 
            ui->tableRepairInfo->item(row, 1)->text().trimmed() : "";
        
        if (!faultMode.isEmpty() && !probability.isEmpty()) {
            context.faultModeProbabilities[faultMode] = probability;
        }
    }

    QString preparedModel = TModelParser::replacePlaceholders(rawModelText, componentName, placeholderValues);

    QRegularExpression placeholderPattern(QStringLiteral("%([^%\\s]+)%"));
    QRegularExpressionMatchIterator placeholderIter = placeholderPattern.globalMatch(preparedModel);
    QStringList unresolvedPlaceholders;
    while (placeholderIter.hasNext()) {
        const QRegularExpressionMatch match = placeholderIter.next();
        const QString name = match.captured(1).trimmed();
        if (!name.isEmpty())
            unresolvedPlaceholders.append(name);
    }
    unresolvedPlaceholders.removeDuplicates();

    int syntheticIndex = 0;
    const QRegularExpression invalidPlaceholderChars(QStringLiteral("[^A-Za-z0-9_]+"));
    const QRegularExpression leadingUnderscores(QStringLiteral("^_+"));
    const QRegularExpression trailingUnderscores(QStringLiteral("_+$"));
    for (const QString &name : unresolvedPlaceholders) {
        QString sanitized = name;
        sanitized.replace(invalidPlaceholderChars, QStringLiteral("_"));
        sanitized.remove(leadingUnderscores);
        sanitized.remove(trailingUnderscores);
        if (sanitized.isEmpty())
            sanitized = QStringLiteral("placeholder");
        const QString replacement = QStringLiteral("__placeholder_%1_%2__").arg(sanitized).arg(syntheticIndex++);
        preparedModel.replace(QStringLiteral("%") + name + QStringLiteral("%"), replacement);
    }

    auto makePortKey = [](const QString &functionBlock, const QString &portName) -> QString {
        const QString block = functionBlock.trimmed();
        const QString port = portName.trimmed();
        if (port.isEmpty())
            return QString();
        if (block.isEmpty())
            return port;
        return QString("%1.%2").arg(block, port);
    };

    QMap<QString, QString> portTypeMap;
    QMap<QString, QStringList> portVariablesMap;
    if (m_componentContainerId > 0 && T_ProjectDatabase.isValid()) {
        QSqlQuery configQuery(T_ProjectDatabase);
        configQuery.prepare(QStringLiteral("SELECT function_block, port_name, port_type, variables_json "
                                           "FROM port_config WHERE container_id = ?"));
        configQuery.addBindValue(m_componentContainerId);
        if (configQuery.exec()) {
            while (configQuery.next()) {
                const QString functionBlock = configQuery.value(0).toString();
                const QString portName = configQuery.value(1).toString();
                const QString key = makePortKey(functionBlock, portName);
                if (key.isEmpty())
                    continue;

                QString portType = configQuery.value(2).toString().trimmed().toLower();
                if (!portType.isEmpty())
                    portTypeMap.insert(key, portType);

                QStringList variables;
                const QString json = configQuery.value(3).toString();
                if (!json.isEmpty()) {
                    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8());
                    if (doc.isArray()) {
                        const QJsonArray array = doc.array();
                        for (const QJsonValue &val : array) {
                            if (val.isObject()) {
                                const QString name = val.toObject().value(QStringLiteral("name")).toString().trimmed();
                                if (!name.isEmpty())
                                    variables.append(name);
                            } else if (val.isString()) {
                                const QString name = val.toString().trimmed();
                                if (!name.isEmpty())
                                    variables.append(name);
                            }
                        }
                    }
                }
                if (!variables.isEmpty())
                    portVariablesMap.insert(key, variables);
            }
        }
    }

    QList<PortInfo> ports;
    for (int row = 0; row < ui->tableTerm->rowCount(); ++row) {
        QTableWidgetItem *symbolItem = ui->tableTerm->item(row, 0);
        QTableWidgetItem *connItem = ui->tableTerm->item(row, 1);
        if (!connItem)
            continue;

        PortInfo info;
        info.connNum = connItem->text().trimmed();
        info.functionBlock = symbolItem ? symbolItem->text().trimmed() : QString();
        if (symbolItem) {
            info.symbolId = symbolItem->data(Qt::UserRole).toString();
            info.description = symbolItem->text();
        }
        info.symb2TermInfoId = connItem->data(Qt::UserRole).toString();

        const QString portKeyCombined = makePortKey(info.functionBlock, info.connNum);
        QString configuredType = portTypeMap.value(portKeyCombined).trimmed();
        if (configuredType.isEmpty())
            configuredType = QStringLiteral("electric");
        info.portType = configuredType.toLower();
        info.variableNames = portVariablesMap.value(portKeyCombined);

        if (!info.connNum.isEmpty())
            ports.append(info);
    }

    // 执行校验，传递上下文和原始模型文本（不是替换后的）
    TModelCheckService::run(this, rawModelText, ports, context);
}

void DialogUnitAttr::on_tableRepairInfo_clicked(const QModelIndex &index)
{
    if(!index.isValid()) return;
    ui->TextEdRepairPlan->setText(ui->tableRepairInfo->item(index.row(),2)->text());
    ui->TextEdRepairResource->setText(ui->tableRepairInfo->item(index.row(),3)->text());
}

void DialogUnitAttr::on_TextEdRepairPlan_textChanged()
{
    if(ui->tableRepairInfo->currentRow()<0) return;
    ui->tableRepairInfo->item(ui->tableRepairInfo->currentRow(),2)->setText(ui->TextEdRepairPlan->toPlainText());
}

void DialogUnitAttr::on_TextEdRepairResource_textChanged()
{
    if(ui->tableRepairInfo->currentRow()<0) return;
    ui->tableRepairInfo->item(ui->tableRepairInfo->currentRow(),3)->setText(ui->TextEdRepairResource->toPlainText());
}

void DialogUnitAttr::on_BtnAddUnitPic_clicked() {
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("选择文件"));
    fileDialog.setDirectory(QString(CurProjectPath + PROJECT_PIC_PATH));
    fileDialog.setNameFilter(tr("Images (*.png *.xpm *.jpg *.jpeg *.gif *.webp)"));
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;

    QStringList fileNames = fileDialog.selectedFiles();
    if(fileNames.count() != 1) {
        QMessageBox::warning(nullptr, "提示", "请选择一张图片！");
        return;
    }

    QFileInfo selectedFilePath(fileNames.at(0));
    int newRow = ui->tableWidgetUnitPic->rowCount();
    ui->tableWidgetUnitPic->insertRow(newRow);

    // 设置第一列：图片路径或文件名
    QTableWidgetItem *itemPic = new QTableWidgetItem(fileNames.at(0));
    itemPic->setData(Qt::UserRole, fileNames.at(0)); // 存储图片的绝对路径
    ui->tableWidgetUnitPic->setItem(newRow, 0, itemPic);

    // 设置第二列：标注信息为“否”
    QTableWidgetItem *itemAnnotated = new QTableWidgetItem("否");
    itemAnnotated->setData(Qt::UserRole, ""); // 标注信息为空字符串
    ui->tableWidgetUnitPic->setItem(newRow, 1, itemAnnotated);

    // 选择新添加的行
    ui->tableWidgetUnitPic->setCurrentCell(newRow, 0);

    // 触发点击事件，以显示新添加的图片（如果需要）
    on_tableWidgetUnitPic_clicked(ui->tableWidgetUnitPic->currentIndex());
}

void DialogUnitAttr::on_BtnReplaceUnitPic_clicked() {
    if(ui->tableWidgetUnitPic->currentRow() < 0) {
        QMessageBox::warning(nullptr, "提示", "请选择一条图片记录！");
        return;
    }

    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("选择文件"));
    fileDialog.setDirectory(QString(CurProjectPath + PROJECT_PIC_PATH));
    fileDialog.setNameFilter(tr("Images (*.png *.xpm *.jpg *.jpeg *.gif *.webp)"));
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;

    QStringList fileNames = fileDialog.selectedFiles();
    if(fileNames.count() != 1) {
        QMessageBox::warning(nullptr, "提示", "请选择一张图片！");
        return;
    }

    QFileInfo selectedFilePath(fileNames.at(0));
    int currentRow = ui->tableWidgetUnitPic->currentRow();

    // 更新第一列：图片路径或文件名
    QTableWidgetItem *itemPic = new QTableWidgetItem(fileNames.at(0));
    itemPic->setData(Qt::UserRole, fileNames.at(0)); // 存储新图片的绝对路径
    ui->tableWidgetUnitPic->setItem(currentRow, 0, itemPic);

    // 更新第二列：标注信息为“否”
    QTableWidgetItem *itemAnnotated = new QTableWidgetItem("否");
    itemAnnotated->setData(Qt::UserRole, ""); // 清空标注信息
    ui->tableWidgetUnitPic->setItem(currentRow, 1, itemAnnotated);

    // 重新选择当前行
    ui->tableWidgetUnitPic->setCurrentCell(currentRow, 0);

    // 触发点击事件，以显示新替换的图片（如果需要）
    on_tableWidgetUnitPic_clicked(ui->tableWidgetUnitPic->currentIndex());
}


void DialogUnitAttr::on_tableWidgetUnitPic_clicked(const QModelIndex &index)
{
    m_scene.clear();
    if(index.row()<0) return;
    QString absoluteImagePath = ui->tableWidgetUnitPic->item(index.row(),0)->text();
    //qDebug()<<"absoluteImagePath:"<<absoluteImagePath;
    if(absoluteImagePath.isEmpty())return;
    QPixmap pix(absoluteImagePath);
    if(!pix)return;
    m_scene.SetBackGroundImage(pix);
    ui->graphicsView->ScaleToWidget();
    CurImgPath=absoluteImagePath;
    CurUnitImageIndex=index.row();
    //qDebug()<<"ui->tableWidgetUnitPic->item(index.row(),1)->data(Qt::UserRole).toString():"<<ui->tableWidgetUnitPic->item(index.row(),1)->data(Qt::UserRole).toString();
    LoadPicTag(ui->tableWidgetUnitPic->item(index.row(),1)->data(Qt::UserRole).toString(),ui->graphicsView);
}

void DialogUnitAttr::on_BtnDelUnitPic_clicked()
{
    if(ui->tableWidgetUnitPic->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", "请选择一条图片记录！");
        return;
    }
    ui->tableWidgetUnitPic->removeRow(ui->tableWidgetUnitPic->currentRow());

    // 默认显示第一条
    if (ui->tableWidgetUnitPic->rowCount() > 0) {
        ui->tableWidgetUnitPic->setCurrentIndex(ui->tableWidgetUnitPic->model()->index(0, 0));
        on_tableWidgetUnitPic_clicked(ui->tableWidgetUnitPic->currentIndex());
    } else {
        m_scene.clear();
    }

}

void DialogUnitAttr::SlotDrawTagWrapper(int Type,QColor mColor)
{
    SlotDrawTag(ui->graphicsView,Type,mColor);
}
void DialogUnitAttr::SlotDrawTermTagWrapper(int Type,QColor mColor)
{
    //qDebug()<<"DialogUnitAttr::SlotDrawTermTagWrapper";
    SlotDrawTag(ui->graphicsView_Term,Type,mColor);
}
void DialogUnitAttr::SlotChangeColorWrapper(QColor mColor)
{
    //qDebug()<<"DialogUnitAttr::SlotChangeColorWrapper";
    SlotChangeColor(ui->graphicsView,mColor);
}
void DialogUnitAttr::SlotChangeTermColorWrapper(QColor mColor)
{
    SlotChangeColor(ui->graphicsView_Term,mColor);
}

void DialogUnitAttr::on_BtnCancelSign_clicked()
{
    if(ui->tableWidgetUnitPic->currentRow() < 0) {
        QMessageBox::warning(nullptr, "提示", "请选择一条图片记录！");
        return;
    }
    int currentRow = ui->tableWidgetUnitPic->currentRow();
    QList<QGraphicsItem *> list = m_scene.items();
    for(int i=0;i<list.count();i++)
    {
        if(list[i]->type()!=7)//图片
        {
            m_scene.removeItem(list[i]);
        }
    }
    // 更新第二列：标注信息为“否”
    QTableWidgetItem *itemAnnotated = new QTableWidgetItem("否");
    itemAnnotated->setData(Qt::UserRole, ""); // 清空标注信息
    ui->tableWidgetUnitPic->setItem(currentRow, 1, itemAnnotated);

}

void DialogUnitAttr::on_BtnSave_clicked() //dataFunc 保存器件标注信息（器件位置）
{
    if(ui->tableWidgetUnitPic->currentRow() < 0) {
        QMessageBox::warning(nullptr, "提示", "请选择有效记录后重试！");
        return;
    }

    int currentRow = ui->tableWidgetUnitPic->currentRow();
    QString originalImgPath = ui->tableWidgetUnitPic->item(currentRow, 0)->data(Qt::UserRole).toString();
    QString fileName = QFileInfo(originalImgPath).fileName();

    // 使用copyImageToDirectory辅助函数复制图片
    QString newImgPath = copyImageToDirectory(originalImgPath, CurProjectPath + PROJECT_PIC_PATH, "");


    // 使用genTagInfoFromScene辅助函数生成标签信息
    QString StrTagInfo = genTagInfoFromScene(m_scene, static_cast<int>(m_dialogTag->CurTagColor));
    qDebug()<<"StrTagInfo:"<<StrTagInfo;

    // 更新表格 - 图片列
    ui->tableWidgetUnitPic->item(currentRow, 0)->setText(newImgPath.isEmpty() ? fileName : newImgPath);
    ui->tableWidgetUnitPic->item(currentRow, 0)->setData(Qt::UserRole, newImgPath);

    // 更新表格 - 标注信息列
    QString annotated = isTagInfoValid(StrTagInfo) ? "是" : "否";

    ui->tableWidgetUnitPic->item(currentRow, 1)->setText(annotated);
    ui->tableWidgetUnitPic->item(currentRow, 1)->setData(Qt::UserRole, StrTagInfo);

    // 构建数据库更新用的图片信息字符串
    QStringList StrListPictureInfo;
    for(int i = 0; i < ui->tableWidgetUnitPic->rowCount(); i++) {
         QString mfileName = ui->tableWidgetUnitPic->item(i, 0)->text();
        if(mfileName.isEmpty())continue;
        mfileName = QFileInfo(mfileName).fileName();//取文件名
        QString tagInfo = ui->tableWidgetUnitPic->item(i, 1)->data(Qt::UserRole).toString();
        StrListPictureInfo.append(mfileName + (tagInfo.isEmpty() ? "" : "*" + tagInfo));
    }

    QSqlQuery queryEquipment(T_ProjectDatabase);
    QString SqlStr = "UPDATE Equipment SET Picture=:Picture WHERE Equipment_ID = " + CurEquipment_ID;
    queryEquipment.prepare(SqlStr);
    queryEquipment.bindValue(":Picture", StrListPictureInfo.join("||"));
    if(!queryEquipment.exec()) {
        qDebug() << "Error updating Equipment Picture:" << queryEquipment.lastError().text();
    }
}

//ui->tableTerm: 5）已标注 6）图片路径
void DialogUnitAttr::on_tableTerm_clicked(const QModelIndex &index)
{
    m_scene_term.clear();
    QString absoluteImagePath = ui->tableTerm->item(index.row(),6)->text();
    if(absoluteImagePath.isEmpty())return;
    QPixmap pix(absoluteImagePath);
    if(!pix)return;
    m_scene_term.SetBackGroundImage(pix);
    ui->graphicsView_Term->ScaleToWidget();
    CurImgPath=absoluteImagePath;
    QString strTagInfo = ui->tableTerm->item(index.row(),5)->data(Qt::UserRole).toString();
    if(isTagInfoValid(strTagInfo)) LoadPicTag(strTagInfo,ui->graphicsView_Term);
}

void DialogUnitAttr::on_BtnFromUnitImage_clicked()
{
    if(ui->tableTerm->currentRow() < 0) {
        QMessageBox::warning(nullptr, "提示", "请选择一条端子记录！");
        return;
    }
    int currentRow = ui->tableTerm->currentRow();
    qDebug()<<"CurUnitImageIndex="<<CurUnitImageIndex;
    if(CurUnitImageIndex<ui->tableWidgetUnitPic->rowCount())
    {
        m_scene_term.clear();
        QString absoluteImagePath = ui->tableWidgetUnitPic->item(CurUnitImageIndex,0)->data(Qt::UserRole).toString();
        if(absoluteImagePath.isEmpty())return;

        // 更新第5列：图片路径或文件名
        QTableWidgetItem *itemPic = new QTableWidgetItem(absoluteImagePath);
        itemPic->setData(Qt::UserRole, absoluteImagePath); // 存储新图片的绝对路径
        ui->tableTerm->setItem(currentRow, 5, itemPic);

        // 更新第4列：标注信息为“否”
        QTableWidgetItem *itemAnnotated = new QTableWidgetItem("否");
        itemAnnotated->setData(Qt::UserRole, ""); // 清空标注信息
        ui->tableTerm->setItem(currentRow, 4, itemAnnotated);

        QPixmap pix(absoluteImagePath);
        if(!pix)return;
        m_scene_term.SetBackGroundImage(pix);
        ui->graphicsView_Term->ScaleToWidget();
        CurImgPath=absoluteImagePath;
    }
    CurUnitImageIndex++;
    if(CurUnitImageIndex>=ui->tableWidgetUnitPic->rowCount()) CurUnitImageIndex=0;
}

void DialogUnitAttr::on_BtnFromDisk_clicked()
{
    QFileDialog fileDialog(this);
    fileDialog.setWindowTitle(tr("选择文件"));
    fileDialog.setDirectory(QString(CurProjectPath+PROJECT_PIC_PATH));
    fileDialog.setNameFilter(tr("Images (*.png *.xpm *.jpg *.jpeg *.gif *.webp)"));
    // fileDialog->setFileMode(QFileDialog::ExistingFiles);
    fileDialog.setViewMode(QFileDialog::Detail);
    if (!fileDialog.exec()) return;
    QStringList fileNames=fileDialog.selectedFiles();
    if(fileNames.count()!=1)
    {
        QMessageBox::warning(nullptr, "提示", "请选择一张图片！");
        return;
    }

    CurImgPath=fileNames.at(0);
    int currentRow = ui->tableTerm->currentRow();

    // 更新第5列：图片路径或文件名
    QTableWidgetItem *itemPic = new QTableWidgetItem(CurImgPath);
    itemPic->setData(Qt::UserRole, CurImgPath); // 存储新图片的绝对路径
    ui->tableTerm->setItem(currentRow, 5, itemPic);

    // 更新第4列：标注信息为“否”
    QTableWidgetItem *itemAnnotated = new QTableWidgetItem("否");
    itemAnnotated->setData(Qt::UserRole, ""); // 清空标注信息
    ui->tableTerm->setItem(currentRow, 4, itemAnnotated);

    // 触发点击事件，以显示新替换的图片（如果需要）
    on_tableTerm_clicked(ui->tableTerm->currentIndex());
}

void DialogUnitAttr::on_BtnCancelTermSign_clicked()
{
//    QList<QGraphicsItem *> list = m_scene_term.items();
//    for(int i=0;i<list.count();i++)
//    {
//        if(list[i]->type()!=7)
//        {
//            m_scene_term.removeItem(list[i]);
//        }
//    }

    if(ui->tableTerm->currentRow() < 0) {
        QMessageBox::warning(nullptr, "提示", "请选择一条端子记录！");
        return;
    }
    int currentRow = ui->tableTerm->currentRow();
    QList<QGraphicsItem *> list = m_scene_term.items();
    for(int i=0;i<list.count();i++)
    {
        if(list[i]->type()!=7)//图片
        {
            m_scene_term.removeItem(list[i]);
        }
    }
    // 更新第4列：标注信息为“否”
    QTableWidgetItem *itemAnnotated = new QTableWidgetItem("否");
    itemAnnotated->setData(Qt::UserRole, ""); // 清空标注信息
    ui->tableTerm->setItem(currentRow, 4, itemAnnotated);
}

void DialogUnitAttr::on_BtnSaveTerm_clicked()//dataFunc 保存端口标注信息
{
    if(ui->tableTerm->currentRow()<0)
    {
        QMessageBox::warning(nullptr, "提示", "请选择有效端口后重试！");
        return;
    }

    int currentRow = ui->tableTerm->currentRow();
    QString originalImgPath = ui->tableTerm->item(currentRow, 6)->data(Qt::UserRole).toString();

    // 使用copyImageToDirectory辅助函数复制图片
    CurImgPath = copyImageToDirectory(originalImgPath, CurProjectPath+PROJECT_PIC_PATH, "");
    QString fileName = QFileInfo(CurImgPath).fileName();

    // 使用genTagInfoFromScene辅助函数生成标签信息
    QString StrTagInfo = genTagInfoFromScene(m_scene_term, static_cast<int>(m_dialogTermTag->CurTagColor));
    //qDebug()<<"StrTagInfo:"<<StrTagInfo;

    //更新表格
    ui->tableTerm->item(ui->tableTerm->currentRow(), 6)->setText(CurImgPath);
    ui->tableTerm->item(ui->tableTerm->currentRow(), 5)->setText((isTagInfoValid(StrTagInfo) && !CurImgPath.isEmpty()) ? "是" : "否");
    ui->tableTerm->item(ui->tableTerm->currentRow(), 5)->setData(Qt::UserRole, StrTagInfo);

    //更新数据库
    QString Symb2TermInfo_ID = ui->tableTerm->item(ui->tableTerm->currentRow(),1)->data(Qt::UserRole).toString();
    QSqlQuery querySymb2TermInfo(T_ProjectDatabase);
    QString SqlStr=  "UPDATE Symb2TermInfo SET TestCost=:TestCost,TermPicPath=:TermPicPath,ConnDesc =:ConnDesc WHERE Symb2TermInfo_ID = "+Symb2TermInfo_ID;
    querySymb2TermInfo.prepare(SqlStr);
    querySymb2TermInfo.bindValue(":ConnDesc", ui->tableTerm->item(ui->tableTerm->currentRow(),2)->text());
    querySymb2TermInfo.bindValue(":TestCost",ui->tableTerm->item(ui->tableTerm->currentRow(),4)->text());
    QString termPicPath = fileName + (StrTagInfo.isEmpty() ? "" : "*" + StrTagInfo); // 构建 "文件名*标签信息" 格式的字符串
    querySymb2TermInfo.bindValue(":TermPicPath", termPicPath); // 绑定处理后的路径
    if(!querySymb2TermInfo.exec()) {
        qDebug() << "Error executing SQL query:" << querySymb2TermInfo.lastError().text();
    }
}

QString DialogUnitAttr::getPortVariables(const QString &functionBlock, const QString &portName) const
{
    if (m_componentContainerId <= 0 || !T_ProjectDatabase.isValid())
        return QString();

    QSqlQuery query(T_ProjectDatabase);
    query.prepare("SELECT variables_json FROM port_config "
                  "WHERE container_id = ? AND function_block = ? AND port_name = ?");
    query.addBindValue(m_componentContainerId);
    query.addBindValue(functionBlock);
    query.addBindValue(portName);

    if (!query.exec() || !query.next())
        return QString();

    QString json = query.value(0).toString();
    QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8());
    if (!doc.isArray())
        return QString();

    QStringList vars;
    QJsonArray array = doc.array();
    for (const QJsonValue &val : array) {
        if (val.isObject()) {
            vars.append(val.toObject().value("name").toString());
        }
    }
    return vars.join(",");
}

void DialogUnitAttr::showTableTermContextMenu(const QPoint &pos)
{
    if (!ui->tableTerm->indexAt(pos).isValid())
        return;

    QMenu menu(this);
    QAction *actConfigPort = menu.addAction("配置端口");
    QAction *actRemoveConfig = menu.addAction("删除配置");

    connect(actConfigPort, &QAction::triggered, this, &DialogUnitAttr::onConfigurePort);
    connect(actRemoveConfig, &QAction::triggered, this, &DialogUnitAttr::onRemovePortConfig);

    menu.exec(QCursor::pos());
}

void DialogUnitAttr::onConfigurePort()
{
    int currentRow = ui->tableTerm->currentRow();
    if (currentRow < 0)
        return;

    QString functionBlock = ui->tableTerm->item(currentRow, 0)->text();
    QString portName = ui->tableTerm->item(currentRow, 1)->text();

    PortConfigEditDialog dialog(T_ProjectDatabase, m_componentContainerId, this);
    dialog.setPortInfo(functionBlock, portName);
    dialog.loadConfig();

    if (dialog.exec() == QDialog::Accepted) {
        if (dialog.saveConfig()) {
            // 更新表格中的变量显示
            QString variables = getPortVariables(functionBlock, portName);
            ui->tableTerm->item(currentRow, 3)->setText(variables);
            QMessageBox::information(this, "成功", "端口配置已保存");
        }
    }
}

void DialogUnitAttr::onRemovePortConfig()
{
    int currentRow = ui->tableTerm->currentRow();
    if (currentRow < 0)
        return;

    QString functionBlock = ui->tableTerm->item(currentRow, 0)->text();
    QString portName = ui->tableTerm->item(currentRow, 1)->text();

    QMessageBox::StandardButton reply = QMessageBox::question(
        this, "确认删除", 
        QString("确定要删除端口 %1.%2 的配置吗？").arg(functionBlock, portName),
        QMessageBox::Yes | QMessageBox::No);

    if (reply != QMessageBox::Yes)
        return;

    QSqlQuery query(T_ProjectDatabase);
    query.prepare("DELETE FROM port_config WHERE container_id = ? AND function_block = ? AND port_name = ?");
    query.addBindValue(m_componentContainerId);
    query.addBindValue(functionBlock);
    query.addBindValue(portName);

    if (query.exec()) {
        // 清空表格中的变量显示
        ui->tableTerm->item(currentRow, 3)->setText("");
        QMessageBox::information(this, "成功", "端口配置已删除");
    } else {
        QMessageBox::warning(this, "失败", "删除端口配置失败：" + query.lastError().text());
    }
}

// ===================== 常量管理功能实现 =====================

void DialogUnitAttr::showConstantsContextMenu(const QPoint &pos)
{
    QMenu menu(this);
    
    // 获取点击位置
    QModelIndex index = ui->tableWidgetStructure->indexAt(pos);
    
    if (index.isValid() && index.column() == 0) {
        // 在常量名列点击：插入常量名到编辑器
        QAction *insertAction = menu.addAction("插入常量名到T语言模型");
        connect(insertAction, &QAction::triggered, this, &DialogUnitAttr::onInsertConstantName);
        menu.addSeparator();
    }
    
    // 通用菜单项
    QAction *addAction = menu.addAction("新增");
    connect(addAction, &QAction::triggered, this, &DialogUnitAttr::onAddConstant);
    
    if (ui->tableWidgetStructure->selectionModel()->hasSelection()) {
        QAction *deleteAction = menu.addAction("删除");
        connect(deleteAction, &QAction::triggered, this, &DialogUnitAttr::onDeleteConstants);
    }
    
    menu.exec(ui->tableWidgetStructure->viewport()->mapToGlobal(pos));
}

void DialogUnitAttr::onAddConstant()
{
    int row = ui->tableWidgetStructure->rowCount();
    ui->tableWidgetStructure->insertRow(row);
    
    ui->tableWidgetStructure->setItem(row, 0, new QTableWidgetItem(""));  // 常量名
    ui->tableWidgetStructure->setItem(row, 1, new QTableWidgetItem(""));  // 值
    ui->tableWidgetStructure->setItem(row, 2, new QTableWidgetItem(""));  // 单位
    ui->tableWidgetStructure->setItem(row, 3, new QTableWidgetItem(""));  // 备注
    
    // 自动进入编辑模式
    ui->tableWidgetStructure->editItem(ui->tableWidgetStructure->item(row, 0));
}

void DialogUnitAttr::onDeleteConstants()
{
    QList<int> selectedRows;
    QList<QTableWidgetItem *> selectedItems = ui->tableWidgetStructure->selectedItems();
    
    for (QTableWidgetItem *item : selectedItems) {
        int row = item->row();
        if (!selectedRows.contains(row)) {
            selectedRows.append(row);
        }
    }
    
    if (selectedRows.isEmpty()) {
        return;
    }
    
    // 排序行号（从大到小，避免删除时索引变化）
    std::sort(selectedRows.begin(), selectedRows.end(), std::greater<int>());
    
    // 如果删除多行，二次确认
    if (selectedRows.count() > 1) {
        QMessageBox::StandardButton reply = QMessageBox::question(
            this, "确认删除", 
            QString("确定要删除选中的 %1 个常量吗？").arg(selectedRows.count()),
            QMessageBox::Yes | QMessageBox::No);
        
        if (reply != QMessageBox::Yes) {
            return;
        }
    }
    
    // 删除选中的行
    for (int row : selectedRows) {
        ui->tableWidgetStructure->removeRow(row);
    }
}

void DialogUnitAttr::onInsertConstantName()
{
    int currentRow = ui->tableWidgetStructure->currentRow();
    if (currentRow < 0) {
        return;
    }
    
    QTableWidgetItem *nameItem = ui->tableWidgetStructure->item(currentRow, 0);
    if (!nameItem) {
        return;
    }
    
    QString constantName = nameItem->text().trimmed();
    if (constantName.isEmpty()) {
        QMessageBox::warning(this, "警告", "常量名为空");
        return;
    }
    
    // 插入到T语言模型编辑器的光标位置
    QString textToInsert = "%" + constantName + "%";
    QsciEdit->insert(textToInsert);
    QsciEdit->setFocus();
}

void DialogUnitAttr::loadConstants(const QString &constantsData)
{
    ui->tableWidgetStructure->setRowCount(0);
    
    if (constantsData.isEmpty()) {
        return;
    }
    
    // 格式：常量名1,值1,单位1,备注1;常量名2,值2,单位2,备注2;...
    QStringList constantsList = constantsData.split(";", QString::SkipEmptyParts);
    
    for (const QString &constantStr : constantsList) {
        QStringList parts = constantStr.split(",");
        if (parts.count() >= 2) {  // 至少需要常量名和值
            int row = ui->tableWidgetStructure->rowCount();
            ui->tableWidgetStructure->insertRow(row);
            
            ui->tableWidgetStructure->setItem(row, 0, new QTableWidgetItem(parts.at(0)));  // 常量名
            ui->tableWidgetStructure->setItem(row, 1, new QTableWidgetItem(parts.at(1)));  // 值
            ui->tableWidgetStructure->setItem(row, 2, new QTableWidgetItem(parts.count() > 2 ? parts.at(2) : ""));  // 单位
            ui->tableWidgetStructure->setItem(row, 3, new QTableWidgetItem(parts.count() > 3 ? parts.at(3) : ""));  // 备注
        }
    }
}

QString DialogUnitAttr::saveConstants() const
{
    QStringList constantsList;
    
    for (int i = 0; i < ui->tableWidgetStructure->rowCount(); i++) {
        QString name = ui->tableWidgetStructure->item(i, 0) ? ui->tableWidgetStructure->item(i, 0)->text().trimmed() : "";
        QString value = ui->tableWidgetStructure->item(i, 1) ? ui->tableWidgetStructure->item(i, 1)->text().trimmed() : "";
        QString unit = ui->tableWidgetStructure->item(i, 2) ? ui->tableWidgetStructure->item(i, 2)->text().trimmed() : "";
        QString remark = ui->tableWidgetStructure->item(i, 3) ? ui->tableWidgetStructure->item(i, 3)->text().trimmed() : "";
        
        if (name.isEmpty()) {
            continue;  // 跳过空常量名
        }
        
        QString constantStr = name + "," + value + "," + unit + "," + remark;
        constantsList.append(constantStr);
    }
    
    return constantsList.join(";");
}

bool DialogUnitAttr::validateConstantName(const QString &name, int excludeRow) const
{
    if (name.trimmed().isEmpty()) {
        return false;
    }
    
    // 检查常量名是否重复
    for (int i = 0; i < ui->tableWidgetStructure->rowCount(); i++) {
        if (i == excludeRow) {
            continue;
        }
        
        QTableWidgetItem *item = ui->tableWidgetStructure->item(i, 0);
        if (item && item->text().trimmed() == name.trimmed()) {
            return false;  // 重复
        }
    }
    
    return true;
}

// ==================== 端口变量更新功能 ====================
void DialogUnitAttr::on_BtnUpdatePortVars_clicked()
{
    // 从tableTerm生成端口变量
    QString portVars = TModelHelper::generatePortVariablesFromTable(ui->tableTerm);
    
    // 获取当前T语言模型文本
    QString tmodelText = QsciEdit->text();
    
    // 更新端口变量部分
    QString updatedTModel = TModelHelper::updatePortVariablesInTModel(tmodelText, portVars);
    
    // 设置回编辑器
    QsciEdit->setText(updatedTModel);
    
    QMessageBox::information(this, "提示", "端口变量已更新");
}

// ==================== 维修信息右键菜单 ====================
void DialogUnitAttr::showRepairInfoContextMenu(const QPoint &pos)
{
    QMenu menu;
    QAction *addAction = menu.addAction("新增");
    QAction *deleteAction = menu.addAction("删除");
    QAction *autoFillAction = menu.addAction("从T语言中自动获取");
    
    connect(addAction, &QAction::triggered, this, &DialogUnitAttr::onAddRepairInfo);
    connect(deleteAction, &QAction::triggered, this, &DialogUnitAttr::onDeleteRepairInfo);
    connect(autoFillAction, &QAction::triggered, this, &DialogUnitAttr::onAutoFillFromTModel);
    
    menu.exec(ui->tableRepairInfo->viewport()->mapToGlobal(pos));
}

void DialogUnitAttr::onAddRepairInfo()
{
    int row = ui->tableRepairInfo->rowCount();
    ui->tableRepairInfo->insertRow(row);
    
    // 创建空白项
    for (int col = 0; col < 4; col++) {
        QTableWidgetItem *item = new QTableWidgetItem("");
        ui->tableRepairInfo->setItem(row, col, item);
    }
    
    // 选中新行并开始编辑
    ui->tableRepairInfo->setCurrentCell(row, 0);
    ui->tableRepairInfo->editItem(ui->tableRepairInfo->item(row, 0));
}

void DialogUnitAttr::onDeleteRepairInfo()
{
    QList<QTableWidgetItem*> selectedItems = ui->tableRepairInfo->selectedItems();
    if (selectedItems.isEmpty()) {
        QMessageBox::warning(this, "警告", "请先选择要删除的行");
        return;
    }
    
    // 获取选中的行号（去重）
    QSet<int> selectedRows;
    for (QTableWidgetItem *item : selectedItems) {
        selectedRows.insert(item->row());
    }
    
    // 如果选中多行，二次确认
    if (selectedRows.count() > 1) {
        QMessageBox::StandardButton reply = QMessageBox::question(
            this, 
            "确认删除", 
            QString("确定要删除选中的 %1 行吗？").arg(selectedRows.count()),
            QMessageBox::Yes | QMessageBox::No
        );
        
        if (reply != QMessageBox::Yes) {
            return;
        }
    }
    
    // 从后往前删除（避免行号变化）
    QList<int> rowList = selectedRows.toList();
    std::sort(rowList.begin(), rowList.end(), std::greater<int>());
    
    for (int row : rowList) {
        ui->tableRepairInfo->removeRow(row);
    }
}

void DialogUnitAttr::onAutoFillFromTModel()
{
    QString tmodelText = QsciEdit->text();
    
    if (tmodelText.trimmed().isEmpty()) {
        QMessageBox::information(this, "提示", "T语言模型为空");
        return;
    }
    
    int addedCount = TModelHelper::autoFillFaultModesFromTModel(ui->tableRepairInfo, tmodelText);
    
    if (addedCount > 0) {
        QMessageBox::information(this, "提示", QString("已添加 %1 个故障模式").arg(addedCount));
    } else {
        QMessageBox::information(this, "提示", "没有新的故障模式需要添加");
    }
}
