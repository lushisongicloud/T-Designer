#include "diagnosis_mainwindow.h"
#include "ui_diagnosis_mainwindow.h"
#include <QMessageBox>
#include  <QtDebug>
#include "dialog_select_another_test.h"
#include "dialog_select_test_preference.h"
#include "diaglog_diagnosis_of_details_record.h"
#include "dialog_case_entry_failure_module.h"
#include "dialog_case_entry_symptom_new.h"
#include "dialog_case_entry_test_new.h"
#include "dialog_case_entry_failure_module.h"
#include "thread_init.h"
#include "matrix_d_class.h"
#include <QProcess>
#include "checksum.h"
#include "add_new_account.h"
#if _MSC_VER >= 1600	// MSVC2015 > 1899,	MSVC_VER = 14.0
#pragma execution_character_set("utf-8")
#endif

Matrix_D_class  Matrix_D;//D矩阵
QString diagnosis_model_name;//诊断模型名称
QSqlDatabase TMATE_MDB;//TMATE数据库链接
QSqlQuery qsQuery_TMATE_MDB;//TMATE数据库选择模型
QString sql_prepare;//数据库检索准备语句
Str_account  LoginAccount;//登陆账户

Diagnosis_MainWindow::Diagnosis_MainWindow(QWidget *parent) :
    QMainWindow(parent),
    ui(new Ui::Diagnosis_MainWindow)
{
    dlg_delay=new Dialog_wait(this);
    dlg_delay->setModal(true);

    QScreen *screen = QGuiApplication::primaryScreen ();
    QRect screenRect =  screen->availableVirtualGeometry();
    screenWidth = screenRect.width();

    dlg_showPicture =new QDialog(this);
    dlg_showPicture->setModal(true);
    picture_Label = new QLabel(dlg_showPicture);
    QHBoxLayout *layout = new QHBoxLayout;
    layout->addWidget(picture_Label);
    dlg_showPicture->setLayout(layout);
    dlg_showPicture->setMinimumSize(200,200);

    tableWidgetStyleSheet = "QTableWidget{background-color: rgba(250, 250, 250,0);"
                            "alternate-background-color: rgba(234, 234, 234,0);"
                            "font: 12pt '微软雅黑';"
                            "border-color: rgba(255, 255, 255, 0);}"
                            "QTableWidget::indicator {width: 50px;height: 50px;}"
                            "QTableWidget::indicator:unchecked {image: url(:/new/prefix1/Diagnosis_Image/No.png);}"
                            "QTableWidget::indicator:checked {image: url(:/new/prefix1/Diagnosis_Image/Yes.png);}"
                            "QTableWidget::item{padding-top:15px;padding-bottom:15px;}";

    tableViewStyleSheet = "QTableView{background-color: rgba(250, 250, 250,0);"
                          "alternate-background-color: rgba(234, 234, 234,0);"
                          "font: 12pt '微软雅黑';"
                          "border-color: rgba(255, 255, 255, 0);}"
                          "QTableView::indicator {width: 50px;height: 50px;}"
                          "QTableView::indicator:unchecked {image: url(:/new/prefix1/Diagnosis_Image/No.png);}"
                          "QTableView::indicator:checked {image: url(:/new/prefix1/Diagnosis_Image/Yes.png);}"
                          "QTableView::item{padding-top:15px;padding-bottom:15px;}";


    tableWidgetScrollBarStyleSheet = "QScrollBar:vertical{min-width: 40px;}";
    tableWidgetHorizontalHeaderStyleSheet = "QHeaderView::section {color: black;"
                                            "padding-left: 4px;border: 1px solid #6c6c6c;"
                                            "height: 35px;font: 75 10pt '微软雅黑'}";
    ui->setupUi(this);
    setWindowTitle("设备故障诊断系统");
    connect_TMATE_MDB();//建立TMATE数据库连接
    ui->stackedWidget_main->setCurrentIndex(0);

    ui->Display_menu_bar->trigger();
    init_model_list();//初始化模型列表

    //设置遮罩窗口
    mpShadeWindow = new QWidget(this);
    QString str("QWidget{background-color:rgba(0,0,0,0.6);}");
    mpShadeWindow->setStyleSheet(str);
    mpShadeWindow->setGeometry(0, 0, 1, 1);
    mpShadeWindow->hide();
}

Diagnosis_MainWindow::~Diagnosis_MainWindow()
{
    delete ui;
    delete dlg_delay; //删除对话框
    delete dlg_showPicture;
}

void Diagnosis_MainWindow::connect_TMATE_MDB()//创建TMATE数据库连接
{
    TMATE_MDB= QSqlDatabase::addDatabase("QODBC","TMATE_MDB");//设置数据库驱动
    QString m_strFilePath = "C:/MDB/TMATE.MDB";//数据库文件
    QString dsn = QString("DRIVER={Microsoft Access Driver (*.mdb, *.accdb)}; FIL={MS Access};DBQ=%1;").arg(m_strFilePath);//连接字符串
    TMATE_MDB.setDatabaseName(dsn);//设置连接字符串
    if (!TMATE_MDB.open()) {
        QMessageBox::warning(nullptr, QObject::tr("Database Error"),
                             TMATE_MDB.lastError().text());
    }
    qsQuery_TMATE_MDB = QSqlQuery(TMATE_MDB);//设置数据库选择模型
}

void Diagnosis_MainWindow::hide_menu_bar()
{
    //ui->widget_list->hide();
    //ui->widget_logo->hide();
    //ui->stackedWidget_main->showMaximized();
}

void Diagnosis_MainWindow::show_menu_bar()
{
    //ui->widget_list->show();
    //ui->widget_logo->show();
    //ui->stackedWidget_main->showMaximized();
}
/***********************************************************************************************************************************/
/*****************************************************配置向导模块(操作数据库)*********************************************************/
/***********************************************************************************************************************************/
/////////////////////////////////////////////////////////
///        \brief select_test_preference_UI           ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::on_select_ratio_triggered()//诊断偏好配置按钮
{
    if(diagnosis_model_name == nullptr){
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择模型"),QMessageBox::Yes);
        return;}

    Dialog_select_test_preference *dlg=new Dialog_select_test_preference(this);
    dlg->showNormal();
    dlg->setWindowTitle("设备故障诊断系统");
    dlg->setModal(true);
    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        //更新本地偏好集并存储到数据库
        QList<int> PreferData;
        PreferData = dlg->get_UI_Value();

        Matrix_D.ThisPreferData.TEST_COST_prefer = PreferData[0];
        Matrix_D.ThisPreferData.TEST_LEVEL_prefer = PreferData[1];
        Matrix_D.ThisPreferData.TEST_TIME_prefer = PreferData[2];
        Matrix_D.ThisPreferData.FAULT_PROBABLITY_prefer = PreferData[3];

        sql_prepare = QString("UPDATE MODELS SET TEST_COST_PREFERENCE = %1,TEST_LEVEL_PREFERENCE = %2,TEST_TIME_PREFERENCE = %3,FAULT_PROBABILITY_PREFERENCE = %4 WHERE MODEL_NAME = '%5';")
                .arg(PreferData[0]).arg(PreferData[1]).arg(PreferData[2]).arg(PreferData[3]).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    delete dlg; //删除对话框
}

/////////////////////////////////////////////////////////
///             \brief model_select_UI                ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::init_model_list()//初始化模型列表
{
    ui->tableView_model_select->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑
    ui->tableView_model_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中

    tabModel=new MyQSqlTableModel(this,TMATE_MDB);//数据表
    tabModel->setTable("MODELS"); //设置数据表
    tabModel->setEditStrategy(QSqlTableModel::OnManualSubmit);//数据保存方式，OnManualSubmit,OnRowChange
    if (!(tabModel->select()))//查询数据
    {
        QMessageBox::critical(this, "错误信息",
                              "打开数据表错误,错误信息\n"+tabModel->lastError().text(),
                              QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }

    //字段显示名
    tabModel->setHeaderData(tabModel->fieldIndex("MODEL_NAME"),Qt::Horizontal,"模型名称");
    tabModel->setHeaderData(tabModel->fieldIndex("UPDATED_BY"),Qt::Horizontal,"导入人");
    tabModel->setHeaderData(tabModel->fieldIndex("UPDATE_TIME"),Qt::Horizontal,"导入时间");
    tabModel->setHeaderData(tabModel->fieldIndex("MODEL_TID"),Qt::Horizontal,"模型TID");
    tabModel->setHeaderData(tabModel->fieldIndex("NUM_MODULES"),Qt::Horizontal,"模块个数");
    tabModel->setHeaderData(tabModel->fieldIndex("SYSTEM_MODEL_NAME"),Qt::Horizontal,"系统名称");
    tabModel->setHeaderData(tabModel->fieldIndex("SYSTEM_MODEL_REVISION"),Qt::Horizontal,"模型版本号");
    tabModel->setHeaderData(tabModel->fieldIndex("CREATION_TIME"),Qt::Horizontal,"创建时间");
    tabModel->setHeaderData(tabModel->fieldIndex("CREATED_BY"),Qt::Horizontal,"创建人");
    tabModel->setHeaderData(tabModel->fieldIndex("NOTES"),Qt::Horizontal,"备注");

    ui->tableView_model_select->verticalHeader()->hide();//隐藏行序号
    ui->tableView_model_select->setModel(tabModel);//设置数据模型

    //设置表头
    ui->tableView_model_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableView_model_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗

    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("UPDATED_BY"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("UPDATE_TIME"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("MODEL_TID"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("SYSTEM_MODEL_NAME"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("CREATION_TIME"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("TEST_COST_PREFERENCE"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("TEST_LEVEL_PREFERENCE"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("TEST_TIME_PREFERENCE"),true);//隐藏列
    ui->tableView_model_select->setColumnHidden(tabModel->fieldIndex("FAULT_PROBABILITY_PREFERENCE"),true);//隐藏列

    ui->tableView_model_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableView_model_select->setStyleSheet(tableViewStyleSheet);//设置表格颜色

    ui->tableView_model_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);
    ui->tableView_model_select->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    ui->tableView_model_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格列宽随View变化


    //将征兆与测试双选项目改为征兆
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_DESIGN_FLAG = %1 WHERE TEST_TYPE = 3;")
            .arg(3);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_TYPE = %1 WHERE TEST_TYPE = 3;")
            .arg(1);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();
}

void Diagnosis_MainWindow::on_toolButton_delete_model_clicked()//删除模型按钮
{
    int curRow = ui->tableView_model_select->currentIndex().row();
    QString MODEL_NAME = tabModel->record(curRow).value("MODEL_NAME").toString();//获取当前选择模型名称
    //是否选择了模型
    if(MODEL_NAME == nullptr){
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择模型"),QMessageBox::Yes);
        return;}
    //确认是否删除
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("是否确认从本地数据库移除该模型?"),
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);
    if(result==QMessageBox::Yes)
    {
        delete_lacal_MODELS_all_information(MODEL_NAME);//删除本地该模型所有信息
        QMessageBox::about(this,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("模型已从本地数据库移除"));
        init_model_list();//初始化模型列表
    }
}

void Diagnosis_MainWindow::delete_lacal_MODELS_all_information(QString selected_model)//删除本地所有该模型信息
{
    sql_prepare = QString("DELETE *FROM MODULE_INPUTS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODULE_OUTPUTS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);

    sql_prepare = QString("DELETE *FROM TEST_MEDIA WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODULE_MEDIA WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MULTIMEDIA WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);

    sql_prepare = QString("DELETE *FROM TESTS_IN_TEST_POINT WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM TEST_RESOURCES WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM TEST_OUTCOME_SIGNALS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM TEST_POINTS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM TEST_PROPS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM DEPENDENCY WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MATRIX_D_AND_TEST_MARK WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODULE_SIGNALS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODEL_HIERARCHY WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODULE_PROPS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODELS WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    sql_prepare = QString("DELETE *FROM MODEL_RESOURCES WHERE MODEL_NAME = '%1';" ).arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
}

QString Diagnosis_MainWindow::ModuleBelongsSubSystem(QString ModelName, QString ModuleName)
{
    QString ModuleParentTID;
    QString ModuleParentHierarchyLabel;
    QString ModuleParentName = ModuleName;
    do{
        sql_prepare = QString("SELECT PARENT_TID FROM MODEL_HIERARCHY WHERE MODEL_NAME = '%1' AND NAME = '%2';")
                .arg(ModelName).arg(ModuleParentName);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            ModuleParentTID =  qsQuery_TMATE_MDB.value(0).toString();
        }

        sql_prepare = QString("SELECT MODULE_NAME,HIERARCHY_LABEL FROM MODULE_PROPS WHERE MODEL_NAME = '%1' AND MODULE_TID = '%2';")
                .arg(ModelName).arg(ModuleParentTID);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            ModuleParentHierarchyLabel =  qsQuery_TMATE_MDB.value(1).toString();
            ModuleParentName =   qsQuery_TMATE_MDB.value(0).toString();
        }
    }
    while((ModuleParentHierarchyLabel=="LRU")||(ModuleParentHierarchyLabel=="SRU"));

    return ModuleParentName;

}

void Diagnosis_MainWindow::on_toolButton_start_diagnosis_clicked()//开始诊断按钮,至工具选择界面
{
    //若没有选择模型，发出警告
    int curRow = ui->tableView_model_select->currentIndex().row();
    QString MODEL_NAME = tabModel->record(curRow).value("MODEL_NAME").toString();//获取当前选择模型名称

    if(MODEL_NAME == nullptr){
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择模型"),QMessageBox::Yes);
        return;}

    diagnosis_model_name = MODEL_NAME;//存储需要诊断的模型名称
    Matrix_D.diagnostic_record.list_Diagnosis_test_record.clear();//诊断记录测试列表初始化
    Matrix_D.diagnostic_record.start_time =  QDateTime::currentDateTime();//诊断开始时间
    Matrix_D.diagnostic_record.Diagnosis_Date = QDate::currentDate();//检修日期

    //跳转到工具选择界面
    ui->stackedWidget_main->setCurrentIndex(1);
    if(ui->Display_menu_bar->isChecked())
        ui->Display_menu_bar->trigger();
    hide_menu_bar();

    //初始化诊断设置
    sql_prepare = QString("UPDATE MODELS SET TEST_COST_PREFERENCE = %1,TEST_LEVEL_PREFERENCE = %2,TEST_TIME_PREFERENCE = %3,FAULT_PROBABILITY_PREFERENCE = %4 WHERE MODEL_NAME = '%5';")
            .arg(5).arg(5).arg(10).arg(10).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    init_tool_list(MODEL_NAME,"all");//初始化工具选择列表
}

/////////////////////////////////////////////////////////
///             \brief tool_select_UI                 ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::on_toolButton_tool_select_last_clicked()//工具选择列表上一步按钮,至模型选择界面
{
    ui->stackedWidget_main->setCurrentIndex(0);
    init_model_list();//初始化模型列表
}

void Diagnosis_MainWindow::init_tool_list(QString model_name,QString fuzzy_search)//初始化模型所需工具列表
{
    ui->lineEdit_tool_serch->clear();//清空搜索栏

    init_tool_list_is_not_cell_change = true;
    ui->tableWidget_tool_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_tool_select->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    //ui->tableWidget_tool_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格列宽随View变化
    ui->tableWidget_tool_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("测试仪器") << tr("模型名称") << tr("是否可用");
    ui->tableWidget_tool_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_tool_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_tool_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_tool_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);

    ui->tableWidget_tool_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_tool_select->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_tool_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);

    //设置表头
    ui->tableWidget_tool_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_tool_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗

    //查找数据信息
    typedef struct{
        QString RESOURCE_NAME;
        QString MODEL_NAME;
        bool    AVAILABEL;
        char m_padding [3];//去除警告，字节对齐使用
    }Str_MODEL_RESOURCES;
    QList<Str_MODEL_RESOURCES> MODEL_RESOURCES_List;

    //查找TMATE数据库模型工具需求信息
    if(fuzzy_search == "all")
        sql_prepare = QString("SELECT RESOURCE_NAME,MODEL_NAME,AVAILABLE "
                              "FROM MODEL_RESOURCES WHERE MODEL_NAME = '%1';").arg(model_name);
    else
        sql_prepare = QString("SELECT RESOURCE_NAME,MODEL_NAME,AVAILABLE "
                              "FROM MODEL_RESOURCES WHERE MODEL_NAME = '%1' "
                              "AND RESOURCE_NAME LIKE '%%2%';").arg(model_name).arg(fuzzy_search);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Str_MODEL_RESOURCES MODEL_RESOURCES;
        MODEL_RESOURCES.RESOURCE_NAME = qsQuery_TMATE_MDB.value(0).toString();
        MODEL_RESOURCES.MODEL_NAME = qsQuery_TMATE_MDB.value(1).toString();
        MODEL_RESOURCES.AVAILABEL = qsQuery_TMATE_MDB.value(2).toBool();
        MODEL_RESOURCES_List.append(MODEL_RESOURCES);
    }
    //设置表格的默认的行数
    ui->tableWidget_tool_select->setRowCount(MODEL_RESOURCES_List.size());//设置默认的行数
    ui->tableWidget_tool_select->verticalHeader()->hide();//隐藏行序号
    //数据显示
    for(int i=0;i<MODEL_RESOURCES_List.size();i++)
    {
        ui->tableWidget_tool_select->setItem(i,0,new QTableWidgetItem(MODEL_RESOURCES_List[i].RESOURCE_NAME));
        ui->tableWidget_tool_select->setItem(i,1,new QTableWidgetItem(MODEL_RESOURCES_List[i].MODEL_NAME));

        QTableWidgetItem *checkBox = new QTableWidgetItem();
        if(MODEL_RESOURCES_List[i].AVAILABEL) checkBox->setCheckState(Qt::Checked);
        else checkBox->setCheckState(Qt::Unchecked);

        ui->tableWidget_tool_select ->setItem(i, 2, checkBox);

        ui->tableWidget_tool_select->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_tool_select->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }
    init_tool_list_is_not_cell_change = false;
}

void Diagnosis_MainWindow::on_tableWidget_tool_select_cellChanged(int row, int column)//工具列表选择或取消操作数据库
{
    if(!init_tool_list_is_not_cell_change)
    {
        if(column == 2)
        {
            bool SIGN;
            QString cellchanged_resource_name = ui->tableWidget_tool_select->item(row, 0)->text();
            QString cellchanged_model_name = ui->tableWidget_tool_select->item(row, 1)->text();

            if(ui->tableWidget_tool_select->item(row, 2)->checkState() == Qt::Checked) //选中
                SIGN = true;
            else
                SIGN = false;
            sql_prepare = QString("UPDATE MODEL_RESOURCES SET AVAILABLE= %1 WHERE"
                                  " RESOURCE_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(SIGN).arg(cellchanged_resource_name).arg(cellchanged_model_name);
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
        }
    }
}

void Diagnosis_MainWindow::on_toolButton_tool_select_all_clicked()//工具全选
{
    int row_count = ui->tableWidget_tool_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        if(ui->tableWidget_tool_select->item(i, 2)->checkState() != Qt::Checked)
        {
            ui->tableWidget_tool_select->item(i, 2)->setCheckState(Qt::Checked);
        }
    }
}

void Diagnosis_MainWindow::on_toolButton_tool_not_select_all_clicked()//工具全不选
{
    int row_count = ui->tableWidget_tool_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        if(ui->tableWidget_tool_select->item(i, 2)->checkState() == Qt::Checked)
        {
            ui->tableWidget_tool_select->item(i, 2)->setCheckState(Qt::Unchecked);
        }
    }
}

void Diagnosis_MainWindow::on_btn_tool_serch_clicked()//工具模糊选择
{
    QString fuzzy_search = ui->lineEdit_tool_serch->text();
    init_tool_list(diagnosis_model_name,fuzzy_search);//初始化工具选择列表
}

void Diagnosis_MainWindow::on_toolButton_tool_select_next_clicked()//工具列表选择下一步按钮,至测试选择界面
{
//    ui->stackedWidget_main->setCurrentIndex(2);
//    ui->lineEdit_known_test_description_searching->clear();//清空搜索栏
//    ui->lineEdit_known_test_name_searching->clear();

    //跳转到征兆选择界面
    ui->stackedWidget_main->setCurrentIndex(3);
    ui->lineEdit_known_symptom_name_searching->clear();//清空搜索栏
    ui->lineEdit_known_symptom_discription_searching->clear();

    //数据库操作将所有测试全选跳过
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 1;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    //数据库操作将所有征兆全选跳过
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%3'  AND TEST_TYPE = 2;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    init_symptom_list(diagnosis_model_name,"all","all");//初始化征兆选择列表

    //init_test_list(diagnosis_model_name,"all","all");//初始化测试信号UI列表
}

/////////////////////////////////////////////////////////
///    \brief known_test_signal_select_UI             ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::on_toolButton_known_test_select_last_clicked()//测试选择上一步按钮,至工具选择界面
{
    //跳转到工具选择界面
    ui->stackedWidget_main->setCurrentIndex(1);
    init_tool_list(diagnosis_model_name,"all");//初始化工具选择列表
}

void Diagnosis_MainWindow::init_test_list(QString model_name,QString fuzzy_name_search,QString fuzzy_description_search)//初始化测试信号UI列表
{
    init_known_test_list_is_not_cell_change = true;

    ui->tableWidget_known_test_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_known_test_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_known_test_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_known_test_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);

    ui->tableWidget_known_test_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("现象测试名称") << tr("现象测试描述")<< tr("现象结果描述") << tr("正常")<< tr("异常")<< tr("跳过");
    ui->tableWidget_known_test_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_known_test_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_known_test_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_known_test_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);
    ui->tableWidget_known_test_select->horizontalHeader()->setSectionResizeMode(2, QHeaderView::Stretch);

    ui->tableWidget_known_test_select->setAlternatingRowColors(true);//使表格颜色交错功能为真

    ui->tableWidget_known_test_select->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_known_test_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);

    //设置表头
    ui->tableWidget_known_test_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_known_test_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_known_test_select->setFocusPolicy(Qt::NoFocus);

    //查找数据信息
    typedef struct{
        QString TEST_NAME;
        QString TEST_PROCEDURE;
        QString DESCRIPTION;
        int TEST_SIGNAL_IS_EXIT_OR_NOT;
    }Str_MODEL_TSET_EXIT;
    QList<Str_MODEL_TSET_EXIT> MODEL_TSET_List;


    if(fuzzy_name_search == "all")
        fuzzy_name_search = "";
    if(fuzzy_description_search == "all")
        fuzzy_description_search = "";
    sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,DESCRIPTION,TEST_SIGNAL_IS_EXIT_OR_NOT "
                          "FROM TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 1 AND TEST_NAME LIKE '%%2%' AND TEST_PROCEDURE LIKE '%%3%';")
            .arg(model_name).arg(fuzzy_name_search).arg(fuzzy_description_search);


    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Str_MODEL_TSET_EXIT MODEL_TSET;
        MODEL_TSET.TEST_NAME = qsQuery_TMATE_MDB.value(0).toString();
        MODEL_TSET.TEST_PROCEDURE = qsQuery_TMATE_MDB.value(1).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(MODEL_TSET.TEST_PROCEDURE.startsWith("\n")||MODEL_TSET.TEST_PROCEDURE.startsWith("\r"))
            MODEL_TSET.TEST_PROCEDURE.remove(0,2);
        MODEL_TSET.DESCRIPTION = qsQuery_TMATE_MDB.value(2).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(MODEL_TSET.DESCRIPTION.startsWith("\n")||MODEL_TSET.DESCRIPTION.startsWith("\r"))
            MODEL_TSET.DESCRIPTION.remove(0,2);
        MODEL_TSET.TEST_SIGNAL_IS_EXIT_OR_NOT = qsQuery_TMATE_MDB.value(3).toInt();
        MODEL_TSET_List.append(MODEL_TSET);
    }
    //设置表格的默认的行数
    ui->tableWidget_known_test_select->setRowCount(MODEL_TSET_List.size());//设置默认的行数
    ui->tableWidget_known_test_select->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<MODEL_TSET_List.size();i++)
    {
        ui->tableWidget_known_test_select->setItem(i,0,new QTableWidgetItem(MODEL_TSET_List[i].TEST_NAME));
        ui->tableWidget_known_test_select->setItem(i,1,new QTableWidgetItem(MODEL_TSET_List[i].TEST_PROCEDURE));
        ui->tableWidget_known_test_select->setItem(i,2,new QTableWidgetItem(MODEL_TSET_List[i].DESCRIPTION));

        ui->tableWidget_known_test_select->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_known_test_select->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_known_test_select->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);

        QTableWidgetItem *checkBox_yes = new QTableWidgetItem();
        checkBox_yes->setCheckState(Qt::Unchecked);
        ui->tableWidget_known_test_select ->setItem(i, 3, checkBox_yes);

        QTableWidgetItem *checkBox_no = new QTableWidgetItem();
        checkBox_no->setCheckState(Qt::Unchecked);
        ui->tableWidget_known_test_select ->setItem(i, 4, checkBox_no);

        QTableWidgetItem *checkBox_skip = new QTableWidgetItem();
        checkBox_skip->setCheckState(Qt::Unchecked);
        ui->tableWidget_known_test_select ->setItem(i, 5, checkBox_skip);

        switch (MODEL_TSET_List[i].TEST_SIGNAL_IS_EXIT_OR_NOT)
        {
        case 0:
            ui->tableWidget_known_test_select->item(i, 4)->setCheckState(Qt::Checked);
            break;
        case 1:
            ui->tableWidget_known_test_select->item(i, 3)->setCheckState(Qt::Checked);
            break;
        case 2:
            ui->tableWidget_known_test_select->item(i, 5)->setCheckState(Qt::Checked);
            break;
        default:
            ui->tableWidget_known_test_select->item(i, 5)->setCheckState(Qt::Checked);
        }
    }

    ui->tableWidget_known_test_select->resizeRowsToContents();

    init_known_test_list_is_not_cell_change = false;
}

void Diagnosis_MainWindow::on_tableWidget_known_test_select_cellChanged(int row, int column)//测试选择操作数据库
{
    if(!init_known_test_list_is_not_cell_change)
    {
        QString cellchanged_test_name = ui->tableWidget_known_test_select->item(row, 0)->text();

        int test_state = 2;
        init_known_test_list_is_not_cell_change = true;
        switch (column) {
        case 3://测试正常
            test_state = 1;
            ui->tableWidget_known_test_select->item(row, 3)->setCheckState(Qt::Checked);
            ui->tableWidget_known_test_select->item(row, 4)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_test_select->item(row, 5)->setCheckState(Qt::Unchecked);
            break;
        case 4://测试异常
            test_state = 0;
            ui->tableWidget_known_test_select->item(row, 3)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_test_select->item(row, 4)->setCheckState(Qt::Checked);
            ui->tableWidget_known_test_select->item(row, 5)->setCheckState(Qt::Unchecked);
            break;
        case 5://测试跳过
            test_state = 2;
            ui->tableWidget_known_test_select->item(row, 3)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_test_select->item(row, 4)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_test_select->item(row, 5)->setCheckState(Qt::Checked);
            break;
        default:
            break;
        }
        init_known_test_list_is_not_cell_change = false;

        if(ui->tableWidget_known_test_select->item(row, column)->checkState() == Qt::Checked)
        {
            sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                                  " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(test_state).arg(cellchanged_test_name).arg(diagnosis_model_name);
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
        }
    }
}

void Diagnosis_MainWindow::on_btn_known_test_searching_clicked()//测试模糊选择
{
    QString fuzzy_name_search = ui->lineEdit_known_test_name_searching->text();
    QString  fuzzy_description_search = ui->lineEdit_known_test_description_searching->text();
    init_test_list(diagnosis_model_name,fuzzy_name_search,fuzzy_description_search);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_toolButton_known_test_all_yes_clicked()//测试正常全选
{
    int row_count = ui->tableWidget_known_test_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_known_test_select->item(i, 0)->text();

        sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                              " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                .arg(1).arg(cellchanged_test_name).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_test_list(diagnosis_model_name,ui->lineEdit_known_test_name_searching->text(),ui->lineEdit_known_test_description_searching->text());//初始化测试信号UI列表
}

void Diagnosis_MainWindow::on_toolButton_known_test_all_no_clicked()//测试异常全选
{
    int row_count = ui->tableWidget_known_test_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_known_test_select->item(i, 0)->text();

        sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                              " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                .arg(0).arg(cellchanged_test_name).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_test_list(diagnosis_model_name,ui->lineEdit_known_test_name_searching->text(),ui->lineEdit_known_test_description_searching->text());//初始化测试信号UI列表
}

void Diagnosis_MainWindow::on_toolButton_known_test_all_skip_clicked()//测试跳过全选
{
    int row_count = ui->tableWidget_known_test_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_known_test_select->item(i, 0)->text();

        sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                              " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                .arg(2).arg(cellchanged_test_name).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_test_list(diagnosis_model_name,ui->lineEdit_known_test_name_searching->text(),ui->lineEdit_known_test_description_searching->text());//初始化测试信号UI列表
}

void Diagnosis_MainWindow::on_toolButton_known_test_select_next_clicked()//测试选择下一步按钮,至征兆选择界面
{
    //跳转到征兆选择界面
    ui->stackedWidget_main->setCurrentIndex(3);
    ui->lineEdit_known_symptom_name_searching->clear();//清空搜索栏
    ui->lineEdit_known_symptom_discription_searching->clear();

    //数据库操作将所有征兆全选跳过
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%3'  AND TEST_TYPE = 2;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    init_symptom_list(diagnosis_model_name,"all","all");//初始化征兆选择列表
}

/////////////////////////////////////////////////////////
///    \brief known_symptom_signal_select_UI          ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::on_toolButton_known_symptom_select_last_clicked()//征兆列表选择上一步按钮,至测试选择界面
{
    //跳转到工具选择界面
    ui->stackedWidget_main->setCurrentIndex(1);
    init_tool_list(diagnosis_model_name,"all");//初始化工具选择列表

//    ui->stackedWidget_main->setCurrentIndex(2);
//    ui->lineEdit_known_test_description_searching->clear();//清空搜索栏
//    ui->lineEdit_known_test_name_searching->clear();
//    init_test_list(diagnosis_model_name,"all","all");//初始化测试信号UI列表
}

void Diagnosis_MainWindow::init_symptom_list(QString model_name,QString fuzzy_name_search,QString fuzzy_description_search)//初始化征兆信号UI列表
{
    init_known_symptom_list_is_not_cell_change = true;

    ui->tableWidget_known_symptom_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_known_symptom_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_known_symptom_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);

    ui->tableWidget_known_symptom_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("征兆名称") << tr("征兆描述")  << tr("征兆结果描述") << tr("征兆存在") << tr("征兆不存在") << tr("跳过");
    ui->tableWidget_known_symptom_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_known_symptom_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setSectionResizeMode(2, QHeaderView::Stretch);

    ui->tableWidget_known_symptom_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_known_symptom_select->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_known_symptom_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);


    //设置表头
    ui->tableWidget_known_symptom_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_known_symptom_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_known_symptom_select->setFocusPolicy(Qt::NoFocus);

    //查找数据信息
    typedef struct{
        QString TEST_NAME;
        QString TEST_PROCEDURE;
        QString DESCRIPTION;
        int TEST_SIGNAL_IS_EXIT_OR_NOT;
    }Str_MODEL_TSET_EXIT;
    QList<Str_MODEL_TSET_EXIT> MODEL_TSET_List;


    if(fuzzy_name_search == "all")
        fuzzy_name_search = "";
    if(fuzzy_description_search == "all")
        fuzzy_description_search = "";
    sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,DESCRIPTION,TEST_SIGNAL_IS_EXIT_OR_NOT "
                          "FROM TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2 AND TEST_NAME LIKE '%%2%' AND TEST_PROCEDURE LIKE '%%3%';")
            .arg(model_name).arg(fuzzy_name_search).arg(fuzzy_description_search);


    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Str_MODEL_TSET_EXIT MODEL_TSET;
        MODEL_TSET.TEST_NAME = qsQuery_TMATE_MDB.value(0).toString();
        MODEL_TSET.TEST_PROCEDURE = qsQuery_TMATE_MDB.value(1).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(MODEL_TSET.TEST_PROCEDURE.startsWith("\n")||MODEL_TSET.TEST_PROCEDURE.startsWith("\r"))
            MODEL_TSET.TEST_PROCEDURE.remove(0,2);
        MODEL_TSET.DESCRIPTION = qsQuery_TMATE_MDB.value(2).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(MODEL_TSET.DESCRIPTION.startsWith("\n")||MODEL_TSET.DESCRIPTION.startsWith("\r"))
            MODEL_TSET.DESCRIPTION.remove(0,2);
        //if(MODEL_TSET.TEST_NAME == "T_S1_QJJG_QJDY_桥接底板")
        //qDebug()<<MODEL_TSET.DESCRIPTION;
        MODEL_TSET.TEST_SIGNAL_IS_EXIT_OR_NOT = qsQuery_TMATE_MDB.value(3).toInt();
        MODEL_TSET_List.append(MODEL_TSET);
    }
    //设置表格的默认的行数
    ui->tableWidget_known_symptom_select->setRowCount(MODEL_TSET_List.size());//设置默认的行数
    ui->tableWidget_known_symptom_select->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<MODEL_TSET_List.size();i++)
    {
        ui->tableWidget_known_symptom_select->setItem(i,0,new QTableWidgetItem(MODEL_TSET_List[i].TEST_NAME));
        ui->tableWidget_known_symptom_select->setItem(i,1,new QTableWidgetItem(MODEL_TSET_List[i].TEST_PROCEDURE));
        ui->tableWidget_known_symptom_select->setItem(i,2,new QTableWidgetItem(MODEL_TSET_List[i].DESCRIPTION));


        ui->tableWidget_known_symptom_select->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_known_symptom_select->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_known_symptom_select->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);

        QTableWidgetItem *checkBox_yes = new QTableWidgetItem();
        checkBox_yes->setCheckState(Qt::Unchecked);
        ui->tableWidget_known_symptom_select ->setItem(i, 3, checkBox_yes);

        QTableWidgetItem *checkBox_no = new QTableWidgetItem();
        checkBox_no->setCheckState(Qt::Unchecked);
        ui->tableWidget_known_symptom_select ->setItem(i, 4, checkBox_no);

        QTableWidgetItem *checkBox_skip = new QTableWidgetItem();
        checkBox_skip->setCheckState(Qt::Unchecked);
        ui->tableWidget_known_symptom_select ->setItem(i, 5, checkBox_skip);

        switch (MODEL_TSET_List[i].TEST_SIGNAL_IS_EXIT_OR_NOT)
        {
        case 0:
            ui->tableWidget_known_symptom_select->item(i, 3)->setCheckState(Qt::Checked);
            break;
        case 1:
            ui->tableWidget_known_symptom_select->item(i, 4)->setCheckState(Qt::Checked);
            break;
        case 2:
            ui->tableWidget_known_symptom_select->item(i, 5)->setCheckState(Qt::Checked);
            break;
        default:
            ui->tableWidget_known_symptom_select->item(i, 5)->setCheckState(Qt::Checked);
        }

    }

    ui->tableWidget_known_symptom_select->resizeRowsToContents();

    init_known_symptom_list_is_not_cell_change = false;
}

void Diagnosis_MainWindow::on_btn_known_symptom_searching_clicked()//征兆模糊搜索
{
    QString fuzzy_name_search = ui->lineEdit_known_symptom_name_searching->text();
    QString fuzzy_description_search = ui->lineEdit_known_symptom_discription_searching->text();

    init_symptom_list(diagnosis_model_name,fuzzy_name_search,fuzzy_description_search);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_tableWidget_known_symptom_select_cellChanged(int row, int column)//征召选择操作数据库
{
    if(!init_known_symptom_list_is_not_cell_change)
    {
        QString cellchanged_test_name = ui->tableWidget_known_symptom_select->item(row, 0)->text();

        init_known_symptom_list_is_not_cell_change = true;
        switch (column) {
        case 3:
            ui->tableWidget_known_symptom_select->item(row, 3)->setCheckState(Qt::Checked);
            ui->tableWidget_known_symptom_select->item(row, 4)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_symptom_select->item(row, 5)->setCheckState(Qt::Unchecked);
            break;
        case 4:
            ui->tableWidget_known_symptom_select->item(row, 3)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_symptom_select->item(row, 4)->setCheckState(Qt::Checked);
            ui->tableWidget_known_symptom_select->item(row, 5)->setCheckState(Qt::Unchecked);
            break;
        case 5:
            ui->tableWidget_known_symptom_select->item(row, 3)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_symptom_select->item(row, 4)->setCheckState(Qt::Unchecked);
            ui->tableWidget_known_symptom_select->item(row, 5)->setCheckState(Qt::Checked);
            break;
        default:
            break;
        }
        init_known_symptom_list_is_not_cell_change = false;

        int test_state = column-3;
        if(ui->tableWidget_known_symptom_select->item(row, column)->checkState() == Qt::Checked)
        {
            sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                                  " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(test_state).arg(cellchanged_test_name).arg(diagnosis_model_name);
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
        }
        //init_symptom_list(diagnosis_model_name,ui->lineEdit_known_symptom_searching->text());//初始化测试信号UI列表
    }
}

void Diagnosis_MainWindow::on_toolButton_known_symptom_select_all_clicked()//征兆存在全选
{
    int row_count = ui->tableWidget_known_symptom_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_known_symptom_select->item(i, 0)->text();

        sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                              " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                .arg(0).arg(cellchanged_test_name).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }

    init_symptom_list(diagnosis_model_name,ui->lineEdit_known_symptom_name_searching->text(),ui->lineEdit_known_symptom_discription_searching->text());//初始化测试信号UI列表
}

void Diagnosis_MainWindow::on_toolButton_not_exit_symptom_select_all_clicked()//征兆不存在全选
{
    int row_count = ui->tableWidget_known_symptom_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_known_symptom_select->item(i, 0)->text();

        sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                              " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                .arg(1).arg(cellchanged_test_name).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_symptom_list(diagnosis_model_name,ui->lineEdit_known_symptom_name_searching->text(),ui->lineEdit_known_symptom_discription_searching->text());//初始化测试信号UI列表
}

void Diagnosis_MainWindow::on_toolButton_known_symptom_all_skip_clicked()//征兆跳过全选
{
    int row_count = ui->tableWidget_known_symptom_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_known_symptom_select->item(i, 0)->text();

        sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE"
                              " TEST_NAME='%2' AND MODEL_NAME = '%3';")
                .arg(2).arg(cellchanged_test_name).arg(diagnosis_model_name);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_symptom_list(diagnosis_model_name,ui->lineEdit_known_symptom_name_searching->text(),ui->lineEdit_known_symptom_discription_searching->text());//初始化测试信号UI列表
}

/***********************************************************************************************************************************/
/*****************************************************相关信息初始化*******************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::on_toolButton_known_symptom_select_next_clicked()//征兆选择下一步按钮，跳至诊断界面
{
    //开启初始化线程
    dlg_delay->setModal(true);
    dlg_delay->show();
    dlg_delay->setWindowTitle("设备推理初始化....");
    connect(&thread_init_Data,SIGNAL(init_finished()),this,SLOT(onthread_Data_finished()));
    thread_init_Data.start();//开启线程
}

void Diagnosis_MainWindow::onthread_Data_finished()//初始化线程结束
{
    //关闭线程
    if (thread_init_Data.isRunning())
    {
        thread_init_Data.stopThread();
        thread_init_Data.wait();
    }
    dlg_delay->CloseWindow();
    //跳转到诊断界面
    ui->stackedWidget_main->setCurrentIndex(4);

    //判断当前D矩阵检测是否结束
    if(Matrix_D.diagnosis_end())
        show_the_diagnosis_result();//显示诊断结果
    else
    {
        //初始化第一个测试界面UI
        QString first_TEST_TID = Matrix_D.select_a_test_from_now_test_data();
        show_now_test_data_to_UI(first_TEST_TID);
    }
}

/***********************************************************************************************************************************/
/*****************************************************诊断模块********************************************************************/
/***********************************************************************************************************************************/
void Diagnosis_MainWindow::show_the_diagnosis_result()//显示诊断结果并记录
{
    //若未隔离故障模块个数为0，则输出系统无故障
    bool system_ok = true;
    int fault_num = 0;
    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
    {
        if(Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module)
        {
            system_ok = false;
            fault_num++;
        }
    }
    if(system_ok)//若系统正常
    {
        ui->stackedWidget_main->setCurrentIndex(9);
        Matrix_D.diagnostic_record.fault_module = "系统正常";
    }
    else
    {
        if(fault_num == 1)
        {
            ui->stackedWidget_main->setCurrentIndex(5);
            //诊断结果——故障模块名称
            QString result_module_text = "  异常模块(路径):  ";
            QString result_module_name = "";//诊断结果——故障模块名称
            QString result_module_TID = "";//诊断结果——故障模块TID
            QString result_module_repair = "解决方案:\r\n";//诊断结果——故障模块修理
            for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
            {
                if(Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module)
                {
                    result_module_name.append(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_NAME);
                    result_module_TID.append(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_TID);
                    result_module_repair.append((Matrix_D.list_LOWEST_MODULE_DATA[i].REPAIR_NOTES));
                    break;
                }
            }
            Matrix_D.diagnostic_record.fault_module = result_module_name;
            result_module_repair.replace(QString("<BR>"), QString("\n"));
            ui->label_Remove_replace_Procedures->setText(result_module_repair.remove("<DIV>").remove("</DIV>").remove("&nbsp").remove(";").remove("；"));

            //显示故障模块路径
            QList<QString>  transitive_telation_name = Matrix_D.select_module_transitive_telation(result_module_TID,diagnosis_model_name);//获取模块传递链
            QString label_test_road = "";
            for(int i=(transitive_telation_name.size()-1);i>0;i--)
            {
                label_test_road.append(transitive_telation_name[i]);
                label_test_road.append("->");
            }
            label_test_road.append(transitive_telation_name[0]);
            result_module_text.append(label_test_road);
            ui->label_result->setText(result_module_text);

            //查找相关多媒体信息并显示
            //查找当前故障模块的多媒体信息并存储到多媒体信息表
            Matrix_D.select_multimedia_of_this_module(diagnosis_model_name,result_module_TID);


            for(int i=0;i<ui->tabWidget_solve_image->count();i++){
                ui->tabWidget_solve_image->setCurrentIndex(i);
                delete ui->tabWidget_solve_image->currentWidget();
            }

            ui->tabWidget_solve_image->clear();
            ui->tabWidget_solve_image->tabBar()->hide();
            ui->pushButton_last_solve_image->hide();
            ui->pushButton_next_solve_image->hide();
            ui->tableWidget_solve_file->hide();
            ui->widget_test_module_image_2->hide();

//            if(ui->tabWidget_solve_image->height()<ui->tabWidget_solve_image->width())
//            {
//                ui->tabWidget_solve_image->setMaximumWidth(ui->tabWidget_solve_image->height());
//                ui->tabWidget_solve_image->setMinimumWidth(ui->tabWidget_solve_image->height());
//            }
//            else
//            {
//                ui->tabWidget_solve_image->setMaximumHeight(ui->tabWidget_solve_image->width());
//                ui->tabWidget_solve_image->setMinimumHeight(ui->tabWidget_solve_image->width());
//            }

            //初始化文件列表区域
            ui->tableWidget_solve_file->clear();
            ui->tableWidget_solve_file->horizontalHeader()->setFixedHeight(40);//设置列高
            ui->tableWidget_solve_file->setSelectionBehavior(QAbstractItemView::SelectRows); //设置选择行为时每次选择一行
            ui->tableWidget_solve_file->setEditTriggers(QAbstractItemView::NoEditTriggers); //设置不可编辑
            ui->tableWidget_solve_file->verticalHeader()->setVisible(false); //隐藏列头
            ui->tableWidget_solve_file->horizontalHeader()->setVisible(false); //隐藏行头
            ui->tableWidget_solve_file->setAlternatingRowColors( true ); //切换颜色
            ui->tableWidget_solve_file->setStyleSheet( "QTableView{alternate-background-color: rgb(141, 163, 215);}" ); //切换颜色
            ui->tableWidget_solve_file->horizontalHeader()->setStretchLastSection(true); //设置充满表宽度
            ui->tableWidget_solve_file->horizontalHeader()->setStyleSheet("QHeaderView::section {background-color:rgb(141, 163, 215);color:black;border:none;}");
            ui->tableWidget_solve_file->setColumnCount(1);
            QStringList header;	header << tr("文件");
            ui->tableWidget_solve_file->setHorizontalHeaderLabels(header);
            ui->tableWidget_solve_file->setRowCount(Matrix_D.MULTIMEDIA_List.size());
            int tableWidget_solve_file_Height = 120;
            if(40*Matrix_D.MULTIMEDIA_List.size()<120)
                tableWidget_solve_file_Height = 40*Matrix_D.MULTIMEDIA_List.size();
            ui->tableWidget_solve_file->setMaximumHeight(tableWidget_solve_file_Height);
            ui->tableWidget_solve_file->setMinimumHeight(tableWidget_solve_file_Height);

            int num_of_jpg = 0;
            for(int i=0;i<Matrix_D.MULTIMEDIA_List.size();i++)
            {
                ui->tableWidget_solve_file->setItem(i,0,new QTableWidgetItem(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME));

                if((Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("jpg")||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("JPG")))||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("png")||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("PNG"))))
                {
                    num_of_jpg++;

                    QWidget* widget = new QWidget(this);
                    QVBoxLayout * layout = new QVBoxLayout(widget);//铺满布局

                    QLabel* pLabel = new QLabel(this);
                    pLabel->setSizePolicy(QSizePolicy::Preferred,QSizePolicy::Preferred);//铺满布局
                    layout->addWidget(pLabel);

                    QLabel* name_Label = new QLabel(this);
                    name_Label->setMaximumHeight(20);
                    name_Label->setMinimumWidth(ui->tabWidget_solve_image->width());
                    name_Label->setMaximumWidth(ui->tabWidget_solve_image->width());
                    name_Label->setStyleSheet("font: 75 10pt '微软雅黑';");
                    name_Label->setAlignment(Qt::AlignHCenter);

                    QString picture_name = Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME;
                    picture_name.remove(".jpg").remove(".JPG").remove(".png").remove(".PNG");
                    name_Label->setText(picture_name);
                    layout->addWidget(name_Label);

                    QPixmap photo;
                    photo.loadFromData(Matrix_D.MULTIMEDIA_List[i].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式自动检测
                    pLabel->setPixmap(photo);
                    pLabel->setScaledContents(true);

                    QString name = QString("%1").arg(i);
                    ui->tabWidget_solve_image->addTab(widget,name);
                }

                ui->tabWidget_solve_image->setCurrentIndex(0);

                if(ui->tabWidget_solve_image->count()>1)
                {
                    ui->pushButton_last_solve_image->show();
                    ui->pushButton_next_solve_image->show();
                }
            }

            if(ui->tableWidget_solve_file->rowCount()>0)
                ui->tableWidget_solve_file->show();
            if(ui->tabWidget_solve_image->count()>0)
                ui->widget_test_module_image_2->show();

        }
        else
        {
            ui->stackedWidget_main->setCurrentIndex(10);
            ui->label_fault_vague_group_number->setText(QString::number(fault_num));

            //设置模糊组列表
            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
            ui->tableWidget_fault_vague_group_list->verticalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格行高随View变化
            ui->tableWidget_fault_vague_group_list->verticalHeader()->setMinimumSectionSize(50);
            ui->tableWidget_fault_vague_group_list->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);


            ui->tableWidget_fault_vague_group_list->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
            //设置表格的默认的列数
            QStringList headerString;
            headerString << tr("选择") << tr("模块名称") << tr("部件号") << tr("故障概率") << tr("显示");
            ui->tableWidget_fault_vague_group_list->setColumnCount(headerString.count());//设置列数
            ui->tableWidget_fault_vague_group_list->setHorizontalHeaderLabels(headerString);//设置列标题

            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);
            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setSectionResizeMode(2, QHeaderView::Stretch);
            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setSectionResizeMode(3, QHeaderView::Stretch);
            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setSectionResizeMode(4, QHeaderView::Stretch);
            ui->tableWidget_fault_vague_group_list->setColumnWidth(0,80);

            ui->tableWidget_fault_vague_group_list->setAlternatingRowColors(true);//使表格颜色交错功能为真

            QString StyleSheet = tableWidgetStyleSheet;
            StyleSheet.remove("QTableWidget::item{padding-top:15px;padding-bottom:15px;}");
            ui->tableWidget_fault_vague_group_list->setStyleSheet(StyleSheet);//设置表格颜色

            ui->tableWidget_fault_vague_group_list->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);
            //设置表头
            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
            ui->tableWidget_fault_vague_group_list->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
            ui->tableWidget_fault_vague_group_list->setFocusPolicy(Qt::NoFocus);

            //设置表格的默认的行数
            ui->tableWidget_fault_vague_group_list->setRowCount(fault_num);//设置默认的行数
            ui->tableWidget_fault_vague_group_list->verticalHeader()->hide();//隐藏行序号

            //设置表格数据
            QList<QString> faule_module_name_List;
            QList<double> faule_module_fault_probability_List;
            QList<QString> faule_module_TID_List;
            for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
            {
                if(Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module)
                {
                    faule_module_name_List.append(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_NAME);
                    faule_module_fault_probability_List.append(Matrix_D.list_LOWEST_MODULE_DATA[i].FAULT_PROBABLITY);
                    faule_module_TID_List.append(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_TID);
                }
            }

            for(int i=0;i<fault_num;i++)
            {
                QTableWidgetItem *checkBox_yes = new QTableWidgetItem();
                checkBox_yes->setCheckState(Qt::Unchecked);
                ui->tableWidget_fault_vague_group_list ->setItem(i,0,checkBox_yes);

                ui->tableWidget_fault_vague_group_list->setItem(i,1,new QTableWidgetItem(faule_module_name_List[i]));

                ui->tableWidget_fault_vague_group_list->setItem(i,3,new QTableWidgetItem(QString::number(faule_module_fault_probability_List[i])));
                ui->tableWidget_fault_vague_group_list->item(i,3)->setTextAlignment(Qt::AlignCenter);

                QWidget *w = new QWidget(this); //创建一个widget
                QHBoxLayout *hLayout = new QHBoxLayout(); //创建布局
                QPushButton *btn = new QPushButton;
                btn->setStyleSheet("QPushButton{background-color:gray;min-width: 90px;min-height: 30px;"
                                   "color: white;border-radius: 10px;border: 2px groove gray;border-style: outset;}"
                                   "QPushButton:hover{background-color:white; color: black;}"
                                   "QPushButton:pressed{background-color:rgb(85, 170, 255);border-style:inset; }");
                btn->setText(tr("显示详情"));
                btn->setToolTip(faule_module_TID_List[i]);
                hLayout->addWidget(btn); //添加
                hLayout->setMargin(0); //设置边缘距离 否则会很难看
                hLayout->setAlignment(btn, Qt::AlignCenter); //居中
                w->setLayout(hLayout); //设置widget的布局
                ui->tableWidget_fault_vague_group_list->setCellWidget(i, 4, w); //将widget放到table中
                connect(btn, SIGNAL(clicked(bool)), this, SLOT(fault_vague_group_list_clicked()));
            }
        }
    }
}

void Diagnosis_MainWindow::on_pushButton_last_solve_image_clicked()
{
    if(ui->tabWidget_solve_image->currentIndex()>0)
        ui->tabWidget_solve_image->setCurrentIndex(ui->tabWidget_solve_image->currentIndex()-1);
}

void Diagnosis_MainWindow::on_pushButton_next_solve_image_clicked()
{
    if(ui->tabWidget_solve_image->currentIndex()<ui->tabWidget_solve_image->count()-1)
        ui->tabWidget_solve_image->setCurrentIndex(ui->tabWidget_solve_image->currentIndex()+1);
}

void Diagnosis_MainWindow::show_now_test_data_to_UI(QString TEST_TID)//依据TEST_TID在诊断界面UI显示相关信息
{
    //获取测试的序号
    int TEST_Number = 0;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(TEST_TID == Matrix_D.list_TEST_DATA[i].TEST_TID)
        {
            TEST_Number = i;
            break;
        }
    }

    //显示文字描述信息
    //显示测试TID
    ui->label_diagnosis_test_TID->setText(TEST_TID);
    //显示测试名称
    QString label_diagnosis_test_word = QString("测试模块:%1").arg(Matrix_D.list_TEST_DATA[TEST_Number].TEST_NAME);
    ui->label_diagnosis_test_word->setText(label_diagnosis_test_word);
    //显示测试过程
    QString label_test_procedure = Matrix_D.list_TEST_DATA[TEST_Number].TEST_PROCEDURE;
    ui->label_test_procedure->setText(label_test_procedure);

    //显示测试路径
    QString test_Connected_module_TID = Matrix_D.list_TEST_DATA[TEST_Number].Connected_module_TID;
    QList<QString>  transitive_telation_name = Matrix_D.select_module_transitive_telation(test_Connected_module_TID,diagnosis_model_name);//获取模块传递链

    QString label_test_road = "";
    if(transitive_telation_name.size()>=2)
    {
        for(int i=(transitive_telation_name.size()-2);i>0;i--)
        {
            label_test_road.append(transitive_telation_name[i]);
            label_test_road.append("->");
        }
        label_test_road.append(transitive_telation_name[0]);
    }
    ui->label_test_road->setText(label_test_road);

    //显示测试描述
    QString label_test_description = Matrix_D.list_TEST_DATA[TEST_Number].DESCRIPTION;
    QStringList list = label_test_description.split("<DIV>");


    QStringList list_revise;

    for(int i=0;i<list.size();i++)
    {
        list_revise.append(list[i].remove("</DIV>").remove("\r").remove("\n"));
    }

    QString result_label_test_description;

    int k=0;
    for(int i=0;i<list.size();i++)
    {
        while((k<list_revise.size())&&(list_revise[k]==""))
            k++;
        if(k<list_revise.size())
        {
            result_label_test_description.append(list_revise[k]);
            result_label_test_description.append("\r\n\r\n");
            k++;
        }
    }
    ui->label_test_description_1->setText(result_label_test_description);

    //查找相关多媒体信息并显示
    //查找当前测试的多媒体信息并存储到多媒体信息表
    Matrix_D.select_multimedia_of_this_test(diagnosis_model_name,TEST_TID);


    for(int i=0;i<ui->tabWidget_test_image->count();i++){
        ui->tabWidget_test_image->setCurrentIndex(i);
        delete ui->tabWidget_test_image->currentWidget();
    }

    ui->tabWidget_test_image->clear();
    ui->tabWidget_test_image->tabBar()->hide();
    ui->tableWidget_test_file->hide();
    ui->widget_test_module_image->hide();
    ui->pushButton_last_test_photo->hide();
    ui->pushButton_next_test_photo->hide();

    //初始化文件列表区域
    ui->tableWidget_test_file->clear();
    ui->tableWidget_test_file->horizontalHeader()->setFixedHeight(40);//设置列高
    ui->tableWidget_test_file->setSelectionBehavior(QAbstractItemView::SelectRows); //设置选择行为时每次选择一行
    ui->tableWidget_test_file->setEditTriggers(QAbstractItemView::NoEditTriggers); //设置不可编辑
    ui->tableWidget_test_file->verticalHeader()->setVisible(false); //隐藏列头
    ui->tableWidget_test_file->horizontalHeader()->setVisible(false); //隐藏行头
    ui->tableWidget_test_file->setAlternatingRowColors( true ); //切换颜色
    ui->tableWidget_test_file->setStyleSheet( "QTableView{alternate-background-color: rgb(141, 163, 215);}" ); //切换颜色
    ui->tableWidget_test_file->horizontalHeader()->setStretchLastSection(true); //设置充满表宽度
    ui->tableWidget_test_file->horizontalHeader()->setStyleSheet("QHeaderView::section {background-color:rgb(141, 163, 215);color:black;border:none;}");
    ui->tableWidget_test_file->setColumnCount(1);
    QStringList header;	header << tr("文件");
    ui->tableWidget_test_file->setHorizontalHeaderLabels(header);
    ui->tableWidget_test_file->setRowCount(Matrix_D.MULTIMEDIA_List.size());
    int tableWidget_test_file_Height = 120;
    if(40*Matrix_D.MULTIMEDIA_List.size()<120)
        tableWidget_test_file_Height = 40*Matrix_D.MULTIMEDIA_List.size();
    ui->tableWidget_test_file->setMaximumHeight(tableWidget_test_file_Height);
    ui->tableWidget_test_file->setMinimumHeight(tableWidget_test_file_Height);

    int num_of_jpg = 0;
    for(int i=0;i<Matrix_D.MULTIMEDIA_List.size();i++)
    {

        ui->tableWidget_test_file->setItem(i,0,new QTableWidgetItem(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME));

        if((Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("jpg")||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("JPG")))||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("png")||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("PNG"))))
        {
            num_of_jpg++;

            QWidget* widget = new QWidget(nullptr);
            QVBoxLayout * layout = new QVBoxLayout(widget);//铺满布局

            QString name = QString("%1").arg(i);
            ui->tabWidget_test_image->addTab(widget,name);

            QLabel* pLabel = new QLabel(widget);
            pLabel->setSizePolicy(QSizePolicy::Preferred,QSizePolicy::Preferred);//铺满布局
            layout->addWidget(pLabel);

            QLabel* name_Label = new QLabel(widget);
            name_Label->setMaximumHeight(20);

            name_Label->setStyleSheet("font: 75 10pt '微软雅黑';");
            name_Label->setAlignment(Qt::AlignHCenter);

            QString picture_name = Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME;
            picture_name.remove(".jpg").remove(".JPG").remove(".png").remove(".PNG");
            name_Label->setText(picture_name);
            layout->addWidget(name_Label);

            QPixmap photo;
            photo.loadFromData(Matrix_D.MULTIMEDIA_List[i].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式自动检测

            pLabel->setPixmap(photo);
            pLabel->setScaledContents(true);
        }
        ui->tabWidget_test_image->setCurrentIndex(0);
        if(ui->tabWidget_test_image->count()>1)
        {
            ui->pushButton_last_test_photo->show();
            ui->pushButton_next_test_photo->show();
        }
    }

    if(ui->tableWidget_test_file->rowCount()>0)
        ui->tableWidget_test_file->show();
    if(ui->tabWidget_test_image->count()>0)
        ui->widget_test_module_image->show();
}

void Diagnosis_MainWindow::on_pushButton_last_test_photo_clicked()
{
    if(ui->tabWidget_test_image->currentIndex()>0)
        ui->tabWidget_test_image->setCurrentIndex(ui->tabWidget_test_image->currentIndex()-1);
}

void Diagnosis_MainWindow::on_pushButton_next_test_photo_clicked()
{
    if(ui->tabWidget_test_image->currentIndex()<ui->tabWidget_test_image->count()-1)
        ui->tabWidget_test_image->setCurrentIndex(ui->tabWidget_test_image->currentIndex()+1);
}

void Diagnosis_MainWindow::on_tableWidget_test_file_doubleClicked(const QModelIndex &index)//诊断界面双击文件列表
{
    Q_UNUSED(index)
    QString MEDIA_file_NAME = Matrix_D.MULTIMEDIA_List[ui->tableWidget_test_file->currentRow()].MEDIA_NAME;
    // QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),MEDIA_file_NAME);

    QPixmap photo;
    photo.loadFromData(Matrix_D.MULTIMEDIA_List[ui->tableWidget_test_file->currentRow()].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式自动检测

    picture_Label->setPixmap(photo);
    picture_Label->setScaledContents(true);
    dlg_showPicture->setWindowTitle(Matrix_D.MULTIMEDIA_List[ui->tableWidget_test_file->currentRow()].MEDIA_NAME);
    //dlg_showPicture->setWindowFlags( Qt::MSWindowsFixedSizeDialogHint);

    dlg_showPicture->show();
    dlg_showPicture->move(screenWidth- dlg_showPicture->width(),0);

}

void Diagnosis_MainWindow::on_toolButton_diagnosis_normal_clicked()//测试正常
{

    Matrix_D.diagnostic_record.list_Diagnosis_test_record[Matrix_D.diagnostic_record.list_Diagnosis_test_record.size()-1].yes_or_no = "测试正常";

    //获取当前测试TID
    QString this_TEST_TID = ui->label_diagnosis_test_TID->text();
    //获取当前测试在测试列表中的序号
    int this_TEST_number_in_test_list = 0;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(this_TEST_TID == Matrix_D.list_TEST_DATA[i].TEST_TID)
        {
            this_TEST_number_in_test_list = i;
            break;
        }
    }
    //删除测试行对应D矩阵值为1的列
    for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();j++)
    {
        if(Matrix_D.Matrix_D_value[this_TEST_number_in_test_list][j])
            Matrix_D.delete_one_module_Column(j);//删除D矩阵第Num列
    }
    //删除该测试行
    Matrix_D.delete_one_test_row(this_TEST_number_in_test_list);//删除D矩阵第Num行

    if(!Matrix_D.diagnosis_end())//判断当前D矩阵检测是否结束,若未结束执行下述操作
    {
        //更新诊断界面UI
        QString next_TEST_TID = Matrix_D.select_a_test_from_now_test_data();
        show_now_test_data_to_UI(next_TEST_TID);
    }
    else show_the_diagnosis_result();//显示诊断结果
}

void Diagnosis_MainWindow::on_toolButton_diagnosis_abnormal_clicked()//测试异常
{
    Matrix_D.diagnostic_record.list_Diagnosis_test_record[Matrix_D.diagnostic_record.list_Diagnosis_test_record.size()-1].yes_or_no = "测试异常";
    //获取当前测试TID
    QString this_TEST_TID = ui->label_diagnosis_test_TID->text();
    //获取当前测试在测试列表中的序号
    int this_TEST_number_in_test_list = 0;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(this_TEST_TID == Matrix_D.list_TEST_DATA[i].TEST_TID)
        {
            this_TEST_number_in_test_list = i;
            break;
        }
    }
    //删除测试行对应D矩阵值为0的列
    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
    {
        if(!Matrix_D.Matrix_D_value[this_TEST_number_in_test_list][i])
            Matrix_D.delete_one_module_Column(i);//删除D矩阵第Num列
    }
    //删除该测试行
    Matrix_D.delete_one_test_row(this_TEST_number_in_test_list);//删除D矩阵第Num行

    if(!Matrix_D.diagnosis_end())//判断当前D矩阵检测是否结束
    {
        //更新诊断界面UI
        QString next_TEST = Matrix_D.select_a_test_from_now_test_data();
        show_now_test_data_to_UI(next_TEST);
    }
    else show_the_diagnosis_result();//显示诊断结果
}

void Diagnosis_MainWindow::on_toolButton_skip_this_test_clicked()//跳过该测试
{
    Matrix_D.diagnostic_record.list_Diagnosis_test_record[Matrix_D.diagnostic_record.list_Diagnosis_test_record.size()-1].yes_or_no = "测试跳过";
    //获取当前测试TID
    QString this_TEST_TID = ui->label_diagnosis_test_TID->text();
    //获取当前测试在测试列表中的序号
    int this_TEST_number_in_test_list = 0;
    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(this_TEST_TID == Matrix_D.list_TEST_DATA[i].TEST_TID)
        {
            this_TEST_number_in_test_list = i;
            break;
        }
    }
    //删除该测试行
    Matrix_D.delete_one_test_row(this_TEST_number_in_test_list);//删除D矩阵第Num行,同时删除测试集信息

    if(!Matrix_D.diagnosis_end())//判断当前D矩阵检测是否结束
    {
        //更新诊断界面UI
        QString next_TEST = Matrix_D.select_a_test_from_now_test_data();
        show_now_test_data_to_UI(next_TEST);
    }
    else show_the_diagnosis_result();//显示诊断结果
}

void Diagnosis_MainWindow::on_toolButton_slelct_other_test_clicked()//选择其他测试
{

    Matrix_D.diagnostic_record.list_Diagnosis_test_record[Matrix_D.diagnostic_record.list_Diagnosis_test_record.size()-1].yes_or_no = "测试另选";

    QList<QString> list_test;

    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
    {
        if(Matrix_D.list_TEST_DATA[i].sign_test)
            list_test.append(Matrix_D.list_TEST_DATA[i].TEST_NAME);
    }

    Dialog_select_another_test *dlg=new Dialog_select_another_test(this,&list_test);
    dlg->showNormal();
    dlg->setWindowTitle("设备故障诊断系统");
    dlg->setModal(true);

    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        QString test_name = dlg->get_test_name();

        Matrix_D.one_test_cord.Diagnosis_test_name = test_name;
        Matrix_D.one_test_cord.recommend_or_self_selected = "自选测试";
        Matrix_D.one_test_cord.yes_or_no = "测试正常";
        Matrix_D.diagnostic_record.list_Diagnosis_test_record.append(Matrix_D.one_test_cord);

        QString test_TID;
        for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
        {
            if(Matrix_D.list_TEST_DATA[i].sign_test)
            {
                if(test_name == Matrix_D.list_TEST_DATA[i].TEST_NAME)
                    test_TID = Matrix_D.list_TEST_DATA[i].TEST_TID;
            }
        }
        //更新诊断界面UI
        show_now_test_data_to_UI(test_TID);
    }
    delete dlg; //删除对话框
}

/***********************************************************************************************************************************/
/*****************************************************诊断结果模块********************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::fault_vague_group_list_clicked()//诊断模糊组查看详情
{
    ui->stackedWidget_main->setCurrentIndex(11);
    QPushButton *senderObj=qobject_cast<QPushButton*>(sender());
    if(senderObj == nullptr)
        return;
    QString TID = senderObj->toolTip();

    //诊断结果——故障模块名称
    QString result_module_text = "  异常模块(路径):  ";
    QString result_module_name = "";//诊断结果——故障模块名称
    QString result_module_TID = "";//诊断结果——故障模块TID
    QString Remove_replace_Procedures = "解决方案:\r\n";//诊断结果——故障模块修理

    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
    {
        if(Matrix_D.list_LOWEST_MODULE_DATA[i].sign_module)
        {
            if(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_TID == TID)
            {
                result_module_name.append(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_NAME);
                result_module_TID.append(Matrix_D.list_LOWEST_MODULE_DATA[i].MODULE_TID);
                Remove_replace_Procedures.append((Matrix_D.list_LOWEST_MODULE_DATA[i].REPAIR_NOTES).remove("</DIV>").remove("<DIV>").remove("&nbsp").remove(";").remove("；"));
                break;
            }
        }
    }
    Remove_replace_Procedures.replace(QString("<BR>"), QString("\n"));
    ui->label_Remove_replace_Procedures_2->setText(Remove_replace_Procedures);


    //显示故障模块路径
    QList<QString>  transitive_telation_name = Matrix_D.select_module_transitive_telation(result_module_TID,diagnosis_model_name);//获取模块传递链
    QString label_test_road = "";
    for(int i=(transitive_telation_name.size()-1);i>0;i--)
    {
        label_test_road.append(transitive_telation_name[i]);
        label_test_road.append("->");
    }
    label_test_road.append(transitive_telation_name[0]);
    result_module_text.append(label_test_road);
    ui->label_result_more_fault_details->setText(result_module_text);

    //查找相关多媒体信息并显示
    //查找当前故障模块的多媒体信息并存储到多媒体信息表
    Matrix_D.select_multimedia_of_this_module(diagnosis_model_name,result_module_TID);

    for(int i=0;i<ui->tabWidget_more_fault_details_image->count();i++){
        ui->tabWidget_more_fault_details_image->setCurrentIndex(i);
        delete ui->tabWidget_more_fault_details_image->currentWidget();
    }

    ui->tabWidget_more_fault_details_image->clear();
    ui->tabWidget_more_fault_details_image->tabBar()->hide();
    ui->widget_test_module_image_3->hide();
    ui->pushButton_last_more_fault_details_image->hide();
    ui->pushButton_next_more_fault_details_image->hide();

//    if(ui->tabWidget_more_fault_details_image->height()<ui->tabWidget_more_fault_details_image->width())
//    {
//        ui->tabWidget_more_fault_details_image->setMaximumWidth(ui->tabWidget_more_fault_details_image->height());
//        ui->tabWidget_more_fault_details_image->setMinimumWidth(ui->tabWidget_more_fault_details_image->height());
//    }
//    else
//    {
//        ui->tabWidget_more_fault_details_image->setMaximumHeight(ui->tabWidget_more_fault_details_image->width());
//        ui->tabWidget_more_fault_details_image->setMinimumHeight(ui->tabWidget_more_fault_details_image->width());
//    }

    //初始化文件列表区域
    ui->tableWidget_result_more_fault_details_file->clear();
    ui->tableWidget_result_more_fault_details_file->horizontalHeader()->setFixedHeight(40);//设置列高
    ui->tableWidget_result_more_fault_details_file->setSelectionBehavior(QAbstractItemView::SelectRows); //设置选择行为时每次选择一行
    ui->tableWidget_result_more_fault_details_file->setEditTriggers(QAbstractItemView::NoEditTriggers); //设置不可编辑
    ui->tableWidget_result_more_fault_details_file->verticalHeader()->setVisible(false); //隐藏列头
    ui->tableWidget_result_more_fault_details_file->horizontalHeader()->setVisible(false); //隐藏行头
    ui->tableWidget_result_more_fault_details_file->setAlternatingRowColors( true ); //切换颜色
    ui->tableWidget_result_more_fault_details_file->setStyleSheet( "QTableView{alternate-background-color: rgb(141, 163, 215);}" ); //切换颜色
    ui->tableWidget_result_more_fault_details_file->horizontalHeader()->setStretchLastSection(true); //设置充满表宽度
    ui->tableWidget_result_more_fault_details_file->horizontalHeader()->setStyleSheet("QHeaderView::section {background-color:rgb(141, 163, 215);color:black;border:none;}");
    ui->tableWidget_result_more_fault_details_file->setColumnCount(1);
    QStringList header;	header << tr("文件");
    ui->tableWidget_result_more_fault_details_file->setHorizontalHeaderLabels(header);
    ui->tableWidget_result_more_fault_details_file->setRowCount(Matrix_D.MULTIMEDIA_List.size());
    int tableWidget_solve_file_Height = 120;
    if(40*Matrix_D.MULTIMEDIA_List.size()<120)
        tableWidget_solve_file_Height = 40*Matrix_D.MULTIMEDIA_List.size();
    ui->tableWidget_result_more_fault_details_file->setMaximumHeight(tableWidget_solve_file_Height);
    ui->tableWidget_result_more_fault_details_file->setMinimumHeight(tableWidget_solve_file_Height);

    int num_of_jpg = 0;
    for(int i=0;i<Matrix_D.MULTIMEDIA_List.size();i++)
    {
        ui->tableWidget_result_more_fault_details_file->setItem(i,0,new QTableWidgetItem(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME));

        if((Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("jpg")||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("JPG")))||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("png")||(Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME.contains("PNG"))))
        {
            num_of_jpg++;

            QWidget* widget = new QWidget(this);
            QVBoxLayout * layout = new QVBoxLayout(widget);//铺满布局

            QLabel* pLabel = new QLabel(this);
            pLabel->setSizePolicy(QSizePolicy::Preferred,QSizePolicy::Preferred);//铺满布局
            layout->addWidget(pLabel);

            QLabel* name_Label = new QLabel(this);
            name_Label->setMaximumHeight(20);
            name_Label->setMinimumWidth(ui->tabWidget_more_fault_details_image->width());
            name_Label->setMaximumWidth(ui->tabWidget_more_fault_details_image->width());
            name_Label->setStyleSheet("font: 75 10pt '微软雅黑';");
            name_Label->setAlignment(Qt::AlignHCenter);

            QString picture_name = Matrix_D.MULTIMEDIA_List[i].MEDIA_NAME;
            picture_name.remove(".jpg").remove(".JPG").remove(".png").remove(".PNG");
            name_Label->setText(picture_name);
            layout->addWidget(name_Label);

            QPixmap photo;
            photo.loadFromData(Matrix_D.MULTIMEDIA_List[i].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式自动检测
            pLabel->setPixmap(photo);
            pLabel->setScaledContents(true);

            QString name = QString("%1").arg(i);
            ui->tabWidget_more_fault_details_image->addTab(widget,name);
        }

        ui->tabWidget_more_fault_details_image->setCurrentIndex(0);
        if(ui->tabWidget_more_fault_details_image->count()>1)
        {
            ui->pushButton_last_more_fault_details_image->show();
            ui->pushButton_next_more_fault_details_image->show();
        }
    }

    if(ui->tabWidget_more_fault_details_image->count()>0)
        ui->widget_test_module_image_3->show();
}

void Diagnosis_MainWindow::on_pushButton_last_more_fault_details_image_clicked()
{
    if(ui->tabWidget_more_fault_details_image->currentIndex()>0)
        ui->tabWidget_more_fault_details_image->setCurrentIndex(ui->tabWidget_more_fault_details_image->currentIndex()-1);
}

void Diagnosis_MainWindow::on_pushButton_next_more_fault_details_image_clicked()
{
    if(ui->tabWidget_more_fault_details_image->currentIndex()<ui->tabWidget_more_fault_details_image->count()-1)
        ui->tabWidget_more_fault_details_image->setCurrentIndex(ui->tabWidget_more_fault_details_image->currentIndex()+1);
}

void Diagnosis_MainWindow::on_toolButton_more_fault_details_return_clicked()//模糊组详情界面返回
{
    ui->stackedWidget_main->setCurrentIndex(10);
}

void Diagnosis_MainWindow::on_toolButton_resule_next_clicked()//诊断结果下一步，显示诊断反馈界面
{
    Matrix_D.diagnostic_record.equipment_name = diagnosis_model_name;
    Matrix_D.diagnostic_record.user_name =LoginAccount.User_department;
    Matrix_D.diagnostic_record.maintain_company =LoginAccount.User_department;
    Matrix_D.diagnostic_record.if_solved_or_not = true;
    Matrix_D.diagnostic_record.finish_time =  QDateTime::currentDateTime();//诊断结束时间

    ui->stackedWidget_main->setCurrentIndex(6);
    ui->label_start_time->setText(Matrix_D.diagnostic_record.start_time.toString("yyyy.MM.dd hh:mm:ss"));
    ui->label_finish_time->setText(Matrix_D.diagnostic_record.finish_time.toString("yyyy.MM.dd hh:mm:ss"));
    ui->label_Diagnosis_Date->setText(Matrix_D.diagnostic_record.Diagnosis_Date.toString("yyyy.MM.dd"));
    ui->label_equipment_name->setText(Matrix_D.diagnostic_record.equipment_name);
    ui->label_user_name->setText(Matrix_D.diagnostic_record.user_name);
    ui->label_user_maintain_company->setText(Matrix_D.diagnostic_record.maintain_company);
    ui->radioButton_problem_is_solved->setChecked(Matrix_D.diagnostic_record.if_solved_or_not);
}

void Diagnosis_MainWindow::on_toolButton_resule_OK_next_clicked()//诊断结果下一步，显示诊断反馈界面
{
    Matrix_D.diagnostic_record.equipment_name = diagnosis_model_name;

    Matrix_D.diagnostic_record.user_name =LoginAccount.Operating_user;
    Matrix_D.diagnostic_record.maintain_company = LoginAccount.User_department;
    Matrix_D.diagnostic_record.if_solved_or_not = true;
    Matrix_D.diagnostic_record.finish_time =  QDateTime::currentDateTime();//诊断结束时间

    ui->stackedWidget_main->setCurrentIndex(6);
    ui->label_start_time->setText(Matrix_D.diagnostic_record.start_time.toString("yyyy.MM.dd hh:mm:ss"));
    ui->label_finish_time->setText(Matrix_D.diagnostic_record.finish_time.toString("yyyy.MM.dd hh:mm:ss"));
    ui->label_Diagnosis_Date->setText(Matrix_D.diagnostic_record.Diagnosis_Date.toString("yyyy.MM.dd"));
    ui->label_equipment_name->setText(Matrix_D.diagnostic_record.equipment_name);
    ui->label_user_name->setText(Matrix_D.diagnostic_record.user_name);
    ui->label_user_maintain_company->setText(Matrix_D.diagnostic_record.maintain_company);
    ui->radioButton_problem_is_solved->setChecked(Matrix_D.diagnostic_record.if_solved_or_not);
}

void Diagnosis_MainWindow::on_toolButton_all_result_next_clicked()//诊断结果下一步，显示诊断反馈界面
{
    Matrix_D.diagnostic_record.equipment_name = diagnosis_model_name;
    Matrix_D.diagnostic_record.user_name = LoginAccount.Operating_user;
    Matrix_D.diagnostic_record.maintain_company = LoginAccount.User_department;
    Matrix_D.diagnostic_record.if_solved_or_not = true;
    Matrix_D.diagnostic_record.finish_time =  QDateTime::currentDateTime();//诊断结束时间

    Matrix_D.diagnostic_record.fault_module.clear();
    for(int i=0;i<ui->tableWidget_fault_vague_group_list->rowCount();i++)
    {
        if(ui->tableWidget_fault_vague_group_list->item(i,0)->checkState())
        {
            Matrix_D.diagnostic_record.fault_module.append(ui->tableWidget_fault_vague_group_list->item(i,1)->text());
            Matrix_D.diagnostic_record.fault_module.append(";");
        }
    }

    if(Matrix_D.diagnostic_record.fault_module!="")
        Matrix_D.diagnostic_record.fault_module.remove(Matrix_D.diagnostic_record.fault_module.size()-1,1);

    ui->stackedWidget_main->setCurrentIndex(6);
    ui->label_start_time->setText(Matrix_D.diagnostic_record.start_time.toString("yyyy.MM.dd hh:mm:ss"));
    ui->label_finish_time->setText(Matrix_D.diagnostic_record.finish_time.toString("yyyy.MM.dd hh:mm:ss"));
    ui->label_Diagnosis_Date->setText(Matrix_D.diagnostic_record.Diagnosis_Date.toString("yyyy.MM.dd"));
    ui->label_equipment_name->setText(Matrix_D.diagnostic_record.equipment_name);
    ui->label_user_name->setText(Matrix_D.diagnostic_record.user_name);
    ui->label_user_maintain_company->setText(Matrix_D.diagnostic_record.maintain_company);
    ui->radioButton_problem_is_solved->setChecked(Matrix_D.diagnostic_record.if_solved_or_not);
}

void Diagnosis_MainWindow::on_tableWidget_result_more_fault_details_file_doubleClicked(const QModelIndex &index)//详情查看界面双击文件
{
    Q_UNUSED(index)
    QString MEDIA_file_NAME = Matrix_D.MULTIMEDIA_List[ui->tableWidget_result_more_fault_details_file->currentRow()].MEDIA_NAME;
    //QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),MEDIA_file_NAME);
    QPixmap photo;
    photo.loadFromData(Matrix_D.MULTIMEDIA_List[ui->tableWidget_result_more_fault_details_file->currentRow()].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式自动检测
    picture_Label->setPixmap(photo);
    picture_Label->setScaledContents(true);
    dlg_showPicture->setWindowTitle(Matrix_D.MULTIMEDIA_List[ui->tableWidget_result_more_fault_details_file->currentRow()].MEDIA_NAME);
    dlg_showPicture->showMaximized();
}

void Diagnosis_MainWindow::on_tableWidget_solve_file_doubleClicked(const QModelIndex &index)//仅有一个故障模块文件双击
{
    Q_UNUSED(index)
    QString MEDIA_file_NAME = Matrix_D.MULTIMEDIA_List[ui->tableWidget_solve_file->currentRow()].MEDIA_NAME;
    //    QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),MEDIA_file_NAME);
    QPixmap photo;
    photo.loadFromData(Matrix_D.MULTIMEDIA_List[ui->tableWidget_solve_file->currentRow()].IMAGE_DATA); //从数据库中读出图片为二进制数据，图片格式自动检测

    picture_Label->setPixmap(photo);
    picture_Label->setScaledContents(true);
    dlg_showPicture->setWindowTitle(Matrix_D.MULTIMEDIA_List[ui->tableWidget_solve_file->currentRow()].MEDIA_NAME);
    dlg_showPicture->showMaximized();
}

/***********************************************************************************************************************************/
/*****************************************************记录提交模块********************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::on_toolButton_information_feedback_return_clicked()//记录提交界面点击返回按钮回到主界面
{
    ui->stackedWidget_main->setCurrentIndex(0);
    init_model_list();//初始化模型列表
}

void Diagnosis_MainWindow::on_radioButton_problem_is_solved_clicked(bool checked)//故障已解决选中
{
    Matrix_D.diagnostic_record.if_solved_or_not = checked;
}

void Diagnosis_MainWindow::on_radioButton_problem_is_not_solved_clicked(bool checked)//故障未解决选中
{
    Matrix_D.diagnostic_record.if_solved_or_not = (!checked);
}

void Diagnosis_MainWindow::on_toolButton_information_feedback_submit_clicked()//记录提交界面点击提交记录
{
    //qDebug()<<Matrix_D.diagnostic_record.advance_omen_test;
    Matrix_D.diagnostic_record.boat_number = ui->lineEdit_boat_number->text();
    Matrix_D.diagnostic_record.feedback_text = ui->QTextEdit_information_feedback_text->toPlainText();

    //生成唯一ID
    Matrix_D.diagnostic_record.DIAGNOSTIC_ID = Matrix_D.diagnostic_record.start_time.toString("yyyy-MM-dd hh:mm:ss").remove("-").remove(":").remove(" ");

    //向记录总表添加信息
    sql_prepare = QString("INSERT INTO DIAGNOSTIC_RECORD_LIST (DIAGNOSTIC_ID,start_time,finish_time,"
                          "Diagnosis_Date,feedback_text,user_name,maintain_company,equipment_name,boat_number,"
                          "if_solved_or_not,fault_phenomenon,fault_module,advance_omen_test)"
                          "VALUES ('%1','%2','%3','%4','%5','%6','%7','%8','%9','%10','%11','%12','%13');")
            .arg(Matrix_D.diagnostic_record.DIAGNOSTIC_ID)
            .arg(Matrix_D.diagnostic_record.start_time.toString("yyyy-MM-dd hh:mm:ss"))
            .arg(Matrix_D.diagnostic_record.finish_time.toString("yyyy-MM-dd hh:mm:ss"))
            .arg(Matrix_D.diagnostic_record.Diagnosis_Date.toString("yyyy-MM-dd"))
            .arg(Matrix_D.diagnostic_record.feedback_text)
            .arg(Matrix_D.diagnostic_record.user_name)
            .arg(Matrix_D.diagnostic_record.maintain_company)
            .arg(Matrix_D.diagnostic_record.equipment_name)
            .arg(Matrix_D.diagnostic_record.boat_number)
            .arg(Matrix_D.diagnostic_record.if_solved_or_not)
            .arg(Matrix_D.diagnostic_record.fault_phenomenon)
            .arg(Matrix_D.diagnostic_record.fault_module)
            .arg(Matrix_D.diagnostic_record.advance_omen_test);

    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    //向诊断过程表添加信息
    for(int i=0;i<Matrix_D.diagnostic_record.list_Diagnosis_test_record.size();i++)
    {
        sql_prepare = QString("INSERT INTO DIAGNOSTIC_TEST_PROCESS_RECORD (TEST_ORDER_ID,DIAGNOSTIC_ID,Diagnosis_test_name,"
                              "recommend_or_self_selected,yes_or_no)"
                              "VALUES ('%1','%2','%3','%4','%5');")
                .arg(i+1).arg(Matrix_D.diagnostic_record.DIAGNOSTIC_ID)
                .arg(Matrix_D.diagnostic_record.list_Diagnosis_test_record[i].Diagnosis_test_name)
                .arg(Matrix_D.diagnostic_record.list_Diagnosis_test_record[i].recommend_or_self_selected)
                .arg(Matrix_D.diagnostic_record.list_Diagnosis_test_record[i].yes_or_no);

        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    //向工具表添加信息
    for(int i=0;i<Matrix_D.diagnostic_record.list_tool.size();i++)
    {
        sql_prepare = QString("INSERT INTO DIAGNOSTIC_TOOL_RECORD (DIAGNOSTIC_ID,TOOL)"
                              "VALUES ('%1','%2');")
                .arg(Matrix_D.diagnostic_record.DIAGNOSTIC_ID)
                .arg(Matrix_D.diagnostic_record.list_tool[i]);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }

    QMessageBox messageBox(QMessageBox::NoIcon,
                           "Message", "诊断记录已保存",
                           QMessageBox::Yes); ;
    int result=messageBox.exec();
    switch (result)
    {
    case QMessageBox::Yes:
        ui->stackedWidget_main->setCurrentIndex(0);
        init_model_list();//初始化模型列表
        break;
    default:
        ui->stackedWidget_main->setCurrentIndex(0);
        init_model_list();//初始化模型列表
        break;
    }
}

/***********************************************************************************************************************************/
/*****************************************************记录查询模块********************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::on_checkBox_hide_unresolved_records_clicked(bool checked)//是否隐藏未解决记录
{
    hide_unresolved_records = checked;//是否隐藏未解决记录
    init_diagnosis_record_query_list();
}

void Diagnosis_MainWindow::on_checkBox_hide_solved_records_clicked(bool checked)//是否隐藏解决记录
{
    hide_solved_records = checked;//是否隐藏已解决记录
    init_diagnosis_record_query_list();
}

void Diagnosis_MainWindow::init_diagnosis_record_query_list()//初始化诊断记录查询列表
{
    init_Currently_displayed_diagnostic_record_is_not_cell_change = true;
    //ui->tableWidget_diagnosis_record_table->horizontalHeader()->setDefaultSectionSize(50);//设置默认行高
    ui->tableWidget_diagnosis_record_table->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_diagnosis_record_table->verticalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格行高随View变化
    ui->tableWidget_diagnosis_record_table->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_diagnosis_record_table->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);

    ui->tableWidget_diagnosis_record_table->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("序号") << tr("故障现象") << tr("检修日期") << tr("维修用户") << tr("舰艇舷号") << tr("模型名称") << tr("是否解决") << tr("故障模块") <<("所属分机")  << tr("记录操作")<< tr("录入/自动");
    ui->tableWidget_diagnosis_record_table->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_diagnosis_record_table->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);
    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setSectionResizeMode(5, QHeaderView::Stretch);
    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setSectionResizeMode(7, QHeaderView::Stretch);
    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setSectionResizeMode(8, QHeaderView::Stretch);

    ui->tableWidget_diagnosis_record_table->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_diagnosis_record_table->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_diagnosis_record_table->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);

    //设置表头
    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_diagnosis_record_table->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_diagnosis_record_table->setFocusPolicy(Qt::NoFocus);

    QString query_user_name = ui->lineEdit_record_query_user_name->text();
    QString query_boat_number = ui->lineEdit_record_query_boat_number->text();
    QString query_module_name = ui->lineEdit_record_query_module_name->text();
    QString query_fault_phenomenon = ui->lineEdit_record_query_fault_phenomenon->text();
    QString query_model_name = ui->lineEdit_record_query_model_name->text();
    QString query_start_time = ui->dateTimeEdit_record_query_start_time->dateTime().toString("yyyy-MM-dd hh:mm:ss");
    QString query_finish_time = ui->dateTimeEdit_query_finish_time->dateTime().toString("yyyy-MM-dd hh:mm:ss");


    if(hide_unresolved_records&&hide_solved_records)//全部隐藏
    {
        sql_prepare = QString("");
    }
    if((!hide_unresolved_records)&&hide_solved_records)//隐藏已解决
    {
        sql_prepare = QString("SELECT *FROM DIAGNOSTIC_RECORD_LIST WHERE start_time >= #%1# AND start_time <= #%2# "
                              "AND user_name like '%%3%' AND boat_number like '%%4%' "
                              "AND fault_module like '%%5%' AND equipment_name like '%%6%' "
                              "AND fault_phenomenon like '%%7%' AND if_solved_or_not = %8;")
                .arg(query_start_time).arg(query_finish_time).arg(query_user_name)
                .arg(query_boat_number).arg(query_module_name).arg(query_model_name)
                .arg(query_fault_phenomenon).arg(false);
    }
    if(hide_unresolved_records&&(!hide_solved_records))//隐藏未解决
    {
        sql_prepare = QString("SELECT *FROM DIAGNOSTIC_RECORD_LIST WHERE start_time >= #%1# AND start_time <= #%2# "
                              "AND user_name like '%%3%' AND boat_number like '%%4%' "
                              "AND fault_module like '%%5%' AND equipment_name like '%%6%' "
                              "AND fault_phenomenon like '%%7%' AND if_solved_or_not = %8;")
                .arg(query_start_time).arg(query_finish_time).arg(query_user_name)
                .arg(query_boat_number).arg(query_module_name).arg(query_model_name)
                .arg(query_fault_phenomenon).arg(true);
    }
    if((!hide_unresolved_records)&&(!hide_solved_records))//不隐藏
    {
        sql_prepare = QString("SELECT *FROM DIAGNOSTIC_RECORD_LIST WHERE start_time >= #%1# AND start_time <= #%2# "
                              "AND user_name like '%%3%' AND boat_number like '%%4%' "
                              "AND fault_module like '%%5%' AND equipment_name like '%%6%' "
                              "AND fault_phenomenon like '%%7%';")
                .arg(query_start_time).arg(query_finish_time).arg(query_user_name)
                .arg(query_boat_number).arg(query_module_name).arg(query_model_name)
                .arg(query_fault_phenomenon);
    }

    Currently_displayed_diagnostic_record_list.clear();
    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        str_Currently_displayed_diagnostic_record  one_diagnostic_record;
        one_diagnostic_record.DIAGNOSTIC_ID =  qsQuery_TMATE_MDB.value(0).toString();
        one_diagnostic_record.start_time =  qsQuery_TMATE_MDB.value(1).toDateTime();
        one_diagnostic_record.finish_time =  qsQuery_TMATE_MDB.value(2).toDateTime();
        one_diagnostic_record.Diagnosis_Date =  qsQuery_TMATE_MDB.value(3).toDate();
        one_diagnostic_record.feedback_text =  qsQuery_TMATE_MDB.value(4).toString();
        one_diagnostic_record.user_name =  qsQuery_TMATE_MDB.value(5).toString();
        one_diagnostic_record.maintain_company =  qsQuery_TMATE_MDB.value(6).toString();
        one_diagnostic_record.equipment_name =  qsQuery_TMATE_MDB.value(7).toString();
        one_diagnostic_record.boat_number =  qsQuery_TMATE_MDB.value(8).toString();
        one_diagnostic_record.if_solved_or_not =  qsQuery_TMATE_MDB.value(9).toBool();
        one_diagnostic_record.fault_phenomenon =  qsQuery_TMATE_MDB.value(10).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(one_diagnostic_record.fault_phenomenon.startsWith("\n")||one_diagnostic_record.fault_phenomenon.startsWith("\r"))
            one_diagnostic_record.fault_phenomenon.remove(0,2);
        one_diagnostic_record.fault_module =  qsQuery_TMATE_MDB.value(11).toString();
        one_diagnostic_record.Is_artificial_cord = qsQuery_TMATE_MDB.value(13).toBool();
        Currently_displayed_diagnostic_record_list.append(one_diagnostic_record);
    }

    //查找各故障模块所属分机
    QList<QString> ListFaultModuleBelong;
    for(int i=0;i<Currently_displayed_diagnostic_record_list.size();i++)
    {
        QStringList FaultModuleList = Currently_displayed_diagnostic_record_list[i].fault_module.split(";", QString::SkipEmptyParts);
        QString FaultModuleBelong;
        for(int j=0;j<FaultModuleList.size();j++)
            FaultModuleBelong.append(ModuleBelongsSubSystem(Currently_displayed_diagnostic_record_list[i].equipment_name,FaultModuleList[j])+";");
        ListFaultModuleBelong.append(FaultModuleBelong);
    }
    //设置表格的默认的行数
    ui->tableWidget_diagnosis_record_table->setRowCount(Currently_displayed_diagnostic_record_list.size());//设置默认的行数
    ui->tableWidget_diagnosis_record_table->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<Currently_displayed_diagnostic_record_list.size();i++)
    {
        QString num = QString::number(i, 10);
        QString if_solved_or_not = "是";
        if(!Currently_displayed_diagnostic_record_list[i].if_solved_or_not)
            if_solved_or_not = "否";
        ui->tableWidget_diagnosis_record_table->setItem(i,0,new QTableWidgetItem(num));
        ui->tableWidget_diagnosis_record_table->setItem(i,1,new QTableWidgetItem(Currently_displayed_diagnostic_record_list[i].fault_phenomenon));
        ui->tableWidget_diagnosis_record_table->setItem(i,2,new QTableWidgetItem(Currently_displayed_diagnostic_record_list[i].Diagnosis_Date.toString("yyyy.MM.dd")));
        ui->tableWidget_diagnosis_record_table->setItem(i,3,new QTableWidgetItem(Currently_displayed_diagnostic_record_list[i].user_name));
        ui->tableWidget_diagnosis_record_table->setItem(i,4,new QTableWidgetItem(Currently_displayed_diagnostic_record_list[i].boat_number));
        ui->tableWidget_diagnosis_record_table->setItem(i,5,new QTableWidgetItem(Currently_displayed_diagnostic_record_list[i].equipment_name));
        ui->tableWidget_diagnosis_record_table->setItem(i,6,new QTableWidgetItem(if_solved_or_not));
        ui->tableWidget_diagnosis_record_table->setItem(i,7,new QTableWidgetItem(Currently_displayed_diagnostic_record_list[i].fault_module));
        ui->tableWidget_diagnosis_record_table->setItem(i,8,new QTableWidgetItem(ListFaultModuleBelong[i]));

        QTableWidgetItem *checkBox_yes = new QTableWidgetItem();
        checkBox_yes->setCheckState(Qt::Unchecked);
        ui->tableWidget_diagnosis_record_table ->setItem(i, 9, checkBox_yes);

        if(Currently_displayed_diagnostic_record_list[i].Is_artificial_cord)
            ui->tableWidget_diagnosis_record_table->setItem(i,10,new QTableWidgetItem("录入"));
        else
            ui->tableWidget_diagnosis_record_table->setItem(i,10,new QTableWidgetItem("自动"));
    }

    ui->tableWidget_diagnosis_record_table->resizeRowsToContents();

    //居中显示
    for(int i=0;i<ui->tableWidget_diagnosis_record_table->rowCount();i++)
    {
        ui->tableWidget_diagnosis_record_table->item(i,0)->setTextAlignment(Qt::AlignCenter);
        ui->tableWidget_diagnosis_record_table->item(i,2)->setTextAlignment(Qt::AlignCenter);
        ui->tableWidget_diagnosis_record_table->item(i,3)->setTextAlignment(Qt::AlignCenter);
        ui->tableWidget_diagnosis_record_table->item(i,4)->setTextAlignment(Qt::AlignCenter);
        ui->tableWidget_diagnosis_record_table->item(i,5)->setTextAlignment(Qt::AlignCenter);
        ui->tableWidget_diagnosis_record_table->item(i,6)->setTextAlignment(Qt::AlignCenter);
        ui->tableWidget_diagnosis_record_table->item(i,10)->setTextAlignment(Qt::AlignCenter);
    }

    //设置不可更改
    for(int i = 0; i<ui->tableWidget_diagnosis_record_table->rowCount();i++)
    {
        for(int j = 0; j<(ui->tableWidget_diagnosis_record_table->columnCount()-2);j++)
            ui->tableWidget_diagnosis_record_table->item(i, j)->setFlags(Qt::NoItemFlags);
        ui->tableWidget_diagnosis_record_table->item(i, ui->tableWidget_diagnosis_record_table->columnCount()-1)->setFlags(Qt::NoItemFlags);
    }

    init_Currently_displayed_diagnostic_record_is_not_cell_change = false;
}

void Diagnosis_MainWindow::InitAccountManage()
{
    ui->tableWidget_account_login_record->blockSignals(true);

    ui->tableWidget_account_login_record->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_account_login_record->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    ui->tableWidget_account_login_record->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中

    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("ID") << tr("用户名称") << tr("所属部门") << tr("权限等级") << tr("最后登录时间");
    ui->tableWidget_account_login_record->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_account_login_record->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_account_login_record->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);
    ui->tableWidget_account_login_record->horizontalHeader()->setSectionResizeMode(2, QHeaderView::Stretch);
    ui->tableWidget_account_login_record->horizontalHeader()->setSectionResizeMode(3, QHeaderView::Stretch);
    ui->tableWidget_account_login_record->horizontalHeader()->setSectionResizeMode(4, QHeaderView::Stretch);

    ui->tableWidget_account_login_record->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_account_login_record->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_account_login_record->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);

    //设置表头
    ui->tableWidget_account_login_record->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_account_login_record->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗

    QList<Str_account> ListAccount;

    sql_prepare = QString("SELECT ID,USER,PASSWORD,DEPAERMENT,LIMIT,LOGIN_TIME FROM ACCOUNT;");

    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Str_account Account;
        Account.Operating_ID = qsQuery_TMATE_MDB.value(0).toString();
        Account.Operating_PSW = qsQuery_TMATE_MDB.value(2).toString();
        Account.Operating_limit = qsQuery_TMATE_MDB.value(4).toInt();
        Account.Operating_user = qsQuery_TMATE_MDB.value(1).toString();
        Account.User_department = qsQuery_TMATE_MDB.value(3).toString();
        Account.LoginTime =  qsQuery_TMATE_MDB.value(5).toDateTime();
        ListAccount.append(Account);
    }

    //设置表格的默认的行数
    ui->tableWidget_account_login_record->setRowCount(ListAccount.size());//设置默认的行数
    ui->tableWidget_account_login_record->verticalHeader()->hide();//隐藏行序号
    //数据显示
    for(int i=0;i<ListAccount.size();i++)
    {
        ui->tableWidget_account_login_record->setItem(i,0,new QTableWidgetItem(ListAccount[i].Operating_ID));
        ui->tableWidget_account_login_record->setItem(i,1,new QTableWidgetItem(ListAccount[i].Operating_user));
        ui->tableWidget_account_login_record->setItem(i,2,new QTableWidgetItem(ListAccount[i].User_department));

        if(ListAccount[i].Operating_limit>2)
            ListAccount[i].Operating_limit = 2;
        QStringList LimitGrade = {"管理员","军官","士兵"};
        ui->tableWidget_account_login_record->setItem(i,3,new QTableWidgetItem(LimitGrade[ListAccount[i].Operating_limit]));
        ui->tableWidget_account_login_record->setItem(i,4,new QTableWidgetItem(ListAccount[i].LoginTime.toString("yyyy/MM/dd hh:mm:ss")));


        ui->tableWidget_account_login_record->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_account_login_record->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_account_login_record->item(i,2)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_account_login_record->item(i,3)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
        ui->tableWidget_account_login_record->item(i,4)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);
    }

    ui->tableWidget_account_login_record->blockSignals(false);
}

void Diagnosis_MainWindow::on_tableWidget_diagnosis_record_table_cellChanged(int row, int column)//列表选中
{
    if(!init_Currently_displayed_diagnostic_record_is_not_cell_change)
    {
        if(column == 9)
        {
            if(ui->tableWidget_diagnosis_record_table->item(row, column)->checkState() == Qt::Checked)
            {
                Currently_displayed_diagnostic_record_list[row].pitch_on = true;
            }
            else Currently_displayed_diagnostic_record_list[row].pitch_on = false;
        }
    }
}

void Diagnosis_MainWindow::on_toolButton_record_query_output_clicked()//导出记录
{
    //qDebug()<<"导出记录";
    QList<QString> list_pitch_on_record_DIAGNOSTIC_ID;
    for(int i=0;i<Currently_displayed_diagnostic_record_list.size();i++)
    {
        if(Currently_displayed_diagnostic_record_list[i].pitch_on == true)
            list_pitch_on_record_DIAGNOSTIC_ID.append(Currently_displayed_diagnostic_record_list[i].DIAGNOSTIC_ID);
    }

    //若选中记录
    if(list_pitch_on_record_DIAGNOSTIC_ID.size())
    {
        //写入文件
        QDateTime da_time;
        QString time_str = da_time.currentDateTime().toString("yyyy-MM-dd HH-mm-ss");
        QString dirPath = QCoreApplication::applicationDirPath();

        QDir *DataFile = new QDir;
        bool exist = DataFile->exists("C:/MDB/DataFile");
        if(!exist)
        {
            bool isok = DataFile->mkdir("C:/MDB/DataFile"); // 新建文件夹
                if(!isok)
                    QMessageBox::warning(this,"提示","无法建立文件夹",QMessageBox::Yes);
        }

        QString fileName = "C:/MDB/DataFile/"+time_str+"datafile.txt";
        QFile file(fileName);
        if(!file.open(QIODevice::WriteOnly|QIODevice::Text|QIODevice::Append))
        {
            QMessageBox::warning(this,"提示","无法打开文件",QMessageBox::Yes);
        }
        QTextStream stream(&file);
        for(int i=0;i<list_pitch_on_record_DIAGNOSTIC_ID.size();i++)
        {
            //qDebug()<<list_pitch_on_record_DIAGNOSTIC_ID[i];
            //诊断结果查询
            //故障现象、故障时间、是否解决、故障模块，故障模块所属分机，维修人员，所属部门，舷号、反馈信息
            QStringList StringList_fault_module;
            QList<QString> feedback_text;
            sql_prepare = QString("SELECT Diagnosis_Date,feedback_text,user_name,maintain_company,boat_number,"
                                  "if_solved_or_not,fault_phenomenon,fault_module,advance_omen_test FROM DIAGNOSTIC_RECORD_LIST WHERE DIAGNOSTIC_ID = '%1';")
                    .arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
            qsQuery_TMATE_MDB.exec(sql_prepare);
            while(qsQuery_TMATE_MDB.next())
            {
                QString solve = "未解决";;
                if(qsQuery_TMATE_MDB.value(5).toBool())
                    solve = "已解决";
                stream<<"舰船舷号:  "+qsQuery_TMATE_MDB.value(4).toString().remove("\n").remove("\r").remove(" ").remove("<DIV>").remove("</DIV>")<<"\n"
                     <<"故障现象:  "+qsQuery_TMATE_MDB.value(6).toString().remove("\n").remove("\r").remove(" ").remove("<DIV>").remove("</DIV>")<<"\n"
                    <<"故障时间:  "+qsQuery_TMATE_MDB.value(0).toDate().toString("yyyy-MM-dd")<<"\n"
                   <<"是否解决:  "+solve<<"\n"
                  <<"异常模块:  "+qsQuery_TMATE_MDB.value(7).toString().remove("\n").remove("\r").remove(" ").remove("<DIV>").remove("</DIV>")<<"\n"
                 <<"维修人员:  "+qsQuery_TMATE_MDB.value(2).toString()<<"\n"
                <<"所属部门:  "+qsQuery_TMATE_MDB.value(3).toString()<<"\n"
                <<"反馈留言:  "+qsQuery_TMATE_MDB.value(1).toString()<<"\n"
                <<"\n\n";
            }
        }
        file.close();
       QMessageBox::warning(this,"提示","导出成功!",QMessageBox::Yes);
    }
    else
       QMessageBox::warning(this,"提示","请先选中需要导出的记录",QMessageBox::Yes);


}

void Diagnosis_MainWindow::resizeEvent(QResizeEvent *event)
{
    Q_UNUSED(event)
    ui->widget_test_module_image->setMaximumWidth(this->rect().width()/2);
    ui->widget_test_module_image->setMinimumWidth(this->rect().width()/2);
    ui->widget_test_module_image_2->setMaximumWidth(this->rect().width()/2);
    ui->widget_test_module_image_2->setMinimumWidth(this->rect().width()/2);
    ui->widget_test_module_image_3->setMinimumWidth(this->rect().width()/2);
    ui->widget_test_module_image_3->setMinimumWidth(this->rect().width()/2);
}

void Diagnosis_MainWindow::on_toolButton_record_query_view_details_clicked()//查看详情
{
    QList<QString> list_pitch_on_record_DIAGNOSTIC_ID;
    for(int i=0;i<Currently_displayed_diagnostic_record_list.size();i++)
    {
        if(Currently_displayed_diagnostic_record_list[i].pitch_on == true)
            list_pitch_on_record_DIAGNOSTIC_ID.append(Currently_displayed_diagnostic_record_list[i].DIAGNOSTIC_ID);
    }
    

    for(int i=0;i<list_pitch_on_record_DIAGNOSTIC_ID.size();i++)
    {
        diaglog_diagnosis_of_details_record *dlg=new diaglog_diagnosis_of_details_record(this);
        dlg->showNormal();
        dlg->setWindowTitle("诊断详情");

        //查询诊断过程表信息
        QList<QString> TEST_ORDER_ID;
        QList<QString> Diagnosis_test_name;
        QList<QString> recommend_or_self_selected;
        QList<QString> yes_or_no;
        sql_prepare = QString("SELECT TEST_ORDER_ID,Diagnosis_test_name,recommend_or_self_selected,yes_or_no "
                              "FROM DIAGNOSTIC_TEST_PROCESS_RECORD WHERE DIAGNOSTIC_ID = '%1';")
                .arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            TEST_ORDER_ID.append(qsQuery_TMATE_MDB.value(0).toString());
            Diagnosis_test_name.append(qsQuery_TMATE_MDB.value(1).toString());
            recommend_or_self_selected.append(qsQuery_TMATE_MDB.value(2).toString());
            yes_or_no.append(qsQuery_TMATE_MDB.value(3).toString());
        }

        //诊断结果查询
        QStringList StringList_fault_module;
        QList<QString> feedback_text;
        sql_prepare = QString("SELECT fault_module,feedback_text FROM DIAGNOSTIC_RECORD_LIST WHERE DIAGNOSTIC_ID = '%1';")
                .arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            StringList_fault_module = qsQuery_TMATE_MDB.value(0).toString().split(';');
            feedback_text.append(qsQuery_TMATE_MDB.value(1).toString());
        }


        //诊断工具查询
        QList<QString> list_tool;
        sql_prepare = QString("SELECT TOOL FROM DIAGNOSTIC_TOOL_RECORD WHERE DIAGNOSTIC_ID = '%1';")
                .arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
            list_tool.append(qsQuery_TMATE_MDB.value(0).toString());


        //查询诊断过程表信息
        QStringList StringList_advance_omen_test;
        sql_prepare = QString("SELECT advance_omen_test FROM DIAGNOSTIC_RECORD_LIST WHERE DIAGNOSTIC_ID = '%1';")
                .arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
        qsQuery_TMATE_MDB.exec(sql_prepare);
        while(qsQuery_TMATE_MDB.next())
        {
            StringList_advance_omen_test = qsQuery_TMATE_MDB.value(0).toString().split(';');
        }

        QList<QList<QString>> diagnosis_process;
        diagnosis_process.append(TEST_ORDER_ID);
        diagnosis_process.append(Diagnosis_test_name);
        diagnosis_process.append(recommend_or_self_selected);
        diagnosis_process.append(yes_or_no);
        diagnosis_process.append(StringList_fault_module);
        diagnosis_process.append(list_tool);
        diagnosis_process.append(StringList_advance_omen_test);
        diagnosis_process.append(feedback_text);

        connect(this,SIGNAL(send_the_details_record_to_the_UI(QList<QList<QString>>)),dlg,SLOT(setText(QList<QList<QString>>)));
        send_the_details_record_to_the_UI(diagnosis_process);
        
        int ret=dlg->exec();// 以模态方式显示对话框
        if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
        {
            delete dlg; //删除对话框
        }
    }
}

void Diagnosis_MainWindow::on_toolButton_record_query_query_clicked()//查询按钮
{
    init_diagnosis_record_query_list();
}

void Diagnosis_MainWindow::on_toolButton_record_query_delete_clicked()//删除记录
{
    if(LoginAccount.Operating_limit>=2)
    {
        QMessageBox::warning(this, "错误提示", "您没有删除记录的权限");
    }
    else
    {
        QList<QString> list_pitch_on_record_DIAGNOSTIC_ID;
        for(int i=0;i<Currently_displayed_diagnostic_record_list.size();i++)
        {
            if(Currently_displayed_diagnostic_record_list[i].pitch_on == true)
                list_pitch_on_record_DIAGNOSTIC_ID.append(Currently_displayed_diagnostic_record_list[i].DIAGNOSTIC_ID);
        }
        for(int i=0;i<list_pitch_on_record_DIAGNOSTIC_ID.size();i++)
        {
            sql_prepare = QString("DELETE *FROM DIAGNOSTIC_TEST_PROCESS_RECORD WHERE DIAGNOSTIC_ID = '%1';" ).arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
            qsQuery_TMATE_MDB.exec(sql_prepare);
            sql_prepare = QString("DELETE *FROM DIAGNOSTIC_RECORD_LIST WHERE DIAGNOSTIC_ID = '%1';" ).arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
            qsQuery_TMATE_MDB.exec(sql_prepare);
            sql_prepare = QString("DELETE *FROM DIAGNOSTIC_TOOL_RECORD WHERE DIAGNOSTIC_ID = '%1';" ).arg(list_pitch_on_record_DIAGNOSTIC_ID[i]);
            qsQuery_TMATE_MDB.exec(sql_prepare);
        }
        init_diagnosis_record_query_list();
    }
}
/***********************************************************************************************************************************/
/*****************************************************统计预测模块********************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::iniBarChart()//初始化统计预测树状图
{
    //初始化修理时间曲线图表
    QChart *chart_repair_time = new QChart(); //创建chart
    chart_repair_time->setTitle("修理时间曲线");
    chart_repair_time->setAnimationOptions(QChart::SeriesAnimations);
    chart_repair_time->setBackgroundVisible(false);
    ui->chartViewBar_repair_time->setChart(chart_repair_time); //为ChartView设置chart
    ui->chartViewBar_repair_time->setRenderHint(QPainter::Antialiasing);

    //初始化修理间隔曲线图表
    QChart *chart_repair_interval = new QChart(); //创建chart
    chart_repair_interval->setTitle("修理间隔曲线");
    chart_repair_interval->setAnimationOptions(QChart::SeriesAnimations);
    chart_repair_interval->setBackgroundVisible(false);
    ui->chartViewBar_repair_interval->setChart(chart_repair_interval); //为ChartView设置chart
    ui->chartViewBar_repair_interval->setRenderHint(QPainter::Antialiasing);

    //初始化诊断情况图表
    QChart *chart_diagnosis_result = new QChart(); //创建chart
    chart_diagnosis_result->setTitle("诊断情况");
    chart_diagnosis_result->setAnimationOptions(QChart::SeriesAnimations);
    chart_diagnosis_result->setBackgroundVisible(false);
    ui->chartViewBar_diagnosis_result->setChart(chart_diagnosis_result); //为ChartView设置chart
    ui->chartViewBar_diagnosis_result->setRenderHint(QPainter::Antialiasing);

    //初始化诊断模糊组图表
    QChart *chart_fuzzy_set = new QChart(); //创建chart
    chart_fuzzy_set->setTitle("诊断模糊组");
    chart_fuzzy_set->setAnimationOptions(QChart::SeriesAnimations);
    chart_fuzzy_set->setBackgroundVisible(false);
    ui->chartViewBar_fuzzy_set->setChart(chart_fuzzy_set); //为ChartView设置chart
    ui->chartViewBar_fuzzy_set->setRenderHint(QPainter::Antialiasing);
}

void Diagnosis_MainWindow::build_diagnosis_result(QString boat_name,int solved_number, int undersolved_number)//构建诊断情况图表
{
    //构建诊断情况图表图表
    QChart *chart =ui->chartViewBar_diagnosis_result->chart(); //获取ChartView关联的chart
    chart->removeAllSeries(); //删除所有序列
    chart->removeAxis(chart->axisX()); //删除坐标轴
    chart->removeAxis(chart->axisY()); //删除坐标轴
    //设置数据条目
    QBarSet *set_Data_solved = new QBarSet("已解决");
    QBarSet *set_Data_undersolved = new QBarSet("未解决");

    int sum = solved_number + undersolved_number;
    if(sum!=0){
        int undersolved_ratio = undersolved_number*100/sum;
        int solved_ratio = 100 - undersolved_ratio;
        set_Data_solved->append(solved_ratio);
        set_Data_undersolved->append(undersolved_ratio);}
    else{
        set_Data_solved->append(0);
        set_Data_undersolved->append(0);}

    //创建一个柱状图序列 QBarSeries, 并添加数据集
    QBarSeries *series_1 = new QBarSeries();
    series_1->append(set_Data_solved);
    QBarSeries *series_2 = new QBarSeries();
    series_2->append(set_Data_undersolved);

    chart->addSeries(series_1); //添加柱状图序列
    chart->addSeries(series_2); //添加柱状图序列

    //用于横坐标在字符串列表,即横坐标分组
    QStringList categories;
    categories <<boat_name;

    //用于柱状图的坐标轴
    QBarCategoryAxis *axisX = new QBarCategoryAxis();
    axisX->append(categories); //添加横坐标文字列表
    chart->setAxisX(axisX, series_1); //设置横坐标
    chart->setAxisX(axisX, series_2); //设置横坐标
    axisX->setRange(categories.at(0), categories.at(categories.count()-1)); //坐标轴范围

    //数值型坐标作为纵轴
    QValueAxis *axisY = new QValueAxis;
    axisY->setRange(0, 100);
    axisY->setTitleText("百分比");
    axisY->setTickCount(6);
    axisY->setLabelFormat("%.0f"); //标签格式
    chart->setAxisY(axisY, series_1);
    chart->setAxisY(axisY, series_2);

    chart->legend()->setVisible(true); //显示图例
    chart->legend()->setAlignment(Qt::AlignBottom); //图例显示在下方
}

void Diagnosis_MainWindow::build_repair_time(QList<int> repair_time_list)//构建修理时间曲线图表
{
    //构建诊断情况图表图表
    QChart *chart =ui->chartViewBar_repair_time->chart(); //获取ChartView关联的chart
    chart->removeAllSeries(); //删除所有序列
    chart->removeAxis(chart->axisX()); //删除坐标轴
    chart->removeAxis(chart->axisY()); //删除坐标轴
    //设置数据条目
    QBarSet *set_Data_solved = new QBarSet("修理时间占比(min)");

    int sum = 0;
    for(int i=0;i<repair_time_list.size();i++)
    {
        sum+=repair_time_list[i];
    }

    QList<int> repair_time_tatio_list;

    if(sum!=0)
    {
        int sum_tatio = 0;
        for(int i=0;i<repair_time_list.size();i++)
        {
            repair_time_tatio_list.append(repair_time_list[i]*100/sum);
            sum_tatio+=repair_time_list[i]*100/sum;
        }

        if(sum_tatio!=100)
        {
            repair_time_tatio_list[0] = 100;
            for(int i=1;i<repair_time_list.size();i++)
            {
                repair_time_tatio_list[0]-= repair_time_tatio_list[i];
            }
        }
    }
    else
    {
        for(int i=0;i<repair_time_list.size();i++)
        {
            repair_time_tatio_list.append(0);
        }
    }

    for(int i=0;i<repair_time_list.size();i++)
    {
        set_Data_solved->append(repair_time_tatio_list[i]);
    }

    //创建一个柱状图序列 QBarSeries, 并添加数据集
    QBarSeries *series_1 = new QBarSeries();
    series_1->append(set_Data_solved);

    chart->addSeries(series_1); //添加柱状图序列

    //用于横坐标在字符串列表,即横坐标分组
    QStringList categories;
    for(int i=1;i<30;(i=i+2))
    {
        categories <<QString::number(i);
    }
    categories <<"More";

    //用于柱状图的坐标轴
    QBarCategoryAxis *axisX = new QBarCategoryAxis();
    axisX->append(categories); //添加横坐标文字列表
    chart->setAxisX(axisX, series_1); //设置横坐标
    axisX->setRange(categories.at(0), categories.at(categories.count()-1)); //坐标轴范围

    //数值型坐标作为纵轴
    QValueAxis *axisY = new QValueAxis;
    axisY->setRange(0, 100);
    axisY->setTitleText("百分比");
    axisY->setTickCount(6);
    axisY->setLabelFormat("%.0f"); //标签格式
    chart->setAxisY(axisY, series_1);

    chart->legend()->setVisible(true); //显示图例
    chart->legend()->setAlignment(Qt::AlignBottom); //图例显示在下方
}

void Diagnosis_MainWindow::build_repair_interval(QList<int> repair_interval_list)//构建修理间隔曲线图表
{
    //构建诊断情况图表图表
    QChart *chart =ui->chartViewBar_repair_interval->chart(); //获取ChartView关联的chart
    chart->removeAllSeries(); //删除所有序列
    chart->removeAxis(chart->axisX()); //删除坐标轴
    chart->removeAxis(chart->axisY()); //删除坐标轴
    //设置数据条目
    QBarSet *set_Data_solved = new QBarSet("修理间隔占比(month)");

    int sum = 0;
    for(int i=0;i<repair_interval_list.size();i++)
    {
        sum+=repair_interval_list[i];
    }

    QList<int> repair_interval_tatio_list;

    if(sum!=0)
    {
        int sum_tatio = 0;
        for(int i=0;i<repair_interval_list.size();i++)
        {
            repair_interval_tatio_list.append(repair_interval_list[i]*100/sum);
            sum_tatio += repair_interval_list[i]*100/sum;
        }
        if(sum_tatio!=100)
        {
            repair_interval_tatio_list[0] = 100;
            for(int i=1;i<repair_interval_tatio_list.size();i++)
            {
                repair_interval_tatio_list[0]-= repair_interval_tatio_list[i];
            }
        }
    }

    else
    {
        for(int i=0;i<repair_interval_list.size();i++)
        {
            repair_interval_tatio_list.append(0);
        }
    }

    for(int i=0;i<repair_interval_list.size();i++)
    {
        set_Data_solved->append(repair_interval_tatio_list[i]);
    }

    //创建一个柱状图序列 QBarSeries, 并添加数据集
    QBarSeries *series_1 = new QBarSeries();
    series_1->append(set_Data_solved);


    chart->addSeries(series_1); //添加柱状图序列


    //用于横坐标在字符串列表,即横坐标分组
    QStringList categories;
    categories <<"1" <<"2" <<"3" <<"4" <<"5" <<"6" <<"7" <<"8" <<"9" <<"More";

    //用于柱状图的坐标轴
    QBarCategoryAxis *axisX = new QBarCategoryAxis();
    axisX->append(categories); //添加横坐标文字列表
    chart->setAxisX(axisX, series_1); //设置横坐标
    axisX->setRange(categories.at(0), categories.at(categories.count()-1)); //坐标轴范围

    //数值型坐标作为纵轴
    QValueAxis *axisY = new QValueAxis;
    axisY->setRange(0, 100);
    axisY->setTitleText("百分比");
    axisY->setTickCount(6);
    axisY->setLabelFormat("%.0f"); //标签格式
    chart->setAxisY(axisY, series_1);

    chart->legend()->setVisible(true); //显示图例
    chart->legend()->setAlignment(Qt::AlignBottom); //图例显示在下方
}

void Diagnosis_MainWindow::build_fuzzy_set(QList<int> fuzzy_set_list)//构建诊断模糊组图表
{
    //构建诊断情况图表图表
    QChart *chart =ui->chartViewBar_fuzzy_set->chart(); //获取ChartView关联的chart
    chart->removeAllSeries(); //删除所有序列
    chart->removeAxis(chart->axisX()); //删除坐标轴
    chart->removeAxis(chart->axisY()); //删除坐标轴
    //设置数据条目
    QBarSet *set_Data_solved = new QBarSet("模糊组占比");

    int sum = 0;
    for(int i=0;i<fuzzy_set_list.size();i++)
    {
        sum+=fuzzy_set_list[i];
    }

    QList<int> fuzzy_set_tatio_list;//模糊组百分比

    if(sum!=0)
    {
        int sum_tatio = 0;
        for(int i=0;i<fuzzy_set_list.size();i++)
        {
            fuzzy_set_tatio_list.append(fuzzy_set_list[i]*100/sum);
            sum_tatio += fuzzy_set_list[i]*100/sum;
        }
        if(sum_tatio!=100)
        {
            fuzzy_set_tatio_list[0] = 100;
            for(int i=1;i<fuzzy_set_tatio_list.size();i++)
            {
                fuzzy_set_tatio_list[0]-= fuzzy_set_tatio_list[i];
            }
        }
    }
    else
    {
        for(int i=0;i<fuzzy_set_list.size();i++)
        {
            fuzzy_set_tatio_list.append(0);
        }
    }

    for(int i=0;i<fuzzy_set_list.size();i++)
    {
        set_Data_solved->append(fuzzy_set_tatio_list[i]);
    }

    //创建一个柱状图序列 QBarSeries, 并添加数据集
    QBarSeries *series_1 = new QBarSeries();
    series_1->append(set_Data_solved);


    chart->addSeries(series_1); //添加柱状图序列


    //用于横坐标在字符串列表,即横坐标分组
    QStringList categories;
    categories <<"1" <<"2" <<"3" <<"4" <<"5" <<"6" <<"7" <<"8" <<"9" <<"More";

    //用于柱状图的坐标轴
    QBarCategoryAxis *axisX = new QBarCategoryAxis();
    axisX->append(categories); //添加横坐标文字列表
    chart->setAxisX(axisX, series_1); //设置横坐标
    axisX->setRange(categories.at(0), categories.at(categories.count()-1)); //坐标轴范围

    //数值型坐标作为纵轴
    QValueAxis *axisY = new QValueAxis;
    axisY->setRange(0, 100);
    axisY->setTitleText("百分比");
    axisY->setTickCount(6);
    axisY->setLabelFormat("%.0f"); //标签格式
    chart->setAxisY(axisY, series_1);

    chart->legend()->setVisible(true); //显示图例
    chart->legend()->setAlignment(Qt::AlignBottom); //图例显示在下方
}

void Diagnosis_MainWindow::redrawBarChart(QString boatNumber,QDateTime start_Time,QDateTime finish_Time)//重绘预测树状图
{
    sql_prepare = QString("SELECT *FROM DIAGNOSTIC_RECORD_LIST WHERE start_time >= #%1# "
                          "AND finish_time <= #%2# AND boat_number = '%3' Order By start_time Desc;")
            .arg(start_Time.toString("yyyy-MM-dd hh:mm:ss")).arg(finish_Time.toString("yyyy-MM-dd hh:mm:ss"))
            .arg(boatNumber);

    int solved_ansys = 0;//已解决数目
    int not_solved_ansys = 0;//未解决数目

    QList<int> fuzzy_set_list;//诊断模糊组数据
    fuzzy_set_list <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0;

    QList<int> repair_time_list;//修理时间数据
    repair_time_list <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0;

    QList<int> repair_interval_list;//修理时间间隔数据
    repair_interval_list <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0 <<0;
    QDate last_start_date = QDate::currentDate();//获取系统现在的日期

    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        //问题解决情况统计
        if(qsQuery_TMATE_MDB.value(9).toBool())
            solved_ansys++;
        else
            not_solved_ansys++;
        //诊断模糊组数据统计
        QString fault_module = qsQuery_TMATE_MDB.value(11).toString();
        QStringList strlist=fault_module.split(";");
        if((strlist.size()<10)&&(strlist.size()>0))
            fuzzy_set_list[strlist.size()-1]++;
        else
            fuzzy_set_list[10]++;

        //修理时间统计
        QDateTime start_time =  qsQuery_TMATE_MDB.value(1).toDateTime();
        QDateTime finish_time =  qsQuery_TMATE_MDB.value(2).toDateTime();
        long long num_sec = start_time.secsTo(finish_time);//转换为秒
        long long mun_min = num_sec/60;//转换为分钟///////////////////////////////////
        if((mun_min<=30)&&(mun_min>=0))
            repair_time_list[static_cast<int>(mun_min/2)]++;
        else
            repair_time_list[repair_time_list.size()-1]++;

        //修理间隔统计
        QDate this_start_date = qsQuery_TMATE_MDB.value(3).toDate();
        long long num_day = this_start_date.daysTo(last_start_date);//转换为天
        int num_month = static_cast<int>(num_day/30);
        last_start_date = this_start_date;
        //qDebug()<<num_month;
        if(num_month==0)
            repair_interval_list[0]++;
        else if((num_month<=9)&&(num_month>0))
            repair_interval_list[num_month]++;
        else
            repair_interval_list[repair_interval_list.size()-1]++;
    }
    //重绘表格
    //qDebug()<<solved_ansys<<not_solved_ansys;
    build_diagnosis_result("ALL",solved_ansys,not_solved_ansys);
    build_fuzzy_set(fuzzy_set_list);
    build_repair_time(repair_time_list);
    build_repair_interval(repair_interval_list);
}

void Diagnosis_MainWindow::on_toolButton_record_query_query_2_clicked()//预测模块查询
{
    QString boatNumber = ui->lineEdit_record_query_boat_number_2->text();
    QDateTime start_Time = ui->dateTimeEdit_record_query_start_time_2->dateTime();
    QDateTime finish_Time = ui->dateTimeEdit_query_finish_time_2->dateTime();
    redrawBarChart(boatNumber,start_Time,finish_Time);//重绘预测树状图
}

void Diagnosis_MainWindow::on_toolButton_export_statistics_chart_clicked()
{
    QPixmap pix = QPixmap::grabWidget(ui->widget_5);

    QString strFile =  QDateTime::currentDateTime().toString("yyyyMMddHHmmss") + ".png";

    QString fileName = QFileDialog::getSaveFileName(this, "保存图片", strFile, "PNG (*.png);;BMP (*.bmp);;JPEG (*.jpg *.jpeg)");
    if (!fileName.isNull())
        pix.save(fileName);

}

/***********************************************************************************************************************************/
/**************************************************案例录入模块****************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::init_case_entry_model_list()//初始化案例录入模型列表
{
    ui->tableView_case_entry_model_select->setEditTriggers(QAbstractItemView::NoEditTriggers);//设置表格不可编辑
    ui->tableView_case_entry_model_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中

    //QSqlTableModel  *tabModel;  //数据选择模型
    tabModel=new MyQSqlTableModel(this,TMATE_MDB);//数据表
    tabModel->setTable("MODELS"); //设置数据表
    tabModel->setEditStrategy(QSqlTableModel::OnManualSubmit);//数据保存方式，OnManualSubmit,OnRowChange
    if (!(tabModel->select()))//查询数据
    {
        QMessageBox::critical(this, "错误信息",
                              "打开数据表错误,错误信息\n"+tabModel->lastError().text(),
                              QMessageBox::Ok,QMessageBox::NoButton);
        return;
    }

    //字段显示名
    tabModel->setHeaderData(tabModel->fieldIndex("MODEL_NAME"),Qt::Horizontal,"模型名称");
    tabModel->setHeaderData(tabModel->fieldIndex("UPDATED_BY"),Qt::Horizontal,"导入人");
    tabModel->setHeaderData(tabModel->fieldIndex("UPDATE_TIME"),Qt::Horizontal,"导入时间");
    tabModel->setHeaderData(tabModel->fieldIndex("MODEL_TID"),Qt::Horizontal,"模型TID");
    tabModel->setHeaderData(tabModel->fieldIndex("NUM_MODULES"),Qt::Horizontal,"模块个数");
    tabModel->setHeaderData(tabModel->fieldIndex("SYSTEM_MODEL_NAME"),Qt::Horizontal,"系统名称");
    tabModel->setHeaderData(tabModel->fieldIndex("SYSTEM_MODEL_REVISION"),Qt::Horizontal,"模型版本号");
    tabModel->setHeaderData(tabModel->fieldIndex("CREATION_TIME"),Qt::Horizontal,"创建时间");
    tabModel->setHeaderData(tabModel->fieldIndex("CREATED_BY"),Qt::Horizontal,"创建人");
    tabModel->setHeaderData(tabModel->fieldIndex("NOTES"),Qt::Horizontal,"备注");

    ui->tableView_case_entry_model_select->verticalHeader()->hide();//隐藏行序号
    ui->tableView_case_entry_model_select->setModel(tabModel);//设置数据模型

    //设置表头
    ui->tableView_case_entry_model_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableView_case_entry_model_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗

    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("UPDATED_BY"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("UPDATE_TIME"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("MODEL_TID"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("SYSTEM_MODEL_NAME"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("CREATION_TIME"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("TEST_COST_PREFERENCE"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("TEST_LEVEL_PREFERENCE"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("TEST_TIME_PREFERENCE"),true);//隐藏列
    ui->tableView_case_entry_model_select->setColumnHidden(tabModel->fieldIndex("FAULT_PROBABILITY_PREFERENCE"),true);//隐藏列

    ui->tableView_case_entry_model_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableView_case_entry_model_select->setStyleSheet(tableViewStyleSheet);//设置表格颜色
    ui->tableView_case_entry_model_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);
    //设置表头

    ui->tableView_case_entry_model_select->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
    ui->tableView_case_entry_model_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格列宽随View变化
}

void Diagnosis_MainWindow::on_toolButton_case_entry_model_selected_OK_clicked()//案例录入模型确认选择按钮
{
    //若没有选择模型，发出警告
    int curRow = ui->tableView_case_entry_model_select->currentIndex().row();
    QString MODEL_NAME = tabModel->record(curRow).value("MODEL_NAME").toString();//获取当前选择模型名称

    if(MODEL_NAME == nullptr){
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择模型"),QMessageBox::Yes);
        return;}

    diagnosis_model_name = MODEL_NAME;//存储需要诊断的模型名称
    Matrix_D.diagnostic_record.equipment_name = diagnosis_model_name;

    //数据库操作将所有征兆全选跳过
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 2;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 2;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    //跳转到案例录入-征兆选择界面
    ui->stackedWidget_main->setCurrentIndex(13);
    ui->lineEdit_case_entry_known_symptom_searching->clear();
    ui->radioButton_select_known_symptom_model->setChecked(true);
    user_or_model = "model";
    init_case_entry_symptom_list(diagnosis_model_name,"all","model");//初始化征兆选择列表
}

/////////////////////////////////////////////////////////
///    \brief known_symptom_signal_select_UI          ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::init_case_entry_symptom_list(QString model_name, QString fuzzy_search, QString user_or_model)//案例录入初始化征兆信号UI列表
{ 
    init_case_entry_known_symptom_list_is_not_cell_change = true;

    ui->tableWidget_case_entry__known_symptom_select->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_case_entry__known_symptom_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_case_entry__known_symptom_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_case_entry__known_symptom_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);
    ui->tableWidget_case_entry__known_symptom_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中

    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("征兆名称") << tr("征兆描述") << tr("征兆存在") << tr("征兆不存在") << tr("跳过");
    ui->tableWidget_case_entry__known_symptom_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_case_entry__known_symptom_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_case_entry__known_symptom_select->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_case_entry__known_symptom_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);

    ui->tableWidget_case_entry__known_symptom_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_case_entry__known_symptom_select->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_case_entry__known_symptom_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);

    //设置表头
    ui->tableWidget_case_entry__known_symptom_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_case_entry__known_symptom_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_case_entry__known_symptom_select->setFocusPolicy(Qt::NoFocus);
    //ui->tableWidget_case_entry__known_symptom_select->sett//item->setTextAlignment(Qt::AlignHCenter | Qt::AlignVCenter);//文本对齐格式
    //查找数据信息
    typedef struct{
        QString TEST_NAME;
        QString TEST_PROCEDURE;
        int TEST_SIGNAL_IS_EXIT_OR_NOT;
    }Str_MODEL_TSET_EXIT;
    QList<Str_MODEL_TSET_EXIT> MODEL_TSET_List;

    if(fuzzy_search == "all")
    {
        if(user_or_model == "user")
        {
            sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                                  "FROM CASE_ENTRY_TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2;").arg(model_name);
        }
        else
        {
            sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                                  "FROM TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2;").arg(model_name);
        }
    }
    else
    {
        if(user_or_model == "user")
        {
            sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                                  "FROM CASE_ENTRY_TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2 "
                                  "AND TEST_NAME LIKE '%%2%';").arg(model_name).arg(fuzzy_search);
        }
        else
        {
            sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                                  "FROM TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2 "
                                  "AND TEST_NAME LIKE '%%2%';").arg(model_name).arg(fuzzy_search);
        }
    }

    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Str_MODEL_TSET_EXIT MODEL_TSET;
        MODEL_TSET.TEST_NAME = qsQuery_TMATE_MDB.value(0).toString();
        MODEL_TSET.TEST_PROCEDURE = qsQuery_TMATE_MDB.value(1).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(MODEL_TSET.TEST_PROCEDURE.startsWith("\n")||MODEL_TSET.TEST_PROCEDURE.startsWith("\r"))
            MODEL_TSET.TEST_PROCEDURE.remove(0,2);
        MODEL_TSET.TEST_SIGNAL_IS_EXIT_OR_NOT = qsQuery_TMATE_MDB.value(2).toInt();
        MODEL_TSET_List.append(MODEL_TSET);
    }
    //设置表格的默认的行数
    ui->tableWidget_case_entry__known_symptom_select->setRowCount(MODEL_TSET_List.size());//设置默认的行数
    ui->tableWidget_case_entry__known_symptom_select->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<MODEL_TSET_List.size();i++)
    {
        ui->tableWidget_case_entry__known_symptom_select->setItem(i,0,new QTableWidgetItem(MODEL_TSET_List[i].TEST_NAME));
        //ui->tableWidget_case_entry__known_symptom_select->item(i,0)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);

        ui->tableWidget_case_entry__known_symptom_select->setItem(i,1,new QTableWidgetItem(MODEL_TSET_List[i].TEST_PROCEDURE));
        //ui->tableWidget_case_entry__known_symptom_select->item(i,1)->setTextAlignment(Qt::AlignHCenter|Qt::AlignVCenter);

        QTableWidgetItem *checkBox_yes = new QTableWidgetItem();
        checkBox_yes->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry__known_symptom_select ->setItem(i, 2, checkBox_yes);

        QTableWidgetItem *checkBox_no = new QTableWidgetItem();
        checkBox_no->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry__known_symptom_select ->setItem(i, 3, checkBox_no);

        QTableWidgetItem *checkBox_skip = new QTableWidgetItem();
        checkBox_skip->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry__known_symptom_select ->setItem(i, 4, checkBox_skip);

        switch (MODEL_TSET_List[i].TEST_SIGNAL_IS_EXIT_OR_NOT)
        {
        case 0:
            ui->tableWidget_case_entry__known_symptom_select->item(i, 2)->setCheckState(Qt::Checked);
            break;
        case 1:
            ui->tableWidget_case_entry__known_symptom_select->item(i, 3)->setCheckState(Qt::Checked);
            break;
        case 2:
            ui->tableWidget_case_entry__known_symptom_select->item(i, 4)->setCheckState(Qt::Checked);
            break;
        default:
            ui->tableWidget_case_entry__known_symptom_select->item(i, 4)->setCheckState(Qt::Checked);
        }

    }
    ui->tableWidget_case_entry__known_symptom_select->resizeRowsToContents();
    init_case_entry_known_symptom_list_is_not_cell_change = false;
}

void Diagnosis_MainWindow::on_radioButton_select_known_symptom_model_clicked()//案例录入-征兆信号选择-模型筛选
{
    user_or_model = "model";
    ui->lineEdit_case_entry_known_symptom_searching->clear();
    init_case_entry_symptom_list(diagnosis_model_name,"all",user_or_model);//初始化征兆选择列表
}

void Diagnosis_MainWindow::on_radioButton_select_known_symptom_user_clicked()//案例录入-征兆信号选择-用户筛选
{
    user_or_model = "user";
    ui->lineEdit_case_entry_known_symptom_searching->clear();
    init_case_entry_symptom_list(diagnosis_model_name,"all",user_or_model);//初始化征兆选择列表
}

void Diagnosis_MainWindow::on_btn_case_entry_known_symptom_searching_clicked()//案例录入-征兆信号选择-搜索
{
    QString fuzzy_search = ui->lineEdit_case_entry_known_symptom_searching->text();
    init_case_entry_symptom_list(diagnosis_model_name,fuzzy_search,user_or_model);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_tableWidget_case_entry__known_symptom_select_cellChanged(int row, int column)//案例录入-征兆信号选择操作数据库
{
    if(!init_case_entry_known_symptom_list_is_not_cell_change)
    {
        QString cellchanged_test_name = ui->tableWidget_case_entry__known_symptom_select->item(row, 0)->text();
        int test_state = column-2;

        if(ui->tableWidget_case_entry__known_symptom_select->item(row, column)->checkState() == Qt::Checked)
        {
            if(user_or_model == "user")
            {
                sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                        .arg(test_state).arg(cellchanged_test_name).arg(diagnosis_model_name);
            }
            else
            {
                sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                        .arg(test_state).arg(cellchanged_test_name).arg(diagnosis_model_name);
            }
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
        }
        init_case_entry_symptom_list(diagnosis_model_name, ui->lineEdit_case_entry_known_symptom_searching->text(),user_or_model);
    }
}

void Diagnosis_MainWindow::on_toolButton_case_entry_known_symptom_select_all_clicked()//存在全选
{
    int row_count = ui->tableWidget_case_entry__known_symptom_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_case_entry__known_symptom_select->item(i, 0)->text();

        if(user_or_model == "user")
        {
            sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(0).arg(cellchanged_test_name).arg(diagnosis_model_name);
        }
        else
        {
            sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(0).arg(cellchanged_test_name).arg(diagnosis_model_name);
        }
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_case_entry_symptom_list(diagnosis_model_name, ui->lineEdit_case_entry_known_symptom_searching->text(),user_or_model);
}

void Diagnosis_MainWindow::on_toolButton_case_entry_not_exit_symptom_select_all_clicked()//不存在全选
{
    int row_count = ui->tableWidget_case_entry__known_symptom_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_case_entry__known_symptom_select->item(i, 0)->text();

        if(user_or_model == "user")
        {
            sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(1).arg(cellchanged_test_name).arg(diagnosis_model_name);
        }
        else
        {
            sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(1).arg(cellchanged_test_name).arg(diagnosis_model_name);
        }
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_case_entry_symptom_list(diagnosis_model_name, ui->lineEdit_case_entry_known_symptom_searching->text(),user_or_model);
}

void Diagnosis_MainWindow::on_toolButton_case_entry_known_symptom_all_skip_clicked()//跳过全选
{
    int row_count = ui->tableWidget_case_entry__known_symptom_select->rowCount();
    for(int i=0;i<row_count;i++)
    {
        QString cellchanged_test_name = ui->tableWidget_case_entry__known_symptom_select->item(i, 0)->text();

        if(user_or_model == "user")
        {
            sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(2).arg(cellchanged_test_name).arg(diagnosis_model_name);
        }
        else
        {
            sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                    .arg(2).arg(cellchanged_test_name).arg(diagnosis_model_name);
        }
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }
    init_case_entry_symptom_list(diagnosis_model_name, ui->lineEdit_case_entry_known_symptom_searching->text(),user_or_model);
}

void Diagnosis_MainWindow::on_toolButton_case_entry_known_symptom_select_new_clicked()//征兆新增
//This part is not complete ,the yse and on describe is not used，checksum code error
{
    dialog_case_entry_symptom_new *dlg=new dialog_case_entry_symptom_new(this);
    dlg->showNormal();
    dlg->setWindowTitle("请输入新增征兆信息");
    dlg->setModal(true);

    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        QString case_entry_symptom_name = dlg->get_lineEdit_case_entry_symptom_name();//获取现象名称
        QString get_textEdit_case_entry_symptom_describe = dlg->get_textEdit_case_entry_symptom_describe();//获取现象描述
        QString case_entry_result_Yes_describe = dlg->get_lineEdit_case_entry_result_Yes_describe();//获取Yes结果描述
        QString case_entry_result_No_describe = dlg->get_lineEdit_case_entry_result_No_describe();//获取No结果描述
        QString case_entry_accessory_name = dlg->get_lineEdit_case_entry_accessory_name();//获取文件名称

        //////////////////////////////////////////////////////////////////////////////////
        ////////////////////此区域为向数据库存储信息区域
        /// //////////////////////////////////////////////////////////////////////////////

        //生成唯一CASE_ENTRY_TEST_TID
        QString new_case_entry_TEST_TID = "case_entry_";
        QDateTime curDateTime=QDateTime::currentDateTime();
        new_case_entry_TEST_TID.append(curDateTime.toString("yyyyMMddhhmmss"));

        //将唯一TID，现象名称，现象描述插入CASE_ENTRY_TEST_PROPS表格
        sql_prepare = QString("INSERT INTO CASE_ENTRY_TEST_PROPS (TEST_TID, MODEL_NAME, TEST_NAME, TEST_PROCEDURE, TEST_TYPE) "
                              "VALUES ('%1', '%2', '%3', '%4', 2);")
                .arg(new_case_entry_TEST_TID).arg(diagnosis_model_name)
                .arg(case_entry_symptom_name).arg(get_textEdit_case_entry_symptom_describe);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();

        //获取附件文件信息并存储
        if(case_entry_accessory_name!=nullptr)
        {//文件信息集定义
            typedef struct  {
                QString TID;//测试TID
                QString MODEL_NAME;//测试所属模型
                QString ID;//文件ID
                QString MEDIA_NAME;//文件名称
                QString IMAGE_TYPE;//文件类型
                QString CHECKSUM;//校验码
                long long int FILE_SIZE;//文件大小
            }StrFileData;
            StrFileData OneStrFileData;
            QStringList stringList_case_entry_accessory_name = case_entry_accessory_name.split("<DIV>");
            for(int i=0;i<stringList_case_entry_accessory_name.size();i++)
            {
                //获取测试TID
                OneStrFileData.TID = new_case_entry_TEST_TID;
                //获取测试所属模型
                OneStrFileData.MODEL_NAME = diagnosis_model_name;
                //获取文件ID
                QString File_ID = "case_entry_File_";
                QDateTime curDateTime=QDateTime::currentDateTime();
                File_ID.append(curDateTime.toString("yyyyMMddhhmmss"));
                OneStrFileData.ID = File_ID;
                //获取文件名称
                QStringList File_Name = stringList_case_entry_accessory_name[i].split("/");
                OneStrFileData.MEDIA_NAME = File_Name[File_Name.size()-1];
                //获取文件类型
                OneStrFileData.IMAGE_TYPE = "IMAGE";
                //获取文件大小
                QFile inImg(stringList_case_entry_accessory_name[i]);
                if(!inImg.open(QIODevice::ReadOnly))
                {
                    QMessageBox::warning(nullptr,"Error","Open Image File Failed");
                    return;
                }
                QByteArray inBytearray = inImg.readAll();
                //获取图片大小
                OneStrFileData.FILE_SIZE = inImg.size();
                //获取文件校验码
                //Checksum check;
                //unsigned short check_num = check.CheckSum((unsigned short*)(&inBytearray),(int)OneStrFileData.FILE_SIZE);
                OneStrFileData.CHECKSUM = OneStrFileData.ID;
                //将信息存储到数据库
                sql_prepare = QString("INSERT INTO TEST_MEDIA (TID, MODEL_NAME, ID, MEDIA_NAME, IMAGE_TYPE, CHECKSUM, FILE_SIZE) "
                                      "VALUES ('%1', '%2', '%3', '%4','%5', '%6', %7);")
                        .arg(OneStrFileData.TID).arg(OneStrFileData.MODEL_NAME).arg(OneStrFileData.ID)
                        .arg(OneStrFileData.MEDIA_NAME).arg(OneStrFileData.IMAGE_TYPE).arg(OneStrFileData.CHECKSUM)
                        .arg(OneStrFileData.FILE_SIZE);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.exec();

                sql_prepare = QString("INSERT INTO MULTIMEDIA(FILE_SIZE, CHECKSUM, IMAGE_DATA) "
                                      "VALUES(%1,:CHECKSUM,:IMAGE_DATA);").arg(OneStrFileData.FILE_SIZE);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.bindValue(":CHECKSUM",OneStrFileData.CHECKSUM);
                qsQuery_TMATE_MDB.bindValue(":IMAGE_DATA",inBytearray);
                qsQuery_TMATE_MDB.exec();
                /*                //Debug part
//                sql_prepare = QString("SELECT IMAGE_DATA FROM MULTIMEDIA WHERE CHECKSUM = 'case_entry_File_20200513103832';");
//                qsQuery_TMATE_MDB.exec(sql_prepare);
//                while(qsQuery_TMATE_MDB.next())
//                {
//                    QPixmap photo;
//                    photo.loadFromData(inBytearray);
//                    ui->stackedWidget_main->setCurrentIndex(15);
//                    ui->label->setPixmap(photo);
//                }*/
            }
        }
    }
    delete dlg; //删除对话框
    init_case_entry_symptom_list(diagnosis_model_name, ui->lineEdit_case_entry_known_symptom_searching->text(),user_or_model);
}

void Diagnosis_MainWindow::on_toolButton_case_entry_known_symptom_select_next_clicked()//征兆选择下一步
{
    //将所选征兆数据保存到记录
    sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                          "FROM CASE_ENTRY_TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2 "
                          " AND TEST_SIGNAL_IS_EXIT_OR_NOT = 0;")
            .arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.diagnostic_record.advance_omen_test.append(qsQuery_TMATE_MDB.value(0).toString());
        Matrix_D.diagnostic_record.advance_omen_test.append(";");

        QString test_procedure = qsQuery_TMATE_MDB.value(0).toString();;
        test_procedure.remove(" ").remove("<DIV>").remove("</DIV>").remove("\r").remove("\n");
        if(test_procedure != nullptr)
        {
            Matrix_D.diagnostic_record.fault_phenomenon.append(test_procedure);
            Matrix_D.diagnostic_record.fault_phenomenon.append(",不正常;");
        }
    }
    sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                          "FROM TEST_PROPS WHERE MODEL_NAME = '%1' AND TEST_TYPE = 2"
                          " AND TEST_SIGNAL_IS_EXIT_OR_NOT = 0;").arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.diagnostic_record.advance_omen_test.append(qsQuery_TMATE_MDB.value(0).toString());
        Matrix_D.diagnostic_record.advance_omen_test.append(";");

        QString test_procedure = qsQuery_TMATE_MDB.value(0).toString();;
        test_procedure.remove(" ").remove("<DIV>").remove("</DIV>").remove("\r").remove("\n");
        if(test_procedure != nullptr)
        {
            Matrix_D.diagnostic_record.fault_phenomenon.append(test_procedure);
            Matrix_D.diagnostic_record.fault_phenomenon.append(",不正常;");
        }
    }

    //数据库操作将所有测试全选跳过
    sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 1;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 1;")
            .arg(2).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    ui->stackedWidget_main->setCurrentIndex(14);
    ui->lineEdit_case_entry_test_result_searching->clear();//清空搜索栏
    ui->radioButton_select_test_result_model->setChecked(true);
    user_or_model = "model";
    init_case_entry_test_list(diagnosis_model_name,"all","model",false);//初始化测试信号UI列表
    selected_test_and_state.have_test_selected = false;//默认没有测试被选中
}

/////////////////////////////////////////////////////////
///    \brief test_result_select_UI          ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::init_case_entry_test_list(QString model_name, QString fuzzy_search, QString user_or_model,bool hide_selected_tests)//初始化案例录入初始化测试UI列表
{
    init_case_entry_test_result_list_is_not_cell_change = true;

    ui->tableWidget_case_entry_test_result->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableWidget_case_entry_test_result->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_case_entry_test_result->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_case_entry_test_result->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);
    ui->tableWidget_case_entry_test_result->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中

    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("现象测试名称") << tr("现象测试描述") << tr("正常")<< tr("异常")<< tr("跳过");
    ui->tableWidget_case_entry_test_result->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_case_entry_test_result->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_case_entry_test_result->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_case_entry_test_result->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_case_entry_test_result->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);
    //设置表头
    ui->tableWidget_case_entry_test_result->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_case_entry_test_result->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_case_entry_test_result->setFocusPolicy(Qt::NoFocus);

    ui->tableWidget_case_entry_test_result->horizontalHeader()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->tableWidget_case_entry_test_result->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);

    //查找数据信息
    typedef struct{
        QString TEST_NAME;
        QString TEST_PROCEDURE;
        int TEST_SIGNAL_IS_EXIT_OR_NOT;
    }Str_MODEL_TSET_EXIT;
    QList<Str_MODEL_TSET_EXIT> MODEL_TSET_List;

    QString selected_table;
    if(user_or_model == "user")
        selected_table = "CASE_ENTRY_TEST_PROPS";
    else
        selected_table = "TEST_PROPS";

    QString sql_hide_selected_tests = " ";
    if(hide_selected_tests)
        sql_hide_selected_tests = " AND TEST_SIGNAL_IS_EXIT_OR_NOT = 2 ";

    if(fuzzy_search == "all")
    {
        sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                              "FROM %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 1 %3;")
                .arg(selected_table).arg(model_name).arg(sql_hide_selected_tests);
    }
    else
    {
        sql_prepare = QString("SELECT TEST_NAME,TEST_PROCEDURE,TEST_SIGNAL_IS_EXIT_OR_NOT "
                              "FROM %1 WHERE MODEL_NAME = '%2' AND TEST_TYPE = 1 %3 "
                              "AND TEST_NAME LIKE '%%4%';")
                .arg(selected_table).arg(model_name).arg(sql_hide_selected_tests).arg(fuzzy_search);
    }

    //查找TMATE数据库模型测试信息
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Str_MODEL_TSET_EXIT MODEL_TSET;
        MODEL_TSET.TEST_NAME = qsQuery_TMATE_MDB.value(0).toString();
        MODEL_TSET.TEST_PROCEDURE = qsQuery_TMATE_MDB.value(1).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("<BR>");
        while(MODEL_TSET.TEST_PROCEDURE.startsWith("\n")||MODEL_TSET.TEST_PROCEDURE.startsWith("\r"))
            MODEL_TSET.TEST_PROCEDURE.remove(0,2);
        MODEL_TSET.TEST_SIGNAL_IS_EXIT_OR_NOT = qsQuery_TMATE_MDB.value(2).toInt();
        MODEL_TSET_List.append(MODEL_TSET);
    }
    //设置表格的默认的行数
    ui->tableWidget_case_entry_test_result->setRowCount(MODEL_TSET_List.size());//设置默认的行数
    ui->tableWidget_case_entry_test_result->verticalHeader()->hide();//隐藏行序号

    //数据显示
    for(int i=0;i<MODEL_TSET_List.size();i++)
    {
        ui->tableWidget_case_entry_test_result->setItem(i,0,new QTableWidgetItem(MODEL_TSET_List[i].TEST_NAME));
        ui->tableWidget_case_entry_test_result->setItem(i,1,new QTableWidgetItem(MODEL_TSET_List[i].TEST_PROCEDURE));

        QTableWidgetItem *checkBox_yes = new QTableWidgetItem();
        checkBox_yes->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_test_result ->setItem(i, 2, checkBox_yes);

        QTableWidgetItem *checkBox_no = new QTableWidgetItem();
        checkBox_no->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_test_result ->setItem(i, 3, checkBox_no);

        QTableWidgetItem *checkBox_skip = new QTableWidgetItem();
        checkBox_skip->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_test_result ->setItem(i, 4, checkBox_skip);

        switch (MODEL_TSET_List[i].TEST_SIGNAL_IS_EXIT_OR_NOT)
        {
        case 0:
            ui->tableWidget_case_entry_test_result->item(i, 3)->setCheckState(Qt::Checked);
            break;
        case 1:
            ui->tableWidget_case_entry_test_result->item(i, 2)->setCheckState(Qt::Checked);
            break;
        case 2:
            ui->tableWidget_case_entry_test_result->item(i, 4)->setCheckState(Qt::Checked);
            break;
        default:
            ui->tableWidget_case_entry_test_result->item(i, 4)->setCheckState(Qt::Checked);
        }
    }
    init_case_entry_test_result_list_is_not_cell_change = false;
}

void Diagnosis_MainWindow::on_radioButton_select_test_result_model_clicked()//案例录入-测试结果选择-模型筛选
{
    user_or_model = "model";
    ui->lineEdit_case_entry_test_result_searching->clear();//清空搜索栏
    init_case_entry_test_list(diagnosis_model_name,"all",user_or_model,true);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_radioButton_select_test_result_user_clicked()//案例录入-测试结果选择-用户筛选
{
    user_or_model = "user";
    ui->lineEdit_case_entry_test_result_searching->clear();//清空搜索栏
    init_case_entry_test_list(diagnosis_model_name,"all",user_or_model,true);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_btn_case_entry_test_result_searching_clicked()//案例录入-测试结果选择-搜索
{
    QString fuzzy_search = ui->lineEdit_case_entry_test_result_searching->text();
    init_case_entry_test_list(diagnosis_model_name,fuzzy_search,user_or_model,true);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_tableWidget_case_entry_test_result_cellChanged(int row, int column)//案例录入-征兆信号选择操作数据库
{
    if(!init_case_entry_test_result_list_is_not_cell_change)
    {
        selected_test_and_state.row = row;
        selected_test_and_state.column = column;
        selected_test_and_state.TEST_NAME = ui->tableWidget_case_entry_test_result->item(row, 0)->text();
        selected_test_and_state.TEST_SIGNAL_IS_EXIT_OR_NOT = column-2;

        if(selected_test_and_state.column != 4)
            selected_test_and_state.have_test_selected = true;
        else
            selected_test_and_state.have_test_selected = false;

        QString fuzzy_search = ui->lineEdit_case_entry_test_result_searching->text();
        init_case_entry_test_list(diagnosis_model_name,fuzzy_search,user_or_model,true);//初始化测试选择列表

        init_case_entry_test_result_list_is_not_cell_change = true;
        ui->tableWidget_case_entry_test_result->item(row, 2)->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_test_result->item(row, 3)->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_test_result->item(row, 4)->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_test_result->item(row, column)->setCheckState(Qt::Checked);
        init_case_entry_test_result_list_is_not_cell_change = false;
    }
}

void Diagnosis_MainWindow::on_toolButton_case_entry_test_result_new_clicked()//故障测试新增
//This part is not complete ,the yse and on describe is not used，checksum code error
{
    dialog_case_entry_test_new *dlg=new dialog_case_entry_test_new(this);
    dlg->showNormal();
    dlg->setWindowTitle("请输入新增测试信息");
    dlg->setModal(true);

    QList<QString> list_tool;

    //查找TMATE数据库模型工具需求信息
    sql_prepare = QString("SELECT RESOURCE_NAME FROM MODEL_RESOURCES WHERE MODEL_NAME = '%1';").arg(diagnosis_model_name);

    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
        list_tool.append(qsQuery_TMATE_MDB.value(0).toString());

    connect(this,SIGNAL(send_the_ToolList_to_case_entry_test_new(QList<QString>)),dlg,SLOT(setText(QList<QString>)));
    send_the_ToolList_to_case_entry_test_new(list_tool);

    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        QString case_entry_test_name = dlg->get_lineEdit_case_entry_test_name();//获取测试名称
        QString case_entry_test_describe = dlg->get_textEdit_case_entry_test_describe();//获取测试描述
        QString case_entry_test_result_Yes_describe = dlg->get_lineEdit_case_entry_test_result_Yes_describe();//获取Yes结果描述
        QString case_entry_test_result_No_describe = dlg->get_lineEdit_case_entry_test_result_No_describe();//获取No结果描述
        QString case_entry_test_accessory_name = dlg->get_lineEdit_case_entry_test_accessory_name();//获取测试附件文件名称
        QList<QString> test_need_tool_list = dlg->get_listWidget_test_need_tool_list();//获取测试所需工具集合

        //qDebug()<<case_entry_test_name<<endl;
        //qDebug()<<case_entry_test_describe<<endl;
        //qDebug()<<case_entry_test_result_Yes_describe<<endl;
        //qDebug()<<case_entry_test_result_No_describe<<endl;
        //qDebug()<<case_entry_test_accessory_name<<endl;
        //qDebug()<<test_need_tool_list<<endl;

        //////////////////////////////////////////////////////////////////////////////////
        ////////////////////此区域为向数据库存储信息区域
        /// //////////////////////////////////////////////////////////////////////////////

        //生成唯一CASE_ENTRY_TEST_TID
        QString new_case_entry_TEST_TID = "case_entry_";
        QDateTime curDateTime=QDateTime::currentDateTime();
        new_case_entry_TEST_TID.append(curDateTime.toString("yyyyMMddhhmmss"));

        //将唯一TID，现象名称，现象描述插入CASE_ENTRY_TEST_PROPS表格
        sql_prepare = QString("INSERT INTO CASE_ENTRY_TEST_PROPS (TEST_TID, MODEL_NAME, TEST_NAME, TEST_PROCEDURE, TEST_TYPE) "
                              "VALUES ('%1', '%2', '%3', '%4', 1);")
                .arg(new_case_entry_TEST_TID).arg(diagnosis_model_name)
                .arg(case_entry_test_name).arg(case_entry_test_describe);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();

        //获取附件文件信息并存储
        if(case_entry_test_accessory_name!=nullptr)
        {//文件信息集定义
            typedef struct  {
                QString TID;//测试TID
                QString MODEL_NAME;//测试所属模型
                QString ID;//文件ID
                QString MEDIA_NAME;//文件名称
                QString IMAGE_TYPE;//文件类型
                QString CHECKSUM;//校验码
                long long int FILE_SIZE;//文件大小
            }StrFileData;
            StrFileData OneStrFileData;
            QStringList stringList_case_entry_accessory_name = case_entry_test_accessory_name.split("<DIV>");
            for(int i=0;i<stringList_case_entry_accessory_name.size();i++)
            {
                //获取测试TID
                OneStrFileData.TID = new_case_entry_TEST_TID;
                //获取测试所属模型
                OneStrFileData.MODEL_NAME = diagnosis_model_name;
                //获取文件ID
                QString File_ID = "case_entry_File_";
                QDateTime curDateTime=QDateTime::currentDateTime();
                File_ID.append(curDateTime.toString("yyyyMMddhhmmss"));
                OneStrFileData.ID = File_ID;
                //获取文件名称
                QStringList File_Name = stringList_case_entry_accessory_name[i].split("/");
                OneStrFileData.MEDIA_NAME = File_Name[File_Name.size()-1];
                //获取文件类型
                OneStrFileData.IMAGE_TYPE = "IMAGE";
                //获取文件大小
                QFile inImg(stringList_case_entry_accessory_name[i]);
                if(!inImg.open(QIODevice::ReadOnly))
                {
                    QMessageBox::warning(nullptr,"Error","Open Image File Failed");
                    return;
                }
                QByteArray inBytearray = inImg.readAll();
                //获取图片大小
                OneStrFileData.FILE_SIZE = inImg.size();
                //获取文件校验码
                //Checksum check;
                //unsigned short check_num = check.CheckSum((unsigned short*)(&inBytearray),(int)OneStrFileData.FILE_SIZE);
                OneStrFileData.CHECKSUM = OneStrFileData.ID;
                //将信息存储到数据库
                sql_prepare = QString("INSERT INTO TEST_MEDIA (TID, MODEL_NAME, ID, MEDIA_NAME, IMAGE_TYPE, CHECKSUM, FILE_SIZE) "
                                      "VALUES ('%1', '%2', '%3', '%4','%5', '%6', %7);")
                        .arg(OneStrFileData.TID).arg(OneStrFileData.MODEL_NAME).arg(OneStrFileData.ID)
                        .arg(OneStrFileData.MEDIA_NAME).arg(OneStrFileData.IMAGE_TYPE).arg(OneStrFileData.CHECKSUM)
                        .arg(OneStrFileData.FILE_SIZE);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.exec();

                sql_prepare = QString("INSERT INTO MULTIMEDIA(FILE_SIZE, CHECKSUM, IMAGE_DATA) "
                                      "VALUES(%1,:CHECKSUM,:IMAGE_DATA);").arg(OneStrFileData.FILE_SIZE);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.bindValue(":CHECKSUM",OneStrFileData.CHECKSUM);
                qsQuery_TMATE_MDB.bindValue(":IMAGE_DATA",inBytearray);
                qsQuery_TMATE_MDB.exec();
            }
        }

        //存储所需工具列表信息
        for(int i=0;i<test_need_tool_list.size();i++)
        {
            sql_prepare = QString("INSERT INTO TEST_RESOURCES (TEST_NAME, RESOURCE_NAME, MODEL_NAME) VALUES ('%1', '%2', '%3');")
                    .arg(case_entry_test_name).arg(test_need_tool_list[i]).arg(diagnosis_model_name);
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
        }
    }
    delete dlg; //删除对话框
    init_case_entry_test_list(diagnosis_model_name,"all","model",false);//初始化测试信号UI列表
    selected_test_and_state.have_test_selected = false;//默认没有测试被选中
}

void Diagnosis_MainWindow::save_case_entry_one_test_result_to_record()//将测试信息保存到诊断记录
{
    Matrix_D.one_test_cord.Diagnosis_test_name = selected_test_and_state.TEST_NAME;
    if(user_or_model == "user")
        Matrix_D.one_test_cord.recommend_or_self_selected = "自选用户测试";
    else
        Matrix_D.one_test_cord.recommend_or_self_selected = "自选模型测试";
    if( selected_test_and_state.column == 2)
        Matrix_D.one_test_cord.yes_or_no = "测试正常";
    if( selected_test_and_state.column == 3)
        Matrix_D.one_test_cord.yes_or_no = "测试异常";
    Matrix_D.diagnostic_record.list_Diagnosis_test_record.append(Matrix_D.one_test_cord);

    //将测试所需工具添加到工具表

    //查找TMATE数据库TEST_RESOURCES表所有测试所需资源信息

    sql_prepare = QString("SELECT RESOURCE_NAME FROM TEST_RESOURCES "
                          "WHERE TEST_NAME = '%1' AND MODEL_NAME = '%2';")
            .arg(Matrix_D.one_test_cord.Diagnosis_test_name).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        if(!Matrix_D.diagnostic_record.list_tool.contains(qsQuery_TMATE_MDB.value(0).toString()))
            Matrix_D.diagnostic_record.list_tool.append(qsQuery_TMATE_MDB.value(0).toString());
    }
}

void Diagnosis_MainWindow::on_toolButton_case_entry_test_result_next_clicked()//下一测试
{
    if(selected_test_and_state.have_test_selected)
    {
        if(ui->tableWidget_case_entry_test_result->item(selected_test_and_state.row, selected_test_and_state.column)->checkState() == Qt::Checked)
        {
            if(user_or_model == "user")
            {
                sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                        .arg(selected_test_and_state.TEST_SIGNAL_IS_EXIT_OR_NOT).arg(selected_test_and_state.TEST_NAME).arg(diagnosis_model_name);
            }
            else
            {
                sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                        .arg(selected_test_and_state.TEST_SIGNAL_IS_EXIT_OR_NOT).arg(selected_test_and_state.TEST_NAME).arg(diagnosis_model_name);
            }
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
            selected_test_and_state.have_test_selected = false;

            save_case_entry_one_test_result_to_record();//将测试信息保存到诊断记录
        }
    }
    else
    {
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请至少选择一个测试及结果"),QMessageBox::Yes);
        return;
    }

    ui->lineEdit_case_entry_test_result_searching->clear();//清空搜索栏
    init_case_entry_test_list(diagnosis_model_name,"all",user_or_model,true);//初始化测试选择列表
}

void Diagnosis_MainWindow::on_toolButton_case_entry_test_result_diagnosis_result_clicked()//诊断结论
{
    if(selected_test_and_state.have_test_selected)
    {
        if(ui->tableWidget_case_entry_test_result->item(selected_test_and_state.row, selected_test_and_state.column)->checkState() == Qt::Checked)
        {
            if(user_or_model == "user")
            {
                sql_prepare = QString("UPDATE CASE_ENTRY_TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                        .arg(selected_test_and_state.TEST_SIGNAL_IS_EXIT_OR_NOT).arg(selected_test_and_state.TEST_NAME).arg(diagnosis_model_name);
            }
            else
            {
                sql_prepare = QString("UPDATE TEST_PROPS SET TEST_SIGNAL_IS_EXIT_OR_NOT= %1 WHERE TEST_NAME='%2' AND MODEL_NAME = '%3';")
                        .arg(selected_test_and_state.TEST_SIGNAL_IS_EXIT_OR_NOT).arg(selected_test_and_state.TEST_NAME).arg(diagnosis_model_name);
            }
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
            selected_test_and_state.have_test_selected = false;

            save_case_entry_one_test_result_to_record();//将测试信息保存到诊断记录
        }
    }
    else
    {
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请至少选择一个测试及结果"),QMessageBox::Yes);
        return;
    }

    //操作数据库，将所有模块是否故障设为否
    sql_prepare = QString("UPDATE CASE_ENTRY_MODULE_PROPS SET IS_FAULT_MODULE = %1 WHERE MODEL_NAME = '%2';")
            .arg(false).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    sql_prepare = QString("UPDATE MODULE_PROPS SET IS_FAULT_MODULE = %1 WHERE MODEL_NAME = '%2';")
            .arg(false).arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    ui->stackedWidget_main->setCurrentIndex(15);
    ui->lineEdit_case_entry_fault_module_searching->clear();//清空搜索栏
    ui->radioButton_select_fault_module_model->setChecked(true);
    user_or_model = "model";
    init_case_entry_fault_module_list(diagnosis_model_name,"all","model");
}

/////////////////////////////////////////////////////////
///    \brief fault_module_select_UI          ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::init_case_entry_fault_module_list(QString model_name, QString fuzzy_search, QString user_or_model)//初始化案例录入故障模块选择UI列表
{
    init_case_entry_fault_module_list_is_not_cell_change = true;

    ui->tableWidget_case_entry_fault_module_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Fixed);//设置表格列宽随View变化
    ui->tableWidget_case_entry_fault_module_select->verticalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格行高随View变化
    ui->tableWidget_case_entry_fault_module_select->verticalHeader()->setMinimumSectionSize(50);
    ui->tableWidget_case_entry_fault_module_select->verticalHeader()->setSectionResizeMode(QHeaderView::Fixed);
    ui->tableWidget_case_entry_fault_module_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中

    //设置表格的默认的列数
    QStringList headerString;
    headerString << tr("  ") << tr("模块名称") << tr("部件号")<< tr("所属层级")<< tr("维修备注")<< tr("TID");
    ui->tableWidget_case_entry_fault_module_select->setColumnCount(headerString.count());//设置列数
    ui->tableWidget_case_entry_fault_module_select->setHorizontalHeaderLabels(headerString);//设置列标题

    ui->tableWidget_case_entry_fault_module_select->horizontalHeader()->setSectionResizeMode(1, QHeaderView::Stretch);
    ui->tableWidget_case_entry_fault_module_select->horizontalHeader()->setSectionResizeMode(4, QHeaderView::Stretch);

    ui->tableWidget_case_entry_fault_module_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
    ui->tableWidget_case_entry_fault_module_select->setStyleSheet(tableWidgetStyleSheet);//设置表格颜色

    ui->tableWidget_case_entry_fault_module_select->verticalScrollBar()->setStyleSheet(tableWidgetScrollBarStyleSheet);
    //设置表头
    ui->tableWidget_case_entry_fault_module_select->horizontalHeader()->setStyleSheet(tableWidgetHorizontalHeaderStyleSheet);
    ui->tableWidget_case_entry_fault_module_select->horizontalHeader()->setHighlightSections(false);//选择时表头不加粗
    ui->tableWidget_case_entry_fault_module_select->setFocusPolicy(Qt::NoFocus);


    //查询MODULE_TID,MODULE_NAME,MTTF等
    typedef struct  {
        QString MODULE_TID;//模块ID
        QString MODULE_NAME;//模块名称
        QString HIERARCHY_LABEL;//模块层级
        QString PART_NUM;//部件号
        QString REPAIR_NOTES;//维修说明
        bool isFauildModule;//是否是故障模块
        char m_padding [3];//字节对齐，去除警告
    }StrCaseEntryFaultModuleData;
    StrCaseEntryFaultModuleData OneCaseEntryFaultModuleData;

    QList<StrCaseEntryFaultModuleData> ListCaseEntryFaultModuleData;

    QString selected_table;
    if(user_or_model == "user")
        selected_table = "CASE_ENTRY_MODULE_PROPS";
    else
        selected_table = "MODULE_PROPS";

    if(fuzzy_search == "all")
    {
        sql_prepare = QString("SELECT MODULE_TID,MODULE_NAME,HIERARCHY_LABEL,PART_NUM,REPAIR_NOTES,IS_FAULT_MODULE FROM %1 "
                              " WHERE IS_LOWEST_HIERARCHY = 1 AND MODEL_NAME = '%2';").arg(selected_table).arg(model_name);
    }
    else
    {
        sql_prepare = QString("SELECT MODULE_TID,MODULE_NAME,HIERARCHY_LABEL,PART_NUM,REPAIR_NOTES,IS_FAULT_MODULE FROM %1 "
                              " WHERE IS_LOWEST_HIERARCHY = 1 AND MODEL_NAME = '%2' AND MODULE_NAME LIKE '%%3%';").arg(selected_table).arg(model_name).arg(fuzzy_search);
    }


    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        OneCaseEntryFaultModuleData.MODULE_TID = qsQuery_TMATE_MDB.value(0).toString();
        OneCaseEntryFaultModuleData.MODULE_NAME = qsQuery_TMATE_MDB.value(1).toString();
        OneCaseEntryFaultModuleData.HIERARCHY_LABEL = qsQuery_TMATE_MDB.value(2).toString();
        OneCaseEntryFaultModuleData.PART_NUM = qsQuery_TMATE_MDB.value(3).toString();
        OneCaseEntryFaultModuleData.REPAIR_NOTES = qsQuery_TMATE_MDB.value(4).toString().remove("<DIV>").remove("</DIV>").remove("</BR>").remove("</P>").remove("<P>").remove("&nbsp");
        OneCaseEntryFaultModuleData.REPAIR_NOTES.replace(QString("<BR>"), QString("\n"));
        while(OneCaseEntryFaultModuleData.REPAIR_NOTES.startsWith("\n")||OneCaseEntryFaultModuleData.REPAIR_NOTES.startsWith("\r"))
            OneCaseEntryFaultModuleData.REPAIR_NOTES.remove(0,2);

        OneCaseEntryFaultModuleData.isFauildModule = qsQuery_TMATE_MDB.value(5).toBool();
        ListCaseEntryFaultModuleData.append(OneCaseEntryFaultModuleData);
    }

    //设置表格的默认的行数
    ui->tableWidget_case_entry_fault_module_select->setRowCount(ListCaseEntryFaultModuleData.size());//设置默认的行数
    ui->tableWidget_case_entry_fault_module_select->verticalHeader()->hide();//隐藏行序号
    ui->tableWidget_case_entry_fault_module_select->hideColumn(5);//隐藏TID列

    //数据显示
    for(int i=0;i<ListCaseEntryFaultModuleData.size();i++)
    {
        QTableWidgetItem *checkBox_checked = new QTableWidgetItem();
        if(ListCaseEntryFaultModuleData[i].isFauildModule)
            checkBox_checked->setCheckState(Qt::Checked);
        else
            checkBox_checked->setCheckState(Qt::Unchecked);
        ui->tableWidget_case_entry_fault_module_select ->setItem(i, 0, checkBox_checked);

        ui->tableWidget_case_entry_fault_module_select->setItem(i,1,new QTableWidgetItem(ListCaseEntryFaultModuleData[i].MODULE_NAME));
        ui->tableWidget_case_entry_fault_module_select->setItem(i,2,new QTableWidgetItem(ListCaseEntryFaultModuleData[i].PART_NUM));
        ui->tableWidget_case_entry_fault_module_select->setItem(i,3,new QTableWidgetItem(ListCaseEntryFaultModuleData[i].HIERARCHY_LABEL));
        ui->tableWidget_case_entry_fault_module_select->setItem(i,4,new QTableWidgetItem(ListCaseEntryFaultModuleData[i].REPAIR_NOTES));
        ui->tableWidget_case_entry_fault_module_select->setItem(i,5,new QTableWidgetItem(ListCaseEntryFaultModuleData[i].MODULE_TID));

    }

    ui->tableWidget_case_entry_fault_module_select->resizeRowsToContents();

    //设置不可更改
    for(int i = 0; i<ui->tableWidget_case_entry_fault_module_select->rowCount();i++)
    {
        for(int j = 1; j<(ui->tableWidget_case_entry_fault_module_select->columnCount());j++)
            ui->tableWidget_case_entry_fault_module_select->item(i, j)->setFlags(Qt::NoItemFlags);
    }

    init_case_entry_fault_module_list_is_not_cell_change = false;

}

void Diagnosis_MainWindow::on_btn_case_entry_fault_module_searching_clicked()//故障模块选择搜索
{
    QString fuzzy_search = ui->lineEdit_case_entry_fault_module_searching->text();
    init_case_entry_fault_module_list(diagnosis_model_name,fuzzy_search,user_or_model);//初始化故障模块选择列表
}

void Diagnosis_MainWindow::on_radioButton_select_fault_module_model_clicked()//模型
{
    user_or_model = "model";
    ui->lineEdit_case_entry_fault_module_searching->clear();//清空搜索栏
    init_case_entry_fault_module_list(diagnosis_model_name,"all",user_or_model);//初始化故障模块选择列表
}

void Diagnosis_MainWindow::on_radioButton_select_fault_module_user_clicked()//用户
{
    user_or_model = "user";
    ui->lineEdit_case_entry_fault_module_searching->clear();//清空搜索栏
    init_case_entry_fault_module_list(diagnosis_model_name,"all",user_or_model);//初始化故障模块选择列表
}

void Diagnosis_MainWindow::on_tableWidget_case_entry_fault_module_select_cellChanged(int row, int column)//故障选择操作数据库
{
    if(!init_case_entry_fault_module_list_is_not_cell_change)
    {
        if(column == 0)
        {
            bool SIGN;
            QString cellchanged_module_name = ui->tableWidget_case_entry_fault_module_select->item(row, 1)->text();
            QString cellchanged_module_TID = ui->tableWidget_case_entry_fault_module_select->item(row, 5)->text();
            QString cellchanged_model_name = diagnosis_model_name;

            if(ui->tableWidget_case_entry_fault_module_select->item(row, 0)->checkState() == Qt::Checked) //选中
                SIGN = true;
            else
                SIGN = false;

            if(user_or_model == "user")
            {
                sql_prepare = QString("UPDATE CASE_ENTRY_MODULE_PROPS SET IS_FAULT_MODULE= %1 WHERE"
                                      " MODULE_NAME='%2' AND MODEL_NAME = '%3' AND MODULE_TID = '%4';")
                        .arg(SIGN).arg(cellchanged_module_name).arg(cellchanged_model_name).arg(cellchanged_module_TID);
            }
            else
            {
                sql_prepare = QString("UPDATE MODULE_PROPS SET IS_FAULT_MODULE= %1 WHERE"
                                      " MODULE_NAME='%2' AND MODEL_NAME = '%3' AND MODULE_TID = '%4';")
                        .arg(SIGN).arg(cellchanged_module_name).arg(cellchanged_model_name).arg(cellchanged_module_TID);
            }
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();
        }
    }
}

void Diagnosis_MainWindow::on_toolButton_case_entry_fault_module_select_new_clicked()//新增
//This part is not complete ,the yse and on describe is not used，checksum code error
{
    dialog_case_entry_failure_module *dlg=new dialog_case_entry_failure_module(this);
    dlg->showNormal();
    dlg->setWindowTitle("请输入新增模块信息");
    dlg->setModal(true);

    int ret=dlg->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        QString case_entry_module_name = dlg->get_lineEdit_case_entry_module_name();//获取模块名称
        QString case_entry_module_part = dlg->get_lineEdit_case_entry_module_part();//获取模块部件号
        QString case_entry_module_describe = dlg->get_textEdit_case_entry_module_describe();//获取模块描述
        QString case_entry_module_accessory_name = dlg->get_lineEdit_case_entry_module_accessory_name();//获取附件路径

        //////////////////////////////////////////////////////////////////////////////////
        ////////////////////此区域为向数据库存储信息区域
        /// //////////////////////////////////////////////////////////////////////////////

        //生成唯一CASE_ENTRY_MODULE_TID
        QString new_case_entry_MODULE_TID = "case_entry_module_";
        QDateTime curDateTime=QDateTime::currentDateTime();
        new_case_entry_MODULE_TID.append(curDateTime.toString("yyyyMMddhhmmss"));

        //将唯一TID，现象名称，现象描述插入CASE_ENTRY_MODULE_PROPS表格
        sql_prepare = QString("INSERT INTO CASE_ENTRY_MODULE_PROPS (MODULE_TID, MODEL_NAME, MODULE_NAME, PART_NUM, IS_LOWEST_HIERARCHY, REPAIR_NOTES) VALUES ('%1', '%2', '%3', '%4', %5, '%6');")
                .arg(new_case_entry_MODULE_TID).arg(diagnosis_model_name)
                .arg(case_entry_module_name).arg(case_entry_module_part).arg(1).arg(case_entry_module_describe);

        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();

        //获取附件文件信息并存储
        if(case_entry_module_name!=nullptr)
        {//文件信息集定义
            typedef struct  {
                QString TID;//模块TID
                QString MODEL_NAME;//模块所属模型
                QString ID;//文件ID
                QString MEDIA_NAME;//文件名称
                QString IMAGE_TYPE;//文件类型
                QString CHECKSUM;//校验码
                long long int FILE_SIZE;//文件大小
            }StrFileData;
            StrFileData OneStrFileData;
            QStringList stringList_case_entry_accessory_name = case_entry_module_name.split("<DIV>");
            for(int i=0;i<stringList_case_entry_accessory_name.size();i++)
            {
                //获取模块TID
                OneStrFileData.TID = new_case_entry_MODULE_TID;
                //获取模块所属模型
                OneStrFileData.MODEL_NAME = diagnosis_model_name;
                //获取文件ID
                QString File_ID = "case_entry_module_File_";
                QDateTime curDateTime=QDateTime::currentDateTime();
                File_ID.append(curDateTime.toString("yyyyMMddhhmmss"));
                OneStrFileData.ID = File_ID;
                //获取文件名称
                QStringList File_Name = stringList_case_entry_accessory_name[i].split("/");
                OneStrFileData.MEDIA_NAME = File_Name[File_Name.size()-1];
                //获取文件类型
                OneStrFileData.IMAGE_TYPE = "IMAGE";
                //获取文件大小
                QFile inImg(stringList_case_entry_accessory_name[i]);
                if(!inImg.open(QIODevice::ReadOnly))
                {
                    QMessageBox::warning(nullptr,"Error","Open Image File Failed");
                    return;
                }
                QByteArray inBytearray = inImg.readAll();
                //获取图片大小
                OneStrFileData.FILE_SIZE = inImg.size();
                //获取文件校验码
                //Checksum check;
                //unsigned short check_num = check.CheckSum((unsigned short*)(&inBytearray),(int)OneStrFileData.FILE_SIZE);
                OneStrFileData.CHECKSUM = OneStrFileData.ID;

                //将信息存储到数据库
                sql_prepare = QString("INSERT INTO MODULE_MEDIA (ID, TID, MODEL_NAME, MEDIA_NAME, IMAGE_TYPE, CHECKSUM, FILE_SIZE) "
                                      "VALUES ('%1', '%2', '%3', '%4','%5', '%6', %7);")
                        .arg(OneStrFileData.TID).arg(OneStrFileData.ID).arg(OneStrFileData.MODEL_NAME)
                        .arg(OneStrFileData.MEDIA_NAME).arg(OneStrFileData.IMAGE_TYPE).arg(OneStrFileData.CHECKSUM)
                        .arg(OneStrFileData.FILE_SIZE);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.exec();

                sql_prepare = QString("INSERT INTO MULTIMEDIA(FILE_SIZE, CHECKSUM, IMAGE_DATA) "
                                      "VALUES(%1,:CHECKSUM,:IMAGE_DATA);").arg(OneStrFileData.FILE_SIZE);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.bindValue(":CHECKSUM",OneStrFileData.CHECKSUM);
                qsQuery_TMATE_MDB.bindValue(":IMAGE_DATA",inBytearray);
                qsQuery_TMATE_MDB.exec();
            }
        }
    }
    delete dlg; //删除对话框

    QString fuzzy_search = ui->lineEdit_case_entry_fault_module_searching->text();
    init_case_entry_fault_module_list(diagnosis_model_name,fuzzy_search,user_or_model);//初始化故障模块选择列表
}

void Diagnosis_MainWindow::on_toolButton_case_entry_fault_module_select_next_clicked()//下一步
{
    //存储故障模块
    QList <QString> fault_module_list;
    sql_prepare = QString("SELECT MODULE_NAME FROM CASE_ENTRY_MODULE_PROPS  "
                          "WHERE IS_FAULT_MODULE = true AND MODEL_NAME = '%1';").arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
        fault_module_list.append(qsQuery_TMATE_MDB.value(0).toString());

    sql_prepare = QString("SELECT MODULE_NAME FROM MODULE_PROPS  "
                          "WHERE IS_FAULT_MODULE = true AND MODEL_NAME = '%1';").arg(diagnosis_model_name);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
        fault_module_list.append(qsQuery_TMATE_MDB.value(0).toString());

    if(!fault_module_list.size())
        Matrix_D.diagnostic_record.fault_module = "系统正常";
    else
        for(int i=0;i<fault_module_list.size();i++)
        {
            Matrix_D.diagnostic_record.fault_module.append(fault_module_list[i]);
            Matrix_D.diagnostic_record.fault_module.append(";");
        }
    Matrix_D.diagnostic_record.user_name =LoginAccount.Operating_user;
    Matrix_D.diagnostic_record.maintain_company = LoginAccount.User_department;
    Matrix_D.diagnostic_record.if_solved_or_not = true;

    //跳转并初始化反馈界面
    ui->dateEdit_case_entry_diagnosis_Date->setDate(QDate::currentDate());;
    ui->label_case_entry_user_name->setText(Matrix_D.diagnostic_record.user_name);
    ui->lineEdit_case_entry_maintain_company->setText(Matrix_D.diagnostic_record.maintain_company);
    ui->lineEdit_case_entry_maintain_company->setReadOnly(true);

    ui->label_case_entry_equipment_name->setText(diagnosis_model_name);
    ui->lineEditcase_entry_boat_number->clear();
    ui->dateTimeEdit_case_entry_begin_datetime->setDateTime(QDateTime::currentDateTime());;
    ui->dateTimeEdit_case_entry_finish_datetime->setDateTime(QDateTime::currentDateTime());;
    ui->QTextEdit_case_entry_information_feedback_text->clear();
    ui->radioButton_case_entry_problem_is_not_solved->setChecked(false);
    ui->radioButton_case_entry_problem_is_solved->setChecked(true);

    ui->stackedWidget_main->setCurrentIndex(16);
}

/////////////////////////////////////////////////////////
///    \brief Feedback and submission          ///
/////////////////////////////////////////////////////////

void Diagnosis_MainWindow::on_toolButton_case_entry_information_feedback_submit_clicked()//提交记录
{
    Matrix_D.diagnostic_record.DIAGNOSTIC_ID = Matrix_D.diagnostic_record.DIAGNOSTIC_ID = Matrix_D.diagnostic_record.start_time.toString("yyyy-MM-dd hh:mm:ss").remove("-").remove(":").remove(" ");;//诊断编号
    Matrix_D.diagnostic_record.start_time = ui->dateTimeEdit_case_entry_begin_datetime->dateTime();//诊断开始时间
    Matrix_D.diagnostic_record.finish_time = ui->dateTimeEdit_case_entry_finish_datetime->dateTime();//诊断结束时间
    Matrix_D.diagnostic_record.Diagnosis_Date = ui->dateEdit_case_entry_diagnosis_Date->date();//检修日期
    Matrix_D.diagnostic_record.feedback_text = ui->QTextEdit_case_entry_information_feedback_text->toPlainText();//诊断留言
    Matrix_D.diagnostic_record.maintain_company = ui->lineEdit_case_entry_maintain_company->text();//维修单位
    Matrix_D.diagnostic_record.boat_number = ui->lineEditcase_entry_boat_number->text();//舰艇舷号
    //保存到数据库

    //向记录总表添加信息
    sql_prepare = QString("INSERT INTO DIAGNOSTIC_RECORD_LIST (DIAGNOSTIC_ID,start_time,finish_time,"
                          "Diagnosis_Date,feedback_text,user_name,maintain_company,equipment_name,boat_number,"
                          "if_solved_or_not,fault_phenomenon,fault_module,advance_omen_test,Is_artificial_cord)"
                          "VALUES ('%1','%2','%3','%4','%5','%6','%7','%8','%9','%10','%11','%12','%13','%14');")
            .arg(Matrix_D.diagnostic_record.DIAGNOSTIC_ID)
            .arg(Matrix_D.diagnostic_record.start_time.toString("yyyy-MM-dd hh:mm:ss"))
            .arg(Matrix_D.diagnostic_record.finish_time.toString("yyyy-MM-dd hh:mm:ss"))
            .arg(Matrix_D.diagnostic_record.Diagnosis_Date.toString("yyyy-MM-dd"))
            .arg(Matrix_D.diagnostic_record.feedback_text)
            .arg(Matrix_D.diagnostic_record.user_name)
            .arg(Matrix_D.diagnostic_record.maintain_company)
            .arg(Matrix_D.diagnostic_record.equipment_name)
            .arg(Matrix_D.diagnostic_record.boat_number)
            .arg(Matrix_D.diagnostic_record.if_solved_or_not)
            .arg(Matrix_D.diagnostic_record.fault_phenomenon)
            .arg(Matrix_D.diagnostic_record.fault_module)
            .arg(Matrix_D.diagnostic_record.advance_omen_test)
            .arg(true);

    qsQuery_TMATE_MDB.prepare(sql_prepare);
    qsQuery_TMATE_MDB.exec();

    //向诊断过程表添加信息
    for(int i=0;i<Matrix_D.diagnostic_record.list_Diagnosis_test_record.size();i++)
    {
        sql_prepare = QString("INSERT INTO DIAGNOSTIC_TEST_PROCESS_RECORD (TEST_ORDER_ID,DIAGNOSTIC_ID,Diagnosis_test_name,"
                              "recommend_or_self_selected,yes_or_no)"
                              "VALUES ('%1','%2','%3','%4','%5');")
                .arg(i+1).arg(Matrix_D.diagnostic_record.DIAGNOSTIC_ID)
                .arg(Matrix_D.diagnostic_record.list_Diagnosis_test_record[i].Diagnosis_test_name)
                .arg(Matrix_D.diagnostic_record.list_Diagnosis_test_record[i].recommend_or_self_selected)
                .arg(Matrix_D.diagnostic_record.list_Diagnosis_test_record[i].yes_or_no);

        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }

    //向工具表添加信息
    for(int i=0;i<Matrix_D.diagnostic_record.list_tool.size();i++)
    {
        sql_prepare = QString("INSERT INTO DIAGNOSTIC_TOOL_RECORD (DIAGNOSTIC_ID,TOOL)"
                              "VALUES ('%1','%2');")
                .arg(Matrix_D.diagnostic_record.DIAGNOSTIC_ID)
                .arg(Matrix_D.diagnostic_record.list_tool[i]);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
    }

    QMessageBox messageBox(QMessageBox::NoIcon,
                           "Message", "诊断记录已保存",
                           QMessageBox::Yes); ;
    int result=messageBox.exec();
    //跳转到记录查询界面
    switch (result)
    {
    case QMessageBox::Yes:
    {
        ui->stackedWidget_main->setCurrentIndex(7);

        hide_unresolved_records = false;//是否隐藏未解决记录
        hide_solved_records = false;//是否隐藏已解决记录

        QDateTime startDate(QDate(2001, 1, 1), QTime(0, 0, 0));
        QDateTime finishDate(QDate(2100, 1, 1), QTime(0, 0, 0));
        ui->checkBox_hide_solved_records->setCheckState(Qt::Unchecked);
        ui->checkBox_hide_unresolved_records->setCheckState(Qt::Unchecked);
        ui->lineEdit_record_query_user_name->clear();
        ui->lineEdit_record_query_module_name->clear();
        ui->lineEdit_record_query_fault_phenomenon->clear();
        ui->lineEdit_record_query_model_name->clear();
        ui->lineEdit_record_query_boat_number->clear();
        ui->dateTimeEdit_record_query_start_time->setDateTime(startDate);
        ui->dateTimeEdit_query_finish_time->setDateTime(finishDate);
        init_diagnosis_record_query_list();
    }
        break;
    default:
    {
        ui->stackedWidget_main->setCurrentIndex(7);

        hide_unresolved_records = false;//是否隐藏未解决记录
        hide_solved_records = false;//是否隐藏已解决记录

        QDateTime startDate(QDate(2001, 1, 1), QTime(0, 0, 0));
        QDateTime finishDate(QDate(2100, 1, 1), QTime(0, 0, 0));
        ui->checkBox_hide_solved_records->setCheckState(Qt::Unchecked);
        ui->checkBox_hide_unresolved_records->setCheckState(Qt::Unchecked);
        ui->lineEdit_record_query_user_name->clear();
        ui->lineEdit_record_query_module_name->clear();
        ui->lineEdit_record_query_fault_phenomenon->clear();
        ui->lineEdit_record_query_model_name->clear();
        ui->lineEdit_record_query_boat_number->clear();
        ui->dateTimeEdit_record_query_start_time->setDateTime(startDate);
        ui->dateTimeEdit_query_finish_time->setDateTime(finishDate);
        init_diagnosis_record_query_list();
    }
        break;
    }
}

void Diagnosis_MainWindow::on_radioButton_case_entry_problem_is_solved_clicked()
{
    Matrix_D.diagnostic_record.if_solved_or_not = true;
}

void Diagnosis_MainWindow::on_radioButton_case_entry_problem_is_not_solved_clicked()
{
    Matrix_D.diagnostic_record.if_solved_or_not = false;
}

void Diagnosis_MainWindow::on_btn_add_account_clicked()
{
    mpShadeWindow->setGeometry(0, 0, this->width(), this->height());
    mpShadeWindow->show();//遮罩效果

    //模态对话框，动态创建，用过后删除
    add_new_account    *add_new_account_view=new add_new_account(this); //创建对话框
    Qt::WindowFlags    flags=add_new_account_view->windowFlags();
    add_new_account_view->setWindowFlags(flags | Qt::MSWindowsFixedSizeDialogHint); //设置对话框固定大小

    int ret=add_new_account_view->exec();// 以模态方式显示对话框
    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
    {
        qsQuery_TMATE_MDB.prepare("INSERT INTO ACCOUNT (USER,PASSWORD,DEPAERMENT,LIMIT)"
                                  " VALUES (:USER,:PASSWORD,:DEPAERMENT,:LIMIT)");
        qsQuery_TMATE_MDB.bindValue(":USER",add_new_account_view->get_m_user());
        qsQuery_TMATE_MDB.bindValue(":PASSWORD",add_new_account_view->get_m_passwords());
        qsQuery_TMATE_MDB.bindValue(":DEPAERMENT",add_new_account_view->get_m_department());
        qsQuery_TMATE_MDB.bindValue(":LIMIT",add_new_account_view->get_m_limit());
        qsQuery_TMATE_MDB.exec();

        QString dlgTitle="注册账号";
        QString strInfo=QString::asprintf("注册成功！");
        QMessageBox::information(this, dlgTitle, strInfo,
                                 QMessageBox::Ok,QMessageBox::NoButton);
    }
    delete add_new_account_view; //删除对话框
    mpShadeWindow->hide();//遮罩效果取消
    InitAccountManage();
}

void Diagnosis_MainWindow::on_pushButton_delete_account_clicked()
{
    int curRow = ui->tableWidget_account_login_record->currentRow();
    QString User = ui->tableWidget_account_login_record->item(curRow,1)->text();//获取当前名称
    //是否选择了模型
    if(User == nullptr){
        QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("请先选择要删除的账户"),QMessageBox::Yes);
        return;}
    //确认是否删除
    QMessageBox::StandardButton defaultBtn=QMessageBox::NoButton;
    QMessageBox::StandardButton result;
    result=QMessageBox::warning(this,QString::fromLocal8Bit("Warning"),QString::fromLocal8Bit("是否确认删除该账户?"),
                                QMessageBox::Yes|QMessageBox::No,defaultBtn);
    if(result==QMessageBox::Yes)
    {

        sql_prepare = QString("DELETE FROM ACCOUNT WHERE USER = '%1';").arg(User);
        if(qsQuery_TMATE_MDB.exec(sql_prepare))
            QMessageBox::about(this,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("账户已删除"));
        else
            QMessageBox::about(this,QString::fromLocal8Bit("消息框"),QString::fromLocal8Bit("删除失败"));
        InitAccountManage();
    }
}

void Diagnosis_MainWindow::on_pushButton_change_password_clicked()
{
    int curRow = ui->tableWidget_account_login_record->currentRow();
    QString User = ui->tableWidget_account_login_record->item(curRow,1)->text();//获取当前名称

    QString original_password;//原始密码
    QString New_password_1;//第一次更改密码
    QString New_password_2;//第二次更改密码

    QString dlgTitle="修改密码";
    QString txtLabel_1="请输入原始密码:";
    QString defaultInput="";
    QLineEdit::EchoMode echoMode=QLineEdit::Password;//密码输入
    bool ok=false;
    QString text = QInputDialog::getText(this, dlgTitle,txtLabel_1, echoMode,defaultInput, &ok);
    if (ok)
    {
        //查询数据库对应信息
        sql_prepare=QString::asprintf("SELECT PASSWORD FROM ACCOUNT WHERE USER = '%1'").arg(User);
        qsQuery_TMATE_MDB.prepare(sql_prepare);
        qsQuery_TMATE_MDB.exec();
        while (qsQuery_TMATE_MDB.next())
        {
            original_password = qsQuery_TMATE_MDB.value(0).toString();//原始密码
        }
        text = encrypt(text);

        if( text == original_password)
        {
            QString txtLabel_2="请输入修改密码:";
            bool ok=false;
            New_password_1 = QInputDialog::getText(this, dlgTitle,txtLabel_2, echoMode,defaultInput, &ok);
            if (ok)
            {
                QString txtLabel_3="请再次输入修改密码:";
                bool ok=false;
                New_password_2 = QInputDialog::getText(this, dlgTitle,txtLabel_3, echoMode,defaultInput, &ok);
                if (ok)
                {
                    if( New_password_1 == New_password_2)
                    {
                        New_password_2 = encrypt(New_password_2);

                        sql_prepare=QString::asprintf("UPDATE ACCOUNT SET PASSWORD =  '%1' WHERE USER = '%2' ")
                                .arg(New_password_2).arg(User);
                        qsQuery_TMATE_MDB.prepare(sql_prepare);
                        qsQuery_TMATE_MDB.exec();

                        QString dlgTitle="提示";
                        QString strInfo="密码修改成功";
                        QMessageBox::warning(this, dlgTitle, strInfo);
                    }
                    else
                    {
                        {
                            QString dlgTitle="warning";
                            QString strInfo="输入密码不一致";
                            QMessageBox::warning(this, dlgTitle, strInfo);
                        }
                    }
                }
            }
        }
        else
        {
            QString dlgTitle="warning";
            QString strInfo="原始密码错误";
            QMessageBox::warning(this, dlgTitle, strInfo);
        }
    }
    InitAccountManage();//账号管理表显示更新
}

void Diagnosis_MainWindow::on_pushButton_change_permission_clicked()
{
    int curRow = ui->tableWidget_account_login_record->currentRow();
    QString User = ui->tableWidget_account_login_record->item(curRow,1)->text();//获取当前名称
    QString UserLimit = ui->tableWidget_account_login_record->item(curRow,3)->text();//获取当前权限

    QDialog *dialogChangeLimit =new QDialog();
    dialogChangeLimit->setWindowTitle("修改用户权限");
    dialogChangeLimit->setMinimumSize(QSize(250,100));

    QFormLayout *formlayoutEnterUsernameAndPassword = new QFormLayout(dialogChangeLimit);

    QLabel *lineEditUserName = new QLabel(dialogChangeLimit);
    lineEditUserName->setText(User);

    QComboBox *Limit = new QComboBox();
    QStringList LimitGrade = {"管理员","军官","士兵"};
    Limit->addItems(LimitGrade);//密码输入

    QHBoxLayout *layout = new QHBoxLayout(nullptr);
    QPushButton *pushbuttonOK = new QPushButton(dialogChangeLimit);
    pushbuttonOK->setText("确认");
    QPushButton *pushbuttonCancel = new QPushButton(dialogChangeLimit);
    pushbuttonCancel->setText("取消");
    layout->addWidget(pushbuttonOK);
    layout->addWidget(pushbuttonCancel);

    formlayoutEnterUsernameAndPassword->addRow("用户名:", lineEditUserName);

    formlayoutEnterUsernameAndPassword->addRow("权  限:", Limit);
    formlayoutEnterUsernameAndPassword->addRow(layout);
    Limit->setCurrentText(UserLimit);
    QObject::connect(pushbuttonOK,SIGNAL(clicked()),dialogChangeLimit,SLOT(accept()));
    QObject::connect(pushbuttonCancel,SIGNAL(clicked()),dialogChangeLimit,SLOT(close()));

    if (dialogChangeLimit->exec()==QDialog::Accepted)
    {
        if(UserLimit == "管理员")
        {
            //判断是否是数据库内的账号

            int Num = 0;
            sql_prepare = QString("SELECT COUNT(*) FROM ACCOUNT WHERE USER = '%1';").arg(LoginAccount.Operating_user);
            qsQuery_TMATE_MDB.exec(sql_prepare);
            while(qsQuery_TMATE_MDB.next())
                Num = qsQuery_TMATE_MDB.value(0).toInt();
            if(Num)
            {
                QString dlgTitle="warning";
                QString strInfo="非超级用户无法修改管理员权限";
                QMessageBox::warning(this, dlgTitle, strInfo);
            }
            else
            {
                sql_prepare=QString::asprintf("UPDATE ACCOUNT SET LIMIT =  %1 WHERE USER = '%2' ")
                        .arg(Limit->currentIndex()).arg(User);
                qsQuery_TMATE_MDB.prepare(sql_prepare);
                qsQuery_TMATE_MDB.exec();

                QString dlgTitle="提示";
                QString strInfo="权限修改成功";
                QMessageBox::warning(this, dlgTitle, strInfo);

                InitAccountManage();//账号管理表显示更新
            }
        }
        else
        {
            sql_prepare=QString::asprintf("UPDATE ACCOUNT SET LIMIT =  %1 WHERE USER = '%2' ")
                    .arg(Limit->currentIndex()).arg(User);
            qsQuery_TMATE_MDB.prepare(sql_prepare);
            qsQuery_TMATE_MDB.exec();

            QString dlgTitle="提示";
            QString strInfo="权限修改成功";
            QMessageBox::warning(this, dlgTitle, strInfo);

            InitAccountManage();//账号管理表显示更新
        }
    }
    delete layout;
    delete dialogChangeLimit;
}

/***********************************************************************************************************************************/
/**************************************************左侧功能按钮****************************************************************/
/***********************************************************************************************************************************/
void Diagnosis_MainWindow::on_toolButton_clicked()//重新诊断按钮
{
    //清空案例记录
    Matrix_D.diagnostic_record.DIAGNOSTIC_ID = "";//诊断编号
    Matrix_D.diagnostic_record.start_time = QDateTime::currentDateTime();//诊断开始时间//在点击诊断时初始化
    Matrix_D.diagnostic_record.finish_time = QDateTime::currentDateTime();//诊断结束时间//在诊断反馈界面时初始化
    Matrix_D.diagnostic_record.Diagnosis_Date = QDate::currentDate();//检修日期//在点击诊断时初始化
    Matrix_D.diagnostic_record.feedback_text = "";//诊断留言//点击提交记录时初始化
    Matrix_D.diagnostic_record.user_name = "";//用户名称//在诊断反馈界面初始化
    Matrix_D.diagnostic_record.maintain_company = "";//维修单位//在诊断反馈界面初始化
    Matrix_D.diagnostic_record.equipment_name = "";//装备名称//在诊断反馈界面初始化
    Matrix_D.diagnostic_record.boat_number = "";//舰艇舷号//点击提交记录时初始化
    Matrix_D.diagnostic_record.if_solved_or_not = true;//是否解决//在诊断反馈界面初始化
    Matrix_D.diagnostic_record.fault_phenomenon = "";//故障现象//在初始化条件D矩阵时初始化
    Matrix_D.diagnostic_record.fault_module = "";//诊断故障模块//在结果界面初始化
    Matrix_D.diagnostic_record.list_tool.clear();//工具集合//初始化条件D矩阵时初始化
    Matrix_D.diagnostic_record.advance_omen_test = "";//预先征兆的名称//初始化条件D矩阵时初始化
    Matrix_D.diagnostic_record.list_Diagnosis_test_record.clear();//诊断测试记录//在点击诊断时初始化

    setWindowTitle("设备故障诊断系统");
    ui->stackedWidget_main->setCurrentIndex(0);

    ui->Display_menu_bar->trigger();
    hide_menu_bar();
    init_model_list();//初始化模型列表
}

void Diagnosis_MainWindow::on_toolButton_8_clicked()//结束退出按钮
{
    this->close();
}

void Diagnosis_MainWindow::on_toolButton_4_clicked()//记录查询按钮
{
    ui->stackedWidget_main->setCurrentIndex(7);

    hide_unresolved_records = false;//是否隐藏未解决记录
    hide_solved_records = false;//是否隐藏已解决记录

    QDateTime startDate(QDate(2001, 1, 1), QTime(0, 0, 0));
    QDateTime finishDate(QDate(2100, 1, 1), QTime(0, 0, 0));
    ui->checkBox_hide_solved_records->setCheckState(Qt::Unchecked);
    ui->checkBox_hide_unresolved_records->setCheckState(Qt::Unchecked);
    ui->lineEdit_record_query_user_name->clear();
    ui->lineEdit_record_query_module_name->clear();
    ui->lineEdit_record_query_fault_phenomenon->clear();
    ui->lineEdit_record_query_model_name->clear();
    ui->lineEdit_record_query_boat_number->clear();
    ui->dateTimeEdit_record_query_start_time->setDateTime(startDate);
    ui->dateTimeEdit_query_finish_time->setDateTime(finishDate);

    ui->Display_menu_bar->trigger();
    hide_menu_bar();
    init_diagnosis_record_query_list();
}

void Diagnosis_MainWindow::on_toolButton_6_clicked()//统计预测按钮
{
    ui->Display_menu_bar->trigger();
    hide_menu_bar();
    ui->stackedWidget_main->setCurrentIndex(8);
    iniBarChart();//初始化柱状图
    QString boatNumber = "";
    QString Qstring_start_Time = "2000-01-01 00:00:00";
    QDateTime start_Time = QDateTime::fromString(Qstring_start_Time, "yyyy-MM-dd hh:mm:ss");
    QDateTime finish_Time = QDateTime::currentDateTime();//获取系统现在的时间
    ui->lineEdit_record_query_boat_number_2->clear();
    ui->dateTimeEdit_record_query_start_time_2->setDateTime(start_Time);
    ui->dateTimeEdit_query_finish_time_2->setDateTime(finish_Time);
    redrawBarChart(boatNumber,start_Time,finish_Time);//重绘预测树状图
}

void Diagnosis_MainWindow::on_toolButton_7_clicked()//用户管理
{
    if(LoginAccount.Operating_limit==0)
    {
        ui->stackedWidget_main->setCurrentIndex(17);
        InitAccountManage();
    }

    else
        QMessageBox::warning(this, "错误提示", "您没有用户管理权限");
}

void Diagnosis_MainWindow::on_toolButton_3_clicked()//案例录入
{
    //清空案例记录
    Matrix_D.diagnostic_record.equipment_name = "";//装备名称//在案例录入-模型选择确认时初始化

    Matrix_D.diagnostic_record.advance_omen_test = "";//预先征兆的名称//在案例录入-征召选择确认时初始化
    Matrix_D.diagnostic_record.fault_phenomenon = "";//故障现象//在案例录入-征召选择确认时初始化

    Matrix_D.diagnostic_record.list_Diagnosis_test_record.clear();//诊断测试记录//在例录入-选择下一测试或跳转诊断结论时初始化
    Matrix_D.diagnostic_record.list_tool.clear();//工具集合//随测试初始化

    Matrix_D.diagnostic_record.fault_module = "";//诊断故障模块//在故障模块确定点击下一步时初始化
    Matrix_D.diagnostic_record.user_name = "";//用户名称//在故障模块确定点击下一步时初始化
    Matrix_D.diagnostic_record.if_solved_or_not = true;//是否解决//在故障模块确定点击下一步时初始化并随点击事件改变

    Matrix_D.diagnostic_record.DIAGNOSTIC_ID = "";//诊断编号//在反馈提交初始化
    Matrix_D.diagnostic_record.start_time = QDateTime::currentDateTime();//诊断开始时间//在反馈提交初始化
    Matrix_D.diagnostic_record.finish_time = QDateTime::currentDateTime();//诊断结束时间//在反馈提交初始化
    Matrix_D.diagnostic_record.Diagnosis_Date = QDate::currentDate();//检修日期//在反馈提交初始化
    Matrix_D.diagnostic_record.feedback_text = "";//诊断留言//在反馈提交初始化
    Matrix_D.diagnostic_record.maintain_company = "";//维修单位//在反馈提交初始化
    Matrix_D.diagnostic_record.boat_number = "";//舰艇舷号//在反馈提交初始化



    //跳转并初始化界面
    ui->stackedWidget_main->setCurrentIndex(12);
    ui->Display_menu_bar->trigger();
    hide_menu_bar();
    init_case_entry_model_list();
    /*

//    dialog_case_entry_failure_module *dlg=new dialog_case_entry_failure_module(this);
//    dlg->showNormal();
//    dlg->setWindowTitle("请输入故障模块信息");
//    dlg->setModal(true);
//    QList<QString> list_test;

////    for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
////    {
////        if(Matrix_D.list_TEST_DATA[i].sign_test)
////            list_test.append(Matrix_D.list_TEST_DATA[i].TEST_NAME);
////    }

////    connect(this,SIGNAL(send_the_Testlist_to_select_another_test(QList<QString>)),dlg,SLOT(setText(QList<QString>)));
////    send_the_Testlist_to_select_another_test(list_test);

//    int ret=dlg->exec();// 以模态方式显示对话框
//    if (ret==QDialog::Accepted) //OK键被按下,对话框关闭
//    {
////        QString test_name = dlg->get_test_name();

////        Matrix_D.one_test_cord.Diagnosis_test_name = test_name;
////        Matrix_D.one_test_cord.recommend_or_self_selected = "自选测试";
////        Matrix_D.one_test_cord.yes_or_no = "测试正常";
////        Matrix_D.diagnostic_record.list_Diagnosis_test_record.append(Matrix_D.one_test_cord);

////        QString test_TID;
////        for(int i=0;i<Matrix_D.list_TEST_DATA.size();i++)
////        {
////            if(Matrix_D.list_TEST_DATA[i].sign_test)
////            {
////                if(test_name == Matrix_D.list_TEST_DATA[i].TEST_NAME)
////                    test_TID = Matrix_D.list_TEST_DATA[i].TEST_TID;
////            }
////        }
////        //更新诊断界面UI
////        show_now_test_data_to_UI(test_TID);
//    }
//    delete dlg; //删除对话框
*/
}

QString Diagnosis_MainWindow::encrypt(const QString &str)
{ //字符串MD5算法加密
    QByteArray btArray;

    btArray.append(str);//加入原始字符串

    QCryptographicHash hash(QCryptographicHash::Md5);  //Md5加密算法

    hash.addData(btArray);  //添加数据到加密哈希值

    QByteArray resultArray =hash.result();  //返回最终的哈希值

    QString md5 =resultArray.toHex();//转换为16进制字符串

    return  md5;
}

void Diagnosis_MainWindow::on_Display_menu_bar_triggered(bool checked)
{
    if(checked)
        show_menu_bar();
    else
        hide_menu_bar();
}

/***********************************************************************************************************************************/
/**************************************************上侧功能按钮****************************************************************/
/***********************************************************************************************************************************/

void Diagnosis_MainWindow::on_electronic_manual_triggered()//电子手册按钮
{
    QProcess *helpProcess = new QProcess(this);
    QString model_help = QString("C:/MDB/'%1'.CHM").arg(diagnosis_model_name);
    QDir dir(model_help);
    QStringList argument_first;
    if(dir.exists())
        argument_first.append(model_help);//相对路径
    else
        argument_first.append("C:/MDB/help.CHM");//相对路径
    helpProcess->start("hh.exe",argument_first);
}

/***********************************************************************************************************************************/
/**************************************************弃用代码区****************************************************************/
/***********************************************************************************************************************************/

/*
//    QPixmap label_test_module_image(":/new/prefix1/Diagnosis_Image/module_picture.jpg");
//    ui->label_test_module_image->setPixmap(label_test_module_image);
//    ui->label_test_module_image->resize(label_test_module_image.width(),label_test_module_image.height());

//    QImage* label_test_file=new QImage;
//    label_test_file->load(":/new/prefix1/Diagnosis_Image/test_picture.jpg");
//    ui->label_test_file->setPixmap(QPixmap::fromImage(*label_test_file));
*/

/*    //基于已发现现象简化D矩阵
    QList<QString> Found_fault;//创建已发现故障现象列表
    for(int i=0;i<Matrix_D.list_Signal_DATA.size();i++)
    {
        if(Matrix_D.list_Signal_DATA[i].signal_is_exit)
        {
            Found_fault.append(Matrix_D.list_Signal_DATA[i].SIGNAL_NAME);
        }
    }
    //qDebug()<<Found_fault;

    if(Found_fault.size())
    {
        for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();)
        {
            bool Module_may_fail = false;
            for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals.size();j++)
            {
                if(Found_fault.contains(Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals[j]))
                {
                    Module_may_fail = true;
                }
            }
            if(Module_may_fail)
                i++;
            if(!Module_may_fail)
                Matrix_D.delete_one_module_Column(i);//删除D矩阵第Num列,同时删除模块集信息
        }
    }*/

/*
void Diagnosis_MainWindow::init_the_signal_message(QString selected_model)//初始化信号集
{
    Matrix_D.list_Signal_DATA.clear();
    sql_prepare = QString("SELECT  DISTINCT SIGNAL_NAME FROM MODULE_SIGNALS WHERE  MODEL_NAME = '%1';").arg(selected_model);
    qsQuery_TMATE_MDB.exec(sql_prepare);
    while(qsQuery_TMATE_MDB.next())
    {
        Matrix_D.OneSignalData.SIGNAL_NAME = qsQuery_TMATE_MDB.value(0).toString();
        Matrix_D.OneSignalData.signal_is_exit = false;
        Matrix_D.list_Signal_DATA.append(Matrix_D.OneSignalData);
        //qDebug() << OneSignalData.SIGNAL_NAME<<OneSignalData.signal_is_not_exit;
    }
}

void Diagnosis_MainWindow::init_condition_signal_message(QString selected_model)//初始化配置后的信号集
{
}
*/

/*
//    init_fault_list(diagnosis_model_name);//初始化故障列表


//void Diagnosis_MainWindow::on_toolButton_select_ratio_last_clicked()//偏好选择上一步按钮,至故障选择界面
//{
////    ui->stackedWidget_main->setCurrentIndex(2);
////    init_fault_list(diagnosis_model_name);//初始化故障列表
////    init_the_signal_message(diagnosis_model_name);//初始化信号集
//}

//void Diagnosis_MainWindow::init_fault_list(QString model_name)//初始化故障列表
//{
//    init_fault_list_is_not_cell_change = true;
//    ui->tableWidget_fault_select->verticalHeader()->setDefaultSectionSize(50);//设置默认行高
//    ui->tableWidget_fault_select->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);//设置表格列宽随View变化
//    ui->tableWidget_fault_select->setSelectionBehavior(QAbstractItemView::SelectRows);//设置仅行选中
//    //设置表格的默认的列数
//    QStringList headerString;
//    headerString << tr("模块归属链") << tr("故障信号名称") << tr("是否有故障");
//    ui->tableWidget_fault_select->setColumnCount(headerString.count());//设置列数
//    ui->tableWidget_fault_select->setHorizontalHeaderLabels(headerString);//设置列标题

//    ui->tableWidget_fault_select->setAlternatingRowColors(true);//使表格颜色交错功能为真
//    ui->tableWidget_fault_select->setStyleSheet("QTableWidget{background-color: rgb(250, 250, 250);"
//                                                "alternate-background-color: rgb(234, 234, 234);}");//设置表格颜色

//    Matrix_D.list_LOWEST_MODULE_DATA.clear();//最底层单元数据集结构列表清零
//    init_the_lowest_module_message(model_name);//查找最底层信号数据信息

//    int RowCount = 0;
//    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
//    {
//        if(Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals.size())
//            RowCount+=Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals.size();
//        else RowCount+=1;
//    }

//    //设置表格的默认的行数
//    ui->tableWidget_fault_select->setRowCount(RowCount);//设置默认的列数
//    ui->tableWidget_fault_select->verticalHeader()->hide();//隐藏行序号

//    //数据显示
//    int Row = 0;
//    for(int i=0;i<Matrix_D.list_LOWEST_MODULE_DATA.size();i++)
//    {
//        //qDebug()<<list_LOWEST_MODULE_DATA[i].module_default;
//        //获取模块传递链名称
//        QString Module_ownership_information;
//        for(int j = Matrix_D.list_LOWEST_MODULE_DATA[i].list_parents_TID.size()-2;j>0;j--)
//        {
//            Module_ownership_information.append(Matrix_D.list_LOWEST_MODULE_DATA[i].list_parents_NAME[j]);
//            Module_ownership_information.append("->");
//        }
//        Module_ownership_information.append(Matrix_D.list_LOWEST_MODULE_DATA[i].list_parents_NAME[0]);

//        if(Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals.size())
//        {
//            for(int k=0;k<Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals.size();k++)
//            {
//                ui->tableWidget_fault_select->setItem(Row,0,new QTableWidgetItem(Module_ownership_information));
//                ui->tableWidget_fault_select->setItem(Row,1,new QTableWidgetItem(Matrix_D.list_LOWEST_MODULE_DATA[i].list_signals[k]));
//                QTableWidgetItem *checkBox = new QTableWidgetItem();
//                checkBox->setCheckState(Qt::Unchecked);
//                ui->tableWidget_fault_select ->setItem(Row,2,checkBox);
//                Row++;
//            }
//        }
//        else{
//            ui->tableWidget_fault_select->setItem(Row,0,new QTableWidgetItem(Module_ownership_information));
//            ui->tableWidget_fault_select->setItem(Row,1,new QTableWidgetItem(NULL));
//            QTableWidgetItem *checkBox = new QTableWidgetItem();
//            checkBox->setCheckState(Qt::Unchecked);
//            ui->tableWidget_fault_select ->setItem(Row,2,checkBox);
//            Row++;
//        }
//    }
//    init_fault_list_is_not_cell_change = false;
//}
*/

/*
//    for(int i=0;i<Matrix_D.list_TEST_DATA.size();)
//    {
//        bool test_be_deleted = false;
//        if(Matrix_D.list_TEST_DATA[i].TEST_TYPE==1)//当前项为测试
//        {
//            if(Matrix_D.list_TEST_DATA[i].TEST_SIGNAL_IS_EXIT_OR_NOT == 0)//测试正常
//            {
//                //获取当前测试TID
//                QString this_TEST_TID = Matrix_D.list_TEST_DATA[i].TEST_TID;
//                //删除测试行对应D矩阵值为1的列
//                for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();)
//                {
//                    bool module_should_be_deleted = false;
//                    if(Matrix_D.Matrix_D_value[i][j])
//                    {
//                        module_should_be_deleted = true;
//                    }
//                    if(!module_should_be_deleted)
//                        j++;
//                    if(module_should_be_deleted)
//                        Matrix_D.delete_one_module_Column(j);//删除D矩阵第Num列,同时删除模块集信息
//                }
//                //删除该测试行
//                Matrix_D.delete_one_test_row(i);//删除D矩阵第Num行,同时删除测试集信息
//                test_be_deleted = true;
//                    Matrix_D.print_out();
//            }
//            if(Matrix_D.list_TEST_DATA[i].TEST_SIGNAL_IS_EXIT_OR_NOT == 1)//测试异常
//            {
//                //获取当前测试TID
//                QString this_TEST_TID = Matrix_D.list_TEST_DATA[i].TEST_TID;
//                //删除测试行对应D矩阵值为0的列
//                for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();)
//                {
//                    bool module_should_be_deleted = false;
//                    if(!Matrix_D.Matrix_D_value[i][j])
//                    {
//                        module_should_be_deleted = true;
//                    }
//                    if(!module_should_be_deleted)
//                        j++;
//                    if(module_should_be_deleted)
//                        Matrix_D.delete_one_module_Column(j);//删除D矩阵第Num列,同时删除模块集信息
//                }
//                //删除该测试行
//                Matrix_D.delete_one_test_row(i);//删除D矩阵第Num行,同时删除测试集信息
//                test_be_deleted = true;
//                Matrix_D.print_out();
//            }
//        }
//        if(!test_be_deleted)
//            i++;
//    }
//        if(Matrix_D.list_TEST_DATA[i].TEST_TYPE==2)//当前项为征兆
//        {
//            if(Matrix_D.list_TEST_DATA[i].TEST_SIGNAL_IS_EXIT_OR_NOT == 1)//征兆不存在（相当于测试正常）
//            {
//                //获取当前测试TID
//                QString this_TEST_TID = Matrix_D.list_TEST_DATA[i].TEST_TID;
//                //删除测试行对应D矩阵值为1的列
//                for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();)
//                {
//                    bool module_should_be_deleted = false;
//                    if(Matrix_D.Matrix_D_value[i][j])
//                    {
//                        module_should_be_deleted = true;
//                    }
//                    if(!module_should_be_deleted)
//                        j++;
//                    if(module_should_be_deleted)
//                        Matrix_D.delete_one_module_Column(i);//删除D矩阵第Num列,同时删除模块集信息
//                }
//                //删除该测试行
//                Matrix_D.delete_one_test_row(i);//删除D矩阵第Num行,同时删除测试集信息
//                test_be_deleted = true;
//            }
//            if(Matrix_D.list_TEST_DATA[i].TEST_SIGNAL_IS_EXIT_OR_NOT == 0)//征兆不存在（相当于测试异常）
//            {
//                //获取当前测试TID
//                QString this_TEST_TID = Matrix_D.list_TEST_DATA[i].TEST_TID;
//                //删除测试行对应D矩阵值为0的列
//                for(int j=0;j<Matrix_D.list_LOWEST_MODULE_DATA.size();)
//                {
//                    bool module_should_be_deleted = false;
//                    if(!Matrix_D.Matrix_D_value[i][j])
//                    {
//                        module_should_be_deleted = true;
//                    }
//                    if(!module_should_be_deleted)
//                        j++;
//                    if(module_should_be_deleted)
//                        Matrix_D.delete_one_module_Column(i);//删除D矩阵第Num列,同时删除模块集信息
//                }
//                //删除该测试行
//                Matrix_D.delete_one_test_row(i);//删除D矩阵第Num行,同时删除测试集信息
//                test_be_deleted = true;
//            }
//        }

//    }

}
*/



































































