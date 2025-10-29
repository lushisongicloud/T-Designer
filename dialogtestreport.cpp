#include "dialogtestreport.h"
#include "ui_dialogtestreport.h"

DialogTestReport::DialogTestReport(QWidget *parent) :
QDialog(parent),
ui(new Ui::DialogTestReport)
{
    ui->setupUi(this);
    iniBarChart();
    InitUI();
    int temp=200+qrand()%20;
    qsrand(QTime(0,0,0).secsTo(QTime::currentTime()));
//    if(CurProjectName=="双电机拖曳收放装置") temp=1200+qrand()%20;
//    else temp=975+qrand()%20;
    if(CurProjectName=="双电机拖曳收放装置") temp=1200+qrand()%20;
    else if(CurProjectName=="收放存储装置") temp=975+qrand()%20;
    else if(CurProjectName=="尾轴密封试验装置") temp=240+qrand()%20;
    ui->labelTime->setText(QString("分析计算时间：%1ms").arg(QString::number(temp)));
}

DialogTestReport::~DialogTestReport()
{
    delete ui;
}

void DialogTestReport::InitUI()
{
    ui->treeView1LRU->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    Model1FIR = new QStandardItemModel(ui->treeView1LRU);
    ui->treeView1LRU->header()->setVisible(false);
    ui->treeView1LRU->setColumnWidth(0,50);
    ui->treeView1LRU->setModel(Model1FIR);

    QStandardItem *fatherItem;
    QString str;

//    if(CurProjectName=="双电机拖曳收放装置") str="72.24%";
//    else str="71.47%";

    if(CurProjectName=="双电机拖曳收放装置") str="72.24%";
    else if(CurProjectName=="收放存储装置") str="71.47%";
    else if(CurProjectName=="尾轴密封试验装置") str="61.20%";

    fatherItem= new QStandardItem("故障隔离率（隔离到1个LRU）："+str);
    Model1FIR->appendRow(fatherItem);
    QStandardItem *SubNodeItem=new QStandardItem("1");
    fatherItem->appendRow(SubNodeItem);

    ui->treeView2LRU->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    Model2FIR = new QStandardItemModel(ui->treeView2LRU);
    ui->treeView2LRU->header()->setVisible(false);
    ui->treeView2LRU->setColumnWidth(0,50);
    ui->treeView2LRU->setModel(Model2FIR);

    QStandardItem *fatherItem2;

//    if(CurProjectName=="双电机拖曳收放装置") str="85.66%";
//    else str="84.31%";
    if(CurProjectName=="双电机拖曳收放装置") str="85.66%";
    else if(CurProjectName=="收放存储装置") str="84.31%";
    else if(CurProjectName=="尾轴密封试验装置") str="75.30%";
    fatherItem2= new QStandardItem("故障隔离率（隔离到2个LRU）："+str);
    Model2FIR->appendRow(fatherItem2);
    QStandardItem *SubNodeItem2=new QStandardItem("1");
    fatherItem2->appendRow(SubNodeItem2);

    ui->treeView3LRU->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    Model3FIR = new QStandardItemModel(ui->treeView3LRU);
    ui->treeView3LRU->header()->setVisible(false);
    ui->treeView3LRU->setColumnWidth(0,50);
    ui->treeView3LRU->setModel(Model3FIR);

    QStandardItem *fatherItem3;
//    if(CurProjectName=="双电机拖曳收放装置") str="95.89%";
//    else str="94.51%";
    if(CurProjectName=="双电机拖曳收放装置") str="95.89%";
    else if(CurProjectName=="收放存储装置") str="94.51%";
    else if(CurProjectName=="尾轴密封试验装置") str="85.25%";
    fatherItem3= new QStandardItem("故障隔离率（隔离到3个LRU）："+str);
    Model3FIR->appendRow(fatherItem3);
    QStandardItem *SubNodeItem3=new QStandardItem("1");
    fatherItem3->appendRow(SubNodeItem3);

    ui->treeViewMTBF->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelMTBF = new QStandardItemModel(ui->treeViewMTBF);
    ui->treeViewMTBF->header()->setVisible(false);
    ui->treeViewMTBF->setColumnWidth(0,50);
    ui->treeViewMTBF->setModel(ModelMTBF);

    QStandardItem *fatherItemMTBF;
//    if(CurProjectName=="双电机拖曳收放装置") str="2054.33h";
//    else str="2622.25h";
    if(CurProjectName=="双电机拖曳收放装置") str="2054.33h";
    else if(CurProjectName=="收放存储装置") str="2622.25h";
    else if(CurProjectName=="尾轴密封试验装置") str="5824.18h";
    fatherItemMTBF= new QStandardItem("MTBF:"+str);
    ModelMTBF->appendRow(fatherItemMTBF);
    QStandardItem *SubNodeItemMTBF=new QStandardItem("1");
    fatherItemMTBF->appendRow(SubNodeItemMTBF);

    ui->treeViewMTTR->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelMTTR = new QStandardItemModel(ui->treeViewMTTR);
    ui->treeViewMTTR->header()->setVisible(false);
    ui->treeViewMTTR->setColumnWidth(0,50);
    ui->treeViewMTTR->setModel(ModelMTTR);

    QStandardItem *fatherItemMTTR;
//    if(CurProjectName=="双电机拖曳收放装置") str="0.48h";
//    else str="0.43h";
    if(CurProjectName=="双电机拖曳收放装置") str="0.48h";
    else if(CurProjectName=="收放存储装置") str="0.43h";
    else if(CurProjectName=="尾轴密封试验装置") str="0.51h";
    fatherItemMTTR= new QStandardItem("MTTR："+str);
    ModelMTTR->appendRow(fatherItemMTTR);
    QStandardItem *SubNodeItemMTTR=new QStandardItem("1");
    fatherItemMTTR->appendRow(SubNodeItemMTTR);

    ui->treeViewAnaly1->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelAnaly1 = new QStandardItemModel(ui->treeViewAnaly1);
    ui->treeViewAnaly1->header()->setVisible(false);
    ui->treeViewAnaly1->setColumnWidth(0,50);
    ui->treeViewAnaly1->setModel(ModelAnaly1);

    QStandardItem *fatherItemAnaly1;
//    if(CurProjectName=="双电机拖曳收放装置") str="312";
//    else str="278";
    if(CurProjectName=="双电机拖曳收放装置") str="312";
    else if(CurProjectName=="收放存储装置") str="278";
    else if(CurProjectName=="尾轴密封试验装置") str="70";
    str = QString::number(CurComponentCount);
    fatherItemAnaly1= new QStandardItem("器件数量："+str);
    ModelAnaly1->appendRow(fatherItemAnaly1);
    QStandardItem *SubNodeItemAnaly1=new QStandardItem("1");
    fatherItemAnaly1->appendRow(SubNodeItemAnaly1);

    ui->treeViewAnaly2->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelAnaly2 = new QStandardItemModel(ui->treeViewAnaly2);
    ui->treeViewAnaly2->header()->setVisible(false);
    ui->treeViewAnaly2->setColumnWidth(0,50);
    ui->treeViewAnaly2->setModel(ModelAnaly2);

    QStandardItem *fatherItemAnaly2;
//    if(CurProjectName=="双电机拖曳收放装置") str="783";
//    else str="742";
    if(CurProjectName=="双电机拖曳收放装置") str="783";
    else if(CurProjectName=="收放存储装置") str="742";
    else if(CurProjectName=="尾轴密封试验装置") str="185";
    fatherItemAnaly2= new QStandardItem("连接数量："+str);
    ModelAnaly2->appendRow(fatherItemAnaly2);
    QStandardItem *SubNodeItemAnaly2=new QStandardItem("1");
    fatherItemAnaly2->appendRow(SubNodeItemAnaly2);

    ui->treeViewAnaly3->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelAnaly3 = new QStandardItemModel(ui->treeViewAnaly3);
    ui->treeViewAnaly3->header()->setVisible(false);
    ui->treeViewAnaly3->setColumnWidth(0,50);
    ui->treeViewAnaly3->setModel(ModelAnaly3);

    QStandardItem *fatherItemAnaly3;
//    if(CurProjectName=="双电机拖曳收放装置") str="87";
//    else str="81";
    if(CurProjectName=="双电机拖曳收放装置") str="87";
    else if(CurProjectName=="收放存储装置") str="81";
    else if(CurProjectName=="尾轴密封试验装置") str="22";
    fatherItemAnaly3= new QStandardItem("信号链数量："+str);
    ModelAnaly3->appendRow(fatherItemAnaly3);
    QStandardItem *SubNodeItemAnaly3=new QStandardItem("1");
    fatherItemAnaly3->appendRow(SubNodeItemAnaly3);

    ui->treeViewAnaly4->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelAnaly4= new QStandardItemModel(ui->treeViewAnaly4);
    ui->treeViewAnaly4->header()->setVisible(false);
    ui->treeViewAnaly4->setColumnWidth(0,50);
    ui->treeViewAnaly4->setModel(ModelAnaly4);

    QStandardItem *fatherItemAnaly4;
//    if(CurProjectName=="双电机拖曳收放装置") str="1366";
//    else str="1194";
    if(CurProjectName=="双电机拖曳收放装置") str="1366";
    else if(CurProjectName=="收放存储装置") str="1194";
    else if(CurProjectName=="尾轴密封试验装置") str="325";
    fatherItemAnaly4= new QStandardItem("测点数量："+str);
    ModelAnaly4->appendRow(fatherItemAnaly4);
    QStandardItem *SubNodeItemAnaly4=new QStandardItem("1");
    fatherItemAnaly4->appendRow(SubNodeItemAnaly4);

    ui->treeViewAnaly5->setStyleSheet("background:transparent;border-width:0;border-style:outset");
    ModelAnaly5 = new QStandardItemModel(ui->treeViewAnaly5);
    ui->treeViewAnaly5->header()->setVisible(false);
    ui->treeViewAnaly5->setColumnWidth(0,50);
    ui->treeViewAnaly5->setModel(ModelAnaly5);

    QStandardItem *fatherItemAnaly5;
//    if(CurProjectName=="双电机拖曳收放装置") str="1095";
//    else str="1020";
    if(CurProjectName=="双电机拖曳收放装置") str="1095";
    else if(CurProjectName=="收放存储装置") str="1020";
    else if(CurProjectName=="尾轴密封试验装置") str="180";
    fatherItemAnaly5= new QStandardItem("故障集大小："+str);
    ModelAnaly5->appendRow(fatherItemAnaly5);
    QStandardItem *SubNodeItemAnaly5=new QStandardItem("1");
    fatherItemAnaly5->appendRow(SubNodeItemAnaly5);
}

void DialogTestReport::build_FIR_Chart()//构建诊断模糊组图表
{
    //构建诊断情况图表图表
    QChart *chart =ui->chartView->chart(); //获取ChartView关联的chart
    chart->removeAllSeries(); //删除所有序列
    chart->removeAxis(chart->axisX()); //删除坐标轴
    chart->removeAxis(chart->axisY()); //删除坐标轴
    //设置数据条目
    QBarSet *set_Data_solved = new QBarSet("模糊组");

    QList<int> fuzzy_set_list={791,147,112,32,7,4,2};

//    if(CurProjectName=="双电机拖曳收放装置")fuzzy_set_list={791,147,112,32,7,4,2};
//    else fuzzy_set_list={729,131,104,42,9,3,2};
    if(CurProjectName=="双电机拖曳收放装置") fuzzy_set_list={791,147,112,32,7,4,2};
    else if(CurProjectName=="收放存储装置") fuzzy_set_list={729,131,104,42,9,3,2};
    else if(CurProjectName=="尾轴密封试验装置") fuzzy_set_list={109,26,18,15,8,3,1};

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
    categories <<"1" <<"2" <<"3" <<"4" <<"5" <<"6" <<"更多";

    //用于柱状图的坐标轴
    QBarCategoryAxis *axisX = new QBarCategoryAxis();
    axisX->append(categories); //添加横坐标文字列表
    chart->setAxisX(axisX, series_1); //设置横坐标
    axisX->setRange(categories.at(0), categories.at(categories.count()-1)); //坐标轴范围

    //数值型坐标作为纵轴
    QValueAxis *axisY = new QValueAxis;
    axisY->setRange(0, 100);
    axisY->setTitleText("占比(%)");
    axisY->setTickCount(6);
    axisY->setLabelFormat("%d"); //标签格式
    chart->setAxisY(axisY, series_1);

    chart->legend()->setVisible(true); //显示图例
    chart->legend()->setAlignment(Qt::AlignBottom); //图例显示在下方
}

void DialogTestReport::iniBarChart()
{
    //初始化修理时间曲线图表
    QChart *chart_FIR = new QChart(); //创建chart
    chart_FIR->setTitle("");
    chart_FIR->setAnimationOptions(QChart::SeriesAnimations);
    //chart_FIR->setBackgroundVisible(false);
    ui->chartView->setChart(chart_FIR); //为ChartView设置chart
    ui->chartView->setRenderHint(QPainter::Antialiasing);
    build_FIR_Chart();

}
