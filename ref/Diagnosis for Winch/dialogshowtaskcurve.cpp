#include "dialogshowtaskcurve.h"
#include "ui_dialogshowtaskcurve.h"

int CurYMax=10,CurYMin=-10;
DialogShowTaskCurve::DialogShowTaskCurve(QWidget *parent,myQSqlDatabase *TMATE_Database,QString taskName) :
    QDialog(parent),
    ui(new Ui::DialogShowTaskCurve),m_Database(TMATE_Database),TaskName(taskName)
{
    ui->setupUi(this);
    ui->WarndateEditEnd->setDate(QDate::currentDate());
    InitChart();
    LoadDataCurve();
}

DialogShowTaskCurve::~DialogShowTaskCurve()
{
    delete ui;
}

void DialogShowTaskCurve::LoadDataCurve()
{
    QStringList ListHisData=m_Database->SelectHisDataFromTaskDataSave(ui->WarndateEditStart->date(),ui->WarndateEditEnd->date(),TaskName);
    CurYMax=10;
    CurYMin=-10;
    ui->customPlot->yAxis->setRange(CurYMin,CurYMax);
    ui->customPlot->replot();
    bool FirstIn=true;
    int i;
    for(int i=0;i<8;i++)
    {
        ui->customPlot->graph(i)->clearData();
        ui->customPlot->graph(i)->setName("");
    }
    for(i=0;i<ListHisData.count();i++)
    {
        QStringList ListPara=ListHisData.at(i).split(",");
        int j;
        for(j=0;j<8;j++)
        {
            if(j==ListPara.count()) break;
            if(FirstIn)
            {
               ui->customPlot->graph(j)->clearData();
               ui->customPlot->graph(j)->setName(ListPara.at(j).split("=").at(0));
            }
            double ParaVal=ListPara.at(j).split("=").at(1).toDouble();

            ui->customPlot->graph(j)->addData(i,ParaVal);
            if(CurYMax<ParaVal)
            {
                CurYMax=ParaVal+100;
                ui->customPlot->yAxis->setRange(CurYMin,CurYMax);
                ui->customPlot->replot();

            }
            if(CurYMin>ParaVal)
            {
                CurYMin=ParaVal-100;
                ui->customPlot->yAxis->setRange(CurYMin,CurYMax);
                ui->customPlot->replot();
            }
        }
        FirstIn=false;
    }
    ui->customPlot->xAxis->setRange(0,i);
    ui->customPlot->replot();
}

void DialogShowTaskCurve::InitChart()
{
  // add two new graphs and set their look:添加两个新图形并设置它们的外观：
  ui->customPlot->addGraph();
  ui->customPlot->graph(0)->setPen(QPen(Qt::green)); // line color blue for first graph第一个图形的线颜色为蓝色
  ui->customPlot->graph(0)->setBrush(QBrush(QColor(0, 0, 255, 20))); // first graph will be filled with translucent blue
  ui->customPlot->graph(0)->setVisible(true);
  ui->customPlot->addGraph();                                        //第一个图形将填充半透明的蓝色
  ui->customPlot->graph(1)->setPen(QPen(Qt::red)); // line color red for second graph第二张图的红色线条
  ui->customPlot->graph(1)->setVisible(true);
  ui->customPlot->addGraph();
  ui->customPlot->graph(2)->setPen(QPen(Qt::blue));
  ui->customPlot->graph(2)->setVisible(true);
  ui->customPlot->addGraph();
  ui->customPlot->graph(3)->setPen(QPen(Qt::yellow));
  //customPlot->graph(3)->setVisible(false);
  ui->customPlot->addGraph();
  ui->customPlot->graph(4)->setPen(QPen(Qt::cyan));
  //customPlot->graph(4)->setVisible(false);
  ui->customPlot->addGraph();
  ui->customPlot->graph(5)->setPen(QPen(Qt::magenta));
  ui->customPlot->addGraph();
  ui->customPlot->graph(6)->setPen(QPen(Qt::gray));
  ui->customPlot->addGraph();
  ui->customPlot->graph(7)->setPen(QPen(Qt::black));

  ui->customPlot->legend->setVisible(true);
  ui->customPlot->legend->setBrush(QColor(255,255,255,0));//背景透明
  //让范围自行缩放，以便图0完全适合可见区域：
  ui->customPlot->graph(0)->rescaleAxes();
  // same thing for graph 1, but only enlarge ranges (in case graph 1 is smaller than graph 0):
  //对于图1也是一样，但只放大范围（如果图1小于图0）：
  ui->customPlot->graph(1)->rescaleAxes(true);
  ui->customPlot->graph(2)->rescaleAxes(true);
  ui->customPlot->graph(3)->rescaleAxes(true);
  ui->customPlot->graph(4)->rescaleAxes(true);
  ui->customPlot->graph(5)->rescaleAxes(true);
  ui->customPlot->graph(6)->rescaleAxes(true);
  ui->customPlot->graph(7)->rescaleAxes(true);
  // Note: we could have also just called customPlot->rescaleAxes(); instead
  // Allow user to drag axis ranges with mouse, zoom with mouse wheel and select graphs by clicking:
  //注意：我们也可以调用customPlot->rescaleAxes（）；而不是
  //允许用户使用鼠标拖动轴范围，使用鼠标滚轮缩放并通过单击选择图形：
  ui->customPlot->setInteractions(QCP::iRangeDrag | QCP::iRangeZoom | QCP::iSelectPlottables);

  //customPlot->xAxis->setRange(0, 600);
  //customPlot->yAxis->setRange(-32000, 32000);
}


void DialogShowTaskCurve::on_BtnWarnSearch_clicked()
{
    LoadDataCurve();
}
