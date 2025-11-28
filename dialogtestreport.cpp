#include "dialogtestreport.h"
#include "ui_dialogtestreport.h"

#include <QtMath>
#include <algorithm>
#include <QGraphicsLayout>
#include <QMargins>


DialogTestReport::DialogTestReport(const TestReportMetrics &metrics, QWidget *parent) :
QDialog(parent),
ui(new Ui::DialogTestReport),
rowCount_(0),
startTimestamp_(0),
actualElapsedTime_(0),
metrics_(metrics)
{
    ui->setupUi(this);
    setWindowFlags(windowFlags() | Qt::WindowMinMaxButtonsHint | Qt::WindowSystemMenuHint);
    setSizeGripEnabled(true);
    iniBarChart();
    InitUI();
}

DialogTestReport::DialogTestReport(const TestReportMetrics &metrics, qint64 startTimestamp, QWidget *parent) :
QDialog(parent),
ui(new Ui::DialogTestReport),
rowCount_(0),
startTimestamp_(startTimestamp),
actualElapsedTime_(0),
metrics_(metrics)
{
    ui->setupUi(this);
    setWindowFlags(windowFlags() | Qt::WindowMinMaxButtonsHint | Qt::WindowSystemMenuHint);
    setSizeGripEnabled(true);
    // 计算实际耗时
    actualElapsedTime_ = QDateTime::currentMSecsSinceEpoch() - startTimestamp_;
    
    iniBarChart();
    InitUIWithActualTime(actualElapsedTime_);
}

DialogTestReport::~DialogTestReport()
{
    delete ui;
}
void DialogTestReport::InitUIWithActualTime(qint64 elapsedMs)
{
    ui->labelTime->setText(QString("分析计算时间：%1ms").arg(elapsedMs));
    populateStatisticModels();
}

void DialogTestReport::InitUI()
{
    ui->labelTime->clear();
    populateStatisticModels();
}

void DialogTestReport::populateStatisticModels()
{
    const QString detectionText = QString("故障检测率：%1").arg(formatPercent(metrics_.faultDetectionRate));
    const QString isolation1Text = QString("故障隔离率（隔离到1个LRU）：%1").arg(formatPercent(metrics_.faultIsolationRate1));
    const QString isolation2Text = QString("故障隔离率（隔离到2个LRU）：%1").arg(formatPercent(metrics_.faultIsolationRate2));
    const QString isolation3Text = QString("故障隔离率（隔离到3个LRU）：%1").arg(formatPercent(metrics_.faultIsolationRate3));
    const QString mtbfText = QString("MTBF：%1").arg(formatHours(metrics_.mtbfHours));
    const QString mttrText = QString("MTTR：%1").arg(formatHours(metrics_.mttrHours));
    const QString componentText = QString("器件数量：%1").arg(metrics_.componentCount);
    const QString connectionText = QString("连接数量：%1").arg(metrics_.connectionCount);
    const QString functionText = QString("功能数量：%1").arg(metrics_.functionCount);
    const QString testPointText = QString("测点数量：%1").arg(metrics_.testPointCount);
    const QString faultSetText = QString("故障集大小：%1").arg(metrics_.faultSetSize);

    auto setupSingleValueTree = [](QTreeView *view, QStandardItemModel *&model, const QString &text) {
        view->setStyleSheet("background:transparent;border-width:0;border-style:outset");
        model = new QStandardItemModel(view);
        view->header()->setVisible(false);
        view->setColumnWidth(0,50);
        view->setModel(model);
        QStandardItem *root = new QStandardItem(text);
        model->appendRow(root);
        root->appendRow(new QStandardItem("1"));
    };

    setupSingleValueTree(ui->treeViewFDR, ModelFDR, detectionText);
    setupSingleValueTree(ui->treeView1LRU, Model1FIR, isolation1Text);
    setupSingleValueTree(ui->treeView2LRU, Model2FIR, isolation2Text);
    setupSingleValueTree(ui->treeView3LRU, Model3FIR, isolation3Text);
    setupSingleValueTree(ui->treeViewMTBF, ModelMTBF, mtbfText);
    setupSingleValueTree(ui->treeViewMTTR, ModelMTTR, mttrText);
    setupSingleValueTree(ui->treeViewAnaly1, ModelAnaly1, componentText);
    setupSingleValueTree(ui->treeViewAnaly2, ModelAnaly2, connectionText);
    setupSingleValueTree(ui->treeViewAnaly3, ModelAnaly3, functionText);
    setupSingleValueTree(ui->treeViewAnaly4, ModelAnaly4, testPointText);
    setupSingleValueTree(ui->treeViewAnaly5, ModelAnaly5, faultSetText);
}



void DialogTestReport::build_FIR_Chart()//构建诊断模糊组图表
{
    QChart *chart = ui->chartView->chart();
    chart->removeAllSeries();
    chart->removeAxis(chart->axisX());
    chart->removeAxis(chart->axisY());

    QList<int> sizes = metrics_.fuzzyGroupComponentCounts.keys();
    std::sort(sizes.begin(), sizes.end());
    if (sizes.isEmpty()) {
        sizes = {1, 2, 3};
    }

    QStringList categories;
    QBarSet *set = new QBarSet("模糊组器件数");
    int maxValue = 0;
    for (int size : sizes) {
        const int count = metrics_.fuzzyGroupComponentCounts.value(size, 0);
        categories << QString::number(size) + "LRU";
        set->append(count);
        if (count > maxValue) {
            maxValue = count;
        }
    }

    QBarSeries *series = new QBarSeries();
    series->append(set);
    chart->addSeries(series);

    QBarCategoryAxis *axisX = new QBarCategoryAxis();
    axisX->append(categories);
    axisX->setLabelsVisible(true);
    QFont axisFont = axisX->labelsFont();
    if (axisFont.pointSize() > 0 && axisFont.pointSize() > 9)
        axisFont.setPointSize(axisFont.pointSize() - 1);
    else
        axisFont.setPointSize(9);
    axisX->setLabelsFont(axisFont);
    axisX->setLabelsAngle(-35);
    chart->addAxis(axisX, Qt::AlignBottom);
    series->attachAxis(axisX);

    QValueAxis *axisY = new QValueAxis;
    axisY->setLabelFormat("%d");
    const int upperBound = qMax(1, maxValue);
    const int interval = (upperBound <= 5) ? 1 : static_cast<int>(std::ceil(upperBound / 5.0));
    const int roundedUpper = qMax(interval, interval * static_cast<int>(std::ceil(static_cast<double>(upperBound) / interval)));
    const int tickCount = roundedUpper / interval + 1;
    axisY->setTickCount(tickCount);
    axisY->setTickInterval(interval);
    axisY->setRange(0, roundedUpper);
    axisY->setMinorTickCount(0);
    chart->addAxis(axisY, Qt::AlignLeft);
    series->attachAxis(axisY);

    chart->legend()->setVisible(true);
    chart->legend()->setAlignment(Qt::AlignBottom);
    chart->setMargins(QMargins(8, 8, 8, 18));
    if (chart->layout())
        chart->layout()->setContentsMargins(6, 6, 6, 18);
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
    ui->chartView->setSizePolicy(QSizePolicy::Expanding, QSizePolicy::Expanding);
    build_FIR_Chart();

}

QString DialogTestReport::formatPercent(double ratio) const
{
    const double clamped = qBound(0.0, ratio, 1.0);
    return QString::number(clamped * 100.0, 'f', 2) + "%";
}

QString DialogTestReport::formatHours(double hours) const
{
    const double safeHours = qMax(0.0, hours);
    if (safeHours >= 100.0) {
        return QString::number(safeHours, 'f', 1) + " h";
    }
    return QString::number(safeHours, 'f', 2) + " h";
}
