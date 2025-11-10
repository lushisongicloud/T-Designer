#ifndef DIALOGTESTREPORT_H
#define DIALOGTESTREPORT_H

#include <QDialog>
#include <QtCharts>
#include <QChartView>
#include <QElapsedTimer>
#include <QStandardItemModel>
#include <QMap>
#include "common.h"
namespace Ui {
class DialogTestReport;
}

struct TestReportMetrics
{
    int componentCount = 0;
    int connectionCount = 0;
    int testPointCount = 0;
    int faultSetSize = 0;
    double mtbfHours = 0.0;
    double mttrHours = 0.0;
    double faultDetectionRate = 0.0;
    double faultIsolationRate1 = 0.0;
    double faultIsolationRate2 = 0.0;
    double faultIsolationRate3 = 0.0;
    int functionCount = 0;
    QMap<int, int> fuzzyGroupComponentCounts;
};

class DialogTestReport : public QDialog
{
    Q_OBJECT

public:
    explicit DialogTestReport(const TestReportMetrics &metrics, QWidget *parent = nullptr);
    DialogTestReport(const TestReportMetrics &metrics, qint64 startTimestamp, QWidget *parent = nullptr);
    ~DialogTestReport();
    void iniBarChart();
    void build_FIR_Chart();
    void InitUI();
    void InitUIWithActualTime(qint64 elapsedMs);
    QStandardItemModel *ModelFDR,*Model1FIR,*Model2FIR,*Model3FIR,*ModelMTBF,*ModelMTTR,*ModelAnaly1,*ModelAnaly2,*ModelAnaly3,*ModelAnaly4,*ModelAnaly5;

private:
    void populateStatisticModels();
    QString formatPercent(double ratio) const;
    QString formatHours(double hours) const;

    Ui::DialogTestReport *ui;
    int rowCount_;
    qint64 startTimestamp_;
    qint64 actualElapsedTime_;
    TestReportMetrics metrics_;
};

#endif // DIALOGTESTREPORT_H
