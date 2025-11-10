#ifndef DIALOGTESTREPORT_H
#define DIALOGTESTREPORT_H

#include <QDialog>
#include <QtCharts>
#include <QChartView>
#include <QElapsedTimer>
#include "common.h"
namespace Ui {
class DialogTestReport;
}

class DialogTestReport : public QDialog
{
    Q_OBJECT

public:
    explicit DialogTestReport(QWidget *parent = nullptr);
    explicit DialogTestReport(qint64 startTimestamp, QWidget *parent = nullptr);
    ~DialogTestReport();
    void iniBarChart();
    void build_FIR_Chart();
    void InitUI();
    void InitUIWithActualTime(qint64 elapsedMs);
    QStandardItemModel *ModelFDR,*Model1FIR,*Model2FIR,*Model3FIR,*ModelMTBF,*ModelMTTR,*ModelAnaly1,*ModelAnaly2,*ModelAnaly3,*ModelAnaly4,*ModelAnaly5;

private:
    Ui::DialogTestReport *ui;
    int rowCount_;
    qint64 startTimestamp_;
    qint64 actualElapsedTime_;
};

#endif // DIALOGTESTREPORT_H
