#ifndef DIALOGTESTREPORT_H
#define DIALOGTESTREPORT_H

#include <QDialog>
#include <QtCharts>
#include <QChartView>
#include "common.h"
namespace Ui {
class DialogTestReport;
}

class DialogTestReport : public QDialog
{
    Q_OBJECT

public:
    explicit DialogTestReport(QWidget *parent = nullptr);
    //explicit DialogTestReport(int rowCount, QWidget *parent = nullptr); // 添加rowCount参数
    ~DialogTestReport();
    void iniBarChart();
    void build_FIR_Chart();
    void InitUI();
    QStandardItemModel *Model1FIR,*Model2FIR,*Model3FIR,*ModelMTBF,*ModelMTTR,*ModelAnaly1,*ModelAnaly2,*ModelAnaly3,*ModelAnaly4,*ModelAnaly5;

private:
    Ui::DialogTestReport *ui;
    int rowCount_;
};

#endif // DIALOGTESTREPORT_H
