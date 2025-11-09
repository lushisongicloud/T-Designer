#ifndef DIALOGSHOWTASKCURVE_H
#define DIALOGSHOWTASKCURVE_H

#include <QDialog>
#include "qcustomplot.h"
#include "myqsqldatabase.h"
#define MAX_LINE_CNT 8
namespace Ui {
class DialogShowTaskCurve;
}

class DialogShowTaskCurve : public QDialog
{
    Q_OBJECT

public:
    explicit DialogShowTaskCurve(QWidget *parent = nullptr,myQSqlDatabase *TMATE_Database = nullptr,QString taskName="");
    ~DialogShowTaskCurve();
    void InitChart();
    void LoadDataCurve();
    QString TaskName;
    myQSqlDatabase *m_Database = nullptr;//数据库检索类

private slots:
    void on_BtnWarnSearch_clicked();

private:
    Ui::DialogShowTaskCurve *ui;
};

#endif // DIALOGSHOWTASKCURVE_H
