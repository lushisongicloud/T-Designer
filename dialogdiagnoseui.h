#ifndef DIALOGDIAGNOSEUI_H
#define DIALOGDIAGNOSEUI_H

#include <QDialog>
#include "common.h"
#include "qxcombobox.h"
#include <QtSql>
#include <QtCharts>
#include <QChartView>
#include <QMouseEvent>
#include <QGraphicsSimpleTextItem>
#include <QDialog>
#include <QFormLayout>
#include <QLabel>
#include <QComboBox>
namespace Ui {
class dialogDiagnoseUI;
}

class dialogDiagnoseUI : public QDialog
{
    Q_OBJECT

public:
    explicit dialogDiagnoseUI(QWidget *parent = nullptr);
    ~dialogDiagnoseUI();
    void LoadAllFunction();
    void LoadAllTools();
    void SetStackIndex(int index);
    void init_symptom_list();//初始化征兆信号UI列表
    void AddOrModifyExec(int Mode,QString StrSelectedCmd,QString StrExecState,QString StrExecStateVal);//Mode=1:add Mode=2:modify
    void LoadTestPointInfo(QString TestPointName,QString CurrentInOutName,QStringList ListTermStr);
    QMdiSubWindow *mdisubwindow;
    QString FunctionID,CurTestPointName;

private slots:
    void on_toolButton_start_diagnosis_clicked();

    void on_toolButton_known_symptom_add_clicked();

    void on_toolButton_not_exit_symptom_modify_clicked();

    void on_toolButton_known_symptom_delete_clicked();

    void on_toolButton_known_symptom_select_next_clicked();

    void on_btm_CalTestResult_clicked();

private:
    Ui::dialogDiagnoseUI *ui;

signals:
    void signalUpdateExec(QString FunctionID);
    void signalStartDiagnose(QString SendCmdStr);
    void signalSendCmdStr(QString SendCmdStr);
};

#endif // DIALOGDIAGNOSEUI_H
