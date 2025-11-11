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
#include <QElapsedTimer>
#include <QTime>
#include "BO/diagnosisengine.h"
#include "DO/diagnosistreenode.h"

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
    
    // 新的诊断决策树相关方法
    void displayCurrentTest();
    void recordTestResult(TestOutcome outcome);
    void showDiagnosisResult();

protected:
    void resizeEvent(QResizeEvent *event) override;
    
    QMdiSubWindow *mdisubwindow;
    QString FunctionID,CurTestPointName;
    DiagnosisEngine *diagnosisEngine;
    int currentTreeId;
    
    // 推理时间统计
    QElapsedTimer reasoningTimer;
    qint64 lastReasoningTime;
    
    // 当前诊断的功能名称
    QString currentFunctionName;

private slots:
    void on_toolButton_start_diagnosis_clicked();

    void on_toolButton_known_symptom_add_clicked();

    void on_toolButton_not_exit_symptom_modify_clicked();

    void on_toolButton_known_symptom_delete_clicked();

    void on_toolButton_known_symptom_select_next_clicked();

    void on_BtnLastStep_clicked();

    void on_toolButton_skip_this_test_clicked();

    void on_toolButton_slelct_other_test_clicked();

    void on_btn_TestPass_clicked();

    void on_btn_TestFail_clicked();

private:
    Ui::dialogDiagnoseUI *ui;

signals:
    void signalUpdateExec(QString FunctionID);
    void signalStartDiagnose(QString SendCmdStr);
    void signalSendCmdStr(QString SendCmdStr);
};

#endif // DIALOGDIAGNOSEUI_H
