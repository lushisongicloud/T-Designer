#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>
#include <QDebug>
#include <QTreeWidget>
#include<QTableWidgetItem>

#include "widget/mycombobox.h"
#include "sqlitedatabase.h"
#include "BO/systementity.h"
#include "DO/diagnosisgraph.h"
#include "testability/testability_types.h"
#include "variable_range_config.h"


namespace Ui {
class MainWindow;
}

class MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    explicit MainWindow(QWidget *parent = nullptr);
    ~MainWindow();

    void initUI();

    void databaseConnect();

    void openModel(QString modelName);

    void insertIntoTestTable(const QString& variable, const QString& value, const double& confidence, Qt::CheckState checkState, const QString& obsType);
    void insertIntoResultTable(const QString& componentNames, const QString& failureModes, const double& probability);

    static QMap<QString, QStringList> obsTemplates;

    bool getIsPenetrativeSolve() const { return isPenetrativeSolve; }

public slots:
    void onTableTestItemChanged(QTableWidgetItem* item);
    void onConfirmButtonClicked();

    void onSolvingStarted();
    void onSolvingFinished(QStringList ans);
    void onProgressUpdated(int progress);
    void onResultEntityListUpdated(const QList<resultEntity>& resultEntityList);
    void onOutlierObsUpdated(const QMap<QString, double>& outlierObs);

private slots:

    void on_actionOpenModel_triggered();

    void on_actionParseModel_triggered();

    void on_actionCheckModel_triggered();

    void on_actionSaveModel_triggered();

    void on_pushButtonSolve_clicked();

    void on_actionCreatNewComponent_triggered();

    void UpdateUI();

    void on_comboBox_Solve_Type_currentIndexChanged(int index);

    void on_actionSaveAs_triggered();

    void on_Btn_AddObs_clicked();

    void on_Btn_DelObs_clicked();

    void on_Btn_RecommendObs_clicked();

    void on_Btn_SolveAns_clicked();

    void checkDuplicateAndUpdateColor();

    void on_Btn_selectFunction_clicked();

    void on_radioButton_Penetrative_toggled(bool checked);

    void on_Btn_IncrementalSolve_clicked();

    void on_actionGenerateDMatrix_triggered();

    void on_actionOpenDMatrix_triggered();

private:
    Ui::MainWindow *ui;
    QLabel *labViewCord = nullptr;
    SQliteDatabase *database = nullptr;
    SystemEntity *systemEntity = nullptr;
    QString currentModelName;
    QString functionDescription;
    model currentModel;
    bool isPenetrativeSolve=true;

    QTime timeSlove;
    QTimer *TimerUpdateUI;

    DiagnosisGraph *diagnosisGraph = nullptr;

    QList<TestItem> testItemList;
    QList<resultEntity> completeResultEntityList;
    QList<resultEntity> currentResultEntityList;
    QString currentFunctionName;
    QString currentFunctionLink;
    int lastResultEntityIndex = 0;
    QMap<QString,FunctionInfo> functionInfoMap;
    rangeconfig::VariableRangeConfig variableRangeConfig;
    testability::DMatrixBuildOptions lastDMatrixOptions;

    void resultProcessAndUpdateColor();
    void refreshFunctionStateFromModel();
    void applyVariableRangeConfigFromString(const QString &functionXml);
};

class NumericTableWidgetItem : public QTableWidgetItem
{
public:
    NumericTableWidgetItem(const QString& txt = QString()):QTableWidgetItem(txt){}
    bool operator <(const QTableWidgetItem &other) const
    {
        return this->text().toDouble() < other.text().toDouble();
    }
};
#endif // MAINWINDOW_H
