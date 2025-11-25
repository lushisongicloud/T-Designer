#ifndef SELECTFUNCTIONDIALOG_H
#define SELECTFUNCTIONDIALOG_H

#include <QDialog>
#include <QInputDialog>
#include <QAction>
#include <QMenu>
#include <QMainWindow>
#include <QMouseEvent>
#include <QObject>
#include <QtXml>
#include <QPushButton>
#include <QLayout>
#include <QDebug>
#include <QTreeWidget>
#include <QTableWidgetItem>
#include <QFormLayout>
#include "mycombobox.h"
#include "../BO/componententity.h"
#include "BO/systementity.h"
#include "../variable_range_config.h"
#include "../function_variable_config.h"
#include "functionvariablevaluedialog.h"

namespace Ui {
class SelectFunctionDialog;
}

class MainWindow;

class SelectFunctionDialog : public QDialog
{
    Q_OBJECT

public:
    explicit SelectFunctionDialog(SystemEntity* systemEntity, const QString& systemDescription, const QString& functionDescription, QWidget *parent = nullptr);
    //~SelectFunctionDialog();

    QList<TestItem> getLocalTestItemList();
    QString getLocalFunctionDescription() const { return localFunctionDescription; }
    QString getLocalLink() const { return localLink; }
    QList<resultEntity> getLocalResultEntityList() const {return localResultEntityList;}

    const rangeconfig::VariableRangeConfig &getVariableRangeConfig() const { return variableRangeConfig; }
    const functionvalues::FunctionVariableConfig &getCurrentVariableConfig() const { return currentFunctionVariableConfig; }
    QTreeWidget* GetTreeWidget() const;
    void ShowSet();


    QString getCurrentfunctionName() const { return currentFunctionName;}//当前被诊断功能名
    QMap<QString, QString> getFunctionLinkMap()const { return functionLinkMap;}//功能名-链路信息
    QMap<QString, QString> getFunctionComponentDependencyMap() const {return functionComponentDependencyMap;}//功能名-器件依赖关系
    QMap<QString, QString> getFunctionDependencyMap() const {return functionDependencyMap;}//功能名-功能依赖关系
    QMap<QString, FunctionInfo> getFunctionInfoMap() const {return functionInfoMap;}
    QString negateRange(const QString &input) const;
protected:
    void keyPressEvent(QKeyEvent* event) override;

private slots:
    void onTableFunctionItemChanged(QTableWidgetItem* item);
    void checkDuplicateAndUpdateColor();
    void insertIntoFunctionTable(const QString& variable, const QString& value, const double& confidence, const QString& constrainType);
    void insertIntoResultTable(const QString& componentNames, const QString& failureModes, const double& probability);
    void insertIntoFunctionDependencyTable(const QString &componentAndFunctionString);
    void updateFunctionDependencyTable(const QString &componentAndFunctionString);
    QString generateQStringFromFunctionDependencyTable();
    void addFunction(bool isSubFunction);
    void getAllFunctionNames(QTreeWidgetItem *item, QStringList &functionNames);
    void on_functionTree_itemClicked(QTreeWidgetItem *item, int column);
    void on_contextMenuRequested(const QPoint &pos);
    void onTableFunctionDependencyContextMenu(const QPoint& pos);
    void onTextEditComponentDependencyContextMenu(const QPoint& pos);

    void on_btn_AddFunc_clicked();

    void on_btn_DelFunc_clicked();

    void on_btn_AddObs_clicked();

    void on_btn_DelObs_clicked();

    void on_btn_Ok_clicked();

    void on_btn_Cancel_clicked();

    void on_btn_SaveFunc_clicked();

    void on_btn_UpdateSubFunc_clicked();

    void on_btn_OfflineSolve_clicked();

    void on_btn_CalBoundaryConditions_clicked();

    void onSolvingStarted();
    void onSolvingFinished(QStringList ans);
    void onProgressUpdated(int progress);
    void onResultEntityListUpdated(const QList<resultEntity>& resultEntityList);
    void onOutlierObsUpdated(const QMap<QString, double>& outlierObs);
    void on_btn_CheckConstraints_clicked();

private:
    void updateConstraintIntegrityLabel(const QString &status);
    void markConstraintIntegrityUnknown();
    QList<TestItem> buildConstraintCheckItems(bool invertActuator) const;
    void showVariableRangeDialog();
    void loadVariableRangeConfig(const QDomDocument &doc);
    void updateFunctionIntegrityEntry(const QString &functionName, const QString &status);
    void loadFunctionVariableConfig(const QString &functionName, const QDomElement &functionElement);
    void saveCurrentVariableConfigToMap();
    void ensureFunctionVariableConfig(const QString &functionName);
    QStringList currentLinkElements() const;
    QStringList currentAllComponentElements() const;
    bool variableMatchesLink(const QString &variable, const QStringList &linkElements) const;
    void updateSatSamplesFromModel(const QMap<QString, QString> &model, const QStringList &componentElements);
    QString formatModelSample(const QString &valueText) const;
    QMap<QString, QString> currentConstraintValueMap() const;
    void showFunctionVariableValueDialog();
    QVector<functionvalues::FunctionVariableRow> assembleVariableRows(const QStringList &linkElements) const;
    QStringList collectFunctionVariables(const QStringList &componentElements) const;
    QString solveVariableFeasibleRange(const QString &variable,
                                       const QString &typeKey,
                                       const QStringList &typicalValues,
                                       QString &errorMessage);
    QList<TestItem> buildPositiveSolveItems() const;
    QList<TestItem> buildVariableSolveItems(const QList<TestItem> &baseItems,
                                            const QString &variable,
                                            const QString &valueExpression) const;
    TestItem makeVariableSetterItem(const QString &variable, const QString &valueExpression) const;
    bool checkSatisfiable(const QString &systemDescription,
                          const QList<TestItem> &items);
    QString formatInterval(double lower, double upper) const;
    void applyVariableRowsToConfig(const QVector<functionvalues::FunctionVariableRow> &rows);
    QString croppedSystemDescriptionForCurrentLink(const QStringList &linkElements) const;
    void updateCurrentFunctionXml();
    QList<QTreeWidgetItem*> findFunctionTreeItems(const QString &functionName) const;
    void writeFunctionXml(const QString &functionName,
                          const functionvalues::FunctionVariableConfig &config);

    SystemEntity* systemEntity;
    QString systemDescription;
    QString localFunctionDescription; // To hold the local version of the function description
    MainWindow *mainWindow;
    QString localLink;
    Ui::SelectFunctionDialog *ui;
    int lastResultEntityIndex = 0;

    void resultProcessAndUpdateColor();
    void updateFunctionTree();
    void addTreeStructureToXML(QTreeWidgetItem* parentItem, QDomElement& parentElement, QDomDocument& doc);
    void addFunctionToXML(QTreeWidgetItem *item, QDomElement &parentElement, QDomDocument &doc);
    void addTreeItemsFromXML(QDomElement &element, QTreeWidgetItem *parentItem, QDomElement &root);
    void processTreeItem(QTreeWidgetItem *item);
    QStringList getDeviceNamesInConnection(const QString &line);
    bool isDeviceMatched(const QStringList &devicesInConnection, const QSet<QString> &functionLink);
    void recursiveAdd(QList<TestItem> &testItemListToCheck, TestItem item, QString& functionLinks,bool isTopLevel);
    QStringList boundaryDeviceToAddList(const QStringList &boundaryDeviceList, QList<TestItem>& currentTestItemList);
    QString CalFunctionDependency();
    QString CalComponentDependency(QString linkText, QString allComponent = "");
    QList<TestItem> processTestItemListForPenetrativeSolve(QList<TestItem> &currentTestItemList, QString& LinkText);

    QList<TestItem> testItemList; // To hold the local version of the test items
    QList<resultEntity> localResultEntityList;
    QString currentFunctionName;
    QStringList functionNameList;//功能列表
    QMap<QString, QString> functionActuatorNameMap;//功能-执行器名称列表
    QMap<QString, QStringList> functionActuatorConstraintMap;//功能-执行器约束列表
    QMap<QString, QList<TestItem>> functionConstraintsMap;//功能-约束列表
    QMap<QString, QString> functionLinkMap;//功能-链路信息
    QMap<QString, QString> functionComponentDependencyMap;//功能-器件依赖关系，
    QMap<QString, QString> functionAllComponentMap;//功能-全部相关器件，
    QMap<QString, QString> functionDependencyMap;//功能-功能依赖关系，
    QMap<QString, double> functionFaultProbabilityMap;//功能-失效概率
    QMap<QString,FunctionInfo> functionInfoMap;
    QMap<QString, QString> functionConstraintIntegrityMap;
    QString currentConstraintIntegrityStatus;
    rangeconfig::VariableRangeConfig variableRangeConfig;
    functionvalues::FunctionVariableConfig currentFunctionVariableConfig;
    QMap<QString, functionvalues::FunctionVariableConfig> functionVariableConfigMap;
    bool isLoading = false;
};

#endif // SELECTFUNCTIONDIALOG_H
