#ifndef TESTMANAGEMENTDIALOG_H
#define TESTMANAGEMENTDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QVector>
#include <memory>

#include "BO/containerrepository.h"
#include "BO/test/testdefinition.h"
#include "BO/test/testgeneratorservice.h"
#include "BO/test/diagnosticmatrixbuilder.h"

namespace Ui {
class TestManagementDialog;
}

class QTreeWidgetItem;

class TestManagementDialog : public QDialog
{
    Q_OBJECT

public:
    TestManagementDialog(int containerId, const QSqlDatabase &db, QWidget *parent = nullptr);
    ~TestManagementDialog() override;

protected:
    void closeEvent(QCloseEvent *event) override;

private slots:
    void on_btnGenerate_clicked();
    void on_btnAdd_clicked();
    void on_btnEdit_clicked();
    void on_btnDelete_clicked();
    void on_btnSave_clicked();
    void on_tableTests_currentCellChanged(int currentRow, int currentColumn, int previousRow, int previousColumn);
    void on_btnApplyTargets_clicked();
    void on_btnApplyConstraints_clicked();
    void on_btnEvaluatePrediction_clicked();
    void on_btnBuildDecisionTree_clicked();
    void on_comboDecisionTree_currentIndexChanged(int index);
    void on_treeDecision_currentItemChanged(QTreeWidgetItem *current, QTreeWidgetItem *previous);

private:
    void initializeGenerator();
    void loadData();
    void refreshTable();
    void updateDetails(int row);
    void updateCoverage();
    bool saveChanges();
    void markDirty();
    void configureTables();
    void rebuildMatrix();
    void refreshMatrixView();
    void refreshAllocationView();
    void refreshCandidateList();
    void refreshPredictionView();
    void refreshDecisionTreeView();
    void loadAnalysisFromEntity();
    void applyAnalysisToUi();
    void loadDecisionTreeList();
    void loadDecisionTreeFromDatabase(int treeId);
    void displayNodeDetails(QTreeWidgetItem *item);
    void persistAnalysis();
    QString testDisplayText(const GeneratedTest &test) const;
    QStringList candidateTestsByHeuristics(double maxCost, double maxDuration, int maxCount) const;
    QString decisionNodeSummary(const std::shared_ptr<DecisionNode> &node, int depth = 0) const;
    QVariantMap decisionNodeToVariant(const std::shared_ptr<DecisionNode> &node) const;
    void populateDecisionTreeWidget(const std::shared_ptr<DecisionNode> &node, QTreeWidgetItem *parentItem = nullptr);
    std::shared_ptr<DecisionNode> decisionNodeFromVariant(const QVariantMap &object) const;

    Ui::TestManagementDialog *ui;
    int m_containerId;
    QSqlDatabase m_db;
    ContainerRepository m_repo;
    std::unique_ptr<BehaviorAggregator> m_aggregator;
    FunctionDependencyResolver m_resolver;
    std::unique_ptr<TestGeneratorService> m_generator;
    QVector<GeneratedTest> m_tests;
    ContainerEntity m_entity;
    QVector<ContainerEntity> m_childEntities;
    DiagnosticMatrixBuilder m_matrixBuilder;
    QVariantMap m_analysisData;
    QStringList m_candidateTests;
    bool m_dirty = false;
    QString m_title;
};

#endif // TESTMANAGEMENTDIALOG_H
