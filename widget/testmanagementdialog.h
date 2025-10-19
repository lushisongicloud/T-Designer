#ifndef TESTMANAGEMENTDIALOG_H
#define TESTMANAGEMENTDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QVector>
#include <memory>

#include "BO/containerrepository.h"
#include "BO/test/testdefinition.h"
#include "BO/test/testgeneratorservice.h"

namespace Ui {
class TestManagementDialog;
}

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

private:
    void initializeGenerator();
    void loadData();
    void refreshTable();
    void updateDetails(int row);
    void updateCoverage();
    bool saveChanges();
    void markDirty();

    Ui::TestManagementDialog *ui;
    int m_containerId;
    QSqlDatabase m_db;
    ContainerRepository m_repo;
    std::unique_ptr<BehaviorAggregator> m_aggregator;
    FunctionDependencyResolver m_resolver;
    std::unique_ptr<TestGeneratorService> m_generator;
    QVector<GeneratedTest> m_tests;
    ContainerEntity m_entity;
    bool m_dirty = false;
    QString m_title;
};

#endif // TESTMANAGEMENTDIALOG_H
