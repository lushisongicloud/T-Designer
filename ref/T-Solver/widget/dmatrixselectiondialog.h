#ifndef DMATRIXSELECTIONDIALOG_H
#define DMATRIXSELECTIONDIALOG_H

#include <QDialog>
#include <QVector>

#include "testability/testability_types.h"

class QComboBox;
class QLineEdit;
class QStandardItem;
class QStandardItemModel;
class QTableView;

class DMatrixSelectionDialog : public QDialog
{
    Q_OBJECT
public:
    enum class Target {
        Tests,
        Faults
    };

    explicit DMatrixSelectionDialog(Target target, QWidget *parent = nullptr);
    ~DMatrixSelectionDialog() override;

    void setTests(const QVector<testability::TestDefinition> &tests,
                  const QVector<bool> &enabledStates);
    void setFaults(const QVector<testability::FaultDefinition> &faults,
                   const QVector<bool> &enabledStates);

    QVector<bool> enabledStates() const;

private slots:
    void onFilterTextChanged(const QString &text);
    void onTypeFilterChanged(int index);
    void onEnableSelected();
    void onDisableSelected();
    void onSelectAllRows();
    void onInvertSelection();
    void onItemChanged(QStandardItem *item);

private:
    void accept() override;
    void reject() override;
    struct TestRow {
        testability::TestDefinition definition;
        bool enabled = true;
    };

    struct FaultRow {
        testability::FaultDefinition definition;
        bool enabled = true;
    };

    void rebuildModel();
    void updateRowVisibility();
    bool matchesFilter(int row) const;
    void setRowChecked(int row, bool checked);
    QList<int> selectedRows() const;

    bool updatingModel = false;

    Target target = Target::Tests;
    QVector<TestRow> tests;
    QVector<FaultRow> faults;

    QLineEdit *filterEdit = nullptr;
    QComboBox *typeCombo = nullptr;
    QTableView *tableView = nullptr;
    QStandardItemModel *model = nullptr;

    QString filterText;
    int typeFilterIndex = 0;
};

#endif // DMATRIXSELECTIONDIALOG_H
