#ifndef FUNCTIONMANAGERDIALOG_H
#define FUNCTIONMANAGERDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QVector>

#include "BO/function/functioninfo.h"
#include "BO/function/functionrepository.h"

namespace Ui {
class FunctionManagerDialog;
}

class SystemEntity;

class FunctionManagerDialog : public QDialog
{
    Q_OBJECT
public:
    explicit FunctionManagerDialog(const QSqlDatabase &db,
                                   int containerId,
                                   const QString &systemDescription = QString(),
                                   SystemEntity *systemEntity = nullptr,
                                   QWidget *parent = nullptr);
    ~FunctionManagerDialog() override;

private slots:
    void onAdd();
    void onEdit();
    void onDelete();
    void onRefresh();
    void onTableDoubleClicked(int row, int column);
    void onSelectionChanged();
    void onAutoDependency();
    void onAutoBoundary();
    void onCheckIntegrity();
    void onAddOffline();
    void onRemoveOffline();
    void onSaveOffline();
    void onSaveRecord();

private:
    void loadData();
    void loadFromFunctionDocument();
    void persistFunctionDocument();
    FunctionRecord fromFunctionInfo(const FunctionInfo &info) const;
    FunctionInfo toFunctionInfo(const FunctionRecord &record) const;
    void updateButtons();
    FunctionRecord currentRecord() const;
    void displayRecord(const FunctionRecord &record);
    void populateOfflineTable();
    void syncOfflineFromTable();
    QStringList parseList(const QString &text) const;
    QList<QPair<QString, QString>> parseCmdValList(const QString &text) const;
    QString serializeCmdValList(const QList<QPair<QString, QString>> &pairs) const;
    void applyOfflineResultsToRecord(FunctionRecord &record) const;
    void restoreOfflineResultsFromRecord(const FunctionRecord &record);
    QString serializeOfflineResults() const;
    void deserializeOfflineResults(const QString &serialized);
    void syncCurrentRecordFromUi();
    void applyAutoDependency(FunctionRecord &record);
    QStringList computeAutoDependency(const FunctionRecord &record) const;
    QStringList computeBoundaryCandidates(const FunctionRecord &record, bool *ok) const;
    QString actuatorVariable(const FunctionRecord &record) const;

    Ui::FunctionManagerDialog *ui;
    QSqlDatabase m_db;
    FunctionRepository m_repo;
    int m_containerId = 0;
    QList<FunctionRecord> m_records;
    FunctionRecord m_currentRecord;
    QVector<FunctionOfflineResult> m_offlineResults;
    QString m_systemDescription;
    QMap<QString, FunctionInfo> m_functionMap;
    SystemEntity *m_systemEntity = nullptr;
};

#endif // FUNCTIONMANAGERDIALOG_H
