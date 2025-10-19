#ifndef FUNCTIONEDITDIALOG_H
#define FUNCTIONEDITDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QVector>

#include "BO/function/functionrepository.h"
#include "BO/function/functionanalysisservice.h"

struct PortOption
{
    QString portName;
    QString description;
};

namespace Ui {
class FunctionEditDialog;
}

class FunctionEditDialog : public QDialog
{
    Q_OBJECT

public:
    explicit FunctionEditDialog(const QSqlDatabase &db, QWidget *parent = nullptr);
    void setInitialRecord(const FunctionRecord &record);
    void setSymbol(int symbolId, const QString &symbolName);
    void analyzeCurrentSymbol();

    FunctionRecord record() const { return m_record; }

private slots:
    void onSelectSymbol();
    void onAddInput();
    void onRemoveInput();
    void onAccepted();
    void updateExecList();
    void onAutoAnalyze();

private:
    void loadSymbolPorts();
    QString buildCmdValList() const;
    QString buildExecList() const;
    void populateInputs(const QString &cmdValList);
    void applyAnalysis(const FunctionModelResult &result);

    Ui::FunctionEditDialog *ui;
    QSqlDatabase m_db;
    FunctionRecord m_record;
    QVector<PortOption> m_ports;
    FunctionAnalysisService m_analysisService;
};

#endif // FUNCTIONEDITDIALOG_H
