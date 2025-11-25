#ifndef FUNCTIONEDITDIALOG_H
#define FUNCTIONEDITDIALOG_H

#include <QDialog>
#include <QSqlDatabase>
#include <QVector>

#include "BO/function/functionrepository.h"
#include "BO/function/functionanalysisservice.h"
#include "BO/function/function_variable_config.h"
#include "BO/componententity.h"

namespace functionvalues {
struct FunctionVariableRow;
}
class SystemEntity;

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
    void setSystemContext(SystemEntity *systemEntity, const QString &systemDescription);

    FunctionRecord record() const { return m_record; }

private slots:
    void onSelectSymbol();
    void onAddInput();
    void onRemoveInput();
    void onAccepted();
    void updateExecList();
    void onAutoAnalyze();
    void onAutoLink();
    void onEditVariableValues();

private:
    void loadSymbolPorts();
    QString buildCmdValList() const;
    QString buildExecList() const;
    void populateInputs(const QString &cmdValList);
    void applyAnalysis(const FunctionModelResult &result);
    functionvalues::FunctionVariableConfig currentVariableConfig() const;
    void setCurrentVariableConfig(const functionvalues::FunctionVariableConfig &config);
    QVector<functionvalues::FunctionVariableRow> collectVariableRows() const;
    QMap<QString, QString> currentConstraintMap() const;
    QString variableConfigToXml(const functionvalues::FunctionVariableConfig &config) const;
    functionvalues::FunctionVariableConfig variableConfigFromXml(const QString &xml) const;
    QStringList variableSuggestions() const;
    QString solveVariableRange(const QString &variable,
                               const QString &typeKey,
                               const QStringList &typicalValues,
                               QString &errorMessage) const;
    QList<TestItem> buildBaseTestItems() const;
    TestItem makeVariableSetterItem(const QString &variable, const QString &valueExpression) const;

    Ui::FunctionEditDialog *ui;
    QSqlDatabase m_db;
    FunctionRecord m_record;
    QVector<PortOption> m_ports;
    FunctionAnalysisService m_analysisService;
    functionvalues::FunctionVariableConfig m_variableConfig;
    SystemEntity *m_systemEntity = nullptr;
    QString m_systemDescription;
};

#endif // FUNCTIONEDITDIALOG_H
