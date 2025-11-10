#ifndef FUNCTIONVARIABLEVALUEDIALOG_H
#define FUNCTIONVARIABLEVALUEDIALOG_H

#include <QDialog>
#include <QMap>
#include <QVector>

#include "BO/function/function_variable_config.h"

namespace Ui {
class FunctionVariableValueDialog;
}

struct FunctionVariableRow
{
    QString variable;
    functionvalues::VariableEntry entry;
};

class FunctionVariableValueDialog : public QDialog
{
    Q_OBJECT

public:
    explicit FunctionVariableValueDialog(const QVector<FunctionVariableRow> &rows,
                                         QWidget *parent = nullptr);
    ~FunctionVariableValueDialog() override;

    QVector<FunctionVariableRow> rows() const;
    void setConstraintMap(const QMap<QString, QString> &map) { constraintMap = map; }
    void setVariableSuggestions(const QStringList &suggestions);

private slots:
    void onAddRow();
    void onRemoveRow();
    void onSyncConstraints();

private:
    void setupTable();
    void populateTable(const QVector<FunctionVariableRow> &rows);
    FunctionVariableRow rowFromTable(int row) const;
    void ensureRowForVariable(const QString &variable);
    QStringList suggestionList() const;

    Ui::FunctionVariableValueDialog *ui;
    QMap<QString, QString> constraintMap;
    QStringList variableSuggestionList;
};

#endif // FUNCTIONVARIABLEVALUEDIALOG_H

