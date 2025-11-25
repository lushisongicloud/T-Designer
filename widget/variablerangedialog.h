#ifndef VARIABLERANGEDIALOG_H
#define VARIABLERANGEDIALOG_H

#include <QDialog>
#include <QMap>
#include <QStringList>

#include "BO/function/variable_range_config.h"

class QListWidget;
class QLabel;
class QLineEdit;
class QPushButton;
class QTableWidget;

class VariableRangeDialog : public QDialog
{
    Q_OBJECT

public:
    VariableRangeDialog(const QMap<QString, QStringList> &typeVariables,
                        const rangeconfig::VariableRangeConfig &initialConfig,
                        QWidget *parent = nullptr);

    rangeconfig::VariableRangeConfig config() const { return workingConfig; }

private slots:
    void onTypeSelectionChanged();
    void onDefaultRangeEdited();
    void onVariableCellChanged(int row, int column);
    void onClearOverrideClicked();

private:
    void setupUi();
    void populateTypeList();
    void loadType(const QString &typeKey);
    void refreshVariableRow(int row);
    QString currentTypeKey() const;
    QString formatRange(const rangeconfig::RangeValue &value) const;
    QString formatDouble(double value) const;

    QListWidget *typeListWidget = nullptr;
    QLabel *typeTitleLabel = nullptr;
    QLineEdit *defaultLowerEdit = nullptr;
    QLineEdit *defaultUpperEdit = nullptr;
    QPushButton *clearOverrideButton = nullptr;
    QTableWidget *variableTable = nullptr;

    QMap<QString, QStringList> typeVariables;
    rangeconfig::VariableRangeConfig workingConfig;
    QString activeTypeKey;
    bool updating = false;
};

#endif // VARIABLERANGEDIALOG_H
