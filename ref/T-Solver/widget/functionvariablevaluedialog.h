#ifndef FUNCTIONVARIABLEVALUEDIALOG_H
#define FUNCTIONVARIABLEVALUEDIALOG_H

#include <QDialog>
#include <QVector>
#include <QString>
#include <QStringList>
#include <functional>

class QTableWidget;
class QPushButton;
class QDialogButtonBox;
class QProgressBar;

namespace functionvalues {

struct FunctionVariableRow
{
    QString variable;
    QString typeKey;
    QString constraintValue;
    bool typeLocked = false;
    bool constraintLocked = false;
    QString typicalValues;
    QString valueRange;
    QStringList satSamples;
};

} // namespace functionvalues

class FunctionVariableValueDialog : public QDialog
{
    Q_OBJECT

public:
    using RangeSolver = std::function<QString(const QString &variable,
                                              const QString &typeKey,
                                              const QStringList &typicalValues,
                                              QString &errorMessage)>;

    FunctionVariableValueDialog(const QVector<functionvalues::FunctionVariableRow> &rows,
                                RangeSolver solver,
                                QWidget *parent = nullptr);

    QVector<functionvalues::FunctionVariableRow> resultRows() const { return workingRows; }

protected:
    void accept() override;

private slots:
    void onFillFromSatClicked();
    void onAutofillRangeClicked();
    void onSolveRangeClicked();
    void onSelectAllClicked();
    void onInvertSelectionClicked();
    void onSolveAllClicked();

private:
    void setupUi();
    void populateTable();
    void syncRowsFromTable();
    QVector<int> selectedRowIndexes() const;
    QVector<int> allRowIndexes() const;
    void solveRows(const QVector<int> &rows);
    void setSolvingState(bool active, int maximum = 0);
    static QString formatDouble(double value);

    QTableWidget *table = nullptr;
    QPushButton *btnFillFromSat = nullptr;
    QPushButton *btnAutofillRange = nullptr;
    QPushButton *btnSolveRange = nullptr;
    QPushButton *btnSolveAll = nullptr;
    QPushButton *btnSelectAll = nullptr;
    QPushButton *btnInvertSelection = nullptr;
    QDialogButtonBox *buttonBox = nullptr;
    QProgressBar *progressBar = nullptr;

    QVector<functionvalues::FunctionVariableRow> workingRows;
    RangeSolver solverCallback;
};

#endif // FUNCTIONVARIABLEVALUEDIALOG_H
