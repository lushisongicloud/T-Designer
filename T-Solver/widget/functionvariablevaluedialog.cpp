#include "functionvariablevaluedialog.h"

#include <QCoreApplication>
#include <QDialogButtonBox>
#include <QEventLoop>
#include <QHeaderView>
#include <QHBoxLayout>
#include <QItemSelectionModel>
#include <QMessageBox>
#include <QProgressBar>
#include <QPushButton>
#include <QTableWidget>
#include <QTableWidgetItem>
#include <QVBoxLayout>
#include <algorithm>
#include <cmath>

using functionvalues::FunctionVariableRow;

namespace {

const int COLUMN_VARIABLE = 0;
const int COLUMN_TYPE = 1;
const int COLUMN_CONSTRAINT = 2;
const int COLUMN_TYPICAL = 3;
const int COLUMN_RANGE = 4;
const int COLUMN_SAT = 5;

QString joinSamples(const QStringList &samples)
{
    return samples.join(QString(";"));
}

QStringList splitSamples(const QString &text)
{
    QStringList result;
    const QStringList parts = text.split(QString(";"), QString::SkipEmptyParts);
    for (const QString &part : parts) {
        const QString trimmed = part.trimmed();
        if (!trimmed.isEmpty()) {
            result.append(trimmed);
        }
    }
    return result;
}

bool parseDouble(const QString &text, double *value)
{
    if (!value) {
        return false;
    }
    bool ok = false;
    const double parsed = text.trimmed().toDouble(&ok);
    if (ok) {
        *value = parsed;
    }
    return ok;
}

} // namespace

FunctionVariableValueDialog::FunctionVariableValueDialog(const QVector<FunctionVariableRow> &rows,
                                                         RangeSolver solver,
                                                         QWidget *parent)
    : QDialog(parent),
      workingRows(rows),
      solverCallback(std::move(solver))
{
    setWindowTitle(QString("求解变量可行解范围"));
    resize(920, 560);
    setupUi();
    populateTable();
}

void FunctionVariableValueDialog::setupUi()
{
    auto *layout = new QVBoxLayout(this);

    table = new QTableWidget(this);
    table->setColumnCount(6);
    table->setHorizontalHeaderLabels(QStringList()
                                     << QString("变量名")
                                     << QString("类型")
                                     << QString("约束值")
                                     << QString("典型值")
                                     << QString("取值区间")
                                     << QString("SAT模型可行解"));
    table->horizontalHeader()->setSectionResizeMode(QHeaderView::Stretch);
    table->setSelectionBehavior(QAbstractItemView::SelectRows);
    table->setSelectionMode(QAbstractItemView::ExtendedSelection);
    table->setEditTriggers(QAbstractItemView::DoubleClicked | QAbstractItemView::SelectedClicked | QAbstractItemView::EditKeyPressed);

    layout->addWidget(table);

    auto *selectionLayout = new QHBoxLayout();
    btnSelectAll = new QPushButton(QString("全选"), this);
    btnInvertSelection = new QPushButton(QString("反选"), this);
    selectionLayout->addWidget(btnSelectAll);
    selectionLayout->addWidget(btnInvertSelection);
    selectionLayout->addStretch();
    layout->addLayout(selectionLayout);
    btnFillFromSat = new QPushButton(QString("自动填写选中行典型值"), this);
    btnAutofillRange = new QPushButton(QString("自动填写选中行取值区间"), this);
    btnSolveRange = new QPushButton(QString("求解选中变量的可行域范围"), this);
    btnSolveAll = new QPushButton(QString("一键求取所有变量的可行解范围"), this);

    auto *bulkLayout = new QHBoxLayout();
    bulkLayout->addWidget(btnFillFromSat);
    bulkLayout->addWidget(btnAutofillRange);
    bulkLayout->addWidget(btnSolveRange);
    bulkLayout->addWidget(btnSolveAll);
    bulkLayout->addStretch();
    layout->addLayout(bulkLayout);

    progressBar = new QProgressBar(this);
    progressBar->setVisible(false);
    progressBar->setRange(0, 1);
    progressBar->setValue(0);
    progressBar->setFormat(QString("求解进度: %v/%m"));
    layout->addWidget(progressBar);

    buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok | QDialogButtonBox::Cancel, this);
    layout->addWidget(buttonBox);

    connect(btnSelectAll, &QPushButton::clicked, this, &FunctionVariableValueDialog::onSelectAllClicked);
    connect(btnInvertSelection, &QPushButton::clicked, this, &FunctionVariableValueDialog::onInvertSelectionClicked);
    connect(btnFillFromSat, &QPushButton::clicked, this, &FunctionVariableValueDialog::onFillFromSatClicked);
    connect(btnAutofillRange, &QPushButton::clicked, this, &FunctionVariableValueDialog::onAutofillRangeClicked);
    connect(btnSolveRange, &QPushButton::clicked, this, &FunctionVariableValueDialog::onSolveRangeClicked);
    connect(btnSolveAll, &QPushButton::clicked, this, &FunctionVariableValueDialog::onSolveAllClicked);
    connect(buttonBox, &QDialogButtonBox::accepted, this, &FunctionVariableValueDialog::accept);
    connect(buttonBox, &QDialogButtonBox::rejected, this, &FunctionVariableValueDialog::reject);
}

void FunctionVariableValueDialog::populateTable()
{
    table->setRowCount(workingRows.size());
    for (int row = 0; row < workingRows.size(); ++row) {
        const FunctionVariableRow &entry = workingRows.at(row);

        auto *variableItem = new QTableWidgetItem(entry.variable);
        variableItem->setFlags(variableItem->flags() & ~Qt::ItemIsEditable);
        table->setItem(row, COLUMN_VARIABLE, variableItem);

        auto *typeItem = new QTableWidgetItem(entry.typeKey);
        if (entry.typeLocked) {
            typeItem->setFlags(typeItem->flags() & ~Qt::ItemIsEditable);
        }
        table->setItem(row, COLUMN_TYPE, typeItem);

        auto *constraintItem = new QTableWidgetItem(entry.constraintValue);
        if (entry.constraintLocked) {
            constraintItem->setFlags(constraintItem->flags() & ~Qt::ItemIsEditable);
        }
        table->setItem(row, COLUMN_CONSTRAINT, constraintItem);

        table->setItem(row, COLUMN_TYPICAL, new QTableWidgetItem(entry.typicalValues));
        table->setItem(row, COLUMN_RANGE, new QTableWidgetItem(entry.valueRange));

        auto *satItem = new QTableWidgetItem(joinSamples(entry.satSamples));
        satItem->setFlags(satItem->flags() & ~Qt::ItemIsEditable);
        table->setItem(row, COLUMN_SAT, satItem);
    }
}

void FunctionVariableValueDialog::syncRowsFromTable()
{
    if (!table) {
        return;
    }
    const int rowCount = table->rowCount();
    if (workingRows.size() != rowCount) {
        workingRows.resize(rowCount);
    }
    for (int row = 0; row < rowCount; ++row) {
        FunctionVariableRow entry = workingRows.value(row);
        entry.variable = table->item(row, COLUMN_VARIABLE)->text().trimmed();
        entry.typeKey = table->item(row, COLUMN_TYPE)->text().trimmed();
        entry.constraintValue = table->item(row, COLUMN_CONSTRAINT)->text().trimmed();
        entry.typicalValues = table->item(row, COLUMN_TYPICAL)->text().trimmed();
        entry.valueRange = table->item(row, COLUMN_RANGE)->text().trimmed();
        entry.satSamples = splitSamples(table->item(row, COLUMN_SAT)->text());
        workingRows[row] = entry;
    }
}

QVector<int> FunctionVariableValueDialog::selectedRowIndexes() const
{
    QVector<int> rows;
    if (!table) {
        return rows;
    }
    const QModelIndexList selected = table->selectionModel()->selectedRows();
    rows.reserve(selected.size());
    for (const QModelIndex &index : selected) {
        rows.append(index.row());
    }
    return rows;
}

QVector<int> FunctionVariableValueDialog::allRowIndexes() const
{
    QVector<int> rows;
    if (!table) {
        return rows;
    }
    const int totalRows = table->rowCount();
    rows.reserve(totalRows);
    for (int row = 0; row < totalRows; ++row) {
        rows.append(row);
    }
    return rows;
}

void FunctionVariableValueDialog::setSolvingState(bool active, int maximum)
{
    if (!progressBar) {
        return;
    }

    if (active) {
        const int maxValue = maximum > 0 ? maximum : 1;
        progressBar->setRange(0, maxValue);
        progressBar->setValue(0);
    } else {
        progressBar->setRange(0, 1);
        progressBar->setValue(0);
    }
    progressBar->setVisible(active);

    const bool enabled = !active;
    if (table) {
        table->setEnabled(enabled);
    }
    if (btnFillFromSat) {
        btnFillFromSat->setEnabled(enabled);
    }
    if (btnAutofillRange) {
        btnAutofillRange->setEnabled(enabled);
    }
    if (btnSolveRange) {
        btnSolveRange->setEnabled(enabled);
    }
    if (btnSolveAll) {
        btnSolveAll->setEnabled(enabled);
    }
    if (btnSelectAll) {
        btnSelectAll->setEnabled(enabled);
    }
    if (btnInvertSelection) {
        btnInvertSelection->setEnabled(enabled);
    }
    if (buttonBox) {
        buttonBox->setEnabled(enabled);
    }
}

void FunctionVariableValueDialog::solveRows(const QVector<int> &rows)
{
    if (!solverCallback) {
        QMessageBox::warning(this, QString("提示"), QString("缺少求解算法"));
        return;
    }
    if (rows.isEmpty()) {
        return;
    }

    setSolvingState(true, rows.size());
    QStringList errors;
    int progress = 0;

    for (int row : rows) {
        if (!table || row < 0 || row >= table->rowCount()) {
            ++progress;
            if (progressBar) {
                progressBar->setValue(progress);
            }
            QCoreApplication::processEvents(QEventLoop::AllEvents, 50);
            continue;
        }

        QTableWidgetItem *variableItem = table->item(row, COLUMN_VARIABLE);
        QTableWidgetItem *typeItem = table->item(row, COLUMN_TYPE);
        QTableWidgetItem *typicalItem = table->item(row, COLUMN_TYPICAL);
        QTableWidgetItem *rangeItem = table->item(row, COLUMN_RANGE);

        if (!variableItem || !typeItem || !typicalItem || !rangeItem) {
            errors.append(QString("第 %1 行数据不完整，已跳过。").arg(row + 1));
            ++progress;
            if (progressBar) {
                progressBar->setValue(progress);
            }
            QCoreApplication::processEvents(QEventLoop::AllEvents, 50);
            continue;
        }

        const QString variable = variableItem->text().trimmed();
        const QString typeKey = typeItem->text().trimmed();
        const QString typicalText = typicalItem->text().trimmed();
        QStringList typicalList = splitSamples(typicalText);
        if (typicalList.isEmpty()) {
            errors.append(QString("变量 %1 缺少典型值，无法求解。").arg(variable));
            ++progress;
            if (progressBar) {
                progressBar->setValue(progress);
            }
            QCoreApplication::processEvents(QEventLoop::AllEvents, 50);
            continue;
        }

        QString errorMessage;
        QString rangeText = solverCallback(variable, typeKey, typicalList, errorMessage);
        if (!rangeText.isEmpty()) {
            rangeItem->setText(rangeText);
        } else {
            if (!errorMessage.isEmpty()) {
                errors.append(errorMessage);
            } else {
                errors.append(QString("变量 %1 无法求解有效取值范围。").arg(variable));
            }
        }

        ++progress;
        if (progressBar) {
            progressBar->setValue(progress);
        }
        QCoreApplication::processEvents(QEventLoop::AllEvents, 50);
    }

    setSolvingState(false);

    if (!errors.isEmpty()) {
        QMessageBox::warning(this, QString("提示"), errors.join(QString("\n")));
    }
}

QString FunctionVariableValueDialog::formatDouble(double value)
{
    if (std::fabs(value) < 1e-12) {
        value = 0.0;
    }
    QString text = QString::number(value, 'f', 3);
    if (text.contains(QLatin1Char('.'))) {
        while (text.endsWith(QLatin1Char('0'))) {
            text.chop(1);
        }
        if (text.endsWith(QLatin1Char('.'))) {
            text.chop(1);
        }
    }
    if (text == QString("-0")) {
        text = QString("0");
    }
    return text;
}

void FunctionVariableValueDialog::accept()
{
    syncRowsFromTable();
    QDialog::accept();
}

void FunctionVariableValueDialog::onFillFromSatClicked()
{
    const QVector<int> rows = selectedRowIndexes();
    if (rows.isEmpty()) {
        QMessageBox::information(this, QString("提示"), QString("请先选择需要填写的行"));
        return;
    }
    for (int row : rows) {
        const QString satText = table->item(row, COLUMN_SAT)->text().trimmed();
        if (!satText.isEmpty()) {
            table->item(row, COLUMN_TYPICAL)->setText(satText);
        }
    }
}

void FunctionVariableValueDialog::onAutofillRangeClicked()
{
    const QVector<int> rows = selectedRowIndexes();
    if (rows.isEmpty()) {
        QMessageBox::information(this, QString("提示"), QString("请先选择需要填写的行"));
        return;
    }
    for (int row : rows) {
        if (!table) {
            continue;
        }
        QTableWidgetItem *typeItem = table->item(row, COLUMN_TYPE);
        const QString typeText = typeItem ? typeItem->text().trimmed() : QString();
        const QString typicalText = table->item(row, COLUMN_TYPICAL)->text().trimmed();
        if (typicalText.isEmpty()) {
            continue;
        }
        const QStringList typicalList = splitSamples(typicalText);
        auto isBoolean = [&]() -> bool {
            const QString lowerType = typeText.toLower();
            if (lowerType == QStringLiteral("bool") || lowerType == QStringLiteral("boolean")
                || typeText.contains(QStringLiteral("布尔"), Qt::CaseInsensitive)) {
                return true;
            }
            for (const QString &item : typicalList) {
                const QString value = item.trimmed().toLower();
                if (value == QStringLiteral("true") || value == QStringLiteral("false")
                    || value == QStringLiteral("是") || value == QStringLiteral("否")) {
                    return true;
                }
            }
            return false;
        }();

        if (isBoolean) {
            table->item(row, COLUMN_RANGE)->setText(typicalText);
            continue;
        }

        QStringList intervals;
        for (const QString &item : typicalList) {
            double value = 0.0;
            if (!parseDouble(item, &value)) {
                continue;
            }
            double lower = value * 0.8;
            double upper = value * 1.2;
            if (lower > upper) {
                std::swap(lower, upper);
            }
            intervals.append(QString("[%1, %2]")
                              .arg(formatDouble(lower), formatDouble(upper)));
        }
        if (!intervals.isEmpty()) {
            table->item(row, COLUMN_RANGE)->setText(intervals.join(QString(";")));
        }
    }
}

void FunctionVariableValueDialog::onSolveRangeClicked()
{
    const QVector<int> rows = selectedRowIndexes();
    if (rows.isEmpty()) {
        QMessageBox::information(this, QString("提示"), QString("请先选择需要求解的行"));
        return;
    }
    solveRows(rows);
}

void FunctionVariableValueDialog::onSelectAllClicked()
{
    if (table) {
        table->selectAll();
    }
}

void FunctionVariableValueDialog::onInvertSelectionClicked()
{
    if (!table) {
        return;
    }
    QItemSelectionModel *selectionModel = table->selectionModel();
    if (!selectionModel) {
        return;
    }

    for (int row = 0; row < table->rowCount(); ++row) {
        const bool isSelected = selectionModel->isRowSelected(row, QModelIndex());
        const QItemSelectionModel::SelectionFlag flag = isSelected
                ? QItemSelectionModel::Deselect
                : QItemSelectionModel::Select;
        selectionModel->select(table->model()->index(row, 0),
                               QItemSelectionModel::Rows | flag);
    }
}

void FunctionVariableValueDialog::onSolveAllClicked()
{
    const QVector<int> rows = allRowIndexes();
    if (rows.isEmpty()) {
        QMessageBox::information(this, QString("提示"), QString("没有变量可供求解。"));
        return;
    }

    if (table) {
        table->selectAll();
    }

    onFillFromSatClicked();
    onAutofillRangeClicked();
    solveRows(rows);
}
