#include "widget/functionvariablevaluedialog.h"
#include "ui_functionvariablevaluedialog.h"

#include <QHeaderView>
#include <QLineEdit>
#include <QMessageBox>
#include <QTableWidgetItem>

#include <algorithm>
#include <functional>

namespace {

QString normalizedSamples(const QString &text)
{
    QString cleaned = text;
    cleaned.replace('\n', ';');
    cleaned.replace(',', ';');
    while (cleaned.contains(";;")) {
        cleaned.replace(";;", ";");
    }
    return cleaned.trimmed();
}

QStringList splitSamples(const QString &text)
{
    const QString normalized = normalizedSamples(text);
    if (normalized.isEmpty()) {
        return {};
    }
    return normalized.split(';', QString::SkipEmptyParts);
}

} // namespace

FunctionVariableValueDialog::FunctionVariableValueDialog(const QVector<FunctionVariableRow> &rows,
                                                         QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::FunctionVariableValueDialog)
{
    ui->setupUi(this);
    setupTable();
    populateTable(rows);

    connect(ui->btnAddRow, &QPushButton::clicked, this, &FunctionVariableValueDialog::onAddRow);
    connect(ui->btnRemoveRow, &QPushButton::clicked, this, &FunctionVariableValueDialog::onRemoveRow);
    connect(ui->btnSyncConstraints, &QPushButton::clicked, this, &FunctionVariableValueDialog::onSyncConstraints);
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &QDialog::accept);
    connect(ui->buttonBox, &QDialogButtonBox::rejected, this, &QDialog::reject);
}

FunctionVariableValueDialog::~FunctionVariableValueDialog()
{
    delete ui;
}

void FunctionVariableValueDialog::setupTable()
{
    ui->tableVariables->setColumnCount(6);
    ui->tableVariables->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableVariables->setSelectionMode(QAbstractItemView::ExtendedSelection);
    ui->tableVariables->setEditTriggers(QAbstractItemView::DoubleClicked | QAbstractItemView::SelectedClicked | QAbstractItemView::EditKeyPressed);
    ui->tableVariables->horizontalHeader()->setStretchLastSection(true);
    ui->tableVariables->verticalHeader()->setVisible(false);
}

void FunctionVariableValueDialog::populateTable(const QVector<FunctionVariableRow> &rows)
{
    ui->tableVariables->setRowCount(0);
    for (const FunctionVariableRow &row : rows) {
        const int tableRow = ui->tableVariables->rowCount();
        ui->tableVariables->insertRow(tableRow);
        auto createItem = [&](int column, const QString &text) {
            QTableWidgetItem *item = new QTableWidgetItem(text);
            item->setFlags(Qt::ItemIsSelectable | Qt::ItemIsEditable | Qt::ItemIsEnabled);
            ui->tableVariables->setItem(tableRow, column, item);
        };
        createItem(0, row.variable);
        createItem(1, row.entry.type);
        createItem(2, row.entry.constraintValue);
        createItem(3, row.entry.typicalValues);
        createItem(4, row.entry.valueRange);
        createItem(5, row.entry.satSamples.join(QStringLiteral(";")));
    }
}

QVector<FunctionVariableRow> FunctionVariableValueDialog::rows() const
{
    QVector<FunctionVariableRow> result;
    for (int row = 0; row < ui->tableVariables->rowCount(); ++row) {
        FunctionVariableRow data = rowFromTable(row);
        if (data.variable.trimmed().isEmpty())
            continue;
        result.append(data);
    }
    return result;
}

void FunctionVariableValueDialog::setVariableSuggestions(const QStringList &suggestions)
{
    variableSuggestionList = suggestions;
}

FunctionVariableRow FunctionVariableValueDialog::rowFromTable(int row) const
{
    FunctionVariableRow result;
    if (row < 0 || row >= ui->tableVariables->rowCount())
        return result;
    auto itemText = [&](int column) -> QString {
        QTableWidgetItem *item = ui->tableVariables->item(row, column);
        return item ? item->text().trimmed() : QString();
    };
    result.variable = itemText(0);
    result.entry.type = itemText(1);
    result.entry.constraintValue = itemText(2);
    result.entry.typicalValues = itemText(3);
    result.entry.valueRange = itemText(4);
    result.entry.satSamples = splitSamples(itemText(5));
    return result;
}

void FunctionVariableValueDialog::onAddRow()
{
    const int row = ui->tableVariables->rowCount();
    ui->tableVariables->insertRow(row);
    auto createItem = [&](int column, const QString &text) {
        QTableWidgetItem *item = new QTableWidgetItem(text);
        item->setFlags(Qt::ItemIsSelectable | Qt::ItemIsEditable | Qt::ItemIsEnabled);
        ui->tableVariables->setItem(row, column, item);
    };
    QString variableSuggestion;
    for (const QString &candidate : suggestionList()) {
        bool exists = false;
        for (int r = 0; r < ui->tableVariables->rowCount(); ++r) {
            if (ui->tableVariables->item(r, 0) && ui->tableVariables->item(r, 0)->text().trimmed() == candidate) {
                exists = true;
                break;
            }
        }
        if (!exists) {
            variableSuggestion = candidate;
            break;
        }
    }
    createItem(0, variableSuggestion);
    createItem(1, QString());
    createItem(2, QString());
    createItem(3, QString());
    createItem(4, QString());
    createItem(5, QString());
    ui->tableVariables->setCurrentCell(row, 0);
    ui->tableVariables->editItem(ui->tableVariables->item(row, 0));
}

void FunctionVariableValueDialog::onRemoveRow()
{
    QList<int> rowsToRemove;
    const auto selected = ui->tableVariables->selectionModel()->selectedRows();
    for (const QModelIndex &index : selected) {
        rowsToRemove.append(index.row());
    }
    std::sort(rowsToRemove.begin(), rowsToRemove.end(), std::greater<int>());
    for (int row : rowsToRemove) {
        ui->tableVariables->removeRow(row);
    }
}

void FunctionVariableValueDialog::ensureRowForVariable(const QString &variable)
{
    if (variable.trimmed().isEmpty())
        return;
    for (int row = 0; row < ui->tableVariables->rowCount(); ++row) {
        QTableWidgetItem *item = ui->tableVariables->item(row, 0);
        if (item && item->text().trimmed() == variable) {
            return;
        }
    }
    onAddRow();
    int lastRow = ui->tableVariables->rowCount() - 1;
    if (lastRow >= 0) {
        ui->tableVariables->item(lastRow, 0)->setText(variable);
    }
}

void FunctionVariableValueDialog::onSyncConstraints()
{
    if (constraintMap.isEmpty()) {
        QMessageBox::information(this, tr("同步输入约束"), tr("当前没有可同步的约束。"));
        return;
    }
    for (auto it = constraintMap.constBegin(); it != constraintMap.constEnd(); ++it) {
        const QString variable = it.key().trimmed();
        if (variable.isEmpty()) {
            continue;
        }
        ensureRowForVariable(variable);
        for (int row = 0; row < ui->tableVariables->rowCount(); ++row) {
            QTableWidgetItem *item = ui->tableVariables->item(row, 0);
            if (item && item->text().trimmed() == variable) {
                QTableWidgetItem *constraintItem = ui->tableVariables->item(row, 2);
                if (constraintItem) {
                    constraintItem->setText(it.value());
                }
                break;
            }
        }
    }
}

QStringList FunctionVariableValueDialog::suggestionList() const
{
    return variableSuggestionList;
}
