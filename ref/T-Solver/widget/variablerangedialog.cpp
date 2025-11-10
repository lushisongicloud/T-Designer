#include "variablerangedialog.h"

#include <QDialogButtonBox>
#include <QDoubleValidator>
#include <QHeaderView>
#include <QLabel>
#include <QLineEdit>
#include <QListWidget>
#include <QPushButton>
#include <QTableWidget>
#include <QVBoxLayout>

#include <algorithm>
#include <cmath>
#include <QDebug>

// 调试开关
#define VARIABLE_RANGE_DEBUG 0

#if VARIABLE_RANGE_DEBUG
#define DEBUG qDebug
#else
#define DEBUG if (0) qDebug
#endif

namespace {

QString composeDisplayName(const QString &typeKey)
{
    const QString display = rangeconfig::VariableRangeConfig::typeDisplayName(typeKey);
    if (display == typeKey) {
        return display;
    }
    return QString("%1 (%2)").arg(display, typeKey);
}

} // namespace

VariableRangeDialog::VariableRangeDialog(const QMap<QString, QStringList> &typeVariables,
                                         const rangeconfig::VariableRangeConfig &initialConfig,
                                         QWidget *parent)
    : QDialog(parent),
      typeVariables(typeVariables),
      workingConfig(initialConfig)
{
    DEBUG() << "VariableRangeDialog: Constructor called";
    setWindowTitle(QString("变量取值范围"));
    resize(880, 540);
    setupUi();
    populateTypeList();
}

void VariableRangeDialog::setupUi()
{
    DEBUG() << "VariableRangeDialog: setupUi called";
    auto *mainLayout = new QVBoxLayout(this);
    auto *contentLayout = new QHBoxLayout();
    mainLayout->addLayout(contentLayout);

    typeListWidget = new QListWidget(this);
    typeListWidget->setSelectionMode(QAbstractItemView::SingleSelection);
    typeListWidget->setMinimumWidth(200);
    contentLayout->addWidget(typeListWidget);

    auto *rightLayout = new QVBoxLayout();
    contentLayout->addLayout(rightLayout, 1);

    auto *headerLayout = new QHBoxLayout();
    typeTitleLabel = new QLabel(this);
    typeTitleLabel->setText(QString("请选择变量类型"));
    headerLayout->addWidget(typeTitleLabel);
    headerLayout->addStretch(1);

    headerLayout->addWidget(new QLabel(QString("下限:"), this));
    defaultLowerEdit = new QLineEdit(this);
    defaultLowerEdit->setValidator(new QDoubleValidator(defaultLowerEdit));
    defaultLowerEdit->setMaximumWidth(120);
    headerLayout->addWidget(defaultLowerEdit);

    headerLayout->addSpacing(12);
    headerLayout->addWidget(new QLabel(QString("上限:"), this));
    defaultUpperEdit = new QLineEdit(this);
    defaultUpperEdit->setValidator(new QDoubleValidator(defaultUpperEdit));
    defaultUpperEdit->setMaximumWidth(120);
    headerLayout->addWidget(defaultUpperEdit);

    headerLayout->addSpacing(12);
    clearOverrideButton = new QPushButton(QString("清除选中变量配置"), this);
    headerLayout->addWidget(clearOverrideButton);

    rightLayout->addLayout(headerLayout);

    variableTable = new QTableWidget(this);
    variableTable->setColumnCount(4);
    variableTable->setHorizontalHeaderLabels(QStringList()
                                             << QString("变量")
                                             << QString("继承范围")
                                             << QString("下限")
                                             << QString("上限"));
    variableTable->horizontalHeader()->setStretchLastSection(true);
    variableTable->setSelectionBehavior(QAbstractItemView::SelectRows);
    variableTable->setSelectionMode(QAbstractItemView::ExtendedSelection);
    variableTable->setEditTriggers(QAbstractItemView::DoubleClicked | QAbstractItemView::SelectedClicked | QAbstractItemView::EditKeyPressed);
    rightLayout->addWidget(variableTable, 1);

    auto *buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok | QDialogButtonBox::Cancel, this);
    mainLayout->addWidget(buttonBox);

    connect(buttonBox, &QDialogButtonBox::accepted, this, &QDialog::accept);
    connect(buttonBox, &QDialogButtonBox::rejected, this, &QDialog::reject);
    connect(typeListWidget, &QListWidget::currentRowChanged, this, [this](int){ onTypeSelectionChanged(); });
    connect(defaultLowerEdit, &QLineEdit::editingFinished, this, &VariableRangeDialog::onDefaultRangeEdited);
    connect(defaultUpperEdit, &QLineEdit::editingFinished, this, &VariableRangeDialog::onDefaultRangeEdited);
    connect(variableTable, &QTableWidget::cellChanged, this, &VariableRangeDialog::onVariableCellChanged);
    connect(clearOverrideButton, &QPushButton::clicked, this, &VariableRangeDialog::onClearOverrideClicked);
}

void VariableRangeDialog::populateTypeList()
{
    DEBUG() << "VariableRangeDialog: populateTypeList called";
    QStringList keys = typeVariables.keys();
    std::sort(keys.begin(), keys.end());
    for (const QString &key : keys) {
        DEBUG() << "VariableRangeDialog: Adding key to list:" << key;
        QListWidgetItem *item = new QListWidgetItem(composeDisplayName(key), typeListWidget);
        item->setData(Qt::UserRole, key);
    }
    if (typeListWidget->count() > 0) {
        typeListWidget->setCurrentRow(0);
    } else {
        typeTitleLabel->setText(QString("当前模型没有可配置的变量类型"));
        defaultLowerEdit->setEnabled(false);
        defaultUpperEdit->setEnabled(false);
        clearOverrideButton->setEnabled(false);
        variableTable->setEnabled(false);
    }
}

void VariableRangeDialog::onTypeSelectionChanged()
{
    DEBUG() << "VariableRangeDialog: onTypeSelectionChanged called";
    if (updating) {
        DEBUG() << "VariableRangeDialog: Updating, skipping";
        return;
    }
    const QString typeKey = currentTypeKey();
    DEBUG() << "VariableRangeDialog: Selected type key:" << typeKey;
    if (typeKey.isEmpty()) {
        DEBUG() << "VariableRangeDialog: Type key is empty, returning";
        return;
    }
    loadType(typeKey);
}

void VariableRangeDialog::loadType(const QString &typeKey)
{
    DEBUG() << "VariableRangeDialog: loadType called with typeKey:" << typeKey;
    updating = true;
    activeTypeKey = typeKey;

    typeTitleLabel->setText(composeDisplayName(typeKey));

    rangeconfig::RangeValue typeRange = workingConfig.typeRange(typeKey);
    DEBUG() << "VariableRangeDialog: Type range - lower:" << typeRange.lower << "upper:" << typeRange.upper;
    defaultLowerEdit->setText(formatDouble(typeRange.lower));
    defaultUpperEdit->setText(formatDouble(typeRange.upper));

    QStringList variables = typeVariables.value(typeKey);
    DEBUG() << "VariableRangeDialog: Variables count for type:" << variables.size();
    std::sort(variables.begin(), variables.end());
    variableTable->setRowCount(variables.size());
    for (int row = 0; row < variables.size(); ++row) {
        const QString &variable = variables.at(row);
        DEBUG() << "VariableRangeDialog: Processing variable at row" << row << ":" << variable;
        QTableWidgetItem *nameItem = new QTableWidgetItem(variable);
        nameItem->setFlags(nameItem->flags() & ~Qt::ItemIsEditable);
        variableTable->setItem(row, 0, nameItem);

        QTableWidgetItem *rangeItem = new QTableWidgetItem();
        rangeItem->setFlags(rangeItem->flags() & ~Qt::ItemIsEditable);
        variableTable->setItem(row, 1, rangeItem);

        QTableWidgetItem *lowerItem = new QTableWidgetItem();
        variableTable->setItem(row, 2, lowerItem);
        QTableWidgetItem *upperItem = new QTableWidgetItem();
        variableTable->setItem(row, 3, upperItem);

        refreshVariableRow(row);
    }
    updating = false;
}

void VariableRangeDialog::refreshVariableRow(int row)
{
    DEBUG() << "VariableRangeDialog: refreshVariableRow called for row:" << row;
    if (row < 0 || row >= variableTable->rowCount()) {
        DEBUG() << "VariableRangeDialog: Invalid row index";
        return;
    }
    const QString typeKey = currentTypeKey();
    if (typeKey.isEmpty()) {
        DEBUG() << "VariableRangeDialog: Type key is empty";
        return;
    }

    QTableWidgetItem *varItem = variableTable->item(row, 0);
    if (!varItem) {
        DEBUG() << "VariableRangeDialog: Missing variable item";
        return;
    }
    const QString variable = varItem->text();
    DEBUG() << "VariableRangeDialog: Refreshing variable:" << variable;
    rangeconfig::RangeValue effective = workingConfig.effectiveRange(typeKey, variable);
    rangeconfig::RangeValue override = workingConfig.variableRange(typeKey, variable);

    updating = true;
    if (QTableWidgetItem *rangeItem = variableTable->item(row, 1)) {
        rangeItem->setText(formatRange(effective));
    }
    if (QTableWidgetItem *lowerItem = variableTable->item(row, 2)) {
        lowerItem->setText(override.hasExplicit ? formatDouble(override.lower) : QString());
    }
    if (QTableWidgetItem *upperItem = variableTable->item(row, 3)) {
        upperItem->setText(override.hasExplicit ? formatDouble(override.upper) : QString());
    }
    updating = false;
}

QString VariableRangeDialog::currentTypeKey() const
{
    QListWidgetItem *item = typeListWidget->currentItem();
    if (!item) {
        DEBUG() << "VariableRangeDialog: No current item in type list";
        return QString();
    }
    QString typeKey = item->data(Qt::UserRole).toString();
    DEBUG() << "VariableRangeDialog: Current type key from item:" << typeKey;
    return typeKey;
}

void VariableRangeDialog::onDefaultRangeEdited()
{
    DEBUG() << "VariableRangeDialog: onDefaultRangeEdited called";
    if (updating) {
        DEBUG() << "VariableRangeDialog: Updating, skipping";
        return;
    }
    const QString typeKey = currentTypeKey();
    DEBUG() << "VariableRangeDialog: Editing default range for type:" << typeKey;
    if (typeKey.isEmpty()) {
        DEBUG() << "VariableRangeDialog: Type key is empty, returning";
        return;
    }

    const QString lowerText = defaultLowerEdit->text().trimmed();
    const QString upperText = defaultUpperEdit->text().trimmed();
    DEBUG() << "VariableRangeDialog: Lower text:" << lowerText << "Upper text:" << upperText;
    if (lowerText.isEmpty() || upperText.isEmpty()) {
        DEBUG() << "VariableRangeDialog: Clearing type range";
        workingConfig.clearTypeRange(typeKey);
    } else {
        bool lowerOk = false;
        bool upperOk = false;
        double lower = lowerText.toDouble(&lowerOk);
        double upper = upperText.toDouble(&upperOk);
        DEBUG() << "VariableRangeDialog: Parsed lower:" << lower << "upper:" << upper;
        if (!lowerOk || !upperOk) {
            DEBUG() << "VariableRangeDialog: Failed to parse values, lowerOk:" << lowerOk << "upperOk:" << upperOk;
            return;
        }
        rangeconfig::RangeValue value;
        value.lower = lower;
        value.upper = upper;
        value.hasExplicit = true;
        workingConfig.setTypeRange(typeKey, value);
    }
    loadType(typeKey);
}

void VariableRangeDialog::onVariableCellChanged(int row, int column)
{
    DEBUG() << "VariableRangeDialog: onVariableCellChanged called for row:" << row << "column:" << column;
    if (updating) {
        DEBUG() << "VariableRangeDialog: Updating, skipping";
        return;
    }
    if (column != 2 && column != 3) {
        DEBUG() << "VariableRangeDialog: Column is not 2 or 3, skipping";
        return;
    }
    const QString typeKey = currentTypeKey();
    DEBUG() << "VariableRangeDialog: Type key:" << typeKey;
    if (typeKey.isEmpty()) {
        DEBUG() << "VariableRangeDialog: Type key is empty, returning";
        return;
    }
    QAbstractItemModel *model = variableTable->model();
    if (!model) {
        DEBUG() << "VariableRangeDialog: Missing model";
        return;
    }
    const QModelIndex varIndex = model->index(row, 0);
    const QModelIndex lowerIndex = model->index(row, 2);
    const QModelIndex upperIndex = model->index(row, 3);
    if (!varIndex.isValid() || !lowerIndex.isValid() || !upperIndex.isValid()) {
        DEBUG() << "VariableRangeDialog: Invalid model index";
        return;
    }
    const QString variable = model->data(varIndex).toString();
    QString lowerText = model->data(lowerIndex).toString().trimmed();
    QString upperText = model->data(upperIndex).toString().trimmed();
    DEBUG() << "VariableRangeDialog: Variable:" << variable << "Lower text:" << lowerText << "Upper text:" << upperText;

    const bool hasLower = !lowerText.isEmpty();
    const bool hasUpper = !upperText.isEmpty();

    if (!hasLower && !hasUpper) {
        DEBUG() << "VariableRangeDialog: Clearing variable range for:" << variable;
        workingConfig.clearVariableRange(typeKey, variable);
        refreshVariableRow(row);
        return;
    }

    rangeconfig::RangeValue base = workingConfig.effectiveRange(typeKey, variable);
    double lowerValue = base.lower;
    double upperValue = base.upper;
    bool lowerOk = true;
    bool upperOk = true;

    if (hasLower) {
        lowerValue = lowerText.toDouble(&lowerOk);
    }
    if (hasUpper) {
        upperValue = upperText.toDouble(&upperOk);
    }

    if (!lowerOk || !upperOk) {
        DEBUG() << "VariableRangeDialog: Failed to parse values, lowerOk:" << lowerOk << "upperOk:" << upperOk;
        return;
    }

    if (lowerValue > upperValue) {
        std::swap(lowerValue, upperValue);
    }

    rangeconfig::RangeValue value;
    value.lower = lowerValue;
    value.upper = upperValue;
    value.hasExplicit = true;

    DEBUG() << "VariableRangeDialog: Setting variable range for:" << variable
            << "lower:" << lowerValue << "upper:" << upperValue;
    workingConfig.setVariableRange(typeKey, variable, value);
    refreshVariableRow(row);
}

void VariableRangeDialog::onClearOverrideClicked()
{
    DEBUG() << "VariableRangeDialog: onClearOverrideClicked called";
    const QString typeKey = currentTypeKey();
    DEBUG() << "VariableRangeDialog: Type key:" << typeKey;
    if (typeKey.isEmpty()) {
        DEBUG() << "VariableRangeDialog: Type key is empty, returning";
        return;
    }

    const QModelIndexList rows = variableTable->selectionModel()->selectedRows();
    DEBUG() << "VariableRangeDialog: Selected rows count:" << rows.size();
    if (rows.isEmpty()) {
        DEBUG() << "VariableRangeDialog: No rows selected, returning";
        return;
    }

    updating = true;
    for (const QModelIndex &index : rows) {
        const QString variable = variableTable->item(index.row(), 0)->text();
        DEBUG() << "VariableRangeDialog: Clearing override for variable:" << variable;
        workingConfig.clearVariableRange(typeKey, variable);
    }
    updating = false;
    loadType(typeKey);
}

QString VariableRangeDialog::formatRange(const rangeconfig::RangeValue &value) const
{
    DEBUG() << "VariableRangeDialog: formatRange called";
    return QString("[%1, %2]").arg(formatDouble(value.lower), formatDouble(value.upper));
}

QString VariableRangeDialog::formatDouble(double value) const
{
    DEBUG() << "VariableRangeDialog: formatDouble called with value:" << value;
    if (std::fabs(value) < 1e-12) {
        value = 0.0;
    }
    QString text = QString::number(value, 'f', 12);
    if (text.contains(QLatin1Char('.'))) {
        while (text.endsWith(QLatin1Char('0'))) {
            text.chop(1);
        }
        if (text.endsWith(QLatin1Char('.'))) {
            text.chop(1);
        }
    }
    if (text == QLatin1String("-0")) {
        text = QString("0");
    }
    if (text.isEmpty()) {
        text = QString("0");
    }
    DEBUG() << "VariableRangeDialog: Formatted text:" << text;
    return text;
}
