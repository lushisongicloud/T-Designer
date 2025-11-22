#include "dmatrixselectiondialog.h"

#include <QComboBox>
#include <QDialogButtonBox>
#include <QHeaderView>
#include <QHBoxLayout>
#include <QItemSelectionModel>
#include <QLabel>
#include <QLineEdit>
#include <QPushButton>
#include <QStandardItem>
#include <QStandardItemModel>
#include <QTableView>
#include <QVBoxLayout>
#include <QDebug>
#include <QSignalBlocker>

#include <algorithm>

using namespace testability;

namespace {
QString faultHeaderLabel(int index)
{
    return QStringLiteral("f%1").arg(index + 1);
}

QString testHeaderLabel(int index)
{
    return QStringLiteral("t%1").arg(index + 1);
}

QString testKindName(TestKind kind)
{
    switch (kind) {
    case TestKind::Function:
        return QObject::tr("功能测试");
    case TestKind::Mode:
        return QObject::tr("故障模式测试");
    case TestKind::Signal:
    default:
        return QObject::tr("信号测试");
    }
}

QString faultKindName(FaultKind kind)
{
    switch (kind) {
    case FaultKind::Component:
        return QObject::tr("器件故障模式");
    case FaultKind::Function:
    default:
        return QObject::tr("功能故障");
    }
}

QString joinList(const QStringList &list)
{
    return list.join(QStringLiteral(", "));
}
}

DMatrixSelectionDialog::DMatrixSelectionDialog(Target targetType, QWidget *parent)
    : QDialog(parent)
    , target(targetType)
    , model(new QStandardItemModel(this))
{
    qDebug().noquote() << "[DMatrixSelectionDialog] constructed — target tests?"
                       << (target == Target::Tests);
    setWindowTitle(target == Target::Tests ? tr("选择测试") : tr("选择故障"));
    resize(780, 520);

    auto *mainLayout = new QVBoxLayout(this);

    auto *filterLayout = new QHBoxLayout();
    auto *filterLabel = new QLabel(tr("关键字:"), this);
    filterEdit = new QLineEdit(this);
    filterEdit->setPlaceholderText(tr("输入编号、名称或其他信息"));
    typeCombo = new QComboBox(this);
    if (target == Target::Tests) {
        typeCombo->addItem(tr("全部"));
        typeCombo->addItem(tr("功能测试"));
        typeCombo->addItem(tr("故障模式测试"));
        typeCombo->addItem(tr("信号测试"));
        typeCombo->addItem(tr("已禁用"));
    } else {
        typeCombo->addItem(tr("全部"));
        typeCombo->addItem(tr("功能故障"));
        typeCombo->addItem(tr("器件故障模式"));
        typeCombo->addItem(tr("已禁用"));
    }
    filterLayout->addWidget(filterLabel);
    filterLayout->addWidget(filterEdit);
    auto *typeLabel = new QLabel(target == Target::Tests ? tr("测试类型:") : tr("故障类型:"), this);
    filterLayout->addWidget(typeLabel);
    filterLayout->addWidget(typeCombo);
    mainLayout->addLayout(filterLayout);

    tableView = new QTableView(this);
    tableView->setModel(model);
    tableView->setSelectionBehavior(QAbstractItemView::SelectRows);
    tableView->setSelectionMode(QAbstractItemView::ExtendedSelection);
    tableView->setEditTriggers(QAbstractItemView::NoEditTriggers);
    tableView->horizontalHeader()->setStretchLastSection(true);
    tableView->verticalHeader()->setVisible(false);
    mainLayout->addWidget(tableView, 1);

    auto *buttonRow = new QHBoxLayout();
    auto *enableButton = new QPushButton(tr("启用所选"), this);
    auto *disableButton = new QPushButton(tr("取消所选"), this);
    auto *selectAllButton = new QPushButton(tr("全选"), this);
    auto *invertButton = new QPushButton(tr("反选"), this);
    buttonRow->addWidget(enableButton);
    buttonRow->addWidget(disableButton);
    buttonRow->addWidget(selectAllButton);
    buttonRow->addWidget(invertButton);
    buttonRow->addStretch();
    mainLayout->addLayout(buttonRow);

    auto *buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok | QDialogButtonBox::Cancel, this);
    mainLayout->addWidget(buttonBox);

    connect(filterEdit, &QLineEdit::textChanged, this, &DMatrixSelectionDialog::onFilterTextChanged);
    connect(typeCombo, QOverload<int>::of(&QComboBox::currentIndexChanged), this, &DMatrixSelectionDialog::onTypeFilterChanged);
    connect(enableButton, &QPushButton::clicked, this, &DMatrixSelectionDialog::onEnableSelected);
    connect(disableButton, &QPushButton::clicked, this, &DMatrixSelectionDialog::onDisableSelected);
    connect(selectAllButton, &QPushButton::clicked, this, &DMatrixSelectionDialog::onSelectAllRows);
    connect(invertButton, &QPushButton::clicked, this, &DMatrixSelectionDialog::onInvertSelection);
    connect(buttonBox, &QDialogButtonBox::accepted, this, &QDialog::accept);
    connect(buttonBox, &QDialogButtonBox::rejected, this, &QDialog::reject);
    connect(model, &QStandardItemModel::itemChanged, this, &DMatrixSelectionDialog::onItemChanged);
}

DMatrixSelectionDialog::~DMatrixSelectionDialog()
{
    qDebug().noquote() << "[DMatrixSelectionDialog] destroyed";
}

void DMatrixSelectionDialog::accept()
{
    qDebug().noquote() << "[DMatrixSelectionDialog] accept — target tests?" << (target == Target::Tests);
    QDialog::accept();
}

void DMatrixSelectionDialog::reject()
{
    qDebug().noquote() << "[DMatrixSelectionDialog] reject — target tests?" << (target == Target::Tests);
    QDialog::reject();
}

void DMatrixSelectionDialog::setTests(const QVector<TestDefinition> &testsData,
                                      const QVector<bool> &enabledStates)
{
    if (target != Target::Tests) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] setTests count" << testsData.size();
    tests.clear();
    tests.reserve(testsData.size());
    for (int i = 0; i < testsData.size(); ++i) {
        TestRow row;
        row.definition = testsData.at(i);
        row.enabled = i < enabledStates.size() ? enabledStates.at(i) : true;
        tests.append(row);
    }
    rebuildModel();
}

void DMatrixSelectionDialog::setFaults(const QVector<FaultDefinition> &faultsData,
                                       const QVector<bool> &enabledStates)
{
    if (target != Target::Faults) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] setFaults count" << faultsData.size();
    faults.clear();
    faults.reserve(faultsData.size());
    for (int i = 0; i < faultsData.size(); ++i) {
        FaultRow row;
        row.definition = faultsData.at(i);
        row.enabled = i < enabledStates.size() ? enabledStates.at(i) : true;
        faults.append(row);
    }
    rebuildModel();
}

QVector<bool> DMatrixSelectionDialog::enabledStates() const
{
    QVector<bool> states;
    if (target == Target::Tests) {
        states.reserve(tests.size());
        for (const auto &row : tests) {
            states.append(row.enabled);
        }
    } else {
        states.reserve(faults.size());
        for (const auto &row : faults) {
            states.append(row.enabled);
        }
    }
    return states;
}

void DMatrixSelectionDialog::onFilterTextChanged(const QString &text)
{
    filterText = text.trimmed().toLower();
    updateRowVisibility();
}

void DMatrixSelectionDialog::onTypeFilterChanged(int index)
{
    typeFilterIndex = index;
    updateRowVisibility();
}

void DMatrixSelectionDialog::onEnableSelected()
{
    const QList<int> rows = selectedRows();
    if (rows.isEmpty()) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] enableSelected rows" << rows;
    for (int row : rows) {
        setRowChecked(row, true);
    }
    updateRowVisibility();
}

void DMatrixSelectionDialog::onDisableSelected()
{
    const QList<int> rows = selectedRows();
    if (rows.isEmpty()) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] disableSelected rows" << rows;
    for (int row : rows) {
        setRowChecked(row, false);
    }
    updateRowVisibility();
}

void DMatrixSelectionDialog::onSelectAllRows()
{
    if (!tableView || !tableView->selectionModel()) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] selectAllRows";
    tableView->clearSelection();
    QItemSelectionModel *selection = tableView->selectionModel();
    for (int row = 0; row < model->rowCount(); ++row) {
        if (tableView->isRowHidden(row)) {
            continue;
        }
        selection->select(model->index(row, 0), QItemSelectionModel::Select | QItemSelectionModel::Rows);
    }
}

void DMatrixSelectionDialog::onInvertSelection()
{
    if (!tableView || !tableView->selectionModel()) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] invertSelection";
    QItemSelectionModel *selection = tableView->selectionModel();
    for (int row = 0; row < model->rowCount(); ++row) {
        if (tableView->isRowHidden(row)) {
            continue;
        }
        const QModelIndex index = model->index(row, 0);
        if (selection->isRowSelected(row, QModelIndex())) {
            selection->select(index, QItemSelectionModel::Deselect | QItemSelectionModel::Rows);
        } else {
            selection->select(index, QItemSelectionModel::Select | QItemSelectionModel::Rows);
        }
    }
}

void DMatrixSelectionDialog::onItemChanged(QStandardItem *item)
{
    if (!item || item->column() != 0) {
        return;
    }
    if (updatingModel) {
        return;
    }
    const int row = item->row();
    const bool checked = item->checkState() == Qt::Checked;
    if (target == Target::Tests) {
        if (row >= 0 && row < tests.size()) {
            tests[row].enabled = checked;
        }
    } else if (row >= 0 && row < faults.size()) {
        faults[row].enabled = checked;
    }
    updateRowVisibility();
}

void DMatrixSelectionDialog::rebuildModel()
{
    qDebug().noquote() << "[DMatrixSelectionDialog] rebuildModel — target tests?"
                       << (target == Target::Tests);
    if (target == Target::Tests) {
        const QStringList headers = {
            tr("选择"),
            tr("标号"),
            tr("编号"),
            tr("名称"),
            tr("类型"),
            tr("关联功能"),
            tr("关联器件"),
            tr("故障模式"),
            tr("信号变量")
        };
        model->setColumnCount(headers.size());
        model->setHorizontalHeaderLabels(headers);
        for (int i = 0; i < tests.size(); ++i) {
            const auto &row = tests.at(i);
            QList<QStandardItem *> items;
            auto *checkItem = new QStandardItem();
            checkItem->setCheckable(true);
            checkItem->setEditable(false);
            checkItem->setCheckState(row.enabled ? Qt::Checked : Qt::Unchecked);
            items << checkItem;

            auto makeItem = [](const QString &text) {
                auto *item = new QStandardItem(text);
                item->setEditable(false);
                return item;
            };

            items << makeItem(testHeaderLabel(i));
            items << makeItem(row.definition.id);
            items << makeItem(row.definition.name);
            items << makeItem(testKindName(row.definition.kind));
            items << makeItem(row.definition.relatedFunction);
            items << makeItem(row.definition.componentName);
            items << makeItem(row.definition.failureModeName);
            items << makeItem(row.definition.signalVariable);

            model->appendRow(items);
        }
    } else {
        const QStringList headers = {
            tr("选择"),
            tr("标号"),
            tr("编号"),
            tr("名称"),
            tr("类型"),
            tr("关联功能"),
            tr("相关器件"),
            tr("链路元素")
        };
        model->setColumnCount(headers.size());
        model->setHorizontalHeaderLabels(headers);
        for (int i = 0; i < faults.size(); ++i) {
            const auto &row = faults.at(i);
            QList<QStandardItem *> items;
            auto *checkItem = new QStandardItem();
            checkItem->setCheckable(true);
            checkItem->setEditable(false);
            checkItem->setCheckState(row.enabled ? Qt::Checked : Qt::Unchecked);
            items << checkItem;

            auto makeItem = [](const QString &text) {
                auto *item = new QStandardItem(text);
                item->setEditable(false);
                return item;
            };

            items << makeItem(faultHeaderLabel(i));
            items << makeItem(row.definition.id);
            items << makeItem(row.definition.name);
            items << makeItem(faultKindName(row.definition.kind));
            items << makeItem(row.definition.relatedFunction);
            items << makeItem(joinList(row.definition.relatedComponents));
            items << makeItem(joinList(row.definition.linkElements));

            model->appendRow(items);
        }
    }

    if (tableView) {
        tableView->resizeColumnsToContents();
        if (model->columnCount() > 0) {
            tableView->horizontalHeader()->setSectionResizeMode(0, QHeaderView::ResizeToContents);
        }
        if (model->columnCount() > 1) {
            tableView->horizontalHeader()->setSectionResizeMode(1, QHeaderView::ResizeToContents);
        }
    }

    updateRowVisibility();
}

void DMatrixSelectionDialog::updateRowVisibility()
{
    qDebug().noquote() << "[DMatrixSelectionDialog] updateRowVisibility start";
    if (!tableView || !tableView->selectionModel()) {
        for (int row = 0; row < model->rowCount(); ++row) {
            const bool visible = matchesFilter(row);
            qDebug().noquote() << "  row" << row << "visible?" << visible;
            tableView->setRowHidden(row, !visible);
        }
        if (tableView) {
            tableView->viewport()->update();
        }
        return;
    }
    QItemSelectionModel *selection = tableView->selectionModel();
    for (int row = 0; row < model->rowCount(); ++row) {
        const bool visible = matchesFilter(row);
        qDebug().noquote() << "  row" << row << "visible?" << visible;
        tableView->setRowHidden(row, !visible);
        if (!visible && selection->isRowSelected(row, QModelIndex())) {
            selection->select(model->index(row, 0), QItemSelectionModel::Deselect | QItemSelectionModel::Rows);
        }
    }
    tableView->viewport()->update();
}

bool DMatrixSelectionDialog::matchesFilter(int row) const
{
    const bool hasFilter = !filterText.isEmpty();
    bool textMatch = true;
    bool typeMatch = true;

    if (target == Target::Tests) {
        if (row < 0 || row >= tests.size()) {
            return false;
        }
        const auto &data = tests.at(row).definition;
        const bool enabled = tests.at(row).enabled;
        if (hasFilter) {
            const QString lowerId = data.id.toLower();
            const QString lowerName = data.name.toLower();
            const QString lowerFunction = data.relatedFunction.toLower();
            const QString lowerComponent = data.componentName.toLower();
            const QString lowerMode = data.failureModeName.toLower();
            const QString lowerSignal = data.signalVariable.toLower();
            const QString lowerNote = data.note.toLower();
            textMatch = lowerId.contains(filterText)
                || lowerName.contains(filterText)
                || lowerFunction.contains(filterText)
                || lowerComponent.contains(filterText)
                || lowerMode.contains(filterText)
                || lowerSignal.contains(filterText)
                || lowerNote.contains(filterText);
        }
        switch (typeFilterIndex) {
        case 1:
            typeMatch = data.kind == TestKind::Function;
            break;
        case 2:
            typeMatch = data.kind == TestKind::Mode;
            break;
        case 3:
            typeMatch = data.kind == TestKind::Signal;
            break;
        case 4:
            typeMatch = !enabled;
            break;
        default:
            typeMatch = true;
            break;
        }
    } else {
        if (row < 0 || row >= faults.size()) {
            return false;
        }
        const auto &data = faults.at(row).definition;
        const bool enabled = faults.at(row).enabled;
        if (hasFilter) {
            const QString lowerId = data.id.toLower();
            const QString lowerName = data.name.toLower();
            const QString lowerFunction = data.relatedFunction.toLower();
            const QString lowerComponents = joinList(data.relatedComponents).toLower();
            const QString lowerLinks = joinList(data.linkElements).toLower();
            textMatch = lowerId.contains(filterText)
                || lowerName.contains(filterText)
                || lowerFunction.contains(filterText)
                || lowerComponents.contains(filterText)
                || lowerLinks.contains(filterText);
        }
        switch (typeFilterIndex) {
        case 1:
            typeMatch = data.kind == FaultKind::Function;
            break;
        case 2:
            typeMatch = data.kind == FaultKind::Component;
            break;
        case 3:
            typeMatch = !enabled;
            break;
        default:
            typeMatch = true;
            break;
        }
    }

    return textMatch && typeMatch;
}

void DMatrixSelectionDialog::setRowChecked(int row, bool checked)
{
    if (row < 0 || row >= model->rowCount()) {
        return;
    }
    QStandardItem *item = model->item(row, 0);
    if (!item) {
        return;
    }
    if (updatingModel) {
        return;
    }
    qDebug().noquote() << "[DMatrixSelectionDialog] setRowChecked" << row << "->" << checked;
    updatingModel = true;
    item->setCheckState(checked ? Qt::Checked : Qt::Unchecked);
    updatingModel = false;
    if (target == Target::Tests) {
        if (row >= 0 && row < tests.size()) {
            tests[row].enabled = checked;
        }
    } else if (row >= 0 && row < faults.size()) {
        faults[row].enabled = checked;
    }
    model->dataChanged(item->index(), item->index(), {Qt::CheckStateRole, Qt::DisplayRole});
}

QList<int> DMatrixSelectionDialog::selectedRows() const
{
    QList<int> rows;
    if (!tableView || !tableView->selectionModel()) {
        return rows;
    }
    const QModelIndexList indexes = tableView->selectionModel()->selectedRows();
    for (const QModelIndex &index : indexes) {
        if (!rows.contains(index.row())) {
            rows.append(index.row());
        }
    }
    std::sort(rows.begin(), rows.end());
    return rows;
}
