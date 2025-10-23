#include "widget/functioneditdialog.h"
#include "ui_functioneditdialog.h"

#include "widget/functionsymbolpickerdialog.h"

#include <QMessageBox>
#include <QSqlQuery>
#include <QSqlError>
#include <QTableWidgetItem>
#include <QSet>
#include <QtDebug>

FunctionEditDialog::FunctionEditDialog(const QSqlDatabase &db, QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::FunctionEditDialog)
    , m_db(db)
    , m_analysisService(db)
{
    ui->setupUi(this);
    ui->tableInputs->setColumnCount(2);
    ui->tableInputs->setHorizontalHeaderLabels({tr("变量"), tr("目标值")});
    ui->tableInputs->horizontalHeader()->setStretchLastSection(true);
    ui->tableInputs->verticalHeader()->setVisible(false);
    ui->tableInputs->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableInputs->setSelectionBehavior(QAbstractItemView::SelectRows);

    connect(ui->btnSelectSymbol, &QPushButton::clicked, this, &FunctionEditDialog::onSelectSymbol);
    connect(ui->btnAddInput, &QPushButton::clicked, this, &FunctionEditDialog::onAddInput);
    connect(ui->btnRemoveInput, &QPushButton::clicked, this, &FunctionEditDialog::onRemoveInput);
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &FunctionEditDialog::onAccepted);
    connect(ui->listExecs, &QListWidget::itemChanged, this, &FunctionEditDialog::updateExecList);
    connect(ui->btnAutoAnalyze, &QPushButton::clicked, this, &FunctionEditDialog::onAutoAnalyze);

    ui->btnAutoAnalyze->setEnabled(false);
}

void FunctionEditDialog::setInitialRecord(const FunctionRecord &record)
{
    m_record = record;
    ui->editName->setText(record.name);
    ui->plainRemark->setPlainText(record.remark);
    if (record.symbolId > 0)
        setSymbol(record.symbolId, record.symbolName);
    populateInputs(record.cmdValList);
    const QStringList execs = record.execsList.split(',', QString::SkipEmptyParts);
    for (int i = 0; i < ui->listExecs->count(); ++i) {
        QListWidgetItem *item = ui->listExecs->item(i);
        if (execs.contains(item->text()))
            item->setCheckState(Qt::Checked);
        else
            item->setCheckState(Qt::Unchecked);
    }
    ui->editLink->setText(record.link);
    ui->editComponentDependency->setText(record.componentDependency);
    ui->editAllComponents->setText(record.allComponents);
    ui->editFunctionDependency->setText(record.functionDependency);
    ui->checkPersistent->setChecked(record.persistent);
    ui->spinFaultProbability->setValue(record.faultProbability);
    ui->btnAutoAnalyze->setEnabled(record.symbolId > 0);
}

void FunctionEditDialog::setSymbol(int symbolId, const QString &symbolName)
{
    if (symbolId <= 0)
        return;
    m_record.symbolId = symbolId;
    m_record.symbolName = symbolName;
    ui->editSymbol->setText(symbolName);
    loadSymbolPorts();
    ui->btnAutoAnalyze->setEnabled(true);
}

void FunctionEditDialog::onSelectSymbol()
{
    FunctionSymbolPickerDialog picker(m_db, this);
    if (picker.exec() != QDialog::Accepted)
        return;
    if (picker.selectedSymbolId() == 0)
        return;

    setSymbol(picker.selectedSymbolId(), picker.selectedSymbolName());
    onAutoAnalyze();
}

void FunctionEditDialog::loadSymbolPorts()
{
    m_ports.clear();
    ui->listExecs->clear();
    if (!m_db.isOpen() || m_record.symbolId == 0)
        return;

    QSqlQuery query(m_db);
    query.prepare(QString("SELECT ConnNum, ConnDesc FROM Symb2TermInfo WHERE Symbol_ID = :sid ORDER BY ConnNum"));
    query.bindValue(":sid", m_record.symbolId);
    if (!query.exec()) {
        qWarning() << "FunctionEditDialog" << query.lastError();
        return;
    }

    while (query.next()) {
        PortOption option;
        option.portName = query.value(0).toString();
        option.description = query.value(1).toString();
        m_ports.append(option);

        QListWidgetItem *item = new QListWidgetItem(option.portName, ui->listExecs);
        item->setFlags(item->flags() | Qt::ItemIsUserCheckable);
        item->setCheckState(Qt::Unchecked);
        if (!option.description.isEmpty())
            item->setToolTip(option.description);
    }
}

void FunctionEditDialog::onAddInput()
{
    const int row = ui->tableInputs->rowCount();
    ui->tableInputs->insertRow(row);
    ui->tableInputs->setItem(row, 0, new QTableWidgetItem);
    ui->tableInputs->setItem(row, 1, new QTableWidgetItem);
    ui->tableInputs->editItem(ui->tableInputs->item(row, 0));
}

void FunctionEditDialog::onRemoveInput()
{
    int row = ui->tableInputs->currentRow();
    if (row >= 0)
        ui->tableInputs->removeRow(row);
}

void FunctionEditDialog::applyAnalysis(const FunctionModelResult &result)
{
    if (ui->editName->text().trimmed().isEmpty() && !result.record.name.trimmed().isEmpty())
        ui->editName->setText(result.record.name.trimmed());

    if (!result.record.link.isEmpty())
        ui->editLink->setText(result.record.link);
    if (!result.record.componentDependency.isEmpty())
        ui->editComponentDependency->setText(result.record.componentDependency);
    if (!result.record.allComponents.isEmpty())
        ui->editAllComponents->setText(result.record.allComponents);
    ui->editFunctionDependency->setText(result.record.functionDependency);
    ui->checkPersistent->setChecked(result.record.persistent);
    ui->spinFaultProbability->setValue(result.record.faultProbability);

    const QStringList execItems = result.record.execsList.split(',', QString::SkipEmptyParts);
    QSet<QString> portSet;
    for (const QString &entry : execItems) {
        QString port = entry.trimmed();
        const int dotIndex = port.lastIndexOf('.');
        if (dotIndex >= 0)
            port = port.mid(dotIndex + 1);
        if (!port.isEmpty())
            portSet.insert(port);
    }
    if (!portSet.isEmpty()) {
        for (int i = 0; i < ui->listExecs->count(); ++i) {
            QListWidgetItem *item = ui->listExecs->item(i);
            if (portSet.contains(item->text()))
                item->setCheckState(Qt::Checked);
            else
                item->setCheckState(Qt::Unchecked);
        }
    }
}

void FunctionEditDialog::populateInputs(const QString &cmdValList)
{
    ui->tableInputs->setRowCount(0);
    const QStringList pairs = cmdValList.split(',', QString::SkipEmptyParts);
    for (const QString &pair : pairs) {
        const QStringList parts = pair.split('=');
        if (parts.size() != 2) continue;
        const int row = ui->tableInputs->rowCount();
        ui->tableInputs->insertRow(row);
        ui->tableInputs->setItem(row, 0, new QTableWidgetItem(parts.at(0).trimmed()));
        ui->tableInputs->setItem(row, 1, new QTableWidgetItem(parts.at(1).trimmed()));
    }
}

QString FunctionEditDialog::buildCmdValList() const
{
    QStringList pairs;
    for (int row = 0; row < ui->tableInputs->rowCount(); ++row) {
        const QString key = ui->tableInputs->item(row, 0) ? ui->tableInputs->item(row, 0)->text().trimmed() : QString();
        const QString value = ui->tableInputs->item(row, 1) ? ui->tableInputs->item(row, 1)->text().trimmed() : QString();
        if (key.isEmpty() || value.isEmpty()) continue;
        pairs.append(QString("%1=%2").arg(key, value));
    }
    return pairs.join(',');
}

QString FunctionEditDialog::buildExecList() const
{
    QStringList execs;
    for (int i = 0; i < ui->listExecs->count(); ++i) {
        QListWidgetItem *item = ui->listExecs->item(i);
        if (item->checkState() == Qt::Checked) {
            const QString port = item->text();
            if (!m_record.symbolName.isEmpty())
                execs.append(QString("%1.%2").arg(m_record.symbolName, port));
            else
                execs.append(port);
        }
    }
    execs.removeDuplicates();
    return execs.join(',');
}

void FunctionEditDialog::updateExecList()
{
    Q_UNUSED(this);
}

void FunctionEditDialog::onAutoAnalyze()
{
    if (m_record.symbolId == 0) {
        QMessageBox::information(this, tr("提示"), tr("请先选择功能子块"));
        return;
    }

    const FunctionModelResult result = m_analysisService.analyzeSymbol(m_record.symbolId, ui->editName->text().trimmed());
    if (!result.warnings.isEmpty())
        QMessageBox::information(this, tr("提示"), result.warnings.join("\n"));
    applyAnalysis(result);
}

void FunctionEditDialog::analyzeCurrentSymbol()
{
    onAutoAnalyze();
}

void FunctionEditDialog::onAccepted()
{
    if (ui->editName->text().trimmed().isEmpty()) {
        QMessageBox::warning(this, tr("提示"), tr("功能名称不能为空"));
        return;
    }
    if (m_record.symbolId == 0) {
        QMessageBox::warning(this, tr("提示"), tr("请选择功能子块"));
        return;
    }

    m_record.name = ui->editName->text().trimmed();
    m_record.remark = ui->plainRemark->toPlainText();
    m_record.execsList = buildExecList();
    m_record.cmdValList = buildCmdValList();
    m_record.link = ui->editLink->text().trimmed();
    m_record.componentDependency = ui->editComponentDependency->text().trimmed();
    m_record.allComponents = ui->editAllComponents->text().trimmed();
    m_record.functionDependency = ui->editFunctionDependency->text().trimmed();
    m_record.persistent = ui->checkPersistent->isChecked();
    m_record.faultProbability = ui->spinFaultProbability->value();

    accept();
}

