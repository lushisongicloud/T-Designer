#include "widget/functionmanagerdialog.h"
#include "ui_functionmanagerdialog.h"

#include <QMessageBox>
#include <QTableWidgetItem>
#include <QPushButton>

#include "widget/functioneditdialog.h"



FunctionManagerDialog::FunctionManagerDialog(const QSqlDatabase &db, QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::FunctionManagerDialog)
    , m_db(db)
    , m_repo(db)
{
    ui->setupUi(this);
    setWindowTitle(tr("系统功能管理"));
    resize(720, 520);

    ui->tableFunctions->setColumnCount(6);
    ui->tableFunctions->setHorizontalHeaderLabels({tr("功能名称"), tr("功能子块"), tr("输入约束"), tr("执行器"), tr("器件依赖"), tr("备注")});
    ui->tableFunctions->horizontalHeader()->setStretchLastSection(true);
    ui->tableFunctions->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableFunctions->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableFunctions->setEditTriggers(QAbstractItemView::NoEditTriggers);

    connect(ui->btnAdd, &QPushButton::clicked, this, &FunctionManagerDialog::onAdd);
    connect(ui->btnEdit, &QPushButton::clicked, this, &FunctionManagerDialog::onEdit);
    connect(ui->btnDelete, &QPushButton::clicked, this, &FunctionManagerDialog::onDelete);
    connect(ui->btnRefresh, &QPushButton::clicked, this, &FunctionManagerDialog::onRefresh);
    connect(ui->btnClose, &QPushButton::clicked, this, &QDialog::reject);
    connect(ui->tableFunctions, &QTableWidget::cellDoubleClicked, this, &FunctionManagerDialog::onTableDoubleClicked);
    connect(ui->tableFunctions->selectionModel(), &QItemSelectionModel::selectionChanged,
            this, &FunctionManagerDialog::updateButtons);

    if (!m_repo.ensureTables())
        QMessageBox::warning(this, tr("提示"), tr("数据库不可用"));

    loadData();
    updateButtons();
}

FunctionManagerDialog::~FunctionManagerDialog()
{
    delete ui;
}

void FunctionManagerDialog::loadData()
{
    m_records = m_repo.fetchAll();
    ui->tableFunctions->setRowCount(m_records.size());
    for (int row = 0; row < m_records.size(); ++row) {
        const FunctionRecord &rec = m_records.at(row);
        auto setItem = [&](int column, const QString &text) {
            QTableWidgetItem *item = new QTableWidgetItem(text);
            item->setData(Qt::UserRole, rec.id);
            ui->tableFunctions->setItem(row, column, item);
        };
        setItem(0, rec.name);
        setItem(1, rec.symbolName);
        setItem(2, rec.cmdValList);
        setItem(3, rec.execsList);
        setItem(4, rec.componentDependency);
        setItem(5, rec.remark);
    }
    ui->tableFunctions->setCurrentCell(m_records.isEmpty() ? -1 : 0, 0);
    updateButtons();
}

FunctionRecord FunctionManagerDialog::currentRecord() const
{
    int row = ui->tableFunctions->currentRow();
    if (row < 0 || row >= m_records.size())
        return FunctionRecord{};
    return m_records.at(row);
}

void FunctionManagerDialog::onAdd()
{
    FunctionEditDialog editor(m_db, this);
    if (editor.exec() != QDialog::Accepted)
        return;

    FunctionRecord rec = editor.record();
    int id = m_repo.insert(rec);
    if (id == 0) {
        QMessageBox::warning(this, tr("提示"), tr("保存失败"));
        return;
    }
    loadData();
    for (int row = 0; row < m_records.size(); ++row) {
        if (m_records.at(row).id == id) {
            ui->tableFunctions->setCurrentCell(row, 0);
            break;
        }
    }
}

void FunctionManagerDialog::onEdit()
{
    FunctionRecord rec = currentRecord();
    if (rec.id == 0)
        return;

    FunctionEditDialog editor(m_db, this);
    editor.setInitialRecord(rec);
    if (editor.exec() != QDialog::Accepted)
        return;

    rec = editor.record();
    rec.id = currentRecord().id;
    if (!m_repo.update(rec)) {
        QMessageBox::warning(this, tr("提示"), tr("保存失败"));
        return;
    }
    loadData();
}

void FunctionManagerDialog::onDelete()
{
    FunctionRecord rec = currentRecord();
    if (rec.id == 0)
        return;

    if (QMessageBox::question(this, tr("确认"), tr("是否删除选中的功能？")) != QMessageBox::Yes)
        return;

    if (!m_repo.remove(rec.id)) {
        QMessageBox::warning(this, tr("提示"), tr("删除失败"));
        return;
    }
    loadData();
}

void FunctionManagerDialog::onRefresh()
{
    loadData();
}

void FunctionManagerDialog::onTableDoubleClicked(int row, int column)
{
    Q_UNUSED(row);
    Q_UNUSED(column);
    onEdit();
}

void FunctionManagerDialog::updateButtons()
{
    bool hasSelection = ui->tableFunctions->currentRow() >= 0 && ui->tableFunctions->currentRow() < m_records.size();
    ui->btnEdit->setEnabled(hasSelection);
    ui->btnDelete->setEnabled(hasSelection);
}
