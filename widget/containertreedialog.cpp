#include "widget/containertreedialog.h"
#include "ui_containertreedialog.h"
#include <QMessageBox>
#include <QDialogButtonBox>
#include <algorithm>
#pragma execution_character_set("utf-8")
namespace {

QString comboLabel(ContainerType type)
{
    switch (type) {
    case ContainerType::System: return QString("系统(System)");
    case ContainerType::Subsystem: return QString("子系统(Subsystem)");
    case ContainerType::LRU: return QString("LRU");
    case ContainerType::SRU: return QString("SRU");
    case ContainerType::Module: return QString("模块(Module)");
    case ContainerType::Submodule: return QString("子模块(Submodule)");
    case ContainerType::Component: return QString("元件(Component)");
    }
    return {};
}

QList<ContainerType> allTypes()
{
    return {ContainerType::System, ContainerType::Subsystem, ContainerType::LRU,
            ContainerType::SRU, ContainerType::Module, ContainerType::Submodule, ContainerType::Component};
}

}

ContainerTreeDialog::ContainerTreeDialog(QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::ContainerTreeDialog)
    , m_model(new ContainerModel(this))
    , m_mode(Mode::Manage)
    , m_allowedTypes(allTypes())
{
    ui->setupUi(this);
    ui->treeView->setModel(m_model);
    ui->treeView->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->treeView->setSelectionBehavior(QAbstractItemView::SelectRows);

    connect(ui->btnAdd, &QPushButton::clicked, this, &ContainerTreeDialog::onAdd);
    connect(ui->btnRemove, &QPushButton::clicked, this, &ContainerTreeDialog::onRemove);
    connect(ui->btnRefresh, &QPushButton::clicked, this, &ContainerTreeDialog::onRefresh);
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &ContainerTreeDialog::acceptSelection);
    connect(ui->buttonBox, &QDialogButtonBox::rejected, this, &ContainerTreeDialog::reject);
    connect(ui->treeView, &QTreeView::doubleClicked, this, [this](const QModelIndex &index) {
        if (m_mode == Mode::Select) {
            ui->treeView->setCurrentIndex(index);
            acceptSelection();
        }
    });
    if (ui->treeView->selectionModel()) {
        connect(ui->treeView->selectionModel(), &QItemSelectionModel::currentChanged,
                this, [this](const QModelIndex &, const QModelIndex &) { refreshTypeCombo(); });
    }

    refreshTypeCombo();
}

ContainerTreeDialog::~ContainerTreeDialog()
{
    delete ui;
}

void ContainerTreeDialog::setDatabase(const QSqlDatabase &db)
{
    m_model->setDatabase(db);
    refreshTypeCombo();
}

void ContainerTreeDialog::setMode(Mode mode)
{
    m_mode = mode;
    if (mode == Mode::Manage)
        ui->buttonBox->setStandardButtons(QDialogButtonBox::Close);
    else
        ui->buttonBox->setStandardButtons(QDialogButtonBox::Ok | QDialogButtonBox::Cancel);
}

void ContainerTreeDialog::setAllowedTypes(const QList<ContainerType> &types)
{
    m_allowedTypes = types.isEmpty() ? allTypes() : types;
    refreshTypeCombo();
}

ContainerEntity ContainerTreeDialog::selectedEntity() const
{
    return m_selected;
}

void ContainerTreeDialog::onAdd()
{
    const QString name = ui->editName->text().trimmed();
    if (name.isEmpty()) {
        QMessageBox::warning(this, QString("提示"), QString("请输入容器名称"));
        return;
    }
    int comboIndex = ui->comboType->currentIndex();
    if (comboIndex < 0 || comboIndex >= m_comboTypes.size()) {
        QMessageBox::warning(this, QString("提示"), QString("请选择容器层级"));
        return;
    }
    const ContainerType type = m_comboTypes.at(comboIndex);
    const QModelIndex parentIndex = ui->treeView->currentIndex();
    if (!m_model->addChild(parentIndex, name, type)) {
        QMessageBox::warning(this, QString("错误"), QString("新增容器失败"));
        return;
    }
    ui->editName->clear();
    refreshTypeCombo();
}

void ContainerTreeDialog::onRemove()
{
    QModelIndex index = ui->treeView->currentIndex();
    if (!index.isValid()) return;
    if (QMessageBox::question(this, QString("确认"), QString("是否删除所选容器及其子层级？")) != QMessageBox::Yes) return;
    if (!m_model->removeAt(index)) {
        QMessageBox::warning(this, QString("错误"), QString("删除容器失败"));
    }
    refreshTypeCombo();
}

void ContainerTreeDialog::onRefresh()
{
    m_model->reload();
    refreshTypeCombo();
}

void ContainerTreeDialog::acceptSelection()
{
    if (m_mode == Mode::Manage) {
        accept();
        return;
    }

    QModelIndex index = ui->treeView->currentIndex();
    if (!index.isValid()) {
        QMessageBox::warning(this, QString("提示"), QString("请选择一个容器"));
        return;
    }
    m_selected = m_model->entityForIndex(index);
    if (m_selected.id() == 0) {
        QMessageBox::warning(this, QString("提示"), QString("请选择有效的容器"));
        return;
    }
    if (!m_allowedTypes.isEmpty() && !m_allowedTypes.contains(m_selected.type())) {
        QMessageBox::warning(this, QString("提示"), QString("所选容器层级不在允许范围内"));
        return;
    }
    accept();
}

void ContainerTreeDialog::refreshTypeCombo()
{
    QList<ContainerType> base = m_allowedTypes;
    if (base.isEmpty()) base = allTypes();
    base.removeAll(ContainerType::Component);

    QModelIndex parentIndex = ui->treeView->currentIndex();
    ContainerEntity parentEntity;
    if (parentIndex.isValid()) parentEntity = m_model->entityForIndex(parentIndex);

    ui->comboType->clear();
    m_comboTypes.clear();

    QList<ContainerType> filtered;
    for (ContainerType type : base) {
        if (parentIndex.isValid()) {
            if (!ContainerRepository::canContain(parentEntity.type(), type)) continue;
        } else {
            if (type != ContainerType::System) continue;
        }
        filtered.append(type);
    }

    std::sort(filtered.begin(), filtered.end(), [](ContainerType a, ContainerType b) {
        return static_cast<int>(a) < static_cast<int>(b);
    });

    for (ContainerType type : filtered) {
        ui->comboType->addItem(comboLabel(type));
        m_comboTypes.append(type);
    }

    ui->btnAdd->setEnabled(!m_comboTypes.isEmpty());
}
