#include "widget/containertreedialog.h"
#include "ui_containertreedialog.h"
#include <QMessageBox>
#include <QDialogButtonBox>
#include <QHeaderView>
#include <QMenu>
#include <QInputDialog>
#include <algorithm>
#include <QVector>
#include "widget/containerhierarchyutils.h"
#include "widget/testmanagementdialog.h"
#include "BO/test/testgeneratorservice.h"
#include "BO/test/diagnosticmatrixbuilder.h"
#include "BO/function/functiondependencyresolver.h"
#include "BO/componententity.h"

using namespace ContainerHierarchy;
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
    , m_db(QSqlDatabase::database())
{
    ui->setupUi(this);
    ui->treeView->setModel(m_model);
    ui->treeView->setSelectionMode(QAbstractItemView::ExtendedSelection);
    ui->treeView->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->treeView->setContextMenuPolicy(Qt::CustomContextMenu);
    ui->treeView->setSortingEnabled(true);
    ui->treeView->sortByColumn(1, Qt::AscendingOrder);
    ui->treeView->header()->setSectionResizeMode(0, QHeaderView::Stretch);
    ui->treeView->header()->setSectionResizeMode(1, QHeaderView::ResizeToContents);

    connect(ui->btnAdd, &QPushButton::clicked, this, &ContainerTreeDialog::onAdd);
    connect(ui->btnRemove, &QPushButton::clicked, this, &ContainerTreeDialog::onRemove);
    connect(ui->btnRefresh, &QPushButton::clicked, this, &ContainerTreeDialog::onRefresh);
    connect(ui->buttonBox, &QDialogButtonBox::accepted, this, &ContainerTreeDialog::acceptSelection);
    connect(ui->buttonBox, &QDialogButtonBox::rejected, this, &ContainerTreeDialog::reject);
    connect(ui->treeView, &QTreeView::customContextMenuRequested, this, &ContainerTreeDialog::showContextMenu);
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
    m_db = db;
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
    if (!ui->treeView->selectionModel()) return;
    const QModelIndexList rows = ui->treeView->selectionModel()->selectedRows();
    if (rows.isEmpty()) return;

    if (QMessageBox::question(this, tr("确认"),
                              tr("是否删除选中的%1个容器及其子层级？").arg(rows.count())) != QMessageBox::Yes)
        return;

    ContainerRepository repo(m_db);
    if (!repo.ensureTables()) return;

    for (const QModelIndex &row : rows) {
        ContainerEntity entity = m_model->entityForIndex(row);
        if (entity.id() != 0) repo.remove(entity.id());
    }

    onRefresh();
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

void ContainerTreeDialog::showContextMenu(const QPoint &pos)
{
    QModelIndex index = ui->treeView->indexAt(pos);
    if (!index.isValid()) return;

    if (!ui->treeView->selectionModel()->isSelected(index))
        ui->treeView->selectionModel()->select(index, QItemSelectionModel::Select | QItemSelectionModel::Rows);

    const QModelIndexList rows = ui->treeView->selectionModel()->selectedRows();
    if (rows.isEmpty()) return;

    ContainerRepository repo(m_db);
    if (!repo.ensureTables()) return;

    QMenu menu(this);

    QVector<ContainerEntity> selectedEntities;
    selectedEntities.reserve(rows.size());
    for (const QModelIndex &row : rows)
        selectedEntities.append(m_model->entityForIndex(row));

    QList<int> componentIds;
    for (const ContainerEntity &entity : selectedEntities) {
        if (entity.type() == ContainerType::Component)
            componentIds.append(entity.id());
    }

    if (rows.size() == 1) {
        const ContainerEntity entity = selectedEntities.first();

        QAction *renameAct = menu.addAction(QString("重命名当前容器"));
        connect(renameAct, &QAction::triggered, this, [this, entityId = entity.id()]() {
            ContainerRepository repoLocal(m_db);
            if (!repoLocal.ensureTables()) return;
            ContainerEntity current = repoLocal.getById(entityId);
            bool ok = false;
            QString newName = QInputDialog::getText(this, QString("重命名容器"), QString("名称"), QLineEdit::Normal, current.name(), &ok);
            if (!ok) return;
            newName = newName.trimmed();
            if (newName.isEmpty()) return;
            current.setName(newName);
            repoLocal.update(current);
            onRefresh();
        });

        if (entity.type() != ContainerType::Component) {
            QList<ContainerType> childTypes = ContainerHierarchy::childCandidateTypes(entity.type());
            QAction *addChildAct = menu.addAction(QString("添加低层级容器"));
            if (childTypes.isEmpty()) {
                addChildAct->setEnabled(false);
            } else {
                connect(addChildAct, &QAction::triggered, this, [this, entityId = entity.id(), entityType = entity.type(), childTypes]() {
                    ContainerRepository repoLocal(m_db);
                    if (!repoLocal.ensureTables()) return;
                    ContainerTreeDialog dialog(this);
                    dialog.setDatabase(m_db);
                    dialog.setMode(ContainerTreeDialog::Mode::Select);
                    dialog.setAllowedTypes(childTypes);
                    if (dialog.exec() != QDialog::Accepted) return;
                    ContainerEntity selected = dialog.selectedEntity();
                    if (selected.id() == 0) return;
                    if (!ContainerRepository::canContain(entityType, selected.type())) {
                        QMessageBox::warning(this, QString("错误"), QString("所选容器层级不符合要求"));
                        return;
                    }
                    if (!repoLocal.attachToParent(selected.id(), entityId)) {
                        QMessageBox::warning(this, QString("错误"), QString("添加低层级容器失败"));
                    }
                    onRefresh();
                });
            }

            QList<ContainerType> parentTypes = ContainerHierarchy::parentCandidateTypes(entity.type());
            QAction *attachAct = menu.addAction(QString("将当前层级添加到高层级容器"));
            if (parentTypes.isEmpty()) {
                attachAct->setEnabled(false);
            } else {
                connect(attachAct, &QAction::triggered, this, [this, entityId = entity.id(), entityType = entity.type(), parentTypes]() {
                    ContainerRepository repoLocal(m_db);
                    if (!repoLocal.ensureTables()) return;
                    ContainerTreeDialog dialog(this);
                    dialog.setDatabase(m_db);
                    dialog.setMode(ContainerTreeDialog::Mode::Select);
                    dialog.setAllowedTypes(parentTypes);
                    if (dialog.exec() != QDialog::Accepted) return;
                    ContainerEntity target = dialog.selectedEntity();
                    if (target.id() == 0) return;
                    if (!ContainerRepository::canContain(target.type(), entityType)) {
                        QMessageBox::warning(this, QString("错误"), QString("所选容器层级不符合要求"));
                        return;
                    }
                    if (!repoLocal.attachToParent(entityId, target.id())) {
                        QMessageBox::warning(this, QString("错误"), QString("加入高层级容器失败"));
                    }
                    onRefresh();
                });
            }
        } else {
            QAction *detachAct = menu.addAction(QString("从父容器移除"));
            if (entity.parentId() == 0) {
                detachAct->setEnabled(false);
            } else {
                connect(detachAct, &QAction::triggered, this, [this, entityId = entity.id()]() {
                    ContainerRepository repoLocal(m_db);
                    if (!repoLocal.ensureTables()) return;
                    ContainerHierarchy::detachComponentContainer(repoLocal, entityId);
                    onRefresh();
                });
            }
        }

        QAction *generateTestsAct = menu.addAction(QString("自动生成测试"));
        connect(generateTestsAct, &QAction::triggered, this, [this, container = entity]() {
            ContainerRepository repoLocal(m_db);
            if (!repoLocal.ensureTables()) return;

            BehaviorAggregator aggregator(
                [&](int id) { return repoLocal.getById(id); },
                [&](int id) { return repoLocal.fetchChildren(id); });

            FunctionDependencyResolver resolver;
            auto functions = ContainerHierarchy::fetchFunctionInfoMap(m_db);
            TestGeneratorService service(repoLocal, aggregator, resolver);
            service.setFunctionMap(functions);
            service.setContainerFunctions(ContainerHierarchy::defaultFunctionMapping(container, functions));

            QVector<GeneratedTest> tests = service.generateForContainer(container.id());

            ContainerData containerData(repoLocal.getById(container.id()));
            DiagnosticMatrixBuilder builder;
            builder.rebuild(containerData);
            CoverageStats stats = builder.coverageStats();
            QStringList candidateTests = builder.candidateTests(0.6);

            QString summary = QString("生成了%1项测试。检测覆盖: %2/%3 隔离覆盖: %4")
                                    .arg(tests.size())
                                    .arg(stats.detectedFaults.size())
                                    .arg(stats.totalFaults)
                                    .arg(stats.isolatableFaults.size());
            if (!candidateTests.isEmpty())
                summary += QString(" 候选测试(>=60%): %1").arg(candidateTests.join(QString(", ")));

            QMessageBox::information(this, QString("自动生成测试"), summary);
            onRefresh();
        });

        QAction *manageTestsAct = menu.addAction(QString("管理测试"));
        connect(manageTestsAct, &QAction::triggered, this, [this, containerId = entity.id()]() {
            TestManagementDialog dialog(containerId, m_db, this);
            dialog.exec();
        });

        menu.addSeparator();
        QAction *deleteAct = menu.addAction(QString("删除容器"));
        connect(deleteAct, &QAction::triggered, this, [this, entityId = entity.id()]() {
            if (QMessageBox::question(this, QString("确认"), QString("是否删除当前容器及其子层级？")) != QMessageBox::Yes) return;
            ContainerRepository repoLocal(m_db);
            if (!repoLocal.ensureTables()) return;
            repoLocal.remove(entityId);
            onRefresh();
        });
    } else {
        QAction *detachAct = menu.addAction(QString("从父容器移除"));
        bool canDetach = false;
        for (const ContainerEntity &entity : selectedEntities) {
            if (entity.type() == ContainerType::Component && entity.parentId() != 0) {
                canDetach = true;
                break;
            }
        }
        detachAct->setEnabled(canDetach);
        if (canDetach) {
            connect(detachAct, &QAction::triggered, this, [this, componentIds]() {
                if (componentIds.isEmpty()) return;
                ContainerRepository repoLocal(m_db);
                if (!repoLocal.ensureTables()) return;
                for (int cid : componentIds)
                    ContainerHierarchy::detachComponentContainer(repoLocal, cid);
                onRefresh();
            });
        }

        QAction *deleteAct = menu.addAction(QString("删除容器"));
        connect(deleteAct, &QAction::triggered, this, [this, selectedEntities]() {
            if (QMessageBox::question(this, QString("确认"), QString("是否删除选中的容器及其子层级？")) != QMessageBox::Yes) return;
            ContainerRepository repoLocal(m_db);
            if (!repoLocal.ensureTables()) return;
            for (const ContainerEntity &entity : selectedEntities) {
                if (entity.id() != 0) repoLocal.remove(entity.id());
            }
            onRefresh();
        });
    }

    if (!componentIds.isEmpty()) {
        menu.addSeparator();
        QAction *attachComponentsAct = menu.addAction(QString("将实体元件层添加到高层级容器"));
        connect(attachComponentsAct, &QAction::triggered, this, [this, componentIds, &repo]() {
            QList<ContainerType> allowedParents = ContainerHierarchy::parentCandidateTypes(ContainerType::Component);
            ContainerTreeDialog dialog(this);
            dialog.setDatabase(m_db);
            dialog.setMode(ContainerTreeDialog::Mode::Select);
            dialog.setAllowedTypes(allowedParents);
            if (dialog.exec() != QDialog::Accepted) return;
            ContainerEntity target = dialog.selectedEntity();
            if (target.id() == 0) return;
            if (!ContainerRepository::canContain(target.type(), ContainerType::Component)) {
                QMessageBox::warning(this, QString("错误"), QString("所选容器层级不符合要求"));
                return;
            }
            if (!ContainerHierarchy::attachComponentsToTarget(repo, componentIds, target.id())) {
                QMessageBox::warning(this, QString("错误"), QString("添加到高层级容器失败"));
            }
            onRefresh();
        });
    }

    menu.exec(ui->treeView->viewport()->mapToGlobal(pos));
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
