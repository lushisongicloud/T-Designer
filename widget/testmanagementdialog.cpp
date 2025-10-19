#include "widget/testmanagementdialog.h"
#include "ui_testmanagementdialog.h"

#include <QCloseEvent>
#include <QJsonDocument>
#include <QJsonObject>
#include <QMessageBox>
#include <QHeaderView>
#include <QUuid>

#include "widget/testeditdialog.h"
#include "widget/containerhierarchyutils.h"
#include "BO/test/diagnosticmatrixbuilder.h"

#pragma execution_character_set("utf-8")

TestManagementDialog::TestManagementDialog(int containerId, const QSqlDatabase &db, QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::TestManagementDialog)
    , m_containerId(containerId)
    , m_db(db)
    , m_repo(db)
{
    ui->setupUi(this);
    m_title = windowTitle();

    ui->tableTests->setColumnCount(7);
    ui->tableTests->setHorizontalHeaderLabels({"类别", "名称", "目标", "检测故障", "隔离故障", "费用", "时间"});
    ui->tableTests->horizontalHeader()->setStretchLastSection(true);
    ui->tableTests->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableTests->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableTests->setEditTriggers(QAbstractItemView::NoEditTriggers);

    connect(ui->btnClose, &QPushButton::clicked, this, &QDialog::reject);
    connect(ui->btnGenerate, &QPushButton::clicked, this, &TestManagementDialog::on_btnGenerate_clicked);
    connect(ui->btnAdd, &QPushButton::clicked, this, &TestManagementDialog::on_btnAdd_clicked);
    connect(ui->btnEdit, &QPushButton::clicked, this, &TestManagementDialog::on_btnEdit_clicked);
    connect(ui->btnDelete, &QPushButton::clicked, this, &TestManagementDialog::on_btnDelete_clicked);
    connect(ui->btnSave, &QPushButton::clicked, this, &TestManagementDialog::on_btnSave_clicked);
    connect(ui->tableTests, &QTableWidget::currentCellChanged,
            this, &TestManagementDialog::on_tableTests_currentCellChanged);

    loadData();
}

TestManagementDialog::~TestManagementDialog()
{
    delete ui;
}

void TestManagementDialog::initializeGenerator()
{
    m_generator.reset();
    m_aggregator.reset();

    if (m_containerId == 0)
        return;

    if (!m_repo.ensureTables())
        return;

    m_entity = m_repo.getById(m_containerId);
    if (m_entity.id() == 0)
        return;

    auto loader = [this](int id) { return m_repo.getById(id); };
    auto fetcher = [this](int id) { return m_repo.fetchChildren(id); };
    m_aggregator = std::make_unique<BehaviorAggregator>(loader, fetcher);

    auto functions = ContainerHierarchy::fetchFunctionInfoMap(m_db);
    m_resolver.setDefinitions(functions);

    m_generator = std::make_unique<TestGeneratorService>(m_repo, *m_aggregator, m_resolver);
    m_generator->setFunctionMap(functions);
    m_generator->setContainerFunctions(ContainerHierarchy::defaultFunctionMapping(m_entity, functions));
}

void TestManagementDialog::loadData()
{
    initializeGenerator();
    if (m_entity.id() == 0)
        return;

    ContainerData container(m_entity);
    m_tests = container.tests();
    refreshTable();
    updateCoverage();
    m_dirty = false;
    setWindowTitle(m_title);
    if (!m_tests.isEmpty())
        ui->tableTests->setCurrentCell(0, 0);
    else
        updateDetails(-1);
}

void TestManagementDialog::refreshTable()
{
    ui->tableTests->setRowCount(m_tests.size());
    for (int row = 0; row < m_tests.size(); ++row) {
        const GeneratedTest &test = m_tests.at(row);
        auto setItem = [&](int column, const QString &text) {
            QTableWidgetItem *item = new QTableWidgetItem(text);
            item->setData(Qt::UserRole, row);
            ui->tableTests->setItem(row, column, item);
        };
        setItem(0, testCategoryToString(test.category));
        setItem(1, test.name);
        setItem(2, test.targetId);
        setItem(3, test.detectableFaults.join(QString(", ")));
        setItem(4, test.isolatableFaults.join(QString(", ")));
        setItem(5, QString::number(test.estimatedCost, 'f', 2));
        setItem(6, QString::number(test.estimatedDuration, 'f', 2));
    }
}

void TestManagementDialog::updateDetails(int row)
{
    if (row < 0 || row >= m_tests.size()) {
        ui->plainDetails->clear();
        ui->btnEdit->setEnabled(false);
        ui->btnDelete->setEnabled(false);
        return;
    }

    ui->btnEdit->setEnabled(true);
    ui->btnDelete->setEnabled(true);

    const GeneratedTest &test = m_tests.at(row);
    QString detail;
    detail += tr("名称: %1\n").arg(test.name);
    detail += tr("类别: %1\n").arg(testCategoryToString(test.category));
    detail += tr("目标: %1\n").arg(test.targetId);
    detail += tr("检测故障: %1\n").arg(test.detectableFaults.join(QString(", ")));
    detail += tr("隔离故障: %1\n").arg(test.isolatableFaults.join(QString(", ")));
    detail += tr("费用: %1\n").arg(test.estimatedCost, 0, 'f', 2);
    detail += tr("时间: %1\n").arg(test.estimatedDuration, 0, 'f', 2);
    detail += tr("描述:\n%1\n").arg(test.description);

    QJsonObject metricsObj = QJsonObject::fromVariantMap(test.metrics);
    QJsonDocument doc(metricsObj);
    detail += tr("指标:\n%1").arg(QString::fromUtf8(doc.toJson(QJsonDocument::Indented)));

    ui->plainDetails->setPlainText(detail);
}

void TestManagementDialog::updateCoverage()
{
    if (m_entity.id() == 0) {
        ui->labelCoverage->setText(tr("覆盖信息不可用"));
        return;
    }

    ContainerData container(m_entity);
    container.setTests(m_tests);
    DiagnosticMatrixBuilder builder;
    builder.rebuild(container);
    CoverageStats stats = builder.coverageStats();

    if (stats.totalFaults == 0) {
        ui->labelCoverage->setText(tr("测试: %1，尚无故障模型").arg(stats.totalTests));
        return;
    }

    ui->labelCoverage->setText(
        tr("测试: %1，故障: %2，检测覆盖: %3/%4，隔离覆盖: %5")
            .arg(stats.totalTests)
            .arg(stats.totalFaults)
            .arg(stats.detectedFaults.size())
            .arg(stats.totalFaults)
            .arg(stats.isolatableFaults.size()));
}

bool TestManagementDialog::saveChanges()
{
    if (m_entity.id() == 0)
        return false;

    ContainerData data(m_repo.getById(m_entity.id()));
    data.setTests(m_tests);
    if (!m_repo.update(data.entity())) {
        QMessageBox::warning(this, tr("保存失败"), tr("写入数据库失败"));
        return false;
    }
    m_entity = m_repo.getById(m_entity.id());
    m_dirty = false;
    setWindowTitle(m_title);
    updateCoverage();
    return true;
}

void TestManagementDialog::markDirty()
{
    if (!m_dirty) {
        m_dirty = true;
        setWindowTitle(m_title + QString(" *"));
    }
}

void TestManagementDialog::closeEvent(QCloseEvent *event)
{
    if (m_dirty) {
        auto ret = QMessageBox::question(this, "未保存的修改", "是否保存修改？", QMessageBox::Yes | QMessageBox::No | QMessageBox::Cancel, QMessageBox::Cancel);
        if (ret == QMessageBox::Cancel) {
            event->ignore();
            return;
        }
        if (ret == QMessageBox::Yes) {
            if (!saveChanges()) {
                event->ignore();
                return;
            }
        }
    }
    QDialog::closeEvent(event);
}

void TestManagementDialog::on_btnGenerate_clicked()
{
    if (!m_generator)
        initializeGenerator();
    if (!m_generator)
        return;

    m_tests = m_generator->generateForContainer(m_containerId);
    m_entity = m_repo.getById(m_containerId);
    refreshTable();
    updateCoverage();
    m_dirty = false;
    setWindowTitle(m_title);
    if (!m_tests.isEmpty())
        ui->tableTests->setCurrentCell(0, 0);
    else
        updateDetails(-1);
}

void TestManagementDialog::on_btnAdd_clicked()
{
    GeneratedTest test;
    test.category = TestCategory::Signal;
    test.id = QString("user:%1").arg(QUuid::createUuid().toString(QUuid::WithoutBraces));
    TestEditDialog dialog(this);
    dialog.setTest(test);
    if (dialog.exec() != QDialog::Accepted)
        return;

    m_tests.append(dialog.test());
    refreshTable();
    ui->tableTests->setCurrentCell(m_tests.size() - 1, 0);
    updateCoverage();
    markDirty();
}

void TestManagementDialog::on_btnEdit_clicked()
{
    int row = ui->tableTests->currentRow();
    if (row < 0 || row >= m_tests.size())
        return;

    TestEditDialog dialog(this);
    dialog.setTest(m_tests.at(row));
    if (dialog.exec() != QDialog::Accepted)
        return;

    m_tests[row] = dialog.test();
    refreshTable();
    ui->tableTests->setCurrentCell(row, 0);
    updateCoverage();
    markDirty();
}

void TestManagementDialog::on_btnDelete_clicked()
{
    int row = ui->tableTests->currentRow();
    if (row < 0 || row >= m_tests.size())
        return;

    if (QMessageBox::question(this, "确认删除", "是否删除选中的测试？") != QMessageBox::Yes)
        return;

    m_tests.removeAt(row);
    refreshTable();
    updateCoverage();
    if (!m_tests.isEmpty()) {
        int nextRow = qMin(row, m_tests.size() - 1);
        ui->tableTests->setCurrentCell(nextRow, 0);
    } else {
        updateDetails(-1);
    }
    markDirty();
}

void TestManagementDialog::on_btnSave_clicked()
{
    if (saveChanges())
        QMessageBox::information(this, "提示", "保存成功");
}

void TestManagementDialog::on_tableTests_currentCellChanged(int currentRow, int, int, int)
{
    updateDetails(currentRow);
}
