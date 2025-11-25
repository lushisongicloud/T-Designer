#include "widget/testmanagementdialog.h"
#include "ui_testmanagementdialog.h"

#include <algorithm>
#include <functional>
#include <QCloseEvent>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QListWidgetItem>
#include <QMessageBox>
#include <QHeaderView>
#include <QTreeWidgetItem>
#include <QUuid>
#include <QSqlQuery>
#include <QSqlError>
#include <QDebug>
#include <QTimer>
#include <QPushButton>
#include <QFileInfo>
#include <QDir>

#include "widget/testeditdialog.h"
#include "widget/containerhierarchyutils.h"
#include "BO/test/dmatrixservice.h"
#include "widget/dmatrixviewerdialog.h"

namespace {
struct TestScore {
    GeneratedTest test;
    int detectionCount = 0;
};
}

TestManagementDialog::TestManagementDialog(int containerId, const QSqlDatabase &db, QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::TestManagementDialog)
    , m_containerId(containerId)
    , m_db(db)
    , m_repo(db)
{
    ui->setupUi(this);
    m_title = windowTitle();

    // 隐藏除"决策树"外的所有tab页
    ui->tabWidget->removeTab(ui->tabWidget->indexOf(ui->tabTests));
    ui->tabWidget->removeTab(ui->tabWidget->indexOf(ui->tabMatrix));
    ui->tabWidget->removeTab(ui->tabWidget->indexOf(ui->tabTargets));
    ui->tabWidget->removeTab(ui->tabWidget->indexOf(ui->tabConstraints));
    ui->tabWidget->removeTab(ui->tabWidget->indexOf(ui->tabPrediction));
    ui->labelCoverage->setVisible(false);

    configureTables();

    connect(ui->btnClose, &QPushButton::clicked, this, &QDialog::reject);
    connect(ui->btnViewDMatrix, &QPushButton::clicked, this, &TestManagementDialog::onViewDMatrix);
    connect(ui->btnGenerate, &QPushButton::clicked, this, &TestManagementDialog::on_btnGenerate_clicked);
    connect(ui->btnAdd, &QPushButton::clicked, this, &TestManagementDialog::on_btnAdd_clicked);
    connect(ui->btnEdit, &QPushButton::clicked, this, &TestManagementDialog::on_btnEdit_clicked);
    connect(ui->btnDelete, &QPushButton::clicked, this, &TestManagementDialog::on_btnDelete_clicked);
    connect(ui->btnSave, &QPushButton::clicked, this, &TestManagementDialog::on_btnSave_clicked);
    connect(ui->tableTests, &QTableWidget::currentCellChanged,
            this, &TestManagementDialog::on_tableTests_currentCellChanged);
    connect(ui->btnApplyTargets, &QPushButton::clicked, this, &TestManagementDialog::on_btnApplyTargets_clicked);
    connect(ui->btnApplyConstraints, &QPushButton::clicked, this, &TestManagementDialog::on_btnApplyConstraints_clicked);
    connect(ui->btnEvaluatePrediction, &QPushButton::clicked, this, &TestManagementDialog::on_btnEvaluatePrediction_clicked);
    connect(ui->btnBuildDecisionTree, &QPushButton::clicked, this, &TestManagementDialog::on_btnBuildDecisionTree_clicked);
    connect(ui->comboDecisionTree, QOverload<int>::of(&QComboBox::currentIndexChanged),
            this, &TestManagementDialog::on_comboDecisionTree_currentIndexChanged);
    connect(ui->treeDecision, &QTreeWidget::currentItemChanged,
            this, &TestManagementDialog::on_treeDecision_currentItemChanged);

    loadData();
}

TestManagementDialog::~TestManagementDialog()
{
    delete ui;
}

void TestManagementDialog::configureTables()
{
    ui->tableTests->setColumnCount(7);
    ui->tableTests->setHorizontalHeaderLabels({"类别", "名称", "目标", "检测故障", "隔离故障", "费用", "时间"});
    ui->tableTests->horizontalHeader()->setStretchLastSection(true);
    ui->tableTests->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableTests->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableTests->setEditTriggers(QAbstractItemView::NoEditTriggers);

    ui->tableMatrix->setColumnCount(4);
    ui->tableMatrix->setHorizontalHeaderLabels({"测试", "故障", "检测", "隔离"});
    ui->tableMatrix->horizontalHeader()->setStretchLastSection(true);
    ui->tableMatrix->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableMatrix->setEditTriggers(QAbstractItemView::NoEditTriggers);

    ui->tableTargetAllocation->setColumnCount(3);
    ui->tableTargetAllocation->setHorizontalHeaderLabels({"容器", "检测率", "隔离率"});
    ui->tableTargetAllocation->horizontalHeader()->setStretchLastSection(true);
    ui->tableTargetAllocation->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableTargetAllocation->setEditTriggers(QAbstractItemView::NoEditTriggers);

    ui->tablePredictionBreakdown->setColumnCount(2);
    ui->tablePredictionBreakdown->setHorizontalHeaderLabels({"指标", "数值"});
    ui->tablePredictionBreakdown->horizontalHeader()->setStretchLastSection(true);
    ui->tablePredictionBreakdown->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tablePredictionBreakdown->setEditTriggers(QAbstractItemView::NoEditTriggers);

    ui->treeDecision->header()->setStretchLastSection(true);

    // 设置决策树splitter的默认比例为3:1
    ui->splitterDecision->setStretchFactor(0, 3);
    ui->splitterDecision->setStretchFactor(1, 1);
}

void TestManagementDialog::initializeGenerator()
{
    m_generator.reset();
    m_aggregator.reset();

    if (m_containerId == 0) {
        qWarning() << "TestManagementDialog: m_containerId == 0";
        return;
    }

    if (!m_repo.ensureTables()) {
        qWarning() << "TestManagementDialog: ensureTables() 失败";
        return;
    }

    m_entity = m_repo.getById(m_containerId);
    
    if (m_entity.id() == 0) {
        qWarning() << "TestManagementDialog: 未找到 container_id =" << m_containerId;
        return;
    }

    auto loader = [this](int id) { return m_repo.getById(id); };
    auto fetcher = [this](int id) { return m_repo.fetchChildren(id); };
    m_aggregator = std::make_unique<BehaviorAggregator>(loader, fetcher);

    auto functions = ContainerHierarchy::fetchFunctionInfoMap(m_db);
    m_resolver.setDefinitions(functions);

    m_generator = std::make_unique<TestGeneratorService>(m_repo, *m_aggregator, m_resolver);
    m_generator->setFunctionMap(functions);
    m_generator->setContainerFunctions(ContainerHierarchy::defaultFunctionMapping(m_entity, functions));

    m_childEntities = QVector<ContainerEntity>::fromList(m_repo.fetchChildren(m_entity.id()));
}

void TestManagementDialog::loadData()
{
    initializeGenerator();
    if (m_entity.id() == 0)
        return;

    ContainerData container(m_entity);
    m_tests = container.tests();
    m_analysisData = container.analysisData();

    refreshTable();
    rebuildMatrix();
    applyAnalysisToUi();
    updateCoverage();
    refreshPredictionView();
    refreshDecisionTreeView();
    loadDecisionTreeList();

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

void TestManagementDialog::rebuildMatrix()
{
    ContainerData container(m_entity);
    container.setTests(m_tests);
    m_matrixBuilder.rebuild(container);
    refreshMatrixView();
}

void TestManagementDialog::refreshMatrixView()
{
    const QVector<MatrixEntry> &entries = m_matrixBuilder.entries();
    ui->tableMatrix->setRowCount(entries.size());
    for (int row = 0; row < entries.size(); ++row) {
        const MatrixEntry &entry = entries.at(row);
        auto setItem = [&](int column, const QString &text) {
            QTableWidgetItem *item = new QTableWidgetItem(text);
            item->setData(Qt::UserRole, row);
            ui->tableMatrix->setItem(row, column, item);
        };
        setItem(0, entry.testId);
        setItem(1, entry.faultId);
        setItem(2, entry.detects ? tr("是") : tr("否"));
        setItem(3, entry.isolates ? tr("是") : tr("否"));
    }

    CoverageStats stats = m_matrixBuilder.coverageStats();
    if (stats.totalFaults == 0) {
        ui->plainMatrixInfo->setPlainText(tr("尚无故障定义"));
        return;
    }

    QString info;
    info += tr("测试数量: %1\n").arg(stats.totalTests);
    info += tr("故障数量: %1\n").arg(stats.totalFaults);
    info += tr("检测覆盖: %1\n").arg(stats.detectedFaults.size());
    info += tr("隔离覆盖: %1").arg(stats.isolatableFaults.size());
    ui->plainMatrixInfo->setPlainText(info);
}

void TestManagementDialog::updateCoverage()
{
    CoverageStats stats = m_matrixBuilder.coverageStats();
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
    data.setAnalysisData(m_analysisData);
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

void TestManagementDialog::refreshAllocationView()
{
    const QVariantMap targets = m_analysisData.value(QString("targets")).toMap();
    const double detection = targets.value(QString("detection"), ui->spinTargetDetection->value()).toDouble();
    const double isolation = targets.value(QString("isolation"), ui->spinTargetIsolation->value()).toDouble();

    QVariantList allocations = m_analysisData.value(QString("allocations")).toList();
    ui->tableTargetAllocation->setRowCount(0);

    auto appendRow = [&](const QString &name, double det, double iso) {
        const int row = ui->tableTargetAllocation->rowCount();
        ui->tableTargetAllocation->insertRow(row);
        ui->tableTargetAllocation->setItem(row, 0, new QTableWidgetItem(name));
        ui->tableTargetAllocation->setItem(row, 1, new QTableWidgetItem(QString::number(det, 'f', 3)));
        ui->tableTargetAllocation->setItem(row, 2, new QTableWidgetItem(QString::number(iso, 'f', 3)));
    };

    QString containerName = m_entity.name();
    if (containerName.trimmed().isEmpty())
        containerName = tr("容器 %1").arg(m_entity.id());
    appendRow(containerName, detection, isolation);

    for (const QVariant &value : allocations) {
        const QVariantMap alloc = value.toMap();
        const int cid = alloc.value(QString("containerId")).toInt();
        double det = alloc.value(QString("detection"), detection).toDouble();
        double iso = alloc.value(QString("isolation"), isolation).toDouble();
        QString name = alloc.value(QString("name")).toString();
        if (name.trimmed().isEmpty()) {
            auto it = std::find_if(m_childEntities.begin(), m_childEntities.end(), [cid](const ContainerEntity &entity) {
                return entity.id() == cid;
            });
            if (it != m_childEntities.end())
                name = it->name();
        }
        if (name.trimmed().isEmpty())
            name = tr("子容器 %1").arg(cid);
        appendRow(name, det, iso);
    }
}

void TestManagementDialog::refreshCandidateList()
{
    ui->listCandidateTests->clear();
    if (m_candidateTests.isEmpty()) {
        auto *item = new QListWidgetItem(tr("尚未选择候选测试"));
        item->setFlags(Qt::NoItemFlags);
        ui->listCandidateTests->addItem(item);
        return;
    }

    QStringList validated;
    for (const QString &testId : m_candidateTests) {
        auto it = std::find_if(m_tests.begin(), m_tests.end(), [&](const GeneratedTest &test) {
            return test.id == testId;
        });
        if (it == m_tests.end()) continue;
        validated.append(testId);
        ui->listCandidateTests->addItem(testDisplayText(*it));
    }

    if (validated.size() != m_candidateTests.size()) {
        m_candidateTests = validated;
        m_analysisData.insert(QString("candidates"), m_candidateTests);
        markDirty();
    }
}

void TestManagementDialog::refreshPredictionView()
{
    const QVariantMap prediction = m_analysisData.value(QString("prediction")).toMap();
    if (prediction.isEmpty()) {
        ui->labelPredictionSummary->setText(tr("尚未计算预测"));
        ui->tablePredictionBreakdown->setRowCount(0);
        return;
    }

    const double detectionRate = prediction.value(QString("detectionRate")).toDouble();
    const double isolationRate = prediction.value(QString("isolationRate")).toDouble();
    const int detected = prediction.value(QString("detectedFaults")).toInt();
    const int isolatable = prediction.value(QString("isolatableFaults")).toInt();
    const int total = prediction.value(QString("totalFaults")).toInt();

    ui->labelPredictionSummary->setText(
        tr("检测率: %1%，隔离率: %2% (%3/%4, %5/%4)")
            .arg(detectionRate * 100.0, 0, 'f', 1)
            .arg(isolationRate * 100.0, 0, 'f', 1)
            .arg(detected)
            .arg(total)
            .arg(isolatable));

    ui->tablePredictionBreakdown->setRowCount(0);
    auto appendRow = [&](const QString &name, const QString &value) {
        const int row = ui->tablePredictionBreakdown->rowCount();
        ui->tablePredictionBreakdown->insertRow(row);
        ui->tablePredictionBreakdown->setItem(row, 0, new QTableWidgetItem(name));
        ui->tablePredictionBreakdown->setItem(row, 1, new QTableWidgetItem(value));
    };
    appendRow(tr("检测率"), QString::number(detectionRate, 'f', 4));
    appendRow(tr("隔离率"), QString::number(isolationRate, 'f', 4));
    appendRow(tr("覆盖故障"), tr("%1/%2").arg(detected).arg(total));
    appendRow(tr("隔离故障"), tr("%1/%2").arg(isolatable).arg(total));
}

void TestManagementDialog::refreshDecisionTreeView()
{
    ui->treeDecision->clear();
    const QVariantMap decision = m_analysisData.value(QString("decisionTree")).toMap();
    if (decision.isEmpty()) {
        ui->plainDecisionNotes->setPlainText(tr("尚未生成决策树"));
        return;
    }

    std::shared_ptr<DecisionNode> root = decisionNodeFromVariant(decision);
    if (!root) {
        ui->plainDecisionNotes->setPlainText(tr("无法解析已保存的决策树"));
        return;
    }

    populateDecisionTreeWidget(root);
    ui->plainDecisionNotes->setPlainText(decisionNodeSummary(root));
}

void TestManagementDialog::applyAnalysisToUi()
{
    const QVariantMap targets = m_analysisData.value(QString("targets")).toMap();
    if (!targets.isEmpty()) {
        ui->spinTargetDetection->setValue(targets.value(QString("detection"), ui->spinTargetDetection->value()).toDouble());
        ui->spinTargetIsolation->setValue(targets.value(QString("isolation"), ui->spinTargetIsolation->value()).toDouble());
    }

    const QVariantMap constraints = m_analysisData.value(QString("constraints")).toMap();
    if (!constraints.isEmpty()) {
        ui->spinMaxCost->setValue(constraints.value(QString("maxCost"), ui->spinMaxCost->value()).toDouble());
        ui->spinMaxDuration->setValue(constraints.value(QString("maxDuration"), ui->spinMaxDuration->value()).toDouble());
        ui->spinMaxCount->setValue(constraints.value(QString("maxCount"), ui->spinMaxCount->value()).toInt());
    }

    m_candidateTests = m_analysisData.value(QString("candidates")).toStringList();
    refreshAllocationView();
    refreshCandidateList();
}

QString TestManagementDialog::testDisplayText(const GeneratedTest &test) const
{
    return QString("[%1] %2 (费用:%3 时间:%4)")
        .arg(testCategoryToString(test.category))
        .arg(test.name)
        .arg(test.estimatedCost, 0, 'f', 1)
        .arg(test.estimatedDuration, 0, 'f', 1);
}

QStringList TestManagementDialog::candidateTestsByHeuristics(double maxCost, double maxDuration, int maxCount) const
{
    QList<TestScore> scores;
    scores.reserve(m_tests.size());
    for (const GeneratedTest &test : m_tests) {
        TestScore score;
        score.test = test;
        score.detectionCount = test.detectableFaults.count();
        scores.append(score);
    }

    std::sort(scores.begin(), scores.end(), [](const TestScore &a, const TestScore &b) {
        if (a.detectionCount == b.detectionCount)
            return a.test.estimatedCost < b.test.estimatedCost;
        return a.detectionCount > b.detectionCount;
    });

    QStringList selected;
    double costSum = 0.0;
    double durationSum = 0.0;
    int count = 0;
    for (const TestScore &score : scores) {
        const GeneratedTest &test = score.test;
        if (maxCount > 0 && count >= maxCount)
            break;
        if (maxCost > 0.0 && costSum + test.estimatedCost > maxCost)
            continue;
        if (maxDuration > 0.0 && durationSum + test.estimatedDuration > maxDuration)
            continue;
        selected.append(test.id);
        costSum += test.estimatedCost;
        durationSum += test.estimatedDuration;
        ++count;
    }

    if (selected.isEmpty() && !scores.isEmpty())
        selected.append(scores.first().test.id);
    return selected;
}

QString TestManagementDialog::decisionNodeSummary(const std::shared_ptr<DecisionNode> &node, int depth) const
{
    if (!node)
        return QString();

    QString indent(depth * 2, ' ');
    QString text;
    if (node->isLeaf) {
        if (node->faultId.isEmpty())
            text += indent + tr("叶节点: 未覆盖的故障\n");
        else
            text += indent + tr("叶节点: %1\n").arg(node->faultId);
        return text;
    }

    text += indent + tr("测试: %1\n").arg(node->testId);
    for (const auto &child : node->children)
        text += decisionNodeSummary(child, depth + 1);
    return text;
}

QVariantMap TestManagementDialog::decisionNodeToVariant(const std::shared_ptr<DecisionNode> &node) const
{
    QVariantMap map;
    if (!node)
        return map;
    map.insert(QString("isLeaf"), node->isLeaf);
    if (!node->testId.isEmpty())
        map.insert(QString("test"), node->testId);
    if (!node->faultId.isEmpty())
        map.insert(QString("fault"), node->faultId);
    QVariantList children;
    for (const auto &child : node->children)
        children.append(decisionNodeToVariant(child));
    if (!children.isEmpty())
        map.insert(QString("children"), children);
    return map;
}

std::shared_ptr<DecisionNode> TestManagementDialog::decisionNodeFromVariant(const QVariantMap &object) const
{
    if (object.isEmpty())
        return nullptr;
    auto node = std::make_shared<DecisionNode>();
    node->isLeaf = object.value(QString("isLeaf")).toBool();
    node->testId = object.value(QString("test")).toString();
    node->faultId = object.value(QString("fault")).toString();
    const QVariantList children = object.value(QString("children")).toList();
    for (const QVariant &value : children) {
        auto child = decisionNodeFromVariant(value.toMap());
        if (child)
            node->children.append(child);
    }
    return node;
}

void TestManagementDialog::populateDecisionTreeWidget(const std::shared_ptr<DecisionNode> &node, QTreeWidgetItem *parentItem)
{
    if (!node)
        return;

    QString label;
    if (node->isLeaf) {
        label = node->faultId.isEmpty() ? tr("未隔离故障") : node->faultId;
    } else {
        label = tr("测试: %1").arg(node->testId);
    }

    QTreeWidgetItem *item = nullptr;
    if (parentItem) {
        item = new QTreeWidgetItem(parentItem);
    } else {
        item = new QTreeWidgetItem(ui->treeDecision);
    }
    item->setText(0, label);

    for (const auto &child : node->children)
        populateDecisionTreeWidget(child, item);
}

void TestManagementDialog::closeEvent(QCloseEvent *event)
{
    if (m_dirty) {
        auto ret = QMessageBox::question(this, tr("未保存的修改"), tr("是否保存修改？"),
                                         QMessageBox::Yes | QMessageBox::No | QMessageBox::Cancel, QMessageBox::Cancel);
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

    m_tests = m_generator->generateForContainer(m_containerId, true);
    m_entity = m_repo.getById(m_containerId);
    loadData();
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
    rebuildMatrix();
    updateCoverage();
    refreshPredictionView();
    markDirty();
    ui->tableTests->setCurrentCell(m_tests.size() - 1, 0);
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
    rebuildMatrix();
    updateCoverage();
    refreshPredictionView();
    markDirty();
    ui->tableTests->setCurrentCell(row, 0);
}

void TestManagementDialog::on_btnDelete_clicked()
{
    int row = ui->tableTests->currentRow();
    if (row < 0 || row >= m_tests.size())
        return;

    if (QMessageBox::question(this, tr("确认"), tr("是否删除选中的测试？")) != QMessageBox::Yes)
        return;

    m_tests.removeAt(row);
    refreshTable();
    rebuildMatrix();
    updateCoverage();
    refreshPredictionView();
    markDirty();

    if (!m_tests.isEmpty()) {
        int nextRow = qMin(row, m_tests.size() - 1);
        ui->tableTests->setCurrentCell(nextRow, 0);
    } else {
        updateDetails(-1);
    }
}

void TestManagementDialog::on_btnSave_clicked()
{
    if (saveChanges())
        QMessageBox::information(this, tr("提示"), tr("保存成功"));
}

void TestManagementDialog::on_tableTests_currentCellChanged(int currentRow, int, int, int)
{
    updateDetails(currentRow);
}

void TestManagementDialog::on_btnApplyTargets_clicked()
{
    QVariantMap targets;
    targets.insert(QString("detection"), ui->spinTargetDetection->value());
    targets.insert(QString("isolation"), ui->spinTargetIsolation->value());
    m_analysisData.insert(QString("targets"), targets);

    QVariantList allocations;
    const int childCount = m_childEntities.size();
    for (const ContainerEntity &child : m_childEntities) {
        QVariantMap alloc;
        alloc.insert(QString("containerId"), child.id());
        alloc.insert(QString("name"), child.name());
        alloc.insert(QString("detection"), targets.value(QString("detection")));
        alloc.insert(QString("isolation"), targets.value(QString("isolation")));
        allocations.append(alloc);
    }
    m_analysisData.insert(QString("allocations"), allocations);
    refreshAllocationView();
    markDirty();
}

void TestManagementDialog::on_btnApplyConstraints_clicked()
{
    const double maxCost = ui->spinMaxCost->value();
    const double maxDuration = ui->spinMaxDuration->value();
    const int maxCount = ui->spinMaxCount->value();

    m_candidateTests = candidateTestsByHeuristics(maxCost, maxDuration, maxCount);
    refreshCandidateList();

    QVariantMap constraints;
    constraints.insert(QString("maxCost"), maxCost);
    constraints.insert(QString("maxDuration"), maxDuration);
    constraints.insert(QString("maxCount"), maxCount);
    m_analysisData.insert(QString("constraints"), constraints);
    m_analysisData.insert(QString("candidates"), m_candidateTests);
    markDirty();
}

void TestManagementDialog::on_btnEvaluatePrediction_clicked()
{
    QStringList testsToEvaluate = m_candidateTests;
    if (testsToEvaluate.isEmpty()) {
        for (const GeneratedTest &test : m_tests)
            testsToEvaluate.append(test.id);
    }

    CoverageSummary summary = m_matrixBuilder.coverageSummary(testsToEvaluate);
    QVariantMap prediction;
    prediction.insert(QString("detectionRate"), summary.detectionRate);
    prediction.insert(QString("isolationRate"), summary.isolationRate);
    prediction.insert(QString("detectedFaults"), summary.detectedFaults);
    prediction.insert(QString("isolatableFaults"), summary.isolatableFaults);
    prediction.insert(QString("totalFaults"), summary.totalFaults);
    prediction.insert(QString("tests"), testsToEvaluate);
    m_analysisData.insert(QString("prediction"), prediction);
    refreshPredictionView();
    markDirty();
}

void TestManagementDialog::on_btnBuildDecisionTree_clicked()
{
    // 清空三个控件的所有内容
    ui->comboDecisionTree->clear();
    ui->treeDecision->clear();
    ui->plainDecisionNotes->clear();
    
    // 延迟120ms后重新加载并刷新
    QTimer::singleShot(120, this, [this]() {
        // 重新加载决策树列表
        loadDecisionTreeList();
        
        // 如果有决策树，选择第一个（索引1，因为索引0是"-- 请选择决策树 --"）
        if (ui->comboDecisionTree->count() > 1) {
            ui->comboDecisionTree->setCurrentIndex(1);
        }
    });
}

void TestManagementDialog::loadDecisionTreeList()
{
    ui->comboDecisionTree->clear();
    
    if (!m_db.isOpen()) {
        qWarning() << "TestManagementDialog: 数据库未打开";
        return;
    }

    QSqlQuery query(m_db);
    query.prepare("SELECT tree_id, name, description FROM diagnosis_tree ORDER BY tree_id DESC");
    
    if (!query.exec()) {
        qWarning() << "加载决策树列表失败:" << query.lastError().text();
        return;
    }

    ui->comboDecisionTree->addItem("-- 请选择决策树 --", -1);
    
    while (query.next()) {
        int treeId = query.value(0).toInt();
        QString name = query.value(1).toString();
        QString description = query.value(2).toString();
        
        QString displayText = name.isEmpty() ? QString("决策树 #%1").arg(treeId) : name;
        if (!description.isEmpty()) {
            displayText += QString(" (%1)").arg(description);
        }
        
        ui->comboDecisionTree->addItem(displayText, treeId);
    }
}

void TestManagementDialog::on_comboDecisionTree_currentIndexChanged(int index)
{
    if (index < 0)
        return;

    int treeId = ui->comboDecisionTree->currentData().toInt();
    if (treeId <= 0) {
        ui->treeDecision->clear();
        ui->plainDecisionNotes->clear();
        return;
    }

    loadDecisionTreeFromDatabase(treeId);
}

void TestManagementDialog::loadDecisionTreeFromDatabase(int treeId)
{
    ui->treeDecision->clear();
    ui->plainDecisionNotes->clear();

    if (!m_db.isOpen()) {
        qWarning() << "TestManagementDialog: 数据库未打开";
        return;
    }

    QSqlQuery query(m_db);
    query.prepare("SELECT root_node_id FROM diagnosis_tree WHERE tree_id = ?");
    query.addBindValue(treeId);
    
    if (!query.exec()) {
        qWarning() << "查询决策树失败:" << query.lastError().text();
        ui->plainDecisionNotes->setPlainText("无法加载决策树根节点");
        return;
    }
    
    if (!query.next()) {
        qWarning() << "未找到 tree_id =" << treeId;
        ui->plainDecisionNotes->setPlainText("无法加载决策树根节点");
        return;
    }

    int rootNodeId = query.value(0).toInt();
    
    if (rootNodeId <= 0) {
        qWarning() << "决策树 tree_id =" << treeId << "的 root_node_id 无效:" << rootNodeId;
        ui->plainDecisionNotes->setPlainText("决策树根节点未设置");
        return;
    }

    std::function<void(int, QTreeWidgetItem*, bool, QString, QString)> loadNode = 
        [&](int nodeId, QTreeWidgetItem *parentItem, bool isRoot, QString parentPassText, QString parentFailText) {
        
        QSqlQuery nodeQuery(m_db);
        // 基础查询,只查询所有数据库都有的字段
        nodeQuery.prepare("SELECT node_id, node_type, test_id, state_id, outcome, comment, "
                         "test_description, expected_result, fault_hypothesis, isolation_level, test_priority, parent_node_id "
                         "FROM diagnosis_tree_node WHERE node_id = ?");
        nodeQuery.addBindValue(nodeId);
        
        if (!nodeQuery.exec()) {
            qWarning() << "查询节点" << nodeId << "失败:" << nodeQuery.lastError().text();
            return;
        }
        
        if (!nodeQuery.next()) {
            qWarning() << "未找到 node_id =" << nodeId;
            return;
        }

        int currentNodeId = nodeQuery.value(0).toInt();
        QString nodeType = nodeQuery.value(1).toString();
        int testId = nodeQuery.value(2).toInt();
        int stateId = nodeQuery.value(3).toInt();
        QString outcome = nodeQuery.value(4).toString();
        QString comment = nodeQuery.value(5).toString();
        QString testDescription = nodeQuery.value(6).toString();
        QString expectedResult = nodeQuery.value(7).toString();
        QString faultHypothesis = nodeQuery.value(8).toString();
        int isolationLevel = nodeQuery.value(9).toInt();
        double testPriority = nodeQuery.value(10).toDouble();
        int parentNodeId = nodeQuery.value(11).toInt();
        
        // 使用默认按钮文本(旧数据库不支持自定义按钮文本)
        QString passButtonText = "是";
        QString failButtonText = "否";

        QString nodeLabel;
        
        // 辅助函数：截断字符串
        auto truncateString = [](const QString &str, int maxLen = 20) -> QString {
            if (str.length() <= maxLen)
                return str;
            return str.left(maxLen) + "...";
        };
        
        // 辅助函数：查找冒号位置（支持全角和半角）
        auto findColonPos = [](const QString &str) -> int {
            int pos1 = str.indexOf(':');   // 半角冒号
            int pos2 = str.indexOf("：");  // 全角冒号
            if (pos1 < 0) return pos2;
            if (pos2 < 0) return pos1;
            return qMin(pos1, pos2);  // 返回最先出现的冒号位置
        };
        
        // 统一转换为小写进行比较，以支持不同大小写
        QString nodeTypeLower = nodeType.toLower();
        
        if (nodeTypeLower == "branch") {
            // Branch 节点：根节点显示"根节点"，其他显示父节点的 pass_button_text
            if (isRoot || parentNodeId == 0) {
                nodeLabel = "根节点";
            } else {
                // 显示父节点的 pass_button_text
                nodeLabel = parentPassText.isEmpty() ? "分支节点" : QString("[%1]").arg(parentPassText);
            }
        } else if (nodeTypeLower == "test") {
            // Test 节点：显示"测试：..."格式
            QString testDesc;
            if (!testDescription.isEmpty()) {
                testDesc = testDescription;
            } else if (!comment.isEmpty()) {
                testDesc = comment;
            } else {
                testDesc = QString("【测试】 #%1").arg(testId);
            }
            nodeLabel = QString("【测试】 %1").arg(truncateString(testDesc, 40));
        } else if (nodeTypeLower == "fault") {
            // Fault 节点：显示父节点的 fail_button_text + 故障类型（冒号前的内容）
            QString faultType;
            QString faultText = faultHypothesis.isEmpty() ? comment : faultHypothesis;
            if (!faultText.isEmpty()) {
                int colonPos = findColonPos(faultText);  // 支持全角和半角冒号
                faultType = colonPos > 0 ? faultText.left(colonPos).trimmed() : faultText.trimmed();
            } else {
                faultType = QString("故障 #%1").arg(stateId);
            }
            
            // 组合父节点的fail_button_text和故障类型
            if (!parentFailText.isEmpty()) {
                nodeLabel = QString("[%1] %2").arg(parentFailText).arg(truncateString(faultType, 30));
            } else {
                nodeLabel = truncateString(faultType, 40);
            }
        } else {
            // 未知节点类型，显示节点ID和类型
            nodeLabel = QString("节点 #%1 [%2]").arg(currentNodeId).arg(nodeType);
        }

        QTreeWidgetItem *item = nullptr;
        if (parentItem) {
            item = new QTreeWidgetItem(parentItem);
        } else {
            item = new QTreeWidgetItem(ui->treeDecision);
        }
        item->setText(0, nodeLabel);
        
        QVariantMap nodeData;
        nodeData["node_id"] = currentNodeId;
        nodeData["node_type"] = nodeType;
        nodeData["test_id"] = testId;
        nodeData["state_id"] = stateId;
        nodeData["outcome"] = outcome;
        nodeData["comment"] = comment;
        nodeData["test_description"] = testDescription;
        nodeData["expected_result"] = expectedResult;
        nodeData["fault_hypothesis"] = faultHypothesis;
        nodeData["isolation_level"] = isolationLevel;
        nodeData["test_priority"] = testPriority;
        nodeData["parent_node_id"] = parentNodeId;
        nodeData["pass_button_text"] = passButtonText;
        nodeData["fail_button_text"] = failButtonText;
        item->setData(0, Qt::UserRole, nodeData);

        QSqlQuery childQuery(m_db);
        childQuery.prepare("SELECT node_id FROM diagnosis_tree_node WHERE parent_node_id = ? ORDER BY node_id");
        childQuery.addBindValue(currentNodeId);
        
        if (childQuery.exec()) {
            while (childQuery.next()) {
                int childNodeId = childQuery.value(0).toInt();
                // 递归加载子节点，传递当前节点的按钮文本
                loadNode(childNodeId, item, false, passButtonText, failButtonText);
            }
        }
    };

    loadNode(rootNodeId, nullptr, true, QString(), QString());
    
    // 默认折叠所有节点
    ui->treeDecision->collapseAll();
    
    // 检查是否成功加载
    if (ui->treeDecision->topLevelItemCount() == 0) {
        qWarning() << "决策树 tree_id =" << treeId << "加载失败: 未生成任何节点";
    }
}

void TestManagementDialog::on_treeDecision_currentItemChanged(QTreeWidgetItem *current, QTreeWidgetItem *previous)
{
    Q_UNUSED(previous);
    displayNodeDetails(current);
}

void TestManagementDialog::displayNodeDetails(QTreeWidgetItem *item)
{
    if (!item) {
        ui->plainDecisionNotes->clear();
        return;
    }

    QVariantMap nodeData = item->data(0, Qt::UserRole).toMap();
    if (nodeData.isEmpty()) {
        ui->plainDecisionNotes->setPlainText("节点无详细信息");
        return;
    }

    QString details;
    
    // 定义字段映射表，用于显示所有非空字段
    QList<QPair<QString, QString>> fieldMap = {
        {"node_id", "节点ID"},
        {"node_type", "节点类型"},
        {"parent_node_id", "父节点ID"},
        {"test_id", "测试ID"},
        {"state_id", "状态ID"},
        {"outcome", "测试结果"},
        {"test_description", "测试描述"},
        {"expected_result", "期望结果"},
        {"fault_hypothesis", "故障假设"},
        {"isolation_level", "隔离级别"},
        {"test_priority", "测试优先级"},
        {"pass_button_text", "通过按钮文本"},
        {"fail_button_text", "失败按钮文本"},
        {"comment", "备注"}
    };
    
    // 遍历所有字段，显示非空字段
    for (const auto &field : fieldMap) {
        const QString &key = field.first;
        const QString &label = field.second;
        
        if (!nodeData.contains(key))
            continue;
            
        QVariant value = nodeData.value(key);
        
        // 跳过空值
        if (value.isNull())
            continue;
            
        // 根据类型处理值
        QString displayValue;
        if (value.type() == QVariant::Int) {
            int intVal = value.toInt();
            // 跳过为0的ID字段（表示未设置）
            if ((key.endsWith("_id") || key == "isolation_level") && intVal == 0)
                continue;
            displayValue = QString::number(intVal);
        } else if (value.type() == QVariant::Double) {
            double doubleVal = value.toDouble();
            // 跳过为0的优先级（表示未设置）
            if (key == "test_priority" && qFuzzyCompare(doubleVal, 0.0))
                continue;
            displayValue = QString::number(doubleVal, 'f', 3);
        } else {
            QString strVal = value.toString();
            if (strVal.isEmpty())
                continue;
            displayValue = strVal;
        }
        
        // 格式化输出
        if (key == "comment" && displayValue.length() > 50) {
            // 备注字段较长时单独一行
            details += QString("\n%1:\n%2\n").arg(label).arg(displayValue);
        } else if (key == "test_description" || key == "fault_hypothesis" || key == "expected_result") {
            // 描述性字段可能较长
            if (displayValue.length() > 40) {
                details += QString("\n%1:\n%2\n").arg(label).arg(displayValue);
            } else {
                details += QString("%1: %2\n").arg(label).arg(displayValue);
            }
        } else {
            details += QString("%1: %2\n").arg(label).arg(displayValue);
        }
    }
    
    if (details.isEmpty()) {
        details = "该节点没有详细信息";
    }

    ui->plainDecisionNotes->setPlainText(details);
}

void TestManagementDialog::onViewDMatrix()
{
    DMatrixService service(m_db);
    if (!service.ensureTable()) {
        QMessageBox::warning(this, tr("提示"), tr("dmatrix_meta 表不可用"));
        return;
    }

    QFileInfo dbInfo(m_db.databaseName());
    const QString projectDir = dbInfo.absolutePath();
    const QString projectName = dbInfo.completeBaseName();

    DMatrixLoadResult load = service.loadLatest(m_containerId, projectDir, projectName);
    if (!load.found) {
        QMessageBox::information(this, tr("提示"), tr("尚未生成 D 矩阵，请在主界面通过“D矩阵”按钮生成。"));
        return;
    }

    DMatrixViewerDialog dialog(this);
    dialog.setMatrix(load.result, load.options, load.csvPath, load.metadataPath);
    dialog.applyState(load.stateJson);

    connect(&dialog, &DMatrixViewerDialog::saveRequested, this,
            [service, cid = m_containerId](const QString &metadataPath,
                                           const QString &csvPath,
                                           const QVector<bool> &faultStates,
                                           const QVector<bool> &testStates) {
                const QString state = DMatrixService::serializeState(faultStates, testStates);
                service.saveMetadata(cid, metadataPath, csvPath, state);
            });

    connect(&dialog, &DMatrixViewerDialog::buildRequested, &dialog, [&dialog]() {
        QMessageBox::information(&dialog, QObject::tr("提示"), QObject::tr("请在主界面通过“D矩阵”按钮生成或更新。"));
    });

    dialog.exec();
}
