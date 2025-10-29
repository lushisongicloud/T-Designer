#include "widget/testmanagementdialog.h"
#include "ui_testmanagementdialog.h"

#include <algorithm>
#include <QCloseEvent>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QListWidgetItem>
#include <QMessageBox>
#include <QHeaderView>
#include <QTreeWidgetItem>
#include <QUuid>

#include "widget/testeditdialog.h"
#include "widget/containerhierarchyutils.h"

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

    configureTables();

    connect(ui->btnClose, &QPushButton::clicked, this, &QDialog::reject);
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
    QStringList testsForTree = m_candidateTests;
    if (testsForTree.isEmpty()) {
        for (const GeneratedTest &test : m_tests)
            testsForTree.append(test.id);
    }

    std::shared_ptr<DecisionNode> root = m_matrixBuilder.buildDecisionTree(testsForTree);
    m_analysisData.insert(QString("decisionTree"), decisionNodeToVariant(root));
    refreshDecisionTreeView();
    markDirty();
}
