#include "BO/test/diagnosticmatrixbuilder.h"

#include <algorithm>

DiagnosticMatrixBuilder::DiagnosticMatrixBuilder() = default;

void DiagnosticMatrixBuilder::rebuild(const ContainerData &container)
{
    m_entries.clear();
    m_tests = container.tests();
    m_faultIds.clear();
    m_detectionMap.clear();
    m_isolationMap.clear();

    const BehaviorSpec &behavior = container.behavior();
    for (const BehaviorMode &mode : behavior.faultModes) {
        if (!mode.modeId.isEmpty())
            m_faultIds.insert(mode.modeId);
    }

    for (const GeneratedTest &test : m_tests) {
        QSet<QString> detect = QSet<QString>::fromList(test.detectableFaults);
        QSet<QString> isolate = QSet<QString>::fromList(test.isolatableFaults);
        for (const QString &fault : detect) {
            MatrixEntry entry;
            entry.testId = test.id;
            entry.faultId = fault;
            entry.detects = true;
            entry.isolates = isolate.contains(fault);
            m_entries.append(entry);
        }
        for (const QString &fault : isolate) {
            if (detect.contains(fault)) continue;
            MatrixEntry entry;
            entry.testId = test.id;
            entry.faultId = fault;
            entry.detects = false;
            entry.isolates = true;
            m_entries.append(entry);
        }
        m_detectionMap.insert(test.id, detect);
        m_isolationMap.insert(test.id, isolate);
    }
}

CoverageStats DiagnosticMatrixBuilder::coverageStats() const
{
    CoverageStats stats;
    stats.totalTests = m_tests.size();
    stats.totalFaults = m_faultIds.size();

    for (const MatrixEntry &entry : m_entries) {
        if (entry.detects)
            stats.detectedFaults.insert(entry.faultId);
        if (entry.isolates)
            stats.isolatableFaults.insert(entry.faultId);
    }

    const double denominator = stats.totalFaults > 0 ? static_cast<double>(stats.totalFaults) : 1.0;
    for (auto it = m_detectionMap.constBegin(); it != m_detectionMap.constEnd(); ++it) {
        stats.detectionRateByTest.insert(it.key(), static_cast<double>(it.value().size()) / denominator);
    }
    return stats;
}

CoverageSummary DiagnosticMatrixBuilder::coverageSummary(const QStringList &testIds) const
{
    CoverageSummary summary;
    summary.totalFaults = m_faultIds.size();

    QSet<QString> detect;
    QSet<QString> isolate;
    const QSet<QString> allowed = QSet<QString>::fromList(testIds);
    for (const QString &testId : allowed) {
        detect.unite(m_detectionMap.value(testId));
        isolate.unite(m_isolationMap.value(testId));
    }
    summary.detectedFaults = detect.size();
    summary.isolatableFaults = isolate.size();
    if (!m_faultIds.isEmpty()) {
        const double total = static_cast<double>(m_faultIds.size());
        summary.detectionRate = detect.size() / total;
        summary.isolationRate = isolate.size() / total;
    }
    return summary;
}

QStringList DiagnosticMatrixBuilder::candidateTests(double minDetectionRate) const
{
    QStringList candidates;
    CoverageStats stats = coverageStats();
    for (auto it = stats.detectionRateByTest.constBegin(); it != stats.detectionRateByTest.constEnd(); ++it) {
        if (it.value() >= minDetectionRate)
            candidates.append(it.key());
    }
    candidates.removeDuplicates();
    return candidates;
}

QStringList DiagnosticMatrixBuilder::candidateTests(const QStringList &availableTests, double minDetectionRate) const
{
    QStringList candidates;
    if (m_faultIds.isEmpty()) return candidates;
    const double total = static_cast<double>(m_faultIds.size());
    const QSet<QString> allowed = QSet<QString>::fromList(availableTests);
    for (const QString &testId : allowed) {
        const QSet<QString> detect = m_detectionMap.value(testId);
        if (detect.isEmpty()) continue;
        const double rate = static_cast<double>(detect.size()) / total;
        if (rate >= minDetectionRate)
            candidates.append(testId);
    }
    candidates.removeDuplicates();
    return candidates;
}

std::shared_ptr<DecisionNode> DiagnosticMatrixBuilder::buildDecisionTree() const
{
    if (m_tests.isEmpty() || m_faultIds.isEmpty())
        return std::make_shared<DecisionNode>();
    return buildTreeRecursive(m_tests, m_faultIds, {});
}

std::shared_ptr<DecisionNode> DiagnosticMatrixBuilder::buildDecisionTree(const QStringList &testIds) const
{
    if (testIds.isEmpty())
        return buildDecisionTree();

    QVector<GeneratedTest> subset;
    subset.reserve(testIds.size());
    QSet<QString> faults;
    const QSet<QString> allowed = QSet<QString>::fromList(testIds);
    for (const GeneratedTest &test : m_tests) {
        if (!allowed.contains(test.id)) continue;
        subset.append(test);
        faults.unite(m_detectionMap.value(test.id));
        faults.unite(m_isolationMap.value(test.id));
    }

    if (subset.isEmpty())
        return buildDecisionTree();
    if (faults.isEmpty())
        faults = m_faultIds;

    return buildTreeRecursive(subset, faults, {});
}

std::shared_ptr<DecisionNode> DiagnosticMatrixBuilder::buildTreeRecursive(const QVector<GeneratedTest> &tests,
                                                                         const QSet<QString> &faults,
                                                                         QSet<QString> usedTests) const
{
    auto node = std::make_shared<DecisionNode>();
    if (faults.isEmpty()) {
        node->isLeaf = true;
        return node;
    }
    if (faults.size() == 1 || usedTests.size() == tests.size()) {
        node->isLeaf = true;
        node->faultId = *faults.begin();
        return node;
    }

    const GeneratedTest *bestTest = nullptr;
    int bestScore = -1;
    for (const GeneratedTest &test : tests) {
        if (usedTests.contains(test.id)) continue;
        QSet<QString> detect = QSet<QString>::fromList(test.detectableFaults);
        detect &= faults;
        QSet<QString> isolate = QSet<QString>::fromList(test.isolatableFaults);
        isolate &= faults;
        int score = isolate.size() * 2 + detect.size();
        if (score > bestScore) {
            bestScore = score;
            bestTest = &test;
        }
    }

    if (!bestTest || bestScore <= 0) {
        node->isLeaf = true;
        node->faultId = *faults.begin();
        return node;
    }

    node->testId = bestTest->id;
    QSet<QString> detect = QSet<QString>::fromList(bestTest->detectableFaults);
    detect &= faults;
    if (detect.isEmpty()) {
        node->isLeaf = true;
        node->faultId = *faults.begin();
        return node;
    }

    QSet<QString> remaining = faults - detect;
    usedTests.insert(bestTest->id);
    node->children.append(buildTreeRecursive(tests, detect, usedTests));
    node->children.append(buildTreeRecursive(tests, remaining, usedTests));
    return node;
}
