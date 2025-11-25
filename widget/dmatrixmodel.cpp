#include "dmatrixmodel.h"

#include <QBrush>
#include <QColor>
#include <cmath>

using namespace testability;

namespace {
QString faultHeader(int index)
{
    return QStringLiteral("f%1").arg(index + 1);
}

QString testHeader(int index)
{
    return QStringLiteral("t%1").arg(index + 1);
}

QColor detectedColorForTestKind(TestKind kind)
{
    switch (kind) {
    case TestKind::Function:
        return QColor(QStringLiteral("#4CAF50"));
    case TestKind::Mode:
        return QColor(QStringLiteral("#81D4FA"));
    case TestKind::Signal:
    default:
        return QColor(QStringLiteral("#FFF176"));
    }
}

QString testKindDisplay(TestKind kind)
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

QString faultKindDisplay(FaultKind kind)
{
    switch (kind) {
    case FaultKind::Component:
        return QObject::tr("器件故障模式");
    case FaultKind::Function:
    default:
        return QObject::tr("功能故障");
    }
}

QString formatOptionalNumber(double value)
{
    if (std::isfinite(value)) {
        return QString::number(value, 'g', 6);
    }
    return QObject::tr("未提供");
}
}

DMatrixModel::DMatrixModel(QObject *parent)
    : QAbstractTableModel(parent)
{
}

void DMatrixModel::setMatrix(const DMatrixBuildResult &matrix)
{
    beginResetModel();
    matrix_ = matrix;
    faultEnabled_.resize(matrix_.faults.size());
    for (int i = 0; i < matrix_.faults.size(); ++i) {
        faultEnabled_[i] = matrix_.faults.at(i).enabled;
    }
    testEnabled_.resize(matrix_.tests.size());
    for (int i = 0; i < matrix_.tests.size(); ++i) {
        testEnabled_[i] = matrix_.tests.at(i).enabled;
    }
    endResetModel();
}

int DMatrixModel::rowCount(const QModelIndex &parent) const
{
    if (parent.isValid()) {
        return 0;
    }
    return matrix_.faults.size();
}

int DMatrixModel::columnCount(const QModelIndex &parent) const
{
    if (parent.isValid()) {
        return 0;
    }
    return matrix_.tests.size();
}

QVariant DMatrixModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid()) {
        return QVariant();
    }
    if (index.row() >= matrix_.cells.size() || index.column() >= matrix_.tests.size()) {
        return QVariant();
    }

    const DetectabilityResult &cell = matrix_.cells.at(index.row()).at(index.column());
    const bool faultEnabled = index.row() < faultEnabled_.size() ? faultEnabled_.at(index.row()) : true;
    const bool testEnabled = index.column() < testEnabled_.size() ? testEnabled_.at(index.column()) : true;
    const auto &test = matrix_.tests.at(index.column());
    const auto &fault = matrix_.faults.at(index.row());

    switch (role) {
    case Qt::DisplayRole:
        return QVariant();
    case Qt::TextAlignmentRole:
        return Qt::AlignCenter;
    case Qt::BackgroundRole: {
        QColor color;
        if (cell.detected) {
            color = detectedColorForTestKind(test.kind);
        } else {
            color = QColor(QStringLiteral("#E0E0E0"));
        }
        if (!faultEnabled || !testEnabled) {
            color = color.lighter(140);
        }
        return QBrush(color);
    }
    case Qt::ToolTipRole: {
        QStringList lines;
        lines << tr("测试: %1 (%2)").arg(test.name, test.id);
        lines << tr("测试类型: %1").arg(testKindDisplay(test.kind));
        lines << tr("测试启用: %1").arg(testEnabled ? tr("是") : tr("否"));
        if (!test.description.trimmed().isEmpty()) {
            lines << tr("测试描述: %1").arg(test.description.trimmed());
        }
        if (std::isfinite(test.complexity)) {
            lines << tr("复杂性: %1").arg(formatOptionalNumber(test.complexity));
        }
        if (std::isfinite(test.cost)) {
            lines << tr("测试费用: %1").arg(formatOptionalNumber(test.cost));
        }
        if (std::isfinite(test.duration)) {
            lines << tr("测试时间: %1").arg(formatOptionalNumber(test.duration));
        }
        if (std::isfinite(test.successRate)) {
            const double rate = test.successRate <= 1.0 ? test.successRate * 100.0 : test.successRate;
            lines << tr("检测成功率: %1%").arg(rate, 0, 'f', 2);
        }
        if (!test.note.trimmed().isEmpty()) {
            lines << tr("备注: %1").arg(test.note.trimmed());
        }
        lines << tr("故障: %1 (%2)").arg(fault.name, fault.id);
        lines << tr("故障类型: %1").arg(faultKindDisplay(fault.kind));
        lines << tr("故障启用: %1").arg(faultEnabled ? tr("是") : tr("否"));
        lines << tr("判定: %1").arg(cell.detected ? tr("检测") : tr("未检测"));
        if (!cell.method.trimmed().isEmpty()) {
            lines << tr("策略: %1").arg(cell.method);
        }
        if (!cell.detail.trimmed().isEmpty()) {
            lines << tr("说明: %1").arg(cell.detail);
        }
        if (!std::isnan(cell.metric)) {
            lines << tr("差异比例: %1").arg(cell.metric, 0, 'f', 3);
        }
        return lines.join(QLatin1Char('\n'));
    }
    default:
        return QVariant();
    }
}

QVariant DMatrixModel::headerData(int section, Qt::Orientation orientation, int role) const
{
    if (orientation == Qt::Horizontal) {
        if (section >= matrix_.tests.size()) {
            return QVariant();
        }
        const auto &test = matrix_.tests.at(section);
        const bool enabled = section < testEnabled_.size() ? testEnabled_.at(section) : true;
        if (role == Qt::DisplayRole) {
            if (showTestNames_ && !test.name.isEmpty()) {
                return test.name;
            }
            return testHeader(section);
        }
        if (role == Qt::ToolTipRole) {
            QString tooltip = tr("测试 %1").arg(test.id);
            if (!test.name.isEmpty()) {
                tooltip.append(QLatin1Char('\n')).append(test.name);
            }
            tooltip.append(QLatin1Char('\n')).append(tr("类型: %1").arg(testKindDisplay(test.kind)));
            tooltip.append(QLatin1Char('\n')).append(tr("启用: %1").arg(enabled ? tr("是") : tr("否")));
            if (!test.description.trimmed().isEmpty()) {
                tooltip.append(QLatin1Char('\n')).append(tr("描述: %1").arg(test.description.trimmed()));
            }
            if (std::isfinite(test.complexity)) {
                tooltip.append(QLatin1Char('\n')).append(tr("复杂性: %1").arg(formatOptionalNumber(test.complexity)));
            }
            if (std::isfinite(test.cost)) {
                tooltip.append(QLatin1Char('\n')).append(tr("费用: %1").arg(formatOptionalNumber(test.cost)));
            }
            if (std::isfinite(test.duration)) {
                tooltip.append(QLatin1Char('\n')).append(tr("时间: %1").arg(formatOptionalNumber(test.duration)));
            }
            if (std::isfinite(test.successRate)) {
                const double rate = test.successRate <= 1.0 ? test.successRate * 100.0 : test.successRate;
                tooltip.append(QLatin1Char('\n')).append(tr("成功率: %1%").arg(rate, 0, 'f', 2));
            }
            if (!test.note.trimmed().isEmpty()) {
                tooltip.append(QLatin1Char('\n')).append(tr("备注: %1").arg(test.note.trimmed()));
            }
            return tooltip;
        }
        if (role == Qt::ForegroundRole && !enabled) {
            return QBrush(QColor(QStringLiteral("#757575")));
        }
    } else {
        if (section >= matrix_.faults.size()) {
            return QVariant();
        }
        const auto &fault = matrix_.faults.at(section);
        const bool enabled = section < faultEnabled_.size() ? faultEnabled_.at(section) : true;
        if (role == Qt::DisplayRole) {
            if (showFaultNames_ && !fault.name.isEmpty()) {
                return fault.name;
            }
            return faultHeader(section);
        }
        if (role == Qt::ToolTipRole) {
            QString tooltip = tr("故障 %1").arg(fault.id);
            if (!fault.name.isEmpty()) {
                tooltip.append(QLatin1Char('\n')).append(fault.name);
            }
            tooltip.append(QLatin1Char('\n')).append(tr("类型: %1").arg(faultKindDisplay(fault.kind)));
            tooltip.append(QLatin1Char('\n')).append(tr("启用: %1").arg(enabled ? tr("是") : tr("否")));
            return tooltip;
        }
        if (role == Qt::ForegroundRole && !enabled) {
            return QBrush(QColor(QStringLiteral("#757575")));
        }
    }
    return QVariant();
}

Qt::ItemFlags DMatrixModel::flags(const QModelIndex &index) const
{
    if (!index.isValid()) {
        return Qt::NoItemFlags;
    }
    return Qt::ItemIsEnabled | Qt::ItemIsSelectable;
}

void DMatrixModel::setFaultEnabledStates(const QVector<bool> &states)
{
    const int size = matrix_.faults.size();
    faultEnabled_.resize(size);
    for (int i = 0; i < size; ++i) {
        const bool enabled = i < states.size() ? states.at(i) : true;
        faultEnabled_[i] = enabled;
        if (i < matrix_.faults.size()) {
            matrix_.faults[i].enabled = enabled;
        }
        if (columnCount() > 0) {
            const QModelIndex top = index(i, 0);
            const QModelIndex bottom = index(i, columnCount() - 1);
            emit dataChanged(top, bottom, {Qt::BackgroundRole, Qt::ToolTipRole});
        }
    }
    if (!matrix_.faults.isEmpty()) {
        emit headerDataChanged(Qt::Vertical, 0, matrix_.faults.size() - 1);
    }
}

void DMatrixModel::setTestEnabledStates(const QVector<bool> &states)
{
    const int size = matrix_.tests.size();
    testEnabled_.resize(size);
    for (int i = 0; i < size; ++i) {
        const bool enabled = i < states.size() ? states.at(i) : true;
        testEnabled_[i] = enabled;
        if (i < matrix_.tests.size()) {
            matrix_.tests[i].enabled = enabled;
        }
        if (rowCount() > 0) {
            const QModelIndex top = index(0, i);
            const QModelIndex bottom = index(rowCount() - 1, i);
            emit dataChanged(top, bottom, {Qt::BackgroundRole, Qt::ToolTipRole});
        }
    }
    if (!matrix_.tests.isEmpty()) {
        emit headerDataChanged(Qt::Horizontal, 0, matrix_.tests.size() - 1);
    }
}

void DMatrixModel::setShowFaultNames(bool show)
{
    if (showFaultNames_ == show) {
        return;
    }
    showFaultNames_ = show;
    if (!matrix_.faults.isEmpty()) {
        emit headerDataChanged(Qt::Vertical, 0, matrix_.faults.size() - 1);
    }
}

void DMatrixModel::setShowTestNames(bool show)
{
    if (showTestNames_ == show) {
        return;
    }
    showTestNames_ = show;
    if (!matrix_.tests.isEmpty()) {
        emit headerDataChanged(Qt::Horizontal, 0, matrix_.tests.size() - 1);
    }
}

const FaultDefinition *DMatrixModel::faultAt(int row) const
{
    if (row < 0 || row >= matrix_.faults.size()) {
        return nullptr;
    }
    return &matrix_.faults.at(row);
}

const TestDefinition *DMatrixModel::testAt(int column) const
{
    if (column < 0 || column >= matrix_.tests.size()) {
        return nullptr;
    }
    return &matrix_.tests.at(column);
}
