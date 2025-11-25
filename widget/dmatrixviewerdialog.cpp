#include "dmatrixviewerdialog.h"
#include "ui_dmatrixviewerdialog.h"

#include <QCheckBox>
#include <QDebug>
#include <QDir>
#include <QFile>
#include <QFileDialog>
#include <QFileInfo>
#include <QHeaderView>
#include <QHash>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonParseError>
#include <QMessageBox>
#include <QPainter>
#include <QPlainTextEdit>
#include <QSaveFile>
#include <QStyleOptionHeader>
#include <QTableView>
#include <QTextStream>
#include <QVBoxLayout>
#include <QDialogButtonBox>

#include <cmath>

#include "widget/dmatrixmodel.h"
#include "widget/dmatrixselectiondialog.h"

using namespace testability;

namespace {
QString detectModeToString(DetectMode mode)
{
    switch (mode) {
    case DetectMode::Guaranteed:
        return QObject::tr("保证检测");
    case DetectMode::Exists:
        return QObject::tr("存在检测");
    }
    return QString();
}

QString testKindText(TestKind kind)
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

QString faultKindText(FaultKind kind)
{
    switch (kind) {
    case FaultKind::Component:
        return QObject::tr("器件故障模式");
    case FaultKind::Function:
    default:
        return QObject::tr("功能故障");
    }
}

bool parseStateJson(const QString &json, QVector<bool> *faultStates, QVector<bool> *testStates)
{
    if (json.trimmed().isEmpty())
        return false;
    QJsonParseError error;
    const QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8(), &error);
    if (doc.isNull() || !doc.isObject()) {
        return false;
    }
    const QJsonObject obj = doc.object();
    const QJsonArray faultArray = obj.value(QStringLiteral("faultEnabled")).toArray();
    if (faultStates) {
        QVector<bool> values;
        values.reserve(faultArray.size());
        for (const auto &v : faultArray) values.append(v.toBool(true));
        *faultStates = values;
    }
    const QJsonArray testArray = obj.value(QStringLiteral("testEnabled")).toArray();
    if (testStates) {
        QVector<bool> values;
        values.reserve(testArray.size());
        for (const auto &v : testArray) values.append(v.toBool(true));
        *testStates = values;
    }
    return true;
}

class VerticalHeaderView : public QHeaderView
{
public:
    explicit VerticalHeaderView(QWidget *parent = nullptr)
        : QHeaderView(Qt::Horizontal, parent)
    {
        setDefaultAlignment(Qt::AlignHCenter | Qt::AlignBottom);
        setSectionsClickable(true);
    }

protected:
    QSize sectionSizeFromContents(int logicalIndex) const override
    {
        QSize size = QHeaderView::sectionSizeFromContents(logicalIndex);
        return QSize(size.height(), size.width());
    }

    void paintSection(QPainter *painter, const QRect &rect, int logicalIndex) const override
    {
        if (!painter) {
            return;
        }
        painter->save();
        painter->translate(rect.left(), rect.bottom());
        painter->rotate(-90);

        QRect rotatedRect(0, 0, rect.height(), rect.width());
        QStyleOptionHeader opt;
        initStyleOption(&opt);
        opt.rect = rotatedRect;
        opt.section = logicalIndex;
        opt.orientation = Qt::Vertical;
        opt.text = model() ? model()->headerData(logicalIndex, Qt::Horizontal, Qt::DisplayRole).toString() : QString();
        style()->drawControl(QStyle::CE_Header, &opt, painter, this);
        painter->restore();
    }
};
} // namespace

DMatrixViewerDialog::DMatrixViewerDialog(QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::DMatrixViewerDialog)
    , model(new DMatrixModel(this))
{
    setWindowFlags(windowFlags() | Qt::WindowMaximizeButtonHint | Qt::WindowMinimizeButtonHint);
    resize(1920, 1000);

    ui->setupUi(this);
    ui->tableView->setModel(model);
    ui->tableView->setAlternatingRowColors(false);
    ui->tableView->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableView->setSelectionBehavior(QAbstractItemView::SelectItems);
    ui->tableView->setEditTriggers(QAbstractItemView::NoEditTriggers);
    ui->tableView->horizontalHeader()->setDefaultSectionSize(32);
    ui->tableView->verticalHeader()->setDefaultSectionSize(22);
    ui->tableView->horizontalHeader()->setStretchLastSection(false);
    ui->tableView->verticalHeader()->setStretchLastSection(false);
    auto *verticalHeader = new VerticalHeaderView(ui->tableView);
    ui->tableView->setHorizontalHeader(verticalHeader);
    verticalHeader->setSectionResizeMode(QHeaderView::ResizeToContents);
    ui->btnSave->setEnabled(false);

    connect(ui->btnExport, &QPushButton::clicked, this, &DMatrixViewerDialog::onExportClicked);
    connect(ui->btnBuild, &QPushButton::clicked, this, &DMatrixViewerDialog::onBuildClicked);
    connect(ui->btnSave, &QPushButton::clicked, this, &DMatrixViewerDialog::onSaveClicked);
    connect(ui->btnSaveAs, &QPushButton::clicked, this, &DMatrixViewerDialog::onSaveAsClicked);
    connect(ui->btnSelectTests, &QPushButton::clicked, this, &DMatrixViewerDialog::onSelectTests);
    connect(ui->btnSelectFaults, &QPushButton::clicked, this, &DMatrixViewerDialog::onSelectFaults);
    connect(ui->checkShowFaultNames, &QCheckBox::stateChanged, this, &DMatrixViewerDialog::onShowFaultNamesChanged);
    connect(ui->checkShowTestNames, &QCheckBox::stateChanged, this, &DMatrixViewerDialog::onShowTestNamesChanged);
    connect(ui->tableView, &QTableView::doubleClicked, this, &DMatrixViewerDialog::onCellDoubleClicked);
    connect(ui->btnClose, &QPushButton::clicked, this, &QDialog::reject);
}

DMatrixViewerDialog::~DMatrixViewerDialog()
{
    delete ui;
}

void DMatrixViewerDialog::setMatrix(const DMatrixBuildResult &result,
                                    const DMatrixBuildOptions &options,
                                    const QString &csv,
                                    const QString &meta)
{
    currentOptions = options;
    csvPath = csv;
    metadataPath = meta;
    model->setMatrix(result);
    model->setShowFaultNames(ui->checkShowFaultNames->isChecked());
    model->setShowTestNames(ui->checkShowTestNames->isChecked());
    ui->btnSave->setEnabled(!metadataPath.isEmpty());
    applyVisibility();
    updateSummary();
}

void DMatrixViewerDialog::applyState(const QString &stateJson)
{
    QVector<bool> faultStates;
    QVector<bool> testStates;
    if (!parseStateJson(stateJson, &faultStates, &testStates)) {
        return;
    }
    setEnabledStates(faultStates, testStates);
}

void DMatrixViewerDialog::setEnabledStates(const QVector<bool> &faultStates,
                                           const QVector<bool> &testStates)
{
    if (!model) return;
    if (!faultStates.isEmpty()) {
        model->setFaultEnabledStates(faultStates);
    }
    if (!testStates.isEmpty()) {
        model->setTestEnabledStates(testStates);
    }
    applyVisibility();
    updateSummary();
}

void DMatrixViewerDialog::onExportClicked()
{
    QString suggested = csvPath;
    if (suggested.isEmpty()) {
        suggested = QDir::current().filePath(QString("dmatrix.csv"));
    }
    QString fileName = QFileDialog::getSaveFileName(this, tr("导出CSV"), suggested, tr("CSV 文件 (*.csv)"));
    if (fileName.isEmpty()) {
        return;
    }
    if (!exportCsv(fileName)) {
        QMessageBox::warning(this, tr("导出失败"), tr("无法写入CSV文件"));
    } else {
        QMessageBox::information(this, tr("导出完成"), tr("已导出到 %1").arg(QDir::toNativeSeparators(fileName)));
    }
}

bool DMatrixViewerDialog::exportCsv(const QString &filePath) const
{
    QFile file(filePath);
    if (!file.open(QIODevice::WriteOnly | QIODevice::Text)) {
        return false;
    }

    auto quote = [](const QString &text) {
        QString escaped = text;
        escaped.replace('"', "\"\"");
        return QString("\"%1\"").arg(escaped);
    };

    QTextStream stream(&file);
    stream << quote(QString("测试/故障"));
    for (const auto &fault : model->matrix().faults) {
        stream << ',' << quote(fault.id);
    }
    stream << '\n';

    for (int ti = 0; ti < model->matrix().tests.size(); ++ti) {
        const auto &test = model->matrix().tests.at(ti);
        stream << quote(test.id);
        for (int fi = 0; fi < model->matrix().faults.size(); ++fi) {
            const auto &cell = model->matrix().cells.at(fi).at(ti);
            stream << ',' << (cell.detected ? '1' : '0');
        }
        stream << '\n';
    }

    return true;
}

void DMatrixViewerDialog::updateSummary()
{
    const auto &matrix = model->matrix();
    const QVector<bool> &faultStates = model->faultEnabledStates();
    const QVector<bool> &testStates = model->testEnabledStates();

    int faultEnabledCount = 0;
    int functionFaultCount = 0;
    int functionFaultEnabledCount = 0;
    int componentFaultCount = 0;
    int componentFaultEnabledCount = 0;
    for (int i = 0; i < matrix.faults.size(); ++i) {
        const auto &fault = matrix.faults.at(i);
        const bool enabled = i < faultStates.size() ? faultStates.at(i) : true;
        if (enabled) {
            ++faultEnabledCount;
        }
        switch (fault.kind) {
        case FaultKind::Function:
            ++functionFaultCount;
            if (enabled) {
                ++functionFaultEnabledCount;
            }
            break;
        case FaultKind::Component:
            ++componentFaultCount;
            if (enabled) {
                ++componentFaultEnabledCount;
            }
            break;
        }
    }

    int testEnabledCount = 0;
    for (bool state : testStates) {
        if (state) {
            ++testEnabledCount;
        }
    }

    int functionCount = 0;
    int functionEnabledCount = 0;
    int modeCount = 0;
    int modeEnabledCount = 0;
    int signalCount = 0;
    int signalEnabledCount = 0;
    for (int i = 0; i < matrix.tests.size(); ++i) {
        const auto &test = matrix.tests.at(i);
        const bool enabled = i < testStates.size() ? testStates.at(i) : true;
        switch (test.kind) {
        case TestKind::Function:
            ++functionCount;
            if (enabled) {
                ++functionEnabledCount;
            }
            break;
        case TestKind::Mode:
            ++modeCount;
            if (enabled) {
                ++modeEnabledCount;
            }
            break;
        case TestKind::Signal:
        default:
            ++signalCount;
            if (enabled) {
                ++signalEnabledCount;
            }
            break;
        }
    }

    QStringList parts;
    parts << tr("故障: %1 (功能 %2 (启用 %3), 器件故障模式 %4 (启用 %5))")
               .arg(matrix.faults.size())
               .arg(functionFaultCount)
               .arg(functionFaultEnabledCount)
               .arg(componentFaultCount)
               .arg(componentFaultEnabledCount);
    parts << tr("测试: %1 (功能 %2 (启用 %3), 故障模式 %4 (启用 %5), 信号 %6 (启用 %7))")
               .arg(matrix.tests.size())
               .arg(functionCount)
               .arg(functionEnabledCount)
               .arg(modeCount)
               .arg(modeEnabledCount)
               .arg(signalCount)
               .arg(signalEnabledCount);
    parts << tr("启用测试: %1").arg(testEnabledCount);
    parts << tr("模式: %1").arg(detectModeToString(currentOptions.mode));
    if (!metadataPath.isEmpty()) {
        QFileInfo fileInfo(metadataPath);
        QString displayPath = fileInfo.filePath();
        if (fileInfo.isAbsolute()) {
            displayPath = QDir::current().relativeFilePath(metadataPath);
        }
        parts << tr("元数据: %1").arg(displayPath);
    }
    ui->labelSummary->setText(parts.join(QString("  |  ")));
}

void DMatrixViewerDialog::onShowFaultNamesChanged(int state)
{
    model->setShowFaultNames(state == Qt::Checked);
}

void DMatrixViewerDialog::onShowTestNamesChanged(int state)
{
    model->setShowTestNames(state == Qt::Checked);
}

void DMatrixViewerDialog::onSelectTests()
{
    openSelectionDialog(true);
}

void DMatrixViewerDialog::onSelectFaults()
{
    openSelectionDialog(false);
}

void DMatrixViewerDialog::onSaveClicked()
{
    if (metadataPath.isEmpty()) {
        QMessageBox::warning(this, tr("保存失败"), tr("当前没有可写入的元数据文件。"));
        return;
    }
    if (!saveMetadataToPath(metadataPath)) {
        QMessageBox::warning(this, tr("保存失败"), tr("无法写入元数据文件。"));
        return;
    }
    QMessageBox::information(this, tr("保存完成"), tr("已更新 %1").arg(QDir::toNativeSeparators(metadataPath)));
    emit saveRequested(metadataPath, csvPath, model->faultEnabledStates(), model->testEnabledStates());
}

void DMatrixViewerDialog::onSaveAsClicked()
{
    QString suggested = metadataPath;
    if (suggested.isEmpty()) {
        suggested = QDir::current().filePath(QString("dmatrix.json"));
    }
    QString target = QFileDialog::getSaveFileName(this, tr("另存为"), suggested, tr("D矩阵元数据 (*.json)"));
    if (target.isEmpty()) {
        return;
    }
    if (!target.endsWith(QStringLiteral(".json"), Qt::CaseInsensitive)) {
        target.append(QStringLiteral(".json"));
    }
    if (!saveMetadataToPath(target)) {
        QMessageBox::warning(this, tr("保存失败"), tr("无法写入元数据文件。"));
        return;
    }

    bool csvCopied = true;
    QString newCsvPath = csvPath;
    if (!csvPath.isEmpty()) {
        QFileInfo info(target);
        const QString candidate = info.absolutePath() + QLatin1Char('/') + info.completeBaseName() + QStringLiteral(".csv");
        if (QFileInfo::exists(candidate) && !QFile::remove(candidate)) {
            csvCopied = false;
        } else if (!QFile::copy(csvPath, candidate)) {
            csvCopied = false;
        } else {
            newCsvPath = candidate;
        }
    }

    metadataPath = target;
    if (csvCopied) {
        csvPath = newCsvPath;
    }
    ui->btnSave->setEnabled(true);
    updateSummary();

    if (!csvPath.isEmpty() && !csvCopied) {
        QMessageBox::warning(this,
                             tr("保存完成但存在问题"),
                             tr("元数据已保存，但无法复制CSV文件，请手动处理。"));
    } else {
        QMessageBox::information(this, tr("保存完成"), tr("已保存到 %1").arg(QDir::toNativeSeparators(metadataPath)));
    }
    emit saveRequested(metadataPath, csvPath, model->faultEnabledStates(), model->testEnabledStates());
}

void DMatrixViewerDialog::onCellDoubleClicked(const QModelIndex &index)
{
    showCellDetails(index);
}

void DMatrixViewerDialog::onBuildClicked()
{
    emit buildRequested();
}

void DMatrixViewerDialog::openSelectionDialog(bool forTests)
{
    qDebug().noquote() << "[DMatrixViewer] openSelectionDialog — forTests:" << forTests;
    DMatrixSelectionDialog dialog(forTests ? DMatrixSelectionDialog::Target::Tests
                                           : DMatrixSelectionDialog::Target::Faults,
                                  this);
    if (forTests) {
        qDebug().noquote() << "[DMatrixViewer] setting tests — count:" << model->matrix().tests.size();
        dialog.setTests(model->matrix().tests, model->testEnabledStates());
    } else {
        qDebug().noquote() << "[DMatrixViewer] setting faults — count:" << model->matrix().faults.size();
        dialog.setFaults(model->matrix().faults, model->faultEnabledStates());
    }

    if (dialog.exec() == QDialog::Accepted) {
        if (forTests) {
            qDebug().noquote() << "[DMatrixViewer] dialog accepted — updating test enabled states";
            model->updateTests(dialog.testDefinitions());
            model->setTestEnabledStates(dialog.enabledStates());
        } else {
            qDebug().noquote() << "[DMatrixViewer] dialog accepted — updating fault enabled states";
            model->setFaultEnabledStates(dialog.enabledStates());
        }
        applyVisibility();
        updateSummary();
    } else {
        qDebug().noquote() << "[DMatrixViewer] dialog dismissed without changes";
    }
}

void DMatrixViewerDialog::applyVisibility()
{
    if (!ui || !ui->tableView) {
        return;
    }
    qDebug().noquote() << "[DMatrixViewer] applyVisibility rows:" << model->rowCount()
                       << "cols:" << model->columnCount();
    const QVector<bool> &faultStates = model->faultEnabledStates();
    for (int row = 0; row < model->rowCount(); ++row) {
        const bool enabled = (row < faultStates.size()) ? faultStates.at(row) : true;
        ui->tableView->setRowHidden(row, !enabled);
    }

    const QVector<bool> &testStates = model->testEnabledStates();
    for (int column = 0; column < model->columnCount(); ++column) {
        const bool enabled = (column < testStates.size()) ? testStates.at(column) : true;
        ui->tableView->setColumnHidden(column, !enabled);
    }
}

bool DMatrixViewerDialog::saveMetadataToPath(const QString &path)
{
    if (path.isEmpty()) {
        return false;
    }

    const QString sourcePath = metadataPath.isEmpty() ? path : metadataPath;
    QFile sourceFile(sourcePath);
    if (!sourceFile.open(QIODevice::ReadOnly | QIODevice::Text)) {
        return false;
    }

    QJsonParseError parseError;
    const QJsonDocument doc = QJsonDocument::fromJson(sourceFile.readAll(), &parseError);
    if (doc.isNull() || !doc.isObject()) {
        return false;
    }

    QJsonObject root = doc.object();
    const auto &matrix = model->matrix();

    QHash<QString, bool> faultEnabledMap;
    const QVector<bool> &faultStates = model->faultEnabledStates();
    for (int i = 0; i < matrix.faults.size(); ++i) {
        const QString id = matrix.faults.at(i).id;
        faultEnabledMap.insert(id, i < faultStates.size() ? faultStates.at(i) : true);
    }

    QJsonArray faultsArray = root.value(QStringLiteral("faults")).toArray();
    for (int i = 0; i < faultsArray.size(); ++i) {
        QJsonObject obj = faultsArray.at(i).toObject();
        const QString id = obj.value(QStringLiteral("id")).toString();
        if (faultEnabledMap.contains(id)) {
            obj.insert(QStringLiteral("enabled"), faultEnabledMap.value(id));
            faultsArray.replace(i, obj);
        }
    }
    root.insert(QStringLiteral("faults"), faultsArray);

    auto setOptionalNumber = [](QJsonObject &obj, const QString &key, double value) {
        if (std::isfinite(value)) {
            obj.insert(key, value);
        } else {
            obj.remove(key);
        }
    };

    QHash<QString, bool> testEnabledMap;
    const QVector<bool> &testStates = model->testEnabledStates();
    QHash<QString, testability::TestDefinition> testDefMap;
    for (int i = 0; i < matrix.tests.size(); ++i) {
        const QString id = matrix.tests.at(i).id;
        testEnabledMap.insert(id, i < testStates.size() ? testStates.at(i) : true);
        testDefMap.insert(id, matrix.tests.at(i));
    }

    QJsonArray testsArray = root.value(QStringLiteral("tests")).toArray();
    for (int i = 0; i < testsArray.size(); ++i) {
        QJsonObject obj = testsArray.at(i).toObject();
        const QString id = obj.value(QStringLiteral("id")).toString();
        if (testEnabledMap.contains(id)) {
            obj.insert(QStringLiteral("enabled"), testEnabledMap.value(id));
        }
        const auto defIt = testDefMap.constFind(id);
        if (defIt != testDefMap.constEnd()) {
            const testability::TestDefinition &def = defIt.value();
            obj.insert(QStringLiteral("description"), def.description);
            obj.insert(QStringLiteral("note"), def.note);
            obj.insert(QStringLiteral("remark"), def.note);
            setOptionalNumber(obj, QStringLiteral("complexity"), def.complexity);
            setOptionalNumber(obj, QStringLiteral("cost"), def.cost);
            setOptionalNumber(obj, QStringLiteral("duration"), def.duration);
            setOptionalNumber(obj, QStringLiteral("successRate"), def.successRate);
        }
        testsArray.replace(i, obj);
    }
    root.insert(QStringLiteral("tests"), testsArray);

    sourceFile.close();

    QJsonDocument outDoc(root);
    QSaveFile saveFile(path);
    if (!saveFile.open(QIODevice::WriteOnly | QIODevice::Text)) {
        return false;
    }
    const QByteArray payload = outDoc.toJson(QJsonDocument::Indented);
    if (saveFile.write(payload) != payload.size()) {
        return false;
    }
    if (!saveFile.commit()) {
        return false;
    }
    return true;
}

void DMatrixViewerDialog::showCellDetails(const QModelIndex &index)
{
    if (!index.isValid()) {
        return;
    }
    const auto *fault = model->faultAt(index.row());
    const auto *test = model->testAt(index.column());
    if (!fault || !test) {
        return;
    }

    const DetectabilityResult &cell = model->matrix().cells.at(index.row()).at(index.column());
    const QVector<bool> &faultStates = model->faultEnabledStates();
    const QVector<bool> &testStates = model->testEnabledStates();

    auto yesNo = [this](bool value) { return value ? tr("是") : tr("否"); };

    QStringList lines;
    lines << tr("测试编号: %1").arg(test->id);
    if (!test->name.trimmed().isEmpty()) {
        lines << tr("测试名称: %1").arg(test->name);
    }
    lines << tr("测试类型: %1").arg(testKindText(test->kind));
    lines << tr("测试启用: %1").arg(index.column() < testStates.size() && testStates.at(index.column()) ? tr("是") : tr("否"));
    auto formatOptional = [this](double value, int precision = 2) {
        if (std::isfinite(value)) {
            return QString::number(value, 'f', precision);
        }
        return tr("未提供");
    };
    if (!test->description.trimmed().isEmpty()) {
        lines << tr("测试描述: %1").arg(test->description.trimmed());
    }
    if (std::isfinite(test->complexity)) {
        lines << tr("测试复杂性: %1").arg(formatOptional(test->complexity));
    }
    if (std::isfinite(test->cost)) {
        lines << tr("测试费用: %1").arg(formatOptional(test->cost));
    }
    if (std::isfinite(test->duration)) {
        lines << tr("测试时间: %1").arg(formatOptional(test->duration));
    }
    if (std::isfinite(test->successRate)) {
        const double rate = test->successRate <= 1.0 ? test->successRate * 100.0 : test->successRate;
        lines << tr("检测成功率: %1%").arg(rate, 0, 'f', 2);
    }
    if (!test->relatedFunction.trimmed().isEmpty()) {
        lines << tr("关联功能: %1").arg(test->relatedFunction);
    }
    if (!test->componentName.trimmed().isEmpty()) {
        lines << tr("关联器件: %1").arg(test->componentName);
    }
    if (!test->failureModeName.trimmed().isEmpty()) {
        lines << tr("故障模式: %1").arg(test->failureModeName);
    }
    if (!test->signalVariable.trimmed().isEmpty()) {
        lines << tr("信号变量: %1").arg(test->signalVariable);
    }
    if (!test->note.trimmed().isEmpty()) {
        lines << tr("备注: %1").arg(test->note.trimmed());
    }

    lines << QString();
    lines << tr("故障编号: %1").arg(fault->id);
    if (!fault->name.trimmed().isEmpty()) {
        lines << tr("故障名称: %1").arg(fault->name);
    }
    lines << tr("故障类型: %1").arg(faultKindText(fault->kind));
    lines << tr("故障启用: %1").arg(index.row() < faultStates.size() && faultStates.at(index.row()) ? tr("是") : tr("否"));
    if (!fault->relatedFunction.trimmed().isEmpty()) {
        lines << tr("相关功能: %1").arg(fault->relatedFunction);
    }
    if (!fault->componentName.trimmed().isEmpty()) {
        lines << tr("器件: %1").arg(fault->componentName);
    }
    if (!fault->failureModeName.trimmed().isEmpty()) {
        lines << tr("故障模式: %1").arg(fault->failureModeName);
    }
    if (!fault->relatedComponents.isEmpty()) {
        lines << tr("相关器件: %1").arg(fault->relatedComponents.join(QStringLiteral(", ")));
    }
    if (!fault->linkElements.isEmpty()) {
        lines << tr("链路元素: %1").arg(fault->linkElements.join(QStringLiteral(", ")));
    }

    lines << QString();
    lines << tr("判定结果: %1").arg(cell.detected ? tr("检测") : tr("未检测"));
    lines << tr("保证检测: %1").arg(yesNo(cell.guaranteed));
    lines << tr("正常模型+测试满足: %1").arg(yesNo(cell.normalPassSat));
    lines << tr("故障模型+测试满足: %1").arg(yesNo(cell.faultSat));
    lines << tr("正常模型+否定满足: %1").arg(yesNo(cell.normalSat));
    lines << tr("故障模型+否定满足: %1").arg(yesNo(cell.faultFailSat));
    if (!cell.method.trimmed().isEmpty()) {
        lines << tr("策略: %1").arg(cell.method);
    }
    if (!cell.detail.trimmed().isEmpty()) {
        lines << tr("说明: %1").arg(cell.detail);
    }
    if (!std::isnan(cell.metric)) {
        lines << tr("差异比例: %1").arg(cell.metric, 0, 'f', 3);
    }

    QDialog dialog(this);
    dialog.setWindowTitle(tr("单元格详情"));
    dialog.resize(520, 420);
    auto *layout = new QVBoxLayout(&dialog);
    auto *editor = new QPlainTextEdit(&dialog);
    editor->setReadOnly(true);
    editor->setPlainText(lines.join(QLatin1Char('\n')));
    layout->addWidget(editor);
    auto *buttonBox = new QDialogButtonBox(QDialogButtonBox::Ok, &dialog);
    connect(buttonBox, &QDialogButtonBox::accepted, &dialog, &QDialog::accept);
    layout->addWidget(buttonBox);
    dialog.exec();
}
