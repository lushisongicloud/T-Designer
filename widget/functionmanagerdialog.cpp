#include "widget/functionmanagerdialog.h"
#include "ui_functionmanagerdialog.h"

#include <QHeaderView>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QMessageBox>
#include <QPushButton>
#include <QRegularExpression>
#include <QSet>
#include <QSqlQuery>
#include <QTableWidgetItem>
#include <algorithm>
#include <cstring>
#include <functional>

#include "BO/function/constraintutils.h"
#include "BO/function/systemstructureservice.h"
#include "widget/functioneditdialog.h"

namespace {

constexpr const char *kOfflinePrefix = "#offline:";

QString trimmedText(const QString &text)
{
    QString result = text;
    return result.trimmed();
}

QString componentFromExec(const QString &exec)
{
    const QString trimmed = exec.trimmed();
    if (trimmed.isEmpty())
        return QString();
    const int dotIndex = trimmed.indexOf('.');
    if (dotIndex < 0)
        return trimmed;
    return trimmed.left(dotIndex);
}

} // namespace

FunctionManagerDialog::FunctionManagerDialog(const QSqlDatabase &db,
                                             const QString &systemDescription,
                                             QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::FunctionManagerDialog)
    , m_db(db)
    , m_repo(db)
    , m_systemDescription(systemDescription)
{
    ui->setupUi(this);
    setWindowTitle(tr("系统功能管理"));
    resize(960, 620);

    ui->tableFunctions->setColumnCount(6);
    ui->tableFunctions->setHorizontalHeaderLabels({
        tr("功能名称"),
        tr("功能子块"),
        tr("输入约束"),
        tr("执行器"),
        tr("器件依赖"),
        tr("备注")
    });
    ui->tableFunctions->horizontalHeader()->setStretchLastSection(true);
    ui->tableFunctions->verticalHeader()->setVisible(false);
    ui->tableFunctions->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableFunctions->setSelectionMode(QAbstractItemView::SingleSelection);
    ui->tableFunctions->setEditTriggers(QAbstractItemView::NoEditTriggers);

    ui->tableOffline->setColumnCount(3);
    ui->tableOffline->setHorizontalHeaderLabels({tr("相关器件"), tr("故障模式"), tr("概率")});
    ui->tableOffline->horizontalHeader()->setStretchLastSection(true);
    ui->tableOffline->setSelectionBehavior(QAbstractItemView::SelectRows);
    ui->tableOffline->setSelectionMode(QAbstractItemView::ExtendedSelection);
    ui->tableOffline->setEditTriggers(QAbstractItemView::DoubleClicked | QAbstractItemView::SelectedClicked | QAbstractItemView::EditKeyPressed);

    connect(ui->btnAdd, &QPushButton::clicked, this, &FunctionManagerDialog::onAdd);
    connect(ui->btnEdit, &QPushButton::clicked, this, &FunctionManagerDialog::onEdit);
    connect(ui->btnDelete, &QPushButton::clicked, this, &FunctionManagerDialog::onDelete);
    connect(ui->btnRefresh, &QPushButton::clicked, this, &FunctionManagerDialog::onRefresh);
    connect(ui->btnClose, &QPushButton::clicked, this, &QDialog::reject);
    connect(ui->btnAutoDependency, &QPushButton::clicked, this, &FunctionManagerDialog::onAutoDependency);
    connect(ui->btnAutoBoundary, &QPushButton::clicked, this, &FunctionManagerDialog::onAutoBoundary);
    connect(ui->btnCheckIntegrity, &QPushButton::clicked, this, &FunctionManagerDialog::onCheckIntegrity);
    connect(ui->btnAddOffline, &QPushButton::clicked, this, &FunctionManagerDialog::onAddOffline);
    connect(ui->btnRemoveOffline, &QPushButton::clicked, this, &FunctionManagerDialog::onRemoveOffline);
    connect(ui->btnSaveOffline, &QPushButton::clicked, this, &FunctionManagerDialog::onSaveOffline);
    connect(ui->btnSaveRecord, &QPushButton::clicked, this, &FunctionManagerDialog::onSaveRecord);
    connect(ui->tableFunctions, &QTableWidget::cellDoubleClicked,
            this, &FunctionManagerDialog::onTableDoubleClicked);

    if (!m_repo.ensureTables())
        QMessageBox::warning(this, tr("提示"), tr("数据库不可用"));

    loadData();
    onSelectionChanged();
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
    if (!m_records.isEmpty())
        ui->tableFunctions->setCurrentCell(0, 0);
    onSelectionChanged();
    updateButtons();

    // selection changed signal must be connected after data population to avoid nullptr
    if (ui->tableFunctions->selectionModel()) {
        disconnect(ui->tableFunctions->selectionModel(), nullptr, this, nullptr);
        connect(ui->tableFunctions->selectionModel(), &QItemSelectionModel::selectionChanged,
                this, &FunctionManagerDialog::onSelectionChanged);
    }
}

FunctionRecord FunctionManagerDialog::currentRecord() const
{
    const int row = ui->tableFunctions->currentRow();
    if (row < 0 || row >= m_records.size())
        return FunctionRecord{};
    return m_records.at(row);
}

void FunctionManagerDialog::displayRecord(const FunctionRecord &record)
{
    m_currentRecord = record;
    ui->lineCurrentName->setText(record.name);
    ui->lineLink->setText(record.link);
    ui->lineComponentDependency->setText(record.componentDependency);
    ui->lineAllComponents->setText(record.allComponents);
    ui->lineFunctionDependency->setText(record.functionDependency);
    ui->lineExecs->setText(record.execsList);
    ui->plainCmdVal->setPlainText(record.cmdValList);

    restoreOfflineResultsFromRecord(record);
    populateOfflineTable();
}

void FunctionManagerDialog::onSelectionChanged()
{
    const FunctionRecord rec = currentRecord();
    if (rec.id == 0) {
        ui->lineCurrentName->clear();
        ui->lineLink->clear();
        ui->lineComponentDependency->clear();
        ui->lineAllComponents->clear();
        ui->lineFunctionDependency->clear();
        ui->lineExecs->clear();
        ui->plainCmdVal->clear();
        ui->plainRemark->clear();
        m_offlineResults.clear();
        populateOfflineTable();
        m_currentRecord = FunctionRecord{};
    } else {
        displayRecord(rec);
    }
    updateButtons();
}

void FunctionManagerDialog::onAdd()
{
    FunctionEditDialog editor(m_db, this);
    if (editor.exec() != QDialog::Accepted)
        return;

    FunctionRecord rec = editor.record();
    const int id = m_repo.insert(rec);
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
    const FunctionRecord rec = currentRecord();
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
    Q_UNUSED(row)
    Q_UNUSED(column)
    onEdit();
}

void FunctionManagerDialog::onAutoDependency()
{
    if (m_currentRecord.id == 0)
        return;

    syncCurrentRecordFromUi();
    applyAutoDependency(m_currentRecord);
    ui->lineFunctionDependency->setText(m_currentRecord.functionDependency);
}

void FunctionManagerDialog::onAutoBoundary()
{
    if (m_currentRecord.id == 0)
        return;

    syncCurrentRecordFromUi();
    bool ok = false;
    const QStringList boundary = computeBoundaryCandidates(m_currentRecord, &ok);
    if (!ok)
        return;
    if (boundary.isEmpty()) {
        QMessageBox::information(this, tr("边界条件"), tr("未找到新的边界条件。"));
        return;
    }

    QList<QPair<QString, QString>> pairs = parseCmdValList(ui->plainCmdVal->toPlainText());
    QSet<QString> existing;
    for (const auto &pair : pairs)
        existing.insert(pair.first.trimmed());

    int added = 0;
    for (const QString &candidate : boundary) {
        const QString trimmed = candidate.trimmed();
        if (trimmed.isEmpty() || existing.contains(trimmed))
            continue;
        pairs.append(qMakePair(trimmed, QStringLiteral("boundary")));
        existing.insert(trimmed);
        ++added;
    }

    if (added == 0) {
        QMessageBox::information(this, tr("边界条件"), tr("所有边界变量已存在。"));
        return;
    }

    const QString serialized = serializeCmdValList(pairs);
    ui->plainCmdVal->setPlainText(serialized);
    m_currentRecord.cmdValList = serialized;
    QMessageBox::information(this, tr("边界条件"), tr("已添加 %1 个边界条件。").arg(added));
}

void FunctionManagerDialog::onCheckIntegrity()
{
    if (m_currentRecord.id == 0)
        return;

    syncCurrentRecordFromUi();
    const QString actuator = actuatorVariable(m_currentRecord);
    if (actuator.isEmpty()) {
        QMessageBox::information(this, tr("完整性检查"), tr("当前功能未指定执行器。"));
        return;
    }

    const QList<QPair<QString, QString>> pairs = parseCmdValList(ui->plainCmdVal->toPlainText());
    QString value;
    for (const auto &pair : pairs) {
        if (pair.first.trimmed().compare(actuator, Qt::CaseInsensitive) == 0) {
            value = pair.second.trimmed();
            break;
        }
    }

    if (value.isEmpty()) {
        QMessageBox::information(this, tr("完整性检查"),
                                 tr("未在输入约束中找到执行器约束：%1").arg(actuator));
        return;
    }

    const QString negated = functionconstraints::negateRange(value);
    QString message = tr("执行器变量：%1\n正向约束：%2\n反向示例：%3\n\n"
                         "（当前为启发式检查，未调用求解器验证可满足性。）")
                          .arg(actuator, value, negated);
    QMessageBox::information(this, tr("执行器取反完整性检查"), message);
}

void FunctionManagerDialog::onAddOffline()
{
    syncOfflineFromTable();
    FunctionOfflineResult result;
    m_offlineResults.append(result);
    populateOfflineTable();
    const int row = ui->tableOffline->rowCount() - 1;
    if (row >= 0)
        ui->tableOffline->setCurrentCell(row, 0);
}

void FunctionManagerDialog::onRemoveOffline()
{
    syncOfflineFromTable();
    const auto selected = ui->tableOffline->selectionModel()->selectedRows();
    if (selected.isEmpty())
        return;
    QList<int> rows;
    for (const QModelIndex &index : selected)
        rows.append(index.row());
    std::sort(rows.begin(), rows.end(), std::greater<int>());
    for (int row : rows) {
        if (row >= 0 && row < m_offlineResults.size())
            m_offlineResults.remove(row);
    }
    populateOfflineTable();
}

void FunctionManagerDialog::onSaveOffline()
{
    syncOfflineFromTable();
    QMessageBox::information(this, tr("离线缓存"), tr("离线求解结果已暂存至界面，点击“保存更改”写入数据库。"));
}

void FunctionManagerDialog::onSaveRecord()
{
    if (m_currentRecord.id == 0) {
        QMessageBox::information(this, tr("保存更改"), tr("请选择功能。"));
        return;
    }

    syncCurrentRecordFromUi();
    QList<QPair<QString, QString>> pairs = parseCmdValList(ui->plainCmdVal->toPlainText());
    m_currentRecord.cmdValList = serializeCmdValList(pairs);

    syncOfflineFromTable();
    applyOfflineResultsToRecord(m_currentRecord);

    if (!m_repo.update(m_currentRecord)) {
        QMessageBox::warning(this, tr("提示"), tr("保存失败"));
        return;
    }

    QMessageBox::information(this, tr("保存更改"), tr("功能已更新。"));
    const int savedId = m_currentRecord.id;
    loadData();
    for (int row = 0; row < m_records.size(); ++row) {
        if (m_records.at(row).id == savedId) {
            ui->tableFunctions->setCurrentCell(row, 0);
            break;
        }
    }
}

void FunctionManagerDialog::updateButtons()
{
    const bool hasSelection = (m_currentRecord.id != 0);
    ui->btnEdit->setEnabled(hasSelection);
    ui->btnDelete->setEnabled(hasSelection);
    ui->btnAutoDependency->setEnabled(hasSelection);
    ui->btnAutoBoundary->setEnabled(hasSelection);
    ui->btnCheckIntegrity->setEnabled(hasSelection);
    ui->btnAddOffline->setEnabled(hasSelection);
    ui->btnRemoveOffline->setEnabled(hasSelection);
    ui->btnSaveOffline->setEnabled(hasSelection);
    ui->btnSaveRecord->setEnabled(hasSelection);
}

void FunctionManagerDialog::populateOfflineTable()
{
    ui->tableOffline->setRowCount(m_offlineResults.size());
    for (int row = 0; row < m_offlineResults.size(); ++row) {
        const FunctionOfflineResult &entry = m_offlineResults.at(row);
        auto setItem = [&](int column, const QString &text) {
            QTableWidgetItem *item = new QTableWidgetItem(text);
            item->setFlags(Qt::ItemIsSelectable | Qt::ItemIsEditable | Qt::ItemIsEnabled);
            ui->tableOffline->setItem(row, column, item);
        };
        setItem(0, entry.componentNames.join(QStringLiteral(";")));
        setItem(1, entry.failureModes.join(QStringLiteral(";")));
        setItem(2, QString::number(entry.probability, 'g', 6));
    }
}

void FunctionManagerDialog::syncOfflineFromTable()
{
    QVector<FunctionOfflineResult> results;
    for (int row = 0; row < ui->tableOffline->rowCount(); ++row) {
        FunctionOfflineResult entry;
        auto textAt = [&](int column) -> QString {
            QTableWidgetItem *item = ui->tableOffline->item(row, column);
            return item ? item->text().trimmed() : QString();
        };
        entry.componentNames = parseList(textAt(0));
        entry.failureModes = parseList(textAt(1));
        bool ok = false;
        const double prob = textAt(2).toDouble(&ok);
        entry.probability = ok ? prob : 0.0;
        results.append(entry);
    }
    m_offlineResults = results;
}

QStringList FunctionManagerDialog::parseList(const QString &text) const
{
    QString normalized = text;
    normalized.replace(QLatin1Char('\n'), QLatin1Char(','));
    normalized.replace(QLatin1Char(';'), QLatin1Char(','));
    const QStringList rawParts = normalized.split(',', QString::SkipEmptyParts);
    QStringList list;
    for (const QString &part : rawParts) {
        const QString trimmed = part.trimmed();
        if (!trimmed.isEmpty())
            list.append(trimmed);
    }
    list.removeDuplicates();
    return list;
}

QList<QPair<QString, QString>> FunctionManagerDialog::parseCmdValList(const QString &text) const
{
    QList<QPair<QString, QString>> pairs;
    QString normalized = text;
    normalized.replace('\n', ',');
    const QStringList entries = normalized.split(',', QString::SkipEmptyParts);
    for (const QString &entry : entries) {
        const QString trimmed = entry.trimmed();
        if (trimmed.isEmpty())
            continue;
        const int eq = trimmed.indexOf('=');
        if (eq < 0) {
            pairs.append(qMakePair(trimmed, QString()));
        } else {
            const QString key = trimmed.left(eq).trimmed();
            const QString value = trimmed.mid(eq + 1).trimmed();
            pairs.append(qMakePair(key, value));
        }
    }
    return pairs;
}

QString FunctionManagerDialog::serializeCmdValList(const QList<QPair<QString, QString>> &pairs) const
{
    QStringList entries;
    for (const auto &pair : pairs) {
        const QString key = pair.first.trimmed();
        const QString value = pair.second.trimmed();
        if (key.isEmpty())
            continue;
        if (value.isEmpty())
            entries.append(key);
        else
            entries.append(QStringLiteral("%1=%2").arg(key, value));
    }
    return entries.join(',');
}

void FunctionManagerDialog::applyOfflineResultsToRecord(FunctionRecord &record) const
{
    QStringList remarkLines = ui->plainRemark->toPlainText().split(QLatin1Char('\n'));
    for (int i = remarkLines.size() - 1; i >= 0; --i) {
        if (remarkLines.at(i).trimmed().startsWith(QLatin1String(kOfflinePrefix)))
            remarkLines.removeAt(i);
    }
    QString remark = remarkLines.join(QLatin1String("\n")).trimmed();
    if (!m_offlineResults.isEmpty()) {
        const QString serialized = serializeOfflineResults();
        if (!serialized.isEmpty()) {
            if (!remark.isEmpty())
                remark.append(QLatin1Char('\n'));
            remark.append(QStringLiteral("%1%2").arg(QLatin1String(kOfflinePrefix), serialized));
        }
    }
    record.remark = remark;
}

void FunctionManagerDialog::restoreOfflineResultsFromRecord(const FunctionRecord &record)
{
    m_offlineResults.clear();
    QStringList remarkLines = record.remark.split(QLatin1Char('\n'));
    QStringList userRemark;
    for (const QString &line : remarkLines) {
        const QString trimmed = line.trimmed();
        if (trimmed.startsWith(QLatin1String(kOfflinePrefix))) {
            const QString json = trimmed.mid(int(strlen(kOfflinePrefix))).trimmed();
            deserializeOfflineResults(json);
        } else {
            userRemark.append(line);
        }
    }
    ui->plainRemark->setPlainText(userRemark.join(QLatin1String("\n")).trimmed());
}

QString FunctionManagerDialog::serializeOfflineResults() const
{
    QJsonArray array;
    for (const FunctionOfflineResult &entry : m_offlineResults) {
        QJsonObject obj;
        obj.insert(QStringLiteral("components"), QJsonArray::fromStringList(entry.componentNames));
        obj.insert(QStringLiteral("modes"), QJsonArray::fromStringList(entry.failureModes));
        obj.insert(QStringLiteral("probability"), entry.probability);
        array.append(obj);
    }
    const QJsonDocument doc(array);
    return QString::fromUtf8(doc.toJson(QJsonDocument::Compact));
}

void FunctionManagerDialog::deserializeOfflineResults(const QString &serialized)
{
    if (serialized.isEmpty())
        return;
    const QJsonDocument doc = QJsonDocument::fromJson(serialized.toUtf8());
    if (!doc.isArray())
        return;
    const QJsonArray array = doc.array();
    for (const QJsonValue &value : array) {
        if (!value.isObject())
            continue;
        const QJsonObject obj = value.toObject();
        FunctionOfflineResult entry;
        const QJsonArray comps = obj.value(QStringLiteral("components")).toArray();
        for (const QJsonValue &compVal : comps)
            entry.componentNames.append(compVal.toString());
        const QJsonArray modes = obj.value(QStringLiteral("modes")).toArray();
        for (const QJsonValue &modeVal : modes)
            entry.failureModes.append(modeVal.toString());
        entry.probability = obj.value(QStringLiteral("probability")).toDouble();
        m_offlineResults.append(entry);
    }
}

void FunctionManagerDialog::syncCurrentRecordFromUi()
{
    if (m_currentRecord.id == 0)
        return;
    m_currentRecord.link = trimmedText(ui->lineLink->text());
    m_currentRecord.componentDependency = trimmedText(ui->lineComponentDependency->text());
    m_currentRecord.allComponents = trimmedText(ui->lineAllComponents->text());
    m_currentRecord.functionDependency = trimmedText(ui->lineFunctionDependency->text());
    m_currentRecord.execsList = trimmedText(ui->lineExecs->text());
    m_currentRecord.cmdValList = ui->plainCmdVal->toPlainText().trimmed();
}

void FunctionManagerDialog::applyAutoDependency(FunctionRecord &record)
{
    const QStringList formatted = computeAutoDependency(record);
    record.functionDependency = formatted.join(QLatin1Char(';'));
    if (!formatted.isEmpty()) {
        QMessageBox::information(this, tr("依赖功能"),
                                 tr("已识别 %1 个依赖功能。").arg(formatted.size()));
    } else {
        QMessageBox::information(this, tr("依赖功能"), tr("未匹配到依赖功能。"));
    }
}

QStringList FunctionManagerDialog::computeAutoDependency(const FunctionRecord &record) const
{
    QStringList components = parseList(record.componentDependency);
    if (components.isEmpty())
        components = parseList(record.allComponents);
    if (components.isEmpty())
        return {};

    QSet<QString> unique;
    QStringList formatted;
    for (const QString &component : components) {
        const QString normalizedComponent = component.trimmed();
        if (normalizedComponent.isEmpty())
            continue;
        for (const FunctionRecord &other : m_records) {
            if (other.id == record.id)
                continue;
            const QStringList execs = other.execsList.split(',', QString::SkipEmptyParts);
            for (const QString &exec : execs) {
                if (componentFromExec(exec).compare(normalizedComponent, Qt::CaseInsensitive) == 0) {
                    const QString key = normalizedComponent + QLatin1Char('|') + other.name;
                    if (!unique.contains(key)) {
                        formatted.append(QStringLiteral("%1,%2,").arg(normalizedComponent, other.name));
                        unique.insert(key);
                    }
                }
            }
        }
    }
    return formatted;
}

QStringList FunctionManagerDialog::computeBoundaryCandidates(const FunctionRecord &record, bool *ok) const
{
    if (ok)
        *ok = false;
    QString systemDescription = m_systemDescription;
    if (systemDescription.trimmed().isEmpty() && m_db.isOpen()) {
        QSqlQuery query(m_db);
        if (query.exec(QStringLiteral("SELECT systemDescription FROM models LIMIT 1")) && query.next()) {
            systemDescription = query.value(0).toString();
        }
    }

    if (systemDescription.trimmed().isEmpty()) {
        QMessageBox::warning(nullptr, tr("边界条件"), tr("缺少系统描述，无法计算边界条件。"));
        return {};
    }
    bool consistent = false;
    const QStringList boundary = SystemStructureService::boundaryComponents(systemDescription,
                                                                            record.link,
                                                                            &consistent);
    if (!consistent) {
        QMessageBox::warning(nullptr, tr("边界条件"), tr("系统描述不自洽，无法识别边界条件。"));
        return {};
    }
    if (ok)
        *ok = true;
    return boundary;
}

QString FunctionManagerDialog::actuatorVariable(const FunctionRecord &record) const
{
    const QStringList execs = record.execsList.split(',', QString::SkipEmptyParts);
    if (execs.isEmpty())
        return QString();
    return execs.first().trimmed();
}
