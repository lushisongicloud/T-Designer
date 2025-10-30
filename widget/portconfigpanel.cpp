#include "portconfigpanel.h"
#include "ui_portconfigpanel.h"

#include <QComboBox>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>
#include <QMessageBox>
#include <QSet>
#include <QSignalBlocker>
#include <QSqlError>
#include <QSqlQuery>
#include <QTableWidget>
#include <QTableWidgetItem>
#include <QDebug>

namespace {
const QString kElectric = QStringLiteral("electric");
const QString kHydraulic = QStringLiteral("hydraulic");
const QString kMechanical = QStringLiteral("mechanical");
const QString kOther = QStringLiteral("other");

const QStringList kPortTypes = {kElectric, kHydraulic, kMechanical, kOther};
const QStringList kDirections = {
    QStringLiteral("input"),
    QStringLiteral("output"),
    QStringLiteral("bidirectional"),
    QStringLiteral("internal")
};

QString toJson(const QStringList &vars)
{
    QJsonArray array;
    for (const QString &name : vars) {
        QJsonObject obj;
        obj.insert(QStringLiteral("name"), name);
        array.append(obj);
    }
    return QString::fromUtf8(QJsonDocument(array).toJson(QJsonDocument::Compact));
}

QStringList defaultVariables(const QString &type)
{
    if (type == kElectric)
        return {QStringLiteral("i"), QStringLiteral("u")};
    if (type == kHydraulic)
        return {QStringLiteral("p"), QStringLiteral("q")};
    if (type == kMechanical)
        return {QStringLiteral("F"), QStringLiteral("v")};
    return {};
}

QString defaultMacro(const QString &type, int arity)
{
    if (type == kElectric) {
        return arity == 3 ? QStringLiteral("connect3e") : QStringLiteral("connect2e");
    }
    if (type == kHydraulic) {
        return arity == 3 ? QStringLiteral("connect3h") : QStringLiteral("connect2h");
    }
    if (type == kMechanical) {
        return arity == 3 ? QStringLiteral("connect3m") : QStringLiteral("connect2m");
    }
    return {};
}

} // namespace

PortConfigPanel::PortConfigPanel(QWidget *parent)
    : QWidget(parent)
    , ui(new Ui::PortConfigPanel)
{
    ui->setupUi(this);
    setupPortTable();
    setupMacroTable();

    connect(ui->btnAddPort, &QPushButton::clicked, this, &PortConfigPanel::addPort);
    connect(ui->btnRemovePort, &QPushButton::clicked, this, &PortConfigPanel::removeSelectedPorts);
    connect(ui->btnAddMacro, &QPushButton::clicked, this, &PortConfigPanel::addMacro);
    connect(ui->btnRemoveMacro, &QPushButton::clicked, this, &PortConfigPanel::removeSelectedMacros);

    connect(ui->tablePorts, &QTableWidget::cellChanged, this, &PortConfigPanel::onPortCellChanged);
    connect(ui->tableMacros, &QTableWidget::cellChanged, this, &PortConfigPanel::onMacroCellChanged);
}

PortConfigPanel::PortConfigPanel(const QSqlDatabase &db, QWidget *parent)
    : QWidget(parent)
    , m_db(db)
    , ui(new Ui::PortConfigPanel)
{
    ui->setupUi(this);
    setupPortTable();
    setupMacroTable();

    connect(ui->btnAddPort, &QPushButton::clicked, this, &PortConfigPanel::addPort);
    connect(ui->btnRemovePort, &QPushButton::clicked, this, &PortConfigPanel::removeSelectedPorts);
    connect(ui->btnAddMacro, &QPushButton::clicked, this, &PortConfigPanel::addMacro);
    connect(ui->btnRemoveMacro, &QPushButton::clicked, this, &PortConfigPanel::removeSelectedMacros);

    connect(ui->tablePorts, &QTableWidget::cellChanged, this, &PortConfigPanel::onPortCellChanged);
    connect(ui->tableMacros, &QTableWidget::cellChanged, this, &PortConfigPanel::onMacroCellChanged);
}

PortConfigPanel::~PortConfigPanel()
{
    delete ui;
}

void PortConfigPanel::setDatabase(const QSqlDatabase &db)
{
    m_db = db;
}

void PortConfigPanel::setContainerId(int containerId)
{
    m_containerId = containerId;
}

bool PortConfigPanel::load()
{
    if (!ensureTables())
        return false;
    if (!loadPorts())
        return false;
    if (!loadMacros())
        return false;
    return true;
}

bool PortConfigPanel::save()
{
    if (!validate())
        return false;
    if (!savePorts())
        return false;
    if (!saveMacros())
        return false;
    return true;
}

bool PortConfigPanel::validate(QString *errorMessage) const
{
    if (errorMessage)
        errorMessage->clear();
    if (m_containerId <= 0)
        return true;
    QStringList errors;
    QTableWidget *portTable = ui->tablePorts;
    QSet<QString> uniqueKey;
    for (int row = 0; row < portTable->rowCount(); ++row) {
        const QTableWidgetItem *blockItem = portTable->item(row, 0);
        const QTableWidgetItem *portItem = portTable->item(row, 1);
        const QTableWidgetItem *typeItem = portTable->item(row, 2);
        const QString block = blockItem ? blockItem->text().trimmed() : QString();
        const QString port = portItem ? portItem->text().trimmed() : QString();
        const QString type = typeItem ? typeItem->text().trimmed() : QString();
        if (block.isEmpty() || port.isEmpty())
            errors.append(tr("第 %1 行缺少功能子块或端口名").arg(row + 1));
        if (!kPortTypes.contains(type))
            errors.append(tr("第 %1 行端口类型无效: %2").arg(row + 1).arg(type));
        const QString key = block + QLatin1Char('|') + port;
        if (uniqueKey.contains(key))
            errors.append(tr("重复端口: %1").arg(key));
        uniqueKey.insert(key);
    }
    QTableWidget *macroTable = ui->tableMacros;
    QSet<QString> macroNames;
    QStringList allowedDomains = kPortTypes;
    allowedDomains << QStringLiteral("generic");
    for (int row = 0; row < macroTable->rowCount(); ++row) {
        const QTableWidgetItem *nameItem = macroTable->item(row, 0);
        const QTableWidgetItem *domainItem = macroTable->item(row, 1);
        const QString name = nameItem ? nameItem->text().trimmed() : QString();
        const QString domain = domainItem ? domainItem->text().trimmed() : QString();
        if (name.isEmpty())
            errors.append(tr("第 %1 行宏名称为空").arg(row + 1));
        if (!allowedDomains.contains(domain))
            errors.append(tr("第 %1 行宏领域无效: %2").arg(row + 1).arg(domain));
        if (macroNames.contains(name))
            errors.append(tr("重复宏名称: %1").arg(name));
        macroNames.insert(name);
    }
    if (!errors.isEmpty()) {
        if (errorMessage) {
            *errorMessage = errors.join(QLatin1Char('\n'));
        } else {
            QMessageBox::warning(const_cast<PortConfigPanel *>(this), tr("校验失败"), errors.join(QLatin1Char('\n')));
        }
        return false;
    }
    return true;
}

void PortConfigPanel::addPort()
{
    auto *table = ui->tablePorts;
    const int row = table->rowCount();
    table->insertRow(row);
    PortConfigEntry entry;
    entry.portType = kElectric;
    entry.direction = QStringLiteral("bidirectional");
    entry.variableProfile = QStringLiteral("default");
    entry.variablesJson = toJson(defaultVariables(kElectric));
    entry.connectMacro = defaultMacro(kElectric, 2);
    writePortRow(row, entry);
    emit panelChanged();
}

void PortConfigPanel::removeSelectedPorts()
{
    auto *table = ui->tablePorts;
    const auto selected = table->selectionModel()->selectedRows();
    for (int i = selected.size() - 1; i >= 0; --i)
        table->removeRow(selected.at(i).row());
    emit panelChanged();
}

void PortConfigPanel::addMacro()
{
    auto *table = ui->tableMacros;
    const int row = table->rowCount();
    table->insertRow(row);
    ConnectMacroEntry entry;
    entry.domain = kElectric;
    entry.arity = 2;
    entry.expansionTemplate = QStringLiteral("(assert (= (+ %ARG1%.i %ARG2%.i) 0))");
    writeMacroRow(row, entry);
    emit panelChanged();
}

void PortConfigPanel::removeSelectedMacros()
{
    auto *table = ui->tableMacros;
    const auto selected = table->selectionModel()->selectedRows();
    for (int i = selected.size() - 1; i >= 0; --i)
        table->removeRow(selected.at(i).row());
    emit panelChanged();
}

void PortConfigPanel::onPortCellChanged(int row, int column)
{
    Q_UNUSED(column);
    if (row < 0)
        return;
    auto *table = ui->tablePorts;
    if (column == 2) {
        QTableWidgetItem *typeItem = table->item(row, column);
        if (!typeItem)
            return;
        const QString type = typeItem->text().trimmed();
        if (kPortTypes.contains(type)) {
            QTableWidgetItem *varItem = table->item(row, 5);
            QTableWidgetItem *macroItem = table->item(row, 6);
            if (varItem && macroItem) {
                varItem->setText(toJson(defaultVariables(type)));
                macroItem->setText(defaultMacro(type, 2));
            }
        }
    }
    emit panelChanged();
}

void PortConfigPanel::onMacroCellChanged(int row, int column)
{
    Q_UNUSED(column);
    if (row < 0)
        return;
    emit panelChanged();
}

bool PortConfigPanel::ensureTables()
{
    if (!m_db.isValid() || !m_db.isOpen())
        return false;
    QSqlQuery query(m_db);
    const char *ddlPortConfig =
        "CREATE TABLE IF NOT EXISTS port_config ("
        " port_config_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " container_id INTEGER NOT NULL,"
        " function_block TEXT NOT NULL,"
        " port_name TEXT NOT NULL,"
        " port_type TEXT NOT NULL,"
        " direction TEXT NOT NULL DEFAULT 'bidirectional',"
        " variable_profile TEXT NOT NULL DEFAULT 'default',"
        " variables_json TEXT NOT NULL,"
        " connect_macro TEXT,"
        " custom_metadata TEXT,"
        " updated_at TEXT DEFAULT CURRENT_TIMESTAMP"
        ")";
    if (!query.exec(QString::fromLatin1(ddlPortConfig))) {
        qWarning() << "Failed to create port_config table:" << query.lastError();
        return false;
    }
    const char *ddlPortMacro =
        "CREATE TABLE IF NOT EXISTS port_connect_macro ("
        " macro_id INTEGER PRIMARY KEY AUTOINCREMENT,"
        " container_id INTEGER NOT NULL,"
        " macro_name TEXT NOT NULL,"
        " domain TEXT NOT NULL,"
        " arity INTEGER NOT NULL,"
        " expansion_template TEXT NOT NULL,"
        " description TEXT,"
        " metadata_json TEXT,"
        " updated_at TEXT DEFAULT CURRENT_TIMESTAMP"
        ")";
    if (!query.exec(QString::fromLatin1(ddlPortMacro))) {
        qWarning() << "Failed to create port_connect_macro table:" << query.lastError();
        return false;
    }
    if (!query.exec("CREATE UNIQUE INDEX IF NOT EXISTS idx_port_config_unique ON port_config(container_id, function_block, port_name)")) {
        qWarning() << "Failed to create port_config index:" << query.lastError();
        return false;
    }
    if (!query.exec("CREATE UNIQUE INDEX IF NOT EXISTS idx_connect_macro_unique ON port_connect_macro(container_id, macro_name)")) {
        qWarning() << "Failed to create port_connect_macro index:" << query.lastError();
        return false;
    }
    return true;
}

void PortConfigPanel::setupPortTable()
{
    auto *table = ui->tablePorts;
    table->setColumnCount(7);
    QStringList headers = {
        tr("功能子块"), tr("端口"), tr("类型"), tr("方向"),
        tr("变量集"), tr("变量 JSON"), tr("连接宏")
    };
    table->setHorizontalHeaderLabels(headers);
    table->setSelectionBehavior(QAbstractItemView::SelectRows);
    table->setSelectionMode(QAbstractItemView::SingleSelection);
}

void PortConfigPanel::setupMacroTable()
{
    auto *table = ui->tableMacros;
    table->setColumnCount(6);
    table->setHorizontalHeaderLabels({
        tr("名称"), tr("领域"), tr("端口数"), tr("展开模板"), tr("描述"), tr("附加信息")
    });
    table->setSelectionBehavior(QAbstractItemView::SelectRows);
    table->setSelectionMode(QAbstractItemView::SingleSelection);
}

PortConfigEntry PortConfigPanel::readPortRow(int row) const
{
    auto *table = ui->tablePorts;
    PortConfigEntry entry;
    entry.portConfigId = table->item(row, 0)->data(Qt::UserRole).toInt();
    entry.functionBlock = table->item(row, 0)->text();
    entry.portName = table->item(row, 1)->text();
    entry.portType = table->item(row, 2)->text();
    entry.direction = table->item(row, 3)->text();
    entry.variableProfile = table->item(row, 4)->text();
    entry.variablesJson = table->item(row, 5)->text();
    entry.connectMacro = table->item(row, 6)->text();
    return entry;
}

void PortConfigPanel::writePortRow(int row, const PortConfigEntry &entry)
{
    auto *table = ui->tablePorts;
    const QSignalBlocker blocker(table);
    table->setItem(row, 0, new QTableWidgetItem(entry.functionBlock));
    table->item(row, 0)->setData(Qt::UserRole, entry.portConfigId);
    table->setItem(row, 1, new QTableWidgetItem(entry.portName));
    table->setItem(row, 2, new QTableWidgetItem(entry.portType.isEmpty() ? kElectric : entry.portType));
    table->setItem(row, 3, new QTableWidgetItem(entry.direction.isEmpty() ? QStringLiteral("bidirectional") : entry.direction));
    table->setItem(row, 4, new QTableWidgetItem(entry.variableProfile.isEmpty() ? QStringLiteral("default") : entry.variableProfile));
    table->setItem(row, 5, new QTableWidgetItem(entry.variablesJson));
    table->setItem(row, 6, new QTableWidgetItem(entry.connectMacro));
}

ConnectMacroEntry PortConfigPanel::readMacroRow(int row) const
{
    auto *table = ui->tableMacros;
    ConnectMacroEntry entry;
    entry.macroId = table->item(row, 0)->data(Qt::UserRole).toInt();
    entry.macroName = table->item(row, 0)->text();
    entry.domain = table->item(row, 1)->text();
    entry.arity = table->item(row, 2)->text().toInt();
    entry.expansionTemplate = table->item(row, 3)->text();
    entry.description = table->item(row, 4)->text();
    entry.metadataJson = table->item(row, 5)->text();
    return entry;
}

void PortConfigPanel::writeMacroRow(int row, const ConnectMacroEntry &entry)
{
    auto *table = ui->tableMacros;
    const QSignalBlocker blocker(table);
    table->setItem(row, 0, new QTableWidgetItem(entry.macroName));
    table->item(row, 0)->setData(Qt::UserRole, entry.macroId);
    table->setItem(row, 1, new QTableWidgetItem(entry.domain.isEmpty() ? kElectric : entry.domain));
    const int arity = entry.arity > 0 ? entry.arity : 2;
    table->setItem(row, 2, new QTableWidgetItem(QString::number(arity)));
    table->setItem(row, 3, new QTableWidgetItem(entry.expansionTemplate));
    table->setItem(row, 4, new QTableWidgetItem(entry.description));
    table->setItem(row, 5, new QTableWidgetItem(entry.metadataJson));
}

bool PortConfigPanel::loadPorts()
{
    auto *table = ui->tablePorts;
    const QSignalBlocker blocker(table);
    table->setRowCount(0);
    if (m_containerId <= 0)
        return true;
    QSqlQuery query(m_db);
    query.prepare(QStringLiteral(
        "SELECT port_config_id, function_block, port_name, port_type, direction, variable_profile, variables_json, connect_macro, custom_metadata "
        "FROM port_config WHERE container_id = :cid ORDER BY function_block, port_name"));
    query.bindValue(QStringLiteral(":cid"), m_containerId);
    if (!query.exec()) {
        QMessageBox::warning(this, tr("读取失败"), query.lastError().text());
        return false;
    }
    while (query.next()) {
        const int row = table->rowCount();
        table->insertRow(row);
        PortConfigEntry entry;
        entry.portConfigId = query.value(0).toInt();
        entry.functionBlock = query.value(1).toString();
        entry.portName = query.value(2).toString();
        entry.portType = query.value(3).toString();
        entry.direction = query.value(4).toString();
        entry.variableProfile = query.value(5).toString();
        entry.variablesJson = query.value(6).toString();
        entry.connectMacro = query.value(7).toString();
        entry.customMetadata = query.value(8).toString();
        writePortRow(row, entry);
    }
    return true;
}

bool PortConfigPanel::loadMacros()
{
    auto *table = ui->tableMacros;
    const QSignalBlocker blocker(table);
    table->setRowCount(0);
    if (m_containerId <= 0)
        return true;
    QSqlQuery query(m_db);
    query.prepare(QStringLiteral(
        "SELECT macro_id, macro_name, domain, arity, expansion_template, description, metadata_json "
        "FROM port_connect_macro WHERE container_id = :cid ORDER BY macro_name"));
    query.bindValue(QStringLiteral(":cid"), m_containerId);
    if (!query.exec()) {
        QMessageBox::warning(this, tr("读取失败"), query.lastError().text());
        return false;
    }
    while (query.next()) {
        const int row = table->rowCount();
        table->insertRow(row);
        ConnectMacroEntry entry;
        entry.macroId = query.value(0).toInt();
        entry.macroName = query.value(1).toString();
        entry.domain = query.value(2).toString();
        entry.arity = query.value(3).toInt();
        entry.expansionTemplate = query.value(4).toString();
        entry.description = query.value(5).toString();
        entry.metadataJson = query.value(6).toString();
        writeMacroRow(row, entry);
    }
    return true;
}

bool PortConfigPanel::savePorts()
{
    if (m_containerId <= 0)
        return true;
    if (!m_db.transaction())
        return false;
    QSqlQuery del(m_db);
    del.prepare(QStringLiteral("DELETE FROM port_config WHERE container_id = :cid"));
    del.bindValue(QStringLiteral(":cid"), m_containerId);
    if (!del.exec()) {
        m_db.rollback();
        QMessageBox::warning(this, tr("保存失败"), del.lastError().text());
        return false;
    }
    QSqlQuery ins(m_db);
    ins.prepare(QStringLiteral(
        "INSERT INTO port_config(container_id, function_block, port_name, port_type, direction, variable_profile, variables_json, connect_macro, custom_metadata) "
        "VALUES(:cid,:block,:port,:type,:dir,:profile,:vars,:macro,:meta)"));
    auto *table = ui->tablePorts;
    for (int row = 0; row < table->rowCount(); ++row) {
        PortConfigEntry entry = readPortRow(row);
        ins.bindValue(QStringLiteral(":cid"), m_containerId);
        ins.bindValue(QStringLiteral(":block"), entry.functionBlock);
        ins.bindValue(QStringLiteral(":port"), entry.portName);
        ins.bindValue(QStringLiteral(":type"), entry.portType);
        ins.bindValue(QStringLiteral(":dir"), entry.direction);
        ins.bindValue(QStringLiteral(":profile"), entry.variableProfile);
        ins.bindValue(QStringLiteral(":vars"), entry.variablesJson);
        ins.bindValue(QStringLiteral(":macro"), entry.connectMacro);
        ins.bindValue(QStringLiteral(":meta"), entry.customMetadata);
        if (!ins.exec()) {
            m_db.rollback();
            QMessageBox::warning(this, tr("保存失败"), ins.lastError().text());
            return false;
        }
    }
    if (!m_db.commit()) {
        m_db.rollback();
        return false;
    }
    return true;
}

bool PortConfigPanel::saveMacros()
{
    if (m_containerId <= 0)
        return true;
    if (!m_db.transaction())
        return false;
    QSqlQuery del(m_db);
    del.prepare(QStringLiteral("DELETE FROM port_connect_macro WHERE container_id = :cid"));
    del.bindValue(QStringLiteral(":cid"), m_containerId);
    if (!del.exec()) {
        m_db.rollback();
        QMessageBox::warning(this, tr("保存失败"), del.lastError().text());
        return false;
    }
    QSqlQuery ins(m_db);
    ins.prepare(QStringLiteral(
        "INSERT INTO port_connect_macro(container_id, macro_name, domain, arity, expansion_template, description, metadata_json) "
        "VALUES(:cid,:name,:domain,:arity,:expr,:desc,:meta)"));
    auto *table = ui->tableMacros;
    for (int row = 0; row < table->rowCount(); ++row) {
        ConnectMacroEntry entry = readMacroRow(row);
        ins.bindValue(QStringLiteral(":cid"), m_containerId);
        ins.bindValue(QStringLiteral(":name"), entry.macroName);
        ins.bindValue(QStringLiteral(":domain"), entry.domain);
        ins.bindValue(QStringLiteral(":arity"), entry.arity);
        ins.bindValue(QStringLiteral(":expr"), entry.expansionTemplate);
        ins.bindValue(QStringLiteral(":desc"), entry.description);
        ins.bindValue(QStringLiteral(":meta"), entry.metadataJson);
        if (!ins.exec()) {
            m_db.rollback();
            QMessageBox::warning(this, tr("保存失败"), ins.lastError().text());
            return false;
        }
    }
    if (!m_db.commit()) {
        m_db.rollback();
        return false;
    }
    return true;
}
