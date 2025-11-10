#include "portconfigeditdialog.h"
#include "ui_portconfigeditdialog.h"
#include <QSqlQuery>
#include <QSqlError>
#include <QMessageBox>
#include <QJsonDocument>
#include <QJsonArray>
#include <QJsonObject>
#include <QDebug>

namespace {

QString defaultVariablesForType(const QString &type)
{
    if (type == "electric")
        return "i,u";
    else if (type == "hydraulic")
        return "p,q";
    else if (type == "mechanical")
        return "F,x";
    return "";
}

QString defaultMacroFamilyForType(const QString &type)
{
    if (type == "electric")
        return "electric-connect";
    else if (type == "hydraulic")
        return "hydraulic-connect";
    else if (type == "mechanical")
        return "mechanical-connect";
    return "";
}

} // namespace

PortConfigEditDialog::PortConfigEditDialog(const QSqlDatabase &db, int containerId, QWidget *parent)
    : QDialog(parent)
    , ui(new Ui::PortConfigEditDialog)
    , m_db(db)
    , m_containerId(containerId)
{
    ui->setupUi(this);

    connect(ui->comboPortType, &QComboBox::currentTextChanged, this, &PortConfigEditDialog::onPortTypeChanged);
    connect(ui->comboVariableProfile, &QComboBox::currentTextChanged, this, &PortConfigEditDialog::onVariableProfileChanged);
    connect(ui->tableMacros, &QTableWidget::clicked, this, &PortConfigEditDialog::onMacroTableClicked);
    connect(ui->btnAddMacroFamily, &QPushButton::clicked, this, &PortConfigEditDialog::onAddMacroFamily);
    connect(ui->btnDeleteMacroFamily, &QPushButton::clicked, this, &PortConfigEditDialog::onDeleteMacroFamily);

    ui->tableMacros->setColumnWidth(0, 150);
    ui->tableMacros->setColumnWidth(1, 80);
    ui->tableMacros->setColumnWidth(2, 80);
    ui->tableMacros->setColumnWidth(3, 250);

    // 在构造函数中加载可用的连接宏族
    loadAvailableMacros();
}

PortConfigEditDialog::~PortConfigEditDialog()
{
    delete ui;
}

void PortConfigEditDialog::setPortInfo(const QString &functionBlock, const QString &portName)
{
    m_functionBlock = functionBlock;
    m_portName = portName;
    ui->valueFuncBlock->setText(functionBlock);
    ui->valuePortName->setText(portName);
}

bool PortConfigEditDialog::loadConfig()
{
    if (!m_db.isValid() || m_containerId <= 0)
        return false;

    QSqlQuery query(m_db);
    query.prepare("SELECT port_config_id, port_type, direction, variable_profile, variables_json, connect_macro "
                  "FROM port_config WHERE container_id = ? AND function_block = ? AND port_name = ?");
    query.addBindValue(m_containerId);
    query.addBindValue(m_functionBlock);
    query.addBindValue(m_portName);

    if (!query.exec()) {
        qWarning() << "Failed to load port config:" << query.lastError();
        return false;
    }

    if (query.next()) {
        m_portConfigId = query.value("port_config_id").toInt();
        ui->comboPortType->setCurrentText(query.value("port_type").toString());
        ui->comboDirection->setCurrentText(query.value("direction").toString());
        ui->comboVariableProfile->setCurrentText(query.value("variable_profile").toString());
        ui->editVariables->setText(variablesTextFromJson(query.value("variables_json").toString()));
        ui->comboConnectMacro->setCurrentText(query.value("connect_macro").toString());
    } else {
        // 新建配置，使用默认值
        m_portConfigId = 0;
        ui->comboPortType->setCurrentText("electric");
        ui->comboDirection->setCurrentText("bidirectional");
        ui->comboVariableProfile->setCurrentText("default");
        // 设置默认变量和连接宏族
        updateDefaultVariables();
        updateDefaultMacro();
    }

    return true;
}

bool PortConfigEditDialog::saveConfig()
{
    if (!m_db.isValid() || m_containerId <= 0)
        return false;

    QSqlQuery query(m_db);

    if (m_portConfigId > 0) {
        // 更新现有配置
        query.prepare("UPDATE port_config SET port_type = ?, direction = ?, variable_profile = ?, "
                      "variables_json = ?, connect_macro = ? "
                      "WHERE port_config_id = ?");
        query.addBindValue(ui->comboPortType->currentText());
        query.addBindValue(ui->comboDirection->currentText());
        query.addBindValue(ui->comboVariableProfile->currentText());
        query.addBindValue(variablesJsonFromText(ui->editVariables->text()));
        query.addBindValue(ui->comboConnectMacro->currentText());
        query.addBindValue(m_portConfigId);
    } else {
        // 插入新配置
        query.prepare("INSERT INTO port_config (container_id, function_block, port_name, port_type, "
                      "direction, variable_profile, variables_json, connect_macro) "
                      "VALUES (?, ?, ?, ?, ?, ?, ?, ?)");
        query.addBindValue(m_containerId);
        query.addBindValue(m_functionBlock);
        query.addBindValue(m_portName);
        query.addBindValue(ui->comboPortType->currentText());
        query.addBindValue(ui->comboDirection->currentText());
        query.addBindValue(ui->comboVariableProfile->currentText());
        query.addBindValue(variablesJsonFromText(ui->editVariables->text()));
        query.addBindValue(ui->comboConnectMacro->currentText());
    }

    if (!query.exec()) {
        qWarning() << "Failed to save port config:" << query.lastError();
        QMessageBox::warning(this, "保存失败", "无法保存端口配置：" + query.lastError().text());
        return false;
    }

    return true;
}

PortConfigData PortConfigEditDialog::getConfig() const
{
    PortConfigData config;
    config.portConfigId = m_portConfigId;
    config.functionBlock = m_functionBlock;
    config.portName = m_portName;
    config.portType = ui->comboPortType->currentText();
    config.direction = ui->comboDirection->currentText();
    config.variableProfile = ui->comboVariableProfile->currentText();
    config.variablesText = ui->editVariables->text();
    config.connectMacro = ui->comboConnectMacro->currentText();
    return config;
}

void PortConfigEditDialog::onPortTypeChanged(const QString &type)
{
    if (ui->comboVariableProfile->currentText() == "default") {
        updateDefaultVariables();
    }
    updateDefaultMacro();
}

void PortConfigEditDialog::onVariableProfileChanged(const QString &profile)
{
    if (profile == "default") {
        updateDefaultVariables();
        ui->editVariables->setEnabled(false);
    } else {
        ui->editVariables->setEnabled(true);
    }
}

void PortConfigEditDialog::onMacroTableClicked(const QModelIndex &index)
{
    if (!index.isValid())
        return;
    
    QString macroName = ui->tableMacros->item(index.row(), 0)->text();
    ui->comboConnectMacro->setCurrentText(macroName);
}

void PortConfigEditDialog::loadAvailableMacros()
{
    ui->tableMacros->setRowCount(0);
    ui->comboConnectMacro->clear();
    
    if (!m_db.isValid())
        return;

    // 加载连接宏族
    QSqlQuery query(m_db);
    query.prepare("SELECT family_name, domain, description, macros_json FROM port_connect_macro_family "
                  "ORDER BY domain, family_name");

    if (!query.exec()) {
        qWarning() << "Failed to load macro families:" << query.lastError();
        return;
    }

    while (query.next()) {
        QString familyName = query.value("family_name").toString();
        QString domain = query.value("domain").toString();
        QString description = query.value("description").toString();
        QString macrosJson = query.value("macros_json").toString();
        
        // 解析宏族中的宏
        QJsonDocument doc = QJsonDocument::fromJson(macrosJson.toUtf8());
        if (!doc.isArray())
            continue;
            
        QJsonArray macros = doc.array();
        QString arityList;
        for (const QJsonValue &val : macros) {
            if (val.isObject()) {
                int arity = val.toObject().value("arity").toInt();
                if (!arityList.isEmpty())
                    arityList += ",";
                arityList += QString::number(arity);
            }
        }
        
        int row = ui->tableMacros->rowCount();
        ui->tableMacros->insertRow(row);
        ui->tableMacros->setItem(row, 0, new QTableWidgetItem(familyName));
        ui->tableMacros->setItem(row, 1, new QTableWidgetItem(domain));
        ui->tableMacros->setItem(row, 2, new QTableWidgetItem(arityList));
        ui->tableMacros->setItem(row, 3, new QTableWidgetItem(description));

        ui->comboConnectMacro->addItem(familyName);
    }
}

void PortConfigEditDialog::updateDefaultVariables()
{
    QString type = ui->comboPortType->currentText();
    ui->editVariables->setText(defaultVariablesForType(type));
}

void PortConfigEditDialog::updateDefaultMacro()
{
    QString type = ui->comboPortType->currentText();
    QString defaultFamily = defaultMacroFamilyForType(type);
    
    // 如果当前宏族为空或者不在列表中，设置默认值
    if (ui->comboConnectMacro->currentText().isEmpty() || 
        ui->comboConnectMacro->findText(ui->comboConnectMacro->currentText()) < 0) {
        ui->comboConnectMacro->setCurrentText(defaultFamily);
    }
}

QString PortConfigEditDialog::variablesJsonFromText(const QString &text) const
{
    QStringList vars = text.split(',', QString::SkipEmptyParts);
    QJsonArray array;
    for (const QString &varName : vars) {
        QJsonObject obj;
        obj.insert("name", varName.trimmed());
        array.append(obj);
    }
    return QString::fromUtf8(QJsonDocument(array).toJson(QJsonDocument::Compact));
}

QString PortConfigEditDialog::variablesTextFromJson(const QString &json) const
{
    QJsonDocument doc = QJsonDocument::fromJson(json.toUtf8());
    if (!doc.isArray())
        return QString();

    QStringList vars;
    QJsonArray array = doc.array();
    for (const QJsonValue &val : array) {
        if (val.isObject()) {
            QJsonObject obj = val.toObject();
            vars.append(obj.value("name").toString());
        }
    }
    return vars.join(",");
}

void PortConfigEditDialog::onAddMacroFamily()
{
    // TODO: 实现添加自定义宏族的对话框
    QMessageBox::information(this, "提示", "添加宏族功能待实现\n\n"
                            "说明：宏族包含多个不同端口数（arity）的连接宏，\n"
                            "系统会根据实际连接点上的端口数量自动选择合适的宏。");
}

void PortConfigEditDialog::onDeleteMacroFamily()
{
    int currentRow = ui->tableMacros->currentRow();
    if (currentRow < 0) {
        QMessageBox::warning(this, "警告", "请先选择要删除的宏族");
        return;
    }
    
    QString familyName = ui->tableMacros->item(currentRow, 0)->text();
    
    // 检查是否为内置宏族
    QSqlQuery checkQuery(m_db);
    checkQuery.prepare("SELECT is_builtin FROM port_connect_macro_family WHERE family_name = ?");
    checkQuery.addBindValue(familyName);
    
    if (checkQuery.exec() && checkQuery.next()) {
        bool isBuiltin = checkQuery.value(0).toBool();
        if (isBuiltin) {
            QMessageBox::warning(this, "警告", "不能删除内置宏族");
            return;
        }
    }
    
    QMessageBox::StandardButton reply = QMessageBox::question(
        this, "确认删除", 
        QString("确定要删除宏族 '%1' 吗？").arg(familyName),
        QMessageBox::Yes | QMessageBox::No);
    
    if (reply != QMessageBox::Yes)
        return;
    
    QSqlQuery deleteQuery(m_db);
    deleteQuery.prepare("DELETE FROM port_connect_macro_family WHERE family_name = ?");
    deleteQuery.addBindValue(familyName);
    
    if (deleteQuery.exec()) {
        QMessageBox::information(this, "成功", "宏族已删除");
        loadAvailableMacros();
    } else {
        QMessageBox::warning(this, "失败", "删除宏族失败：" + deleteQuery.lastError().text());
    }
}
