#include "portconfigrepository.h"

QStringList PortConfig::getDefaultVariables(const QString &portType)
{
    if (portType == "electric") {
        return QStringList() << "i" << "u";
    } else if (portType == "hydraulic") {
        return QStringList() << "p" << "q";
    } else if (portType == "mechanical") {
        return QStringList() << "F" << "x";
    }
    return QStringList();
}

PortConfigRepository::PortConfigRepository(const QSqlDatabase &db)
    : m_db(db)
{
}

bool PortConfigRepository::ensureSchema()
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        return false;
    }
    
    QSqlQuery q(m_db);
    // Schema should already exist from project.db template
    // This method can be used to verify or add missing columns
    return true;
}

QList<PortConfig> PortConfigRepository::getPortConfigsByContainer(int containerId, QString *errorMsg)
{
    QList<PortConfig> configs;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return configs;
    }
    
    QSqlQuery query(m_db);
    query.prepare(
        "SELECT port_config_id, container_id, function_block, port_name, port_type, "
        "direction, variable_profile, variables_json, connect_macro, custom_metadata "
        "FROM port_config WHERE container_id = ? ORDER BY function_block, port_name"
    );
    query.addBindValue(containerId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return configs;
    }
    
    while (query.next()) {
        PortConfig config;
        config.portConfigId = query.value(0).toInt();
        config.containerId = query.value(1).toInt();
        config.functionBlock = query.value(2).toString();
        config.portName = query.value(3).toString();
        config.portType = query.value(4).toString();
        config.direction = query.value(5).toString();
        config.variableProfile = query.value(6).toString();
        
        // Parse variables_json
        QString variablesJson = query.value(7).toString();
        QJsonDocument doc = QJsonDocument::fromJson(variablesJson.toUtf8());
        if (doc.isArray()) {
            QJsonArray arr = doc.array();
            for (const QJsonValue &val : arr) {
                config.variables.append(val.toString());
            }
        }
        
        config.connectMacroFamily = query.value(8).toString();
        config.customMetadata = query.value(9).toString();
        
        configs.append(config);
    }
    
    return configs;
}

PortConfig PortConfigRepository::getPortConfig(int portConfigId, QString *errorMsg)
{
    PortConfig config;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return config;
    }
    
    QSqlQuery query(m_db);
    query.prepare(
        "SELECT port_config_id, container_id, function_block, port_name, port_type, "
        "direction, variable_profile, variables_json, connect_macro, custom_metadata "
        "FROM port_config WHERE port_config_id = ?"
    );
    query.addBindValue(portConfigId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return config;
    }
    
    if (query.next()) {
        config.portConfigId = query.value(0).toInt();
        config.containerId = query.value(1).toInt();
        config.functionBlock = query.value(2).toString();
        config.portName = query.value(3).toString();
        config.portType = query.value(4).toString();
        config.direction = query.value(5).toString();
        config.variableProfile = query.value(6).toString();
        
        QString variablesJson = query.value(7).toString();
        QJsonDocument doc = QJsonDocument::fromJson(variablesJson.toUtf8());
        if (doc.isArray()) {
            QJsonArray arr = doc.array();
            for (const QJsonValue &val : arr) {
                config.variables.append(val.toString());
            }
        }
        
        config.connectMacroFamily = query.value(8).toString();
        config.customMetadata = query.value(9).toString();
    } else {
        if (errorMsg) *errorMsg = "未找到端口配置";
    }
    
    return config;
}

PortConfig PortConfigRepository::getPortConfigByName(int containerId, const QString &functionBlock, 
                                                     const QString &portName, QString *errorMsg)
{
    PortConfig config;
    
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return config;
    }
    
    QSqlQuery query(m_db);
    query.prepare(
        "SELECT port_config_id, container_id, function_block, port_name, port_type, "
        "direction, variable_profile, variables_json, connect_macro, custom_metadata "
        "FROM port_config WHERE container_id = ? AND function_block = ? AND port_name = ?"
    );
    query.addBindValue(containerId);
    query.addBindValue(functionBlock);
    query.addBindValue(portName);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "查询失败: " + query.lastError().text();
        return config;
    }
    
    if (query.next()) {
        config.portConfigId = query.value(0).toInt();
        config.containerId = query.value(1).toInt();
        config.functionBlock = query.value(2).toString();
        config.portName = query.value(3).toString();
        config.portType = query.value(4).toString();
        config.direction = query.value(5).toString();
        config.variableProfile = query.value(6).toString();
        
        QString variablesJson = query.value(7).toString();
        QJsonDocument doc = QJsonDocument::fromJson(variablesJson.toUtf8());
        if (doc.isArray()) {
            QJsonArray arr = doc.array();
            for (const QJsonValue &val : arr) {
                config.variables.append(val.toString());
            }
        }
        
        config.connectMacroFamily = query.value(8).toString();
        config.customMetadata = query.value(9).toString();
    }
    
    return config;
}

bool PortConfigRepository::savePortConfig(PortConfig &config, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    // Serialize variables to JSON
    QJsonArray variablesArr;
    for (const QString &var : config.variables) {
        variablesArr.append(var);
    }
    QJsonDocument doc(variablesArr);
    QString variablesJson = QString::fromUtf8(doc.toJson(QJsonDocument::Compact));
    
    QSqlQuery query(m_db);
    query.prepare(
        "INSERT OR REPLACE INTO port_config "
        "(container_id, function_block, port_name, port_type, direction, "
        "variable_profile, variables_json, connect_macro, custom_metadata, updated_at) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, datetime('now'))"
    );
    query.addBindValue(config.containerId);
    query.addBindValue(config.functionBlock);
    query.addBindValue(config.portName);
    query.addBindValue(config.portType);
    query.addBindValue(config.direction);
    query.addBindValue(config.variableProfile);
    query.addBindValue(variablesJson);
    query.addBindValue(config.connectMacroFamily);
    query.addBindValue(config.customMetadata);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "保存失败: " + query.lastError().text();
        return false;
    }
    
    if (config.portConfigId <= 0) {
        config.portConfigId = query.lastInsertId().toInt();
    }
    
    return true;
}

bool PortConfigRepository::updatePortConfig(const PortConfig &config, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    if (config.portConfigId <= 0) {
        if (errorMsg) *errorMsg = "无效的port_config_id";
        return false;
    }
    
    QJsonArray variablesArr;
    for (const QString &var : config.variables) {
        variablesArr.append(var);
    }
    QJsonDocument doc(variablesArr);
    QString variablesJson = QString::fromUtf8(doc.toJson(QJsonDocument::Compact));
    
    QSqlQuery query(m_db);
    query.prepare(
        "UPDATE port_config SET "
        "function_block = ?, port_name = ?, port_type = ?, direction = ?, "
        "variable_profile = ?, variables_json = ?, connect_macro = ?, "
        "custom_metadata = ?, updated_at = datetime('now') "
        "WHERE port_config_id = ?"
    );
    query.addBindValue(config.functionBlock);
    query.addBindValue(config.portName);
    query.addBindValue(config.portType);
    query.addBindValue(config.direction);
    query.addBindValue(config.variableProfile);
    query.addBindValue(variablesJson);
    query.addBindValue(config.connectMacroFamily);
    query.addBindValue(config.customMetadata);
    query.addBindValue(config.portConfigId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "更新失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

bool PortConfigRepository::deletePortConfig(int portConfigId, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    QSqlQuery query(m_db);
    query.prepare("DELETE FROM port_config WHERE port_config_id = ?");
    query.addBindValue(portConfigId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "删除失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}

bool PortConfigRepository::savePortConfigs(const QList<PortConfig> &configs, QString *errorMsg)
{
    for (const PortConfig &config : configs) {
        PortConfig mutableConfig = config;
        if (!savePortConfig(mutableConfig, errorMsg)) {
            return false;
        }
    }
    return true;
}

bool PortConfigRepository::deletePortConfigsByContainer(int containerId, QString *errorMsg)
{
    if (!m_db.isValid() || !m_db.isOpen()) {
        if (errorMsg) *errorMsg = "数据库未打开";
        return false;
    }
    
    QSqlQuery query(m_db);
    query.prepare("DELETE FROM port_config WHERE container_id = ?");
    query.addBindValue(containerId);
    
    if (!query.exec()) {
        if (errorMsg) *errorMsg = "删除失败: " + query.lastError().text();
        return false;
    }
    
    return true;
}
