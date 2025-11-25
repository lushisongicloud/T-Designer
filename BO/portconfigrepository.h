#ifndef PORTCONFIGREPOSITORY_H
#define PORTCONFIGREPOSITORY_H

#include <QString>
#include <QStringList>
#include <QSqlDatabase>
#include <QSqlQuery>
#include <QSqlError>
#include <QVariant>
#include <QDebug>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonArray>

/**
 * @brief Data structure for port configuration
 */
struct PortConfig {
    int portConfigId = -1;
    int containerId = -1;
    QString functionBlock;      // 功能子块名称
    QString portName;           // 端口名称
    QString portType;           // 端口类型：electric/hydraulic/mechanical/other
    QString direction;          // 方向：input/output/bidirectional
    QString variableProfile;    // 变量配置：default/custom
    QStringList variables;      // 变量列表，如["i", "u"]或自定义
    QString connectMacroFamily; // 关联的连接宏族名称
    QString customMetadata;     // 自定义元数据（JSON）
    
    bool isValid() const { return portConfigId > 0 || containerId > 0; }
    
    // 获取默认变量集
    static QStringList getDefaultVariables(const QString &portType);
};

/**
 * @brief Repository for managing port configurations
 */
class PortConfigRepository
{
public:
    explicit PortConfigRepository(const QSqlDatabase &db);
    
    // Query operations
    QList<PortConfig> getPortConfigsByContainer(int containerId, QString *errorMsg = nullptr);
    PortConfig getPortConfig(int portConfigId, QString *errorMsg = nullptr);
    PortConfig getPortConfigByName(int containerId, const QString &functionBlock, 
                                    const QString &portName, QString *errorMsg = nullptr);
    
    // CRUD operations
    bool savePortConfig(PortConfig &config, QString *errorMsg = nullptr);
    bool updatePortConfig(const PortConfig &config, QString *errorMsg = nullptr);
    bool deletePortConfig(int portConfigId, QString *errorMsg = nullptr);
    
    // Batch operations
    bool savePortConfigs(const QList<PortConfig> &configs, QString *errorMsg = nullptr);
    bool deletePortConfigsByContainer(int containerId, QString *errorMsg = nullptr);
    
    // Helper methods
    bool ensureSchema();
    
private:
    QSqlDatabase m_db;
};

#endif // PORTCONFIGREPOSITORY_H
