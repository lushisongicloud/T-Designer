#ifndef SINGLEEQUIPMENTWORKER_H
#define SINGLEEQUIPMENTWORKER_H

#include <QObject>
#include <QPair>
#include <QList>
#include <QMap>
#include <QElapsedTimer>
#include <QTimer>
#include <QSqlDatabase>
#include "../ai/tmodelautogenerator.h"  // 包含完整定义以使用 PortTypeConfig

class TModelAutoGenerator;

// 器件输入数据（由 Manager 准备）
struct EquipmentInputData {
    int equipmentId;
    QString code;
    QString name;
    QString description;
    QString categoryName;  // 最小类别名称
    QList<QPair<QString, QString>> ports;  // functionBlock, portName
    QMap<QString, PortTypeConfig> portConfigs;  // key: "functionBlock.portName"
};

// 器件处理结果
struct EquipmentProcessResult {
    int equipmentId;
    QString code;
    QString name;
    QString categoryName;
    
    enum Status {
        Success,    // 成功
        Failed,     // 失败
        NoPorts,    // 无有效端号
        Skipped     // 跳过（从log恢复时）
    };
    Status status;
    
    QString errorMessage;
    QString tmodel;        // 生成的 T 模型
    QMap<QString, QString> constants;  // 常量定义
    QMap<QString, PortTypeConfig> updatedPortConfigs;  // 更新后的端口配置
    int elapsedSeconds;    // 耗时（秒）
    
    QString statusString() const {
        switch (status) {
            case Success: return "success";
            case Failed: return "failed";
            case NoPorts: return "NoPorts";
            case Skipped: return "skipped";
        }
        return "unknown";
    }
};

// 注册元类型，以便在信号槽中使用
Q_DECLARE_METATYPE(EquipmentProcessResult)

// 单个器件处理工作线程
// 职责：复用 TModelAutoGenerator 进行 AI 生成，返回结果
// 不负责数据库操作（由 Manager 处理）
class SingleEquipmentWorker : public QObject
{
    Q_OBJECT

public:
    explicit SingleEquipmentWorker(const QString &dbConnectionName, const EquipmentInputData &inputData, QObject *parent = nullptr);
    ~SingleEquipmentWorker();

    int getEquipmentId() const { return m_inputData.equipmentId; }
    QString getCode() const { return m_inputData.code; }

signals:
    void logMessage(const QString &message);  // 日志消息（显示在Tab页）
    void streamDelta(const QString &delta);  // AI 流式输出增量
    void finished(const EquipmentProcessResult &result);  // 处理完成
    
    // 数据库操作请求信号（转发到 Manager）
    void requestSavePortConfigs(int equipmentId, const QMap<QString, PortTypeConfig> &configs);
    void requestSaveModel(int equipmentId, const QString &tmodel, const QMap<QString, QString> &constants);
    void requestClearModel(int equipmentId);

public slots:
    void process();  // 开始处理

private slots:
    void onGeneratorLogLine(const QString &line);
    void onGeneratorFinished(int equipmentId, const QString &code, bool success, const QString &message);
    void onConstantsExtracted(const QMap<QString, QString> &constants);
    void onModelGenerated(const QString &tmodel);
    void onStreamDelta(const QString &delta);

private slots:
    void onTimeout();  // 超时处理

private:
    // 输入数据
    QString m_dbConnectionName;  // 主数据库连接名（用于克隆）
    QString m_threadConnectionName;  // 工作线程中的数据库连接名
    QSqlDatabase m_threadDb;  // 线程独立的数据库连接（保持生命周期）
    EquipmentInputData m_inputData;
    
    // 处理结果（累积）
    EquipmentProcessResult m_result;
    
    // 核心生成器（复用单器件逻辑）
    TModelAutoGenerator *m_generator;
    
    // 处理状态
    QElapsedTimer m_timer;
    QTimer *m_timeoutTimer;  // 超时定时器
    bool m_isFinished;       // 防止重复完成
    
    // 辅助方法
    void log(const QString &message);
    void finishWithError(const QString &errorMessage);  // 带错误信息地完成
};

#endif // SINGLEEQUIPMENTWORKER_H
