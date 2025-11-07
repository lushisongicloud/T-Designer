#ifndef TMODEAUTOGENERATOR_H
#define TMODEAUTOGENERATOR_H

#include <QObject>
#include <QSqlDatabase>
#include <QString>
#include <QMap>
#include <QFile>
#include <QTextStream>
#include "BO/ai/deepseekclient.h"

class AiModelGeneratorDialog;

struct ComponentInfo {
    int equipmentId;
    QString code;
    QString name;
    QString description;
    QList<QPair<QString, QString>> ports;  // (functionBlock, portName)
};

struct PortTypeConfig {
    QString functionBlock;
    QString portName;
    QString portType;       // electric/hydraulic/mechanical
    QString variables;      // i,u / p,q / F,x
    QString connectMacro;   // electric-connect / hydraulic-connect / mechanical-connect
};

class TModelAutoGenerator : public QObject
{
    Q_OBJECT

public:
    explicit TModelAutoGenerator(const QSqlDatabase &db, QObject *parent = nullptr);
    explicit TModelAutoGenerator(const QSqlDatabase &db, int selectedEquipmentId, QObject *parent = nullptr);
    ~TModelAutoGenerator();

    // 开始自动生成（显示对话框）
    void startAutoGeneration();

signals:
    void finished();

private slots:
    void processNextComponent();
    void onReasoningDelta(const QString &delta);
    void onContentDelta(const QString &delta);
    void onResponseComplete(const QString &reasoning, const QString &content);
    void onErrorOccurred(const QString &error);

private:
    QSqlDatabase m_db;
    DeepSeekClient *m_deepseekClient;
    AiModelGeneratorDialog *m_dialog;
    QFile *m_logFile;
    QTextStream *m_logStream;
    
    QList<ComponentInfo> m_components;
    // 从外部（例如 DialogUnitManage 已经加载到 UI 的 tableTerm）预加载的端口，优先用于单器件模式
    QList<QPair<QString, QString>> m_preloadedPorts; // functionBlock, portName
    int m_currentIndex;
    int m_retryCount;
    static const int MAX_RETRIES = 3;
    
    enum ProcessStage {
        Stage_PortType,         // 识别端口类型
        Stage_InternalVars,     // 生成内部变量定义
        Stage_NormalMode,       // 生成正常模式
        Stage_FailureMode       // 生成故障模式
    };
    ProcessStage m_currentStage;
    
    QString m_currentReasoning;
    QString m_currentOutput;
    // 端口配置与各阶段生成的 T 模型片段缓存
    QMap<QString, PortTypeConfig> m_portConfigs;  // key: functionBlock.portName
    QString m_internalVarsDef;   // 内部变量定义 SMT 片段
    QString m_normalModeDef;     // 正常模式 SMT 片段
    QString m_failureModeDef;    // 故障模式 SMT 片段
    int m_selectedEquipmentId = 0; // 当前用户选中的器件ID（单个生成模式）
    
    // 初始化
    void initLogFile();
    void loadComponents();
    
    // 阶段处理
    void startPortTypeIdentification();
    void startInternalVarsGeneration();
    void startNormalModeGeneration();
    void startFailureModeGeneration();
    
    // 保存与校验
    bool savePortConfigs(int equipmentId);
    bool saveTModel(int equipmentId, const QString &tmodel);
    bool validateTModel(int equipmentId, const QString &tmodel, QString &errorMsg);
    
    // 提示词生成（保持与实现文件同步，若新增阶段请在此处添加声明）
    QString buildPortTypePrompt(const ComponentInfo &comp);
    QString buildInternalVarsPrompt(const ComponentInfo &comp);
    QString buildNormalModePrompt(const ComponentInfo &comp);
    QString buildFailureModePrompt(const ComponentInfo &comp);
    QString buildSystemPrompt();
    
    // 解析输出
    bool parsePortTypeResponse(const QString &output);
    
    // 辅助函数
    void logMessage(const QString &msg);
    void moveToNextComponent();
    void finishGeneration();
    int resolveContainerId(int equipmentId, bool createIfMissing);
    QString getDefaultVariables(const QString &portType);
    QString getDefaultMacro(const QString &portType);

    // 预览端口列表（在对话框刚显示时向用户提示将要作为提示词输入的端口集合）
    QString buildPortListPreview(const ComponentInfo &comp);

public: // 仅暴露轻量配置接口
    void setPreloadedPorts(const QList<QPair<QString, QString>> &ports) { m_preloadedPorts = ports; }
};

#endif // TMODEAUTOGENERATOR_H
