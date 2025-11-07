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

class DialogUnitManage; // 前向声明以避免循环包含

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
    // 端口类型识别阶段的待补充端口（functionBlock, portName）
    QList<QPair<QString, QString>> m_pendingPorts;
    int m_portTypeAttempt = 0; // 端口类型识别迭代次数
    int m_currentIndex;
    int m_retryCount;
    static const int MAX_RETRIES = 3;
    
    enum ProcessStage {
        Stage_PortType,         // 第一步：仅端口类型识别
        Stage_InternalVars,     // 保留旧阶段（兼容）
        Stage_NormalMode,       // 保留旧阶段（兼容）
        Stage_FailureMode,      // 保留旧阶段（兼容）
        Stage_ModelFull         // 第二步：一次性生成 常量定义 + 内部变量定义 + 正常模式 + 故障模式
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
    void loadExistingPortTypes(int equipmentId); // 读取已存在的端口类型填充 m_portConfigs 并设置 m_pendingPorts
    
    // 阶段处理
    void startPortTypeIdentification();
    void startInternalVarsGeneration(); // 旧流程兼容
    void startNormalModeGeneration();   // 旧流程兼容
    void startFailureModeGeneration();  // 旧流程兼容
    void startModelGeneration();        // 新：第二步一次性生成模型
    
    // 保存与校验
    bool savePortConfigs(int equipmentId);
    bool saveTModel(int equipmentId, const QString &tmodel);
    bool saveFullModel(int equipmentId, const QString &tmodel, const QMap<QString, QString> &constantsMap); // 新：同时保存常量与完整模型到 Equipment
    bool validateTModel(int equipmentId, const QString &tmodel, QString &errorMsg);
    
    // 提示词生成（保持与实现文件同步，若新增阶段请在此处添加声明）
    QString buildPortTypePrompt(const ComponentInfo &comp);
    QString buildInternalVarsPrompt(const ComponentInfo &comp);
    QString buildNormalModePrompt(const ComponentInfo &comp);
    QString buildFailureModePrompt(const ComponentInfo &comp);
    QString buildSystemPrompt(); // 旧：端口类型阶段继续复用，已裁剪为仅端口类型内容
    QString buildModelSystemPrompt();   // 新：模型生成阶段系统提示
    QString buildModelUserPrompt(const ComponentInfo &comp, const QString &portVarsDef);
    
    // 解析输出
    bool parsePortTypeResponse(const QString &output);
    bool parseModelFullResponse(const QString &output, QString &constantsJson, QString &modelBody);
    QString buildPortVarsSection(const ComponentInfo &comp) const; // 从 m_portConfigs 构造 ";;端口变量定义" 部分（不含末尾空行）
    QString extractPortVarsFromDialog() const; // 如果提供了 DialogUnitManage 指针，则从其 QsciEdit 中抽取端口变量定义
    // JSON 提取兼容：支持裸 JSON、```json fenced、``` fenced、'''json、''' 包裹形式及混杂文本
    bool findFirstJson(const QString &text, QString &jsonOut, int &endPos) const; // 解析首个对象或数组，返回结束位置（结束字符后一个索引）
    QString stripFenceWrappers(const QString &text) const; // 去除反引号或单引号围栏
    
    // 辅助函数
    void logMessage(const QString &msg);
    void moveToNextComponent();
    void finishGeneration();
    int resolveContainerId(int equipmentId, bool createIfMissing);
    QString getDefaultVariables(const QString &portType);
    QString getDefaultMacro(const QString &portType);

    // 预览端口列表（在对话框刚显示时向用户提示将要作为提示词输入的端口集合）
    QString buildPortListPreview(const ComponentInfo &comp);
    QString buildPortTypeJson(const ComponentInfo &comp); // 构造完整端口 JSON，包括已知类型与空类型
    int levenshteinDistance(const QString &a, const QString &b) const;
    QString canonicalKey(const QString &s) const; // 去除非字母数字并小写

public: // 仅暴露轻量配置接口
    void setPreloadedPorts(const QList<QPair<QString, QString>> &ports) { m_preloadedPorts = ports; }
    void setUnitManageDialog(DialogUnitManage *dlg) { m_unitManageDialog = dlg; }

signals:
    void constantsExtracted(const QMap<QString, QString> &constants); // 第二步解析出的常量
    void modelGenerated(const QString &tmodel); // 完整 T 模型文本（含端口变量定义）

private:
    DialogUnitManage *m_unitManageDialog = nullptr; // 可选：用于调用 on_BtnUpdatePortVars_clicked 及抽取端口变量
    bool m_isFinished = false; // 防止对象结束后仍接收网络事件

    QString serializeConstants(const QMap<QString, QString> &constantsMap) const; // name,value,unit,remark; 单元与备注为空
    QString deduplicateLines(const QString &text) const; // 去重端口变量重复声明
    QString normalizeConstantValue(const QString &value) const; // 科学计数法与布尔转化
    void normalizeConstantsMap(QMap<QString, QString> &map) const; // 批量规范化
};

#endif // TMODEAUTOGENERATOR_H
