#include "tmodelautogenerator.h"
#include "widget/aimodelgeneratordialog.h"
#include "BO/function/tmodelparser.h"
#include "widget/codecheckdialog.h"
#include "BO/containerrepository.h"
#include "widget/containerhierarchyutils.h"
#include "dialogunitmanage.h" // 新增：用于调用端口变量更新按钮
#include <Qsci/qsciscintilla.h>
#include <QSqlQuery>
#include <QSqlError>
#include <QMessageBox>
#include <QDateTime>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonArray>
#include <QDebug>
#include <QCoreApplication>
#include <QTimer>
#include <QSet>
#include <QTableView>
#include <QThread>
#include <cstdio>

TModelAutoGenerator::TModelAutoGenerator(const QSqlDatabase &db, QObject *parent)
    : QObject(parent)
    , m_db(db)
    , m_deepseekClient(new DeepSeekClient(this))
    , m_dialog(nullptr)
    , m_logFile(nullptr)
    , m_logStream(nullptr)
    , m_currentIndex(0)
    , m_retryCount(0)
    , m_currentStage(Stage_PortType)
    , m_isFinished(false)
{
    m_nextComponentTimer.setSingleShot(true);
    connect(&m_nextComponentTimer, &QTimer::timeout, this, &TModelAutoGenerator::processNextComponent);

    // 连接 DeepSeek 客户端信号
    connect(m_deepseekClient, &DeepSeekClient::reasoningDelta, this, &TModelAutoGenerator::onReasoningDelta);
    connect(m_deepseekClient, &DeepSeekClient::contentDelta, this, &TModelAutoGenerator::onContentDelta);
    connect(m_deepseekClient, &DeepSeekClient::responseComplete, this, &TModelAutoGenerator::onResponseComplete);
    connect(m_deepseekClient, &DeepSeekClient::errorOccurred, this, &TModelAutoGenerator::onErrorOccurred);

    // 从环境变量获取 API Key
    QString apiKey = qEnvironmentVariable("DEEPSEEK_API_KEY");
    if (apiKey.isEmpty()) {
        qWarning() << "DEEPSEEK_API_KEY 环境变量未设置";
    }
    m_deepseekClient->setApiKey(apiKey);
}

TModelAutoGenerator::TModelAutoGenerator(const QSqlDatabase &db, int selectedEquipmentId, QObject *parent)
    : TModelAutoGenerator(db, parent)
{
    m_selectedEquipmentId = selectedEquipmentId;
}

// 无数据库构造函数（用于批量模式）
TModelAutoGenerator::TModelAutoGenerator(QObject *parent)
    : QObject(parent)
    , m_deepseekClient(new DeepSeekClient(this))
    , m_dialog(nullptr)
    , m_logFile(nullptr)
    , m_logStream(nullptr)
    , m_currentIndex(0)
    , m_retryCount(0)
    , m_currentStage(Stage_PortType)
    , m_isFinished(false)
    , m_useDatabaseMode(false)  // 关键：禁用数据库模式
{
    m_nextComponentTimer.setSingleShot(true);
    connect(&m_nextComponentTimer, &QTimer::timeout, this, &TModelAutoGenerator::processNextComponent);

    // 连接 DeepSeek 客户端信号
    connect(m_deepseekClient, &DeepSeekClient::reasoningDelta, this, &TModelAutoGenerator::onReasoningDelta);
    connect(m_deepseekClient, &DeepSeekClient::contentDelta, this, &TModelAutoGenerator::onContentDelta);
    connect(m_deepseekClient, &DeepSeekClient::responseComplete, this, &TModelAutoGenerator::onResponseComplete);
    connect(m_deepseekClient, &DeepSeekClient::errorOccurred, this, &TModelAutoGenerator::onErrorOccurred);

    // 从环境变量获取 API Key
    QString apiKey = qEnvironmentVariable("DEEPSEEK_API_KEY");
    if (apiKey.isEmpty()) {
        qWarning() << "DEEPSEEK_API_KEY 环境变量未设置";
    }
    m_deepseekClient->setApiKey(apiKey);
}

TModelAutoGenerator::~TModelAutoGenerator()
{
    if (m_logStream) {
        delete m_logStream;
    }
    if (m_logFile) {
        m_logFile->close();
        delete m_logFile;
    }
}

void TModelAutoGenerator::setLogFileOverride(const QString &path, bool appendMode)
{
    m_logOverridePath = path;
    m_logAppendMode = appendMode;
    m_disableLogFile = path.isEmpty() && !appendMode;  // 空路径且不追加模式 = 禁用日志文件
    m_logInitialized = false;
    if (m_logStream) {
        delete m_logStream;
        m_logStream = nullptr;
    }
    if (m_logFile) {
        m_logFile->close();
        delete m_logFile;
        m_logFile = nullptr;
    }
}

void TModelAutoGenerator::setComponentData(const ComponentInfo &comp, const QMap<QString, PortTypeConfig> &portConfigs)
{
    // 设置单个组件数据（用于批量模式）
    m_components.clear();
    m_components.append(comp);
    m_portConfigs = portConfigs;  // 直接赋值整个 map
}

void TModelAutoGenerator::cancelGeneration()
{
    m_isFinished = true;
    m_nextComponentTimer.stop();
    if (m_deepseekClient) {
        m_deepseekClient->cancelRequest();
    }
}

void TModelAutoGenerator::startAutoGeneration()
{
    m_isFinished = false;
    
    // 无数据库模式：组件数据已由 setComponentData() 预设，不要清空
    if (m_useDatabaseMode) {
        m_components.clear();
    }

    if (!m_logInitialized) {
        initLogFile();
        m_logInitialized = true;
    }

    // 加载组件
    loadComponents();

    if (m_components.isEmpty()) {
        logMessage("没有需要处理的器件。");
        emit finished();
        return;
    }

    logMessage(QString("开始自动生成，共 %1 个器件").arg(m_components.size()));
    if (!m_components.isEmpty()) {
        const ComponentInfo &first = m_components.first();
        // 端口配置已在 loadComponents() 中加载
        QString preview = buildPortListPreview(first);
        logMessage("=== 端口列表预览 ===\n" + preview + "\n");
    }

    // 开始处理第一个组件
    m_currentIndex = 0;
    processNextComponent();
}

void TModelAutoGenerator::initLogFile()
{
    // 如果已明确禁用日志文件，直接返回
    if (m_disableLogFile) {
        return;
    }
    
    QString logPath = m_logOverridePath;
    if (logPath.isEmpty()) {
        // 增加毫秒和线程ID，确保多线程环境下文件名唯一
        logPath = QString("tmodel_auto_gen_%1_%2_%3.log")
            .arg(QDateTime::currentDateTime().toString("yyyyMMdd_hhmmss"))
            .arg(QDateTime::currentMSecsSinceEpoch() % 1000, 3, 10, QChar('0'))
            .arg((quintptr)QThread::currentThreadId() % 10000);
    } else if (!m_logAppendMode && QFile::exists(logPath)) {
        QFile::remove(logPath);
    }

    QFile::OpenMode mode = QIODevice::WriteOnly | QIODevice::Text;
    if (!m_logOverridePath.isEmpty() && m_logAppendMode) {
        mode |= QIODevice::Append;
    }

    m_logFile = new QFile(logPath);
    if (m_logFile->open(mode)) {
        m_logStream = new QTextStream(m_logFile);
        m_logStream->setCodec("UTF-8");
    } else {
        qWarning() << "无法创建日志文件:" << logPath;
    }
}

void TModelAutoGenerator::loadComponents()
{
    // 数据库模式：清空并重新加载
    // 无数据库模式：保留 setComponentData() 设置的数据
    if (m_useDatabaseMode) {
        m_components.clear();
    }

    // 无数据库模式：组件数据已由 setComponentData() 预设，直接返回
    if (!m_useDatabaseMode) {
        if (m_components.isEmpty()) {
            logMessage("无数据库模式：错误 - 未设置组件数据");
        } else {
            const ComponentInfo &comp = m_components.first();
            logMessage(QString("无数据库模式：使用预设组件 %1 (%2)").arg(comp.code, comp.name));
            logMessage(QString("  端口数量: %1, 端口配置: %2").arg(comp.ports.size()).arg(m_portConfigs.size()));
        }
        return;
    }

    // 数据库模式：从数据库加载组件数据
    // 如果指定了选中器件，则只处理该器件（来自 Equipment 表）
    if (m_selectedEquipmentId > 0) {
        QSqlQuery query(m_db);
        QString sql = QString("SELECT Equipment_ID, PartCode, Name, Desc FROM Equipment WHERE Equipment_ID = %1").arg(m_selectedEquipmentId);
        if (!query.exec(sql)) {
            logMessage("查询选中器件失败: " + query.lastError().text());
            return;
        }
        if (query.next()) {
            ComponentInfo comp;
            comp.equipmentId = query.value("Equipment_ID").toInt();
            comp.code = query.value("PartCode").toString();
            comp.name = query.value("Name").toString();
            comp.description = query.value("Desc").toString();

            logMessage(QString("选中器件: %1 (%2) - %3").arg(comp.code, comp.name, comp.description.left(50)));

            // 端口信息：优先使用外部 UI 预加载端口（例如用户在 DialogUnitManage 中看到的 tableTerm 内容）
            if (!m_preloadedPorts.isEmpty()) {
                comp.ports = m_preloadedPorts; // 已由 UI 收集的 functionBlock/portName
                logMessage(QString("使用预加载端口: %1 条").arg(comp.ports.size()));
                // 即使使用预加载端口，也需要从数据库加载端口描述
                QList<QPair<QString, QString>> tempPorts;
                loadPortsFromDatabase(m_db, comp.equipmentId, tempPorts, &comp.portDescriptions);
                logMessage(QString("从数据库加载端口描述: %1 条").arg(comp.portDescriptions.size()));
            } else {
                // 从数据库加载端口列表和描述
                loadPortsFromDatabase(m_db, comp.equipmentId, comp.ports, &comp.portDescriptions);
                logMessage(QString("从数据库加载端口: %1 条, 描述: %2 条").arg(comp.ports.size()).arg(comp.portDescriptions.size()));
            }

            // 加载该器件的端口配置信息到 m_portConfigs
            loadPortConfigsForEquipment(m_db, comp.equipmentId, m_portConfigs);

            m_components.append(comp);
            logMessage("单器件模式：共 1 个器件加入处理队列");
        } else {
            logMessage("未找到指定的 Equipment 记录");
        }
        return;
    }

    // 否则：保持原批量逻辑，但改为从 Equipment 表读取（库界面主要展示的是 Equipment）。
    QSqlQuery query(m_db);
    if (!query.exec("SELECT Equipment_ID, PartCode, Name, Desc FROM Equipment WHERE Desc IS NOT NULL AND Desc != '' ORDER BY Equipment_ID")) {
        logMessage("查询器件失败: " + query.lastError().text());
        return;
    }

    int candidateCount = 0;
    while (query.next()) {
        candidateCount++;
        ComponentInfo comp;
        comp.equipmentId = query.value("Equipment_ID").toInt();
        comp.code = query.value("PartCode").toString();
        comp.name = query.value("Name").toString();
        comp.description = query.value("Desc").toString();
        logMessage(QString("候选器件: %1 (%2)").arg(comp.code, comp.name));

        // 从数据库加载端口列表和描述
        loadPortsFromDatabase(m_db, comp.equipmentId, comp.ports, &comp.portDescriptions);
        logMessage(QString("  端口数量: %1").arg(comp.ports.size()));

        // 不再跳过无端口器件（满足用户“先不要跳过器件”需求）
        m_components.append(comp);
        if(candidateCount>100)break;
    }

    logMessage(QString("批量模式：共发现 %1 个器件，加入处理队列 %2 个").arg(candidateCount).arg(m_components.size()));
}

void TModelAutoGenerator::processNextComponent()
{
    if (m_currentIndex >= m_components.size()) {
        finishGeneration();
        return;
    }

    const ComponentInfo &comp = m_components[m_currentIndex];

    if (m_dialog) {
        m_dialog->clearAll();
        m_dialog->setCurrentComponent(comp.code, m_currentIndex + 1, m_components.size());
    }

    logMessage(QString("\n========== 处理器件 [%1/%2]: %3 (%4) ==========")
        .arg(m_currentIndex + 1)
        .arg(m_components.size())
        .arg(comp.code)
        .arg(comp.name));

    // 重置状态
    m_retryCount = 0;
    m_currentStage = Stage_PortType;
    
    // 对于批量模式的后续器件，需要重新加载其端口配置
    // (单器件模式或批量模式的第一个器件已在 loadComponents() 中加载)
    if (m_currentIndex > 0) {
        m_portConfigs.clear();
        loadPortConfigsForEquipment(m_db, comp.equipmentId, m_portConfigs);
    }
    
    // 清理数据库中存在但器件实际不存在的端口配置（历史脏数据）
    QSet<QString> actualPortNames;
    for (const auto &p : comp.ports) {
        actualPortNames.insert(p.second);  // portName
    }
    
    QStringList keysToRemove;
    for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
        if (!actualPortNames.contains(it.value().portName)) {
            keysToRemove.append(it.key());
        }
    }
    
    if (!keysToRemove.isEmpty()) {
        logMessage(QString("清理历史遗留端口配置: %1 个").arg(keysToRemove.size()));
        for (const QString &key : keysToRemove) {
            logMessage(QString("  - 移除: %1").arg(key));
            m_portConfigs.remove(key);
        }
    }
    
    m_internalVarsDef.clear();
    m_normalModeDef.clear();
    m_failureModeDef.clear();

    // 开始第一阶段：识别端口类型
    startPortTypeIdentification();
}

void TModelAutoGenerator::startPortTypeIdentification()
{
    const ComponentInfo &comp = m_components[m_currentIndex];
    m_currentStage = Stage_PortType;
    m_currentReasoning.clear();
    m_currentOutput.clear();
    m_reasoningStreamStarted = false;
    m_contentStreamStarted = false;

    // 检查是否所有端口都已有类型配置
    bool allPortsHaveType = true;
    QList<QPair<QString, QString>> sourcePorts = !m_preloadedPorts.isEmpty() ? m_preloadedPorts : comp.ports;
    for (const auto &p : sourcePorts) {
        QString key = p.first + "." + p.second;
        if (!m_portConfigs.contains(key) || m_portConfigs.value(key).portType.trimmed().isEmpty()) {
            allPortsHaveType = false;
            break;
        }
    }

    // 如果所有端口都已有类型，跳过识别阶段，直接进入模型生成
    if (allPortsHaveType && !sourcePorts.isEmpty()) {
        logMessage("所有端口已配置类型，跳过端口类型识别阶段");
        if (!m_portConfigs.isEmpty()) {
            if (savePortConfigs(comp.equipmentId)) 
                logMessage("端口配置保存成功");
            else 
                logMessage("端口配置保存失败");
        }
        startModelGeneration();
        return;
    }

    if (m_dialog) {
        m_dialog->setStatus("识别端口类型...");
    }

    logMessage("阶段1: 识别端口类型 (仅端口类型相关提示，不包含模型生成规则)");
    logMessage(QString("当前器件的端口描述数量: %1").arg(comp.portDescriptions.size()));
    if (!comp.portDescriptions.isEmpty()) {
        logMessage("端口描述详情:");
        for (auto it = comp.portDescriptions.constBegin(); it != comp.portDescriptions.constEnd(); ++it) {
            logMessage(QString("  %1: %2").arg(it.key(), it.value()));
        }
    }

    QString systemPrompt = buildSystemPrompt();
    QString userPrompt = buildPortTypePrompt(comp);

    logMessage("=== DeepSeek Request ===");
    logMessage("System Prompt:\n" + systemPrompt);
    logMessage("User Prompt:\n" + userPrompt);
    if (m_dialog) {
        m_dialog->appendInput("=== 系统提示 ===\n" + systemPrompt);
        m_dialog->appendInput("\n=== 用户输入 ===\n" + userPrompt);
    }

    m_deepseekClient->chatCompletion(systemPrompt, userPrompt, true);
}

// 旧阶段方法兼容保留，但新流程统一改为一次性生成
void TModelAutoGenerator::startInternalVarsGeneration() { startModelGeneration(); }
void TModelAutoGenerator::startNormalModeGeneration() { /* 不再单独调用 */ }
void TModelAutoGenerator::startFailureModeGeneration() { /* 不再单独调用 */ }

void TModelAutoGenerator::startModelGeneration()
{
    const ComponentInfo &comp = m_components[m_currentIndex];
    m_currentStage = Stage_ModelFull;
    m_currentReasoning.clear();
    m_currentOutput.clear();
    m_reasoningStreamStarted = false;
    m_contentStreamStarted = false;

    if (!clearExistingTModel(comp.equipmentId)) {
        logMessage("警告：清除旧的 T 模型失败，继续尝试生成新模型。");
    }
    
    // 仅在非批量模式下操作UI编辑器
    if (!m_isBatchMode && m_unitManageDialog)
        m_unitManageDialog->clearTModelEditor();

    if (m_dialog) {
        m_dialog->setStatus("生成完整 T 模型...");
    }
    logMessage("阶段2: 生成完整模型 (常量定义 + 内部变量定义 + 正常模式 + 故障模式)。调用 UI 更新端口变量定义。");
    logMessage(QString("当前器件的端口描述数量: %1").arg(comp.portDescriptions.size()));
    if (!comp.portDescriptions.isEmpty()) {
        logMessage("端口描述详情:");
        for (auto it = comp.portDescriptions.constBegin(); it != comp.portDescriptions.constEnd(); ++it) {
            logMessage(QString("  %1: %2").arg(it.key(), it.value()));
        }
    }

    // 调用 UI 的端口变量构建逻辑（仅非批量模式）
    QString portVarsDef;
    if (!m_isBatchMode && m_unitManageDialog) {
        m_unitManageDialog->regeneratePortVariables(false);
        portVarsDef = extractPortVarsFromDialog();
        if (portVarsDef.trimmed().isEmpty()) {
            portVarsDef = buildPortVarsSection(comp);
        }
    } else {
        portVarsDef = buildPortVarsSection(comp);
    }

    QString systemPrompt = buildModelSystemPrompt();
    QString userPrompt = buildModelUserPrompt(comp, portVarsDef);

    logMessage("=== DeepSeek Request ===");
    logMessage("System Prompt:\n" + systemPrompt);
    logMessage("User Prompt:\n" + userPrompt);
    if (m_dialog) {
        m_dialog->appendInput("\n\n=== 新请求（完整模型） ===\n");
        m_dialog->appendInput("=== 系统提示 ===\n" + systemPrompt);
        m_dialog->appendInput("\n=== 用户输入 ===\n" + userPrompt);
    }

    m_deepseekClient->chatCompletion(systemPrompt, userPrompt, true);
}

void TModelAutoGenerator::onReasoningDelta(const QString &delta)
{
    if (m_isFinished) return; // 防止结束后仍接收
    m_currentReasoning += delta;
    if (!delta.isEmpty()) {
        if (!m_reasoningStreamStarted) {
            // 批量模式下不打印到终端
            if (!m_isBatchMode) {
                qInfo().noquote() << "[DeepSeek][reasoning-stream]";
            }
            m_reasoningStreamStarted = true;
        }
        // 批量模式下不输出到终端
        if (!m_isBatchMode) {
            writeUtf8ToStdout(delta);
        }
    }
    if (m_dialog) {
        m_dialog->appendReasoning(delta);
    }
}

void TModelAutoGenerator::onContentDelta(const QString &delta)
{
    if (m_isFinished) return; // 防止结束后仍接收
    m_currentOutput += delta;
    if (!delta.isEmpty()) {
        if (!m_contentStreamStarted) {
            // 批量模式下不打印到终端
            if (!m_isBatchMode) {
                qInfo().noquote() << "[DeepSeek][content-stream]";
            }
            m_contentStreamStarted = true;
        }
        // 批量模式下不输出到终端
        if (!m_isBatchMode) {
            writeUtf8ToStdout(delta);
        }
        
        // 发出流式输出信号（用于批量处理的 Tab 页显示）
        emit streamDelta(delta);
    }
    if (m_dialog) {
        m_dialog->appendOutput(delta);
    }
}

void TModelAutoGenerator::onResponseComplete(const QString &reasoning, const QString &content)
{
    if (m_isFinished) return; // 已结束不再处理
    logMessage("AI 响应完成");
    logMessage("思考内容: " + reasoning);
    logMessage("输出内容: " + content);

    m_currentReasoning = reasoning;
    m_currentOutput = content;

    const ComponentInfo &comp = m_components[m_currentIndex];

    switch (m_currentStage) {
    case Stage_PortType: {
        // 新增：迭代端口类型识别逻辑
        if (parsePortTypeResponse(content)) {
            if (!m_pendingPorts.isEmpty() && m_portTypeAttempt < MAX_RETRIES-1) {
                m_portTypeAttempt++;
                logMessage(QString("仍有未识别端口，启动第 %1 轮识别 (最多 %2 轮)").arg(m_portTypeAttempt+1).arg(MAX_RETRIES));
                startPortTypeIdentification();
            } else {
                if (!m_portConfigs.isEmpty()) {
                    if (savePortConfigs(comp.equipmentId)) logMessage("端口配置保存成功"); else logMessage("端口配置保存失败");
                }
                startModelGeneration();
            }
        } else {
            logMessage("端口类型解析失败");
            if (m_portTypeAttempt < MAX_RETRIES-1) {
                m_portTypeAttempt++;
                startPortTypeIdentification();
            } else {
                if (!m_portConfigs.isEmpty()) savePortConfigs(comp.equipmentId);
                startModelGeneration();
            }
        }
        break; }
    case Stage_ModelFull: {
        QString constantsJson, modelBody;
        if (!parseModelFullResponse(content, constantsJson, modelBody)) {
            logMessage("完整模型响应解析失败");
            if (m_retryCount < MAX_RETRIES) { m_retryCount++; startModelGeneration(); }
            else { moveToNextComponent(false, tr("模型解析失败")); }
            break; }
        // 解析常量映射
        QMap<QString, QString> constantsMap;
        if (!constantsJson.trimmed().isEmpty()) {
            QJsonParseError cErr; QJsonDocument cdoc = QJsonDocument::fromJson(constantsJson.toUtf8(), &cErr);
            if (cErr.error == QJsonParseError::NoError) {
                if (cdoc.isObject()) {
                    QJsonObject o = cdoc.object(); for (auto it=o.begin(); it!=o.end(); ++it) constantsMap[it.key()] = it.value().toVariant().toString();
                } else if (cdoc.isArray()) {
                    for (auto v : cdoc.array()) {
                        if (v.isObject()) { QJsonObject o=v.toObject(); for (auto it=o.begin(); it!=o.end(); ++it) constantsMap[it.key()] = it.value().toVariant().toString(); }
                        else if (v.isArray()) { QJsonArray a=v.toArray(); if (a.size()>=2) constantsMap[a.at(0).toString()] = a.at(1).toVariant().toString(); }
                    }
                }
            }
        }
        // 规范化常量（科学计数法与布尔）
        normalizeConstantsMap(constantsMap);
        emit constantsExtracted(constantsMap);
        QString portVarsDef = buildPortVarsSection(comp);
        portVarsDef = deduplicateLines(portVarsDef); // 去重
        QString fullTModel = QString(";;端口变量定义\n%1\n\n%2").arg(portVarsDef, modelBody.trimmed());
        QString errorMsg;
        if (validateTModel(comp.equipmentId, fullTModel, errorMsg)) {
            bool saved = false;
            if (saveFullModel(comp.equipmentId, fullTModel, constantsMap)) {
                logMessage("完整 T 模型与常量保存成功");
                emit modelGenerated(fullTModel);
                saved = true;
            } else {
                logMessage("完整 T 模型保存失败");
            }
            // 仅在非批量模式下刷新 UI（批量模式不操作UI避免错误）
            if (!m_isBatchMode && m_unitManageDialog) {
                QMetaObject::invokeMethod(m_unitManageDialog, "on_tableWidgetUnit_clicked", Qt::QueuedConnection,
                                          Q_ARG(QModelIndex, m_unitManageDialog->findChild<QTableView*>("tableWidgetUnit") ? m_unitManageDialog->findChild<QTableView*>("tableWidgetUnit")->currentIndex() : QModelIndex()));
            }
            moveToNextComponent(saved, saved ? tr("生成完成") : tr("保存失败"));
        } else {
            logMessage("完整 T 模型校验失败: " + errorMsg);
            if (m_retryCount < MAX_RETRIES) { m_retryCount++; startModelGeneration(); }
            else moveToNextComponent(false, errorMsg);
        }
        break; }
    }
}

void TModelAutoGenerator::onErrorOccurred(const QString &error)
{
    logMessage("错误: " + error);

    if (m_dialog) {
        m_dialog->setStatus("错误: " + error);
    }

    if (m_retryCount < MAX_RETRIES) {
        m_retryCount++;
        logMessage(QString("重试 %1/%2").arg(m_retryCount).arg(MAX_RETRIES));

        // 重试当前阶段
        switch (m_currentStage) {
        case Stage_PortType:
            startPortTypeIdentification();
            break;
        case Stage_InternalVars:
        case Stage_NormalMode:
        case Stage_FailureMode:
        case Stage_ModelFull:
            startModelGeneration();
            break;
        }
    } else {
        logMessage("达到最大重试次数，跳过此器件");
        moveToNextComponent(false, tr("达到最大重试次数"));
    }
}

bool TModelAutoGenerator::parsePortTypeResponse(const QString &output)
{
    // 兼容 fenced 或包裹 JSON；提取首个对象
    QString jsonBlock; int endPos=-1;
    if (!findFirstJson(output, jsonBlock, endPos)) {
        logMessage("未找到 JSON 块");
        return false;
    }
    QJsonParseError jerr; QJsonDocument doc = QJsonDocument::fromJson(jsonBlock.toUtf8(), &jerr);
    if (jerr.error != QJsonParseError::NoError || !doc.isObject()) {
        logMessage(QString("JSON 解析失败: %1").arg(jerr.errorString()));
        return false;
    }
    QJsonObject obj = doc.object();
    if (!obj.contains("ports")) {
        logMessage("JSON 中缺少 ports 字段");
        return false;
    }
    QJsonArray ports = obj["ports"].toArray();
    if (ports.isEmpty()) {
        logMessage("返回端口列表为空，可能模型未按要求输出");
        return false;
    }
    QList<QPair<QString, QString>> candidates = m_pendingPorts;
    for (const QJsonValue &val : ports) {
        if (!val.isObject()) continue;
        QJsonObject portObj = val.toObject();
        QString funcBlock = portObj["functionBlock"].toString();
        QString portName = portObj["portName"].toString();
        QString portType = portObj["portType"].toString();
        if (portName.isEmpty() || portType.isEmpty()) continue;
        // 精确端号匹配
        QString chosenFunctionBlock; QList<QPair<QString,QString>> exactMatches;
        for (auto &c : candidates) if (c.second.compare(portName, Qt::CaseInsensitive)==0) exactMatches.append(c);
        if (exactMatches.size()==1) { chosenFunctionBlock = exactMatches.first().first; }
        else if (exactMatches.size()>1) {
            int best=INT_MAX; QString bestFb; QString aiCan = canonicalKey(funcBlock);
            for (auto &m : exactMatches) { int dist = levenshteinDistance(aiCan, canonicalKey(m.first)); if (dist<best){best=dist;bestFb=m.first;} }
            chosenFunctionBlock = bestFb;
        } else {
            int bestDist=INT_MAX; QString bestFb; for (auto &c : candidates) { int dist = levenshteinDistance(canonicalKey(portName), canonicalKey(c.second)); if (dist<bestDist){bestDist=dist;bestFb=c.first;} }
            chosenFunctionBlock = bestFb.isEmpty()?funcBlock:bestFb;
        }
        QString key = chosenFunctionBlock + "." + portName;
        PortTypeConfig cfg; if (m_portConfigs.contains(key)) cfg = m_portConfigs.value(key); else { cfg.functionBlock=chosenFunctionBlock; cfg.portName=portName; }
        cfg.portType = portType; cfg.variables = getDefaultVariables(portType); cfg.connectMacro = getDefaultMacro(portType);
        m_portConfigs.insert(key, cfg);
        for (int i=0;i<m_pendingPorts.size(); ++i) if (m_pendingPorts[i].second.compare(portName, Qt::CaseInsensitive)==0) { m_pendingPorts.removeAt(i); break; }
    }
    logMessage(QString("本轮解析端口: %1, 剩余待识别: %2").arg(ports.size()).arg(m_pendingPorts.size()));
    return true;
}

bool TModelAutoGenerator::savePortConfigs(int equipmentId)
{
    // 无数据库模式：发出信号请求保存
    if (!m_useDatabaseMode) {
        logMessage(QString("无数据库模式：请求保存端口配置，配置数=%1").arg(m_portConfigs.size()));
        if (!m_portConfigs.isEmpty()) {
            logMessage("端口配置详情：");
            for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
                const PortTypeConfig &cfg = it.value();
                logMessage(QString("  %1.%2: %3 (%4)").arg(cfg.functionBlock, cfg.portName, cfg.portType, cfg.variables));
            }
        }
        emit requestSavePortConfigs(equipmentId, m_portConfigs);
        return true;
    }

    // 数据库模式：直接保存
    // 获取或创建 container_id
    int containerId = resolveContainerId(equipmentId, true);
    if (containerId <= 0) {
        logMessage("无法获取 container_id");
        return false;
    }

    QSqlQuery query(m_db);

    for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
        const PortTypeConfig &config = it.value();

        // 检查是否已存在
        query.prepare(
            "SELECT port_config_id FROM port_config "
            "WHERE container_id = ? AND function_block = ? AND port_name = ?"
        );
        query.addBindValue(containerId);
        query.addBindValue(config.functionBlock);
        query.addBindValue(config.portName);

        if (!query.exec()) {
            logMessage("查询端口配置失败: " + query.lastError().text());
            continue;
        }

        // 标准化变量集合：拆分后独立存储 JSON 数组
        QStringList varList = config.variables.split(QRegExp("[,;，；]"), QString::SkipEmptyParts);
        QJsonArray varArray; for (QString v : varList) { v = v.trimmed(); if (!v.isEmpty()) { QJsonObject o; o["name"] = v; varArray.append(o); } }
        QString variablesJson = QString::fromUtf8(QJsonDocument(varArray).toJson(QJsonDocument::Compact));

        if (query.next()) {
            // 更新
            int portConfigId = query.value(0).toInt();
            query.prepare(
                "UPDATE port_config SET port_type = ?, variables_json = ?, connect_macro = ? "
                "WHERE port_config_id = ?"
            );
            query.addBindValue(config.portType);
            query.addBindValue(variablesJson);
            query.addBindValue(config.connectMacro);
            query.addBindValue(portConfigId);
        } else {
            // 插入
            query.prepare(
                "INSERT INTO port_config (container_id, function_block, port_name, port_type, "
                "direction, variable_profile, variables_json, connect_macro) "
                "VALUES (?, ?, ?, ?, 'bidirectional', 'default', ?, ?)"
            );
            query.addBindValue(containerId);
            query.addBindValue(config.functionBlock);
            query.addBindValue(config.portName);
            query.addBindValue(config.portType);
            query.addBindValue(variablesJson);
            query.addBindValue(config.connectMacro);
        }

        if (!query.exec()) {
            logMessage("保存端口配置失败: " + query.lastError().text());
            return false;
        }
    }

    return true;
}

// bool TModelAutoGenerator::saveTModel(int equipmentId, const QString &tmodel)
// {
//     // 无数据库模式：发出信号请求保存
//     if (!m_useDatabaseMode) {
//         logMessage("无数据库模式：请求保存 T 模型");
//         QMap<QString, QString> constants;  // 暂时为空，如需要可扩展
//         emit requestSaveModel(equipmentId, tmodel, constants);
//         return true;
//     }

//     // 数据库模式：直接保存
//     QSqlQuery query(m_db);
//     query.prepare("UPDATE Equipment_Template SET TModel = ? WHERE Equipment_ID = ?");
//     query.addBindValue(tmodel);
//     query.addBindValue(equipmentId);

//     if (!query.exec()) {
//         logMessage("保存 T 模型失败: " + query.lastError().text());
//         return false;
//     }

//     return true;
// }

bool TModelAutoGenerator::validateTModel(int /*equipmentId*/, const QString &tmodel, QString &errorMsg)
{
    // 这里应该调用系统的校验功能
    // 暂时简单检查是否为空
    if (tmodel.trimmed().isEmpty()) {
        errorMsg = "T 模型为空";
        return false;
    }

    // TODO: 调用 CodeCheckDialog 或 TModelParser 进行完整校验

    return true;
}

void TModelAutoGenerator::logMessage(const QString &msg)
{
    QString timestampedMsg = QDateTime::currentDateTime().toString("[yyyy-MM-dd hh:mm:ss] ") + msg;
    
    // 批量模式下不打印到终端
    if (!m_isBatchMode) {
        qDebug().noquote() << timestampedMsg;
    }

    if (m_logStream) {
        *m_logStream << timestampedMsg << "\n";
        m_logStream->flush();
    }

    emit logLine(timestampedMsg);
}

void TModelAutoGenerator::writeUtf8ToStdout(const QString &text)
{
    static QTextStream qstdout(stdout);
    static bool codecSet = false;
    if (!codecSet) {
        qstdout.setCodec("UTF-8");
        codecSet = true;
    }
    qstdout << text;
    qstdout.flush();
}

void TModelAutoGenerator::moveToNextComponent(bool success, const QString &message)
{
    if (m_currentIndex < m_components.size()) {
        const ComponentInfo &comp = m_components[m_currentIndex];
        emit componentFinished(comp.equipmentId, comp.code, success, message);
    }

    m_currentIndex++;
    if (!m_isFinished) {
        m_nextComponentTimer.start(500);
    }
}

void TModelAutoGenerator::finishGeneration()
{
    m_nextComponentTimer.stop();
    logMessage("\n========== 自动生成完成 ==========");
    logMessage(QString("共处理 %1 个器件").arg(m_components.size()));

    m_isFinished = true;
    if (m_deepseekClient) m_deepseekClient->cancelRequest(); // 取消可能仍在进行的网络请求

    if (m_dialog) {
        m_dialog->setStatus("全部完成");
        m_dialog->setCurrentComponent("完成", m_components.size(), m_components.size());
        // 启用关闭按钮
        m_dialog->enableCloseButton();
    }

    emit finished();
}

int TModelAutoGenerator::resolveContainerId(int equipmentId, bool createIfMissing)
{
    // 无数据库模式：不支持容器操作
    if (!m_useDatabaseMode) {
        logMessage("无数据库模式：resolveContainerId 不支持");
        return 0;
    }
    
    // 数据库模式：复用系统统一的 ContainerRepository + ContainerHierarchy 逻辑
    ContainerRepository repo(m_db);
    if (!repo.ensureTables()) {
        qWarning() << "ensureTables failed";
        return 0;
    }
    int existing = repo.componentContainerIdForEquipment(equipmentId);
    if (existing != 0 || !createIfMissing) return existing;
    int created = ContainerHierarchy::ensureComponentContainer(repo, m_db, equipmentId);
    if (created == 0) {
        qWarning() << "ensureComponentContainer failed for equipment" << equipmentId;
    }
    return created;
}

QString TModelAutoGenerator::getDefaultVariables(const QString &portType)
{
    if (portType == "electric")
        return "i,u";
    else if (portType == "hydraulic")
        return "p,q";
    else if (portType == "mechanical")
        return "F,x";
    return "";
}

QString TModelAutoGenerator::getDefaultMacro(const QString &portType)
{
    if (portType == "electric")
        return "electric-connect";
    else if (portType == "hydraulic")
        return "hydraulic-connect";
    else if (portType == "mechanical")
        return "mechanical-connect";
    return "";
}

QString TModelAutoGenerator::buildPortListPreview(const ComponentInfo &comp)
{
    QString result;
    // 如果已有端口，直接列出
    if (!comp.ports.isEmpty()) {
        for (const auto &p : comp.ports) {
            QString key = p.first + "." + p.second;
            QString portTypeInfo = "";
            // 从已加载的配置中获取端口类型
            if (m_portConfigs.contains(key) && !m_portConfigs.value(key).portType.trimmed().isEmpty()) {
                portTypeInfo = QString(" [类型: %1]").arg(m_portConfigs.value(key).portType);
            }
            result += QString("- 功能子块: %1, 端口: %2%3\n").arg(p.first, p.second, portTypeInfo);
        }
        return result.trimmed();
    }
    
    // 无数据库模式：无法查询 TermInfo，直接返回占位说明
    if (!m_useDatabaseMode) {
        result = "(无数据库模式：使用预设端口数据)";
        return result;
    }
    
    // 数据库模式：无端口时，复用 buildPortTypePrompt 的回退逻辑：尝试 TermInfo
    QSqlQuery q(m_db);
    q.prepare("SELECT DISTINCT Spurr_DT, TermNum FROM TermInfo WHERE Equipment_ID = ? AND TermNum != ''");
    q.addBindValue(comp.equipmentId);
    if (q.exec()) {
        while (q.next()) {
            QString fb = q.value(0).toString();
            QString pn = q.value(1).toString();
            if (!fb.isEmpty() && !pn.isEmpty()) {
                QString key = fb + "." + pn;
                QString portTypeInfo = "";
                if (m_portConfigs.contains(key) && !m_portConfigs.value(key).portType.trimmed().isEmpty()) {
                    portTypeInfo = QString(" [类型: %1]").arg(m_portConfigs.value(key).portType);
                }
                result += QString("-- 功能子块: %1, 端口: %2%3\n").arg(fb, pn, portTypeInfo);
            }
        }
    }
    if (result.isEmpty()) {
        // 最终仍无数据时给出占位说明
        result = "(当前未找到端口定义，将在提示词中使用占位假设: 启动回路.IN, 启动回路.OUT, 反馈回路.IN, 数字输出.OUT)";
    }
    return result;
}

// ========== 提示词生成 ==========

QString TModelAutoGenerator::buildSystemPrompt()
{
    // 第一阶段系统提示：仅端口类型识别
    return
        "你是一个器件端口类型识别助手。\n"
        "端口类型枚举: electric(电气), hydraulic(液压), mechanical(机械)。\n"
        "根据器件描述与端口名称，补全为空的端口类型。\n"
        "输出: 仅 JSON {\"ports\": [ {functionBlock, portName, portType}, ... ] }，只包含本轮新识别条目。\n"
        "不要输出解释、空数组或重复已有类型。";
}

QString TModelAutoGenerator::buildModelSystemPrompt()
{
    return QString(
        "你是测试性建模专家，需生成完整 T 语言模型。\n\n"
        
        "【输出格式】\n"
        "第1部分：JSON 常量定义（若无常量可省略）\n"
        "  - 直接输出 JSON 对象，不要用代码块围栏（不要用 ```json 或 '''json）\n"
        "  - 格式：{\"常量定义\": {\"常量名\": 数值, ...}}\n"
        "第2部分：空行\n"
        "第3部分：SMT-LIB2 代码，包含三个章节：\n"
        "  ;;内部变量定义\n"
        "  ;;正常模式\n"
        "  ;;故障模式\n\n"
        
        "【常量定义规则】\n"
        "- JSON格式：{\"常量定义\": {\"常量名\": 数值, ...}}\n"
        "- 常量名要简洁有意义（如Resistance、RatedVoltage、MaxPressure）\n"
        "- 常量值只能是数字，不要用字符串\n"
        "- 不要用代码块标记包裹 JSON\n\n"
        
        "【内部变量定义规则】\n"
        "- 使用 (declare-fun %Name%.变量名 () Real) 或 (declare-fun %Name%.变量名 () Bool)\n"
        "- 变量名建议：电阻R、液阻r、动作状态act、设定压力SetPressure 等\n"
        "- 可以为端口组合定义变量（如 %Name%.A1_A2.R 表示A1-A2端口间的电阻）\n\n"
        
        "【正常模式规则】\n"
        "- 完整描述器件正常工作时的约束关系\n"
        "- 引用常量用 %常量名%（如 %Resistance%、%RatedVoltage%）\n"
        "- 引用端口变量用完整路径（如 %Name%.A1.i、%Name%.A1.u）\n"
        "- 重要约束：;;正常模式中使用的所有变量，必须来自 ';;端口变量定义' 或 ';;内部变量定义,不允许使用未声明的变量！\n"
        "- 常见约束关系：\n"
        "- 基尔霍夫电流定律：(assert (= (+ %Name%.1.i %Name%.2.i) 0))\n"
        "- 欧姆定律：(assert (= (* %Name%.i %Name%.R) %Name%.u))\n"
        "- 条件约束用 ite：(assert (ite 条件 结果1 结果2))\n"
        "- 逻辑蕴含用 =>：(assert (=> 条件 结果))\n\n"
        
        "【故障模式规则】\n"
        "- 每个故障独立完整建模（不要只修改正常模式的某个值）\n"
        "- 可选：在 ;;故障模式 后添加 ;;公共开始，写公共约束，然后每个故障模式只需写差异部分\n"
        "- 每个故障以 ;;故障名称 开头（如 ;;线圈开路、;;绕组开路、;;转轴卡滞）\n"
        "- 重要约束：;;故障模式中使用的所有变量，必须来自 ';;端口变量定义' 或 ';;内部变量定义,不允许使用未声明的变量！\n"
        "- 常见故障类型：\n"
        "  * 开路：电阻 > 100000000\n"
        "  * 短路：电阻 < 1 或阻值很小\n"
        "  * 不动作：act = false 且其他正常\n"
        "  * 接触不良：特定端口电流为0或阻抗很大\n"
        "  * 卡滞：机械端口速度 x = 0\n"
        "  * 泄漏：压力或流量异常\n\n"
        
        "【注释规则（重要）】\n"
        "- 两个分号(;;)是关键字标记，仅用于：章节名（;;内部变量定义、;;正常模式、;;故障模式）、故障名（;;线圈开路）、特殊标记（;;公共开始、;;公共结束）\n"
        "- 普通注释必须用单个分号(;)，例如：\n"
        "  ; 这是电阻值\n"
        "  (assert (= %Name%.R 22))  ; 设置电阻为22欧姆\n"
        "- 不要在代码中使用两个分号作为普通注释\n\n"
        
        "【完整示例：电机】\n"
        "{\"常量定义\": {\"Resistance\": 22, \"OutputF\": 1200, \"ActCurrent\": 0.8, \"RatedVoltage\": 220}}\n\n"
        ";;内部变量定义\n"
        "(declare-fun %Name%.M1.act () Bool)  ; 电机动作状态\n"
        "(declare-fun %Name%.A_B.R () Real)   ; A-B端口间电阻\n\n"
        ";;正常模式\n"
        "; 电阻约束\n"
        "(assert (= %Name%.A_B.R %Resistance%))\n"
        "(assert (>= %Name%.A_B.i 0))\n"
        "; 欧姆定律\n"
        "(assert (= (* %Name%.A_B.i %Name%.A_B.R) %Name%.A_B.u))\n"
        "; 电压范围判断电机是否动作\n"
        "(assert (ite (and (>= %Name%.A_B.u (* %RatedVoltage% 0.8)) (<= %Name%.A_B.u (* %RatedVoltage% 1.2))) (= %Name%.M1.act true) (= %Name%.M1.act false)))\n"
        "; 动作时输出力和位移\n"
        "(assert (ite (= %Name%.M1.act true) (and (> %Name%.M1.x 0) (> %Name%.M1.F 0)) (= %Name%.M1.x 0)))\n\n"
        ";;故障模式\n"
        ";;公共开始\n"
        "; 故障时的公共约束\n"
        "(assert (= (* %Name%.A_B.i %Name%.A_B.R) %Name%.A_B.u))\n"
        "(assert (= %Name%.M1.act false))  ; 故障时不动作\n"
        "(assert (= %Name%.M1.x 0))        ; 故障时无位移\n\n"
        ";;绕组开路\n"
        "; 开路时电阻极大\n"
        "(assert (> %Name%.A_B.R 100000000))\n\n"
        ";;转轴卡滞\n"
        "; 卡滞时电阻正常但无法输出\n"
        "(assert (= %Name%.A_B.R %Resistance%))\n\n"
        ";;公共结束\n"
        
        "【注意事项】\n"
        "- 不要重复输出 ;;端口变量定义（已在用户输入中提供）\n"
        "- 严格约束：;;正常模式和;;故障模式中使用的所有变量，必须且仅能来自以下两个范围：\n"
        "  1. ';;端口变量定义' - 用户输入中已提供的端口变量（如 %Name%.A1.i、%Name%.A1.u）\n"
        "  2. ';;内部变量定义' - 你在输出中定义的内部变量（如 %Name%.act、%Name%.R）\n"
        "  禁止使用任何未在这两部分声明的变量！\n"
        "- 数值计算注意物理单位一致性\n"
        "- 故障模式要覆盖器件的主要失效模式\n"
        "- 记住：单分号(;)用于普通注释，双分号(;;)仅用于关键字标记\n"
    );
}

QString TModelAutoGenerator::buildModelUserPrompt(const ComponentInfo &comp, const QString &portVarsDef)
{
    QString s;
    s += QString("器件信息:\n- 代号: %1\n- 名称: %2\n- 描述: %3\n\n").arg(comp.code, comp.name, comp.description);
    
    // 添加端口描述信息（如果存在）
    if (!comp.portDescriptions.isEmpty()) {
        s += "功能子块描述:\n";
        for (auto it = comp.portDescriptions.constBegin(); it != comp.portDescriptions.constEnd(); ++it) {
            s += QString("%1：%2\n").arg(it.key(), it.value());
        }
        s += "\n";
    }
    
    s += "已有 ';;端口变量定义' 内容 (保持不变, 不要重复声明):\n";
    s += portVarsDef + "\n\n";
    s += "请输出 JSON 常量定义 + 三个分段 (内部变量/正常模式/故障模式)。\n";
    s += "重要：JSON 不要用代码块标记（```json 或 '''json），直接输出裸 JSON 对象。\n\n";
    s += "变量使用严格约束：\n";
    s += "在 ;;正常模式 和 ;;故障模式 中使用的所有变量，必须来自：\n";
    s += "1. 上述 ';;端口变量定义' 中已声明的端口变量\n";
    s += "2. 你在 ';;内部变量定义' 中声明的内部变量\n";
    s += "禁止使用任何未声明的变量！";
    return s;
}

bool TModelAutoGenerator::parseModelFullResponse(const QString &output, QString &constantsJson, QString &modelBody)
{
    QString jsonPart;
    int endPos = -1;
    
    // 1. 提取第一个 JSON 对象或数组
    if (!findFirstJson(output, jsonPart, endPos)) {
        logMessage("警告: 未找到 JSON 常量定义，可能无常量");
        // 无 JSON 也可以接受，整个输出作为模型体
        constantsJson.clear();
        modelBody = stripFenceWrappers(output).trimmed();
        return !modelBody.isEmpty();
    }
    
    // 2. 解析 JSON
    QJsonParseError perr;
    QJsonDocument jdoc = QJsonDocument::fromJson(jsonPart.toUtf8(), &perr);
    if (perr.error != QJsonParseError::NoError) {
        logMessage(QString("JSON 解析失败: %1 (偏移: %2)").arg(perr.errorString()).arg(perr.offset));
        logMessage(QString("JSON 片段: %1").arg(jsonPart.left(200)));
        return false;
    }
    
    // 3. 提取常量定义
    if (jdoc.isObject()) {
        QJsonObject root = jdoc.object();
        if (root.contains("常量定义")) {
            QJsonValue v = root.value("常量定义");
            if (v.isObject()) {
                constantsJson = QJsonDocument(v.toObject()).toJson(QJsonDocument::Compact);
            } else if (v.isArray()) {
                constantsJson = QJsonDocument(v.toArray()).toJson(QJsonDocument::Compact);
            } else {
                constantsJson.clear();
            }
        } else {
            // 整个对象就是常量定义
            constantsJson = jdoc.toJson(QJsonDocument::Compact);
        }
    } else if (jdoc.isArray()) {
        constantsJson = jdoc.toJson(QJsonDocument::Compact);
    }
    
    // 4. 提取模型体（JSON 之后的内容）
    modelBody = output.mid(endPos).trimmed();
    modelBody = stripFenceWrappers(modelBody).trimmed();
    
    logMessage(QString("JSON 常量解析成功，长度: %1，模型体长度: %2")
        .arg(constantsJson.length()).arg(modelBody.length()));
    
    return true;
}

QString TModelAutoGenerator::buildPortVarsSection(const ComponentInfo &comp) const
{
    // 构建实际存在的端口集合（用于过滤历史脏数据）
    QSet<QString> actualPorts;
    for (const auto &p : comp.ports) {
        actualPorts.insert(p.second);  // portName
    }
    
    // 日志：如果配置中有端口不在实际列表中，记录警告
    QStringList skippedPorts;
    for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
        const PortTypeConfig &cfg = it.value();
        if (!actualPorts.contains(cfg.portName)) {
            skippedPorts.append(cfg.portName);
        }
    }
    if (!skippedPorts.isEmpty()) {
        // 使用 qWarning 而非 logMessage，因为本函数是 const
        qWarning() << QString("警告: 跳过数据库中存在但器件实际不存在的端口: %1").arg(skippedPorts.join(", "));
    }
    
    QString result;
    QSet<QString> seen; // 用于去重
    for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
        const PortTypeConfig &cfg = it.value();
        
        // 关键：只处理实际存在的端口，跳过历史遗留配置
        if (!actualPorts.contains(cfg.portName)) {
            continue;
        }
        
        QStringList vars = cfg.variables.split(QRegExp("[,;，；]"), QString::SkipEmptyParts);
        for (QString v : vars) {
            v = v.trimmed(); if (v.isEmpty()) continue;
            QString line = QString("(declare-fun %Name%.%1.%2 () Real)").arg(cfg.portName, v);
            if (seen.contains(line)) continue;
            seen.insert(line);
            result += line + "\n";
        }
    }
    return result.trimmed();
}

QString TModelAutoGenerator::extractPortVarsFromDialog() const
{
    if (!m_unitManageDialog) return QString();
    QsciScintilla *edit = m_unitManageDialog->QsciEdit;
    if (!edit) return QString();
    QString text = edit->text();
    QStringList lines = text.split('\n');
    bool in=false; QString collected;
    for (const QString &line : lines) {
        QString t=line.trimmed();
        if (t==";;端口变量定义") { in=true; continue; }
        if (in && t.startsWith(";;") && t!=";;端口变量定义") break;
        if (in) collected += line + "\n";
    }
    return collected.trimmed();
}

// ===== JSON 提取辅助 =====
bool TModelAutoGenerator::findFirstJson(const QString &text, QString &jsonOut, int &endPos) const
{
    jsonOut.clear(); 
    endPos = -1;
    if (text.isEmpty()) return false;
    
    // 先去除围栏（支持 ```json 和 '''json）
    QString working = stripFenceWrappers(text);
    
    // 查找第一个 JSON 对象 {...} 或数组 [...]
    int start = -1;
    QChar startCh;
    int depth = 0;
    bool inStr = false;
    bool esc = false;
    
    for (int i = 0; i < working.size(); ++i) {
        QChar c = working[i];
        
        // 查找起始字符
        if (start == -1) {
            if (c == '{' || c == '[') {
                start = i;
                startCh = c;
                depth = 1;
                continue;
            }
            continue;
        }
        
        // 处理字符串内容（忽略字符串中的特殊字符）
        if (inStr) {
            if (esc) {
                esc = false;
            } else if (c == '\\') {
                esc = true;
            } else if (c == '"') {
                inStr = false;
            }
            continue;
        }
        
        // 进入字符串
        if (c == '"') {
            inStr = true;
            continue;
        }
        
        // 处理嵌套深度
        if (startCh == '{') {
            if (c == '{') {
                depth++;
            } else if (c == '}') {
                depth--;
                if (depth == 0) {
                    endPos = i + 1;
                    break;
                }
            }
        } else if (startCh == '[') {
            if (c == '[') {
                depth++;
            } else if (c == ']') {
                depth--;
                if (depth == 0) {
                    endPos = i + 1;
                    break;
                }
            }
        }
    }
    
    if (start == -1 || endPos == -1) {
        return false;
    }
    
    jsonOut = working.mid(start, endPos - start).trimmed();
    return true;
}

QString TModelAutoGenerator::serializeConstants(const QMap<QString, QString> &constantsMap) const
{
    // UI 的保存格式: name,value,unit,remark; 此处缺少单位与备注，留空
    QStringList items;
    for (auto it = constantsMap.begin(); it != constantsMap.end(); ++it) {
        const QString &name = it.key();
        const QString &value = it.value();
        if (name.trimmed().isEmpty()) continue;
        items << QString("%1,%2,,").arg(name, value); // 单位与备注留空
    }
    return items.join(";");
}

QString TModelAutoGenerator::deduplicateLines(const QString &text) const
{
    QStringList lines = text.split('\n', QString::SkipEmptyParts);
    QSet<QString> seen; QStringList out;
    for (QString l : lines) { l = l.trimmed(); if (l.isEmpty()) continue; if (seen.contains(l)) continue; seen.insert(l); out << l; }
    return out.join("\n");
}

bool TModelAutoGenerator::saveFullModel(int equipmentId, const QString &tmodel, const QMap<QString, QString> &constantsMap)
{
    // 无数据库模式：发出请求信号
    if (!m_useDatabaseMode) {
        logMessage("无数据库模式：请求保存完整模型");
        emit requestSaveModel(equipmentId, tmodel, constantsMap);
        return true;
    }

    // 数据库模式：直接保存
    QString structureData = serializeConstants(constantsMap);
    QSqlQuery query(m_db);
    query.prepare("UPDATE Equipment SET TModel = :TModel, Structure = :Structure WHERE Equipment_ID = :EID");
    query.bindValue(":TModel", tmodel);
    query.bindValue(":Structure", structureData);
    query.bindValue(":EID", equipmentId);
    if (!query.exec()) {
        logMessage("保存完整模型失败: " + query.lastError().text());
        return false;
    }
    return true;
}

QString TModelAutoGenerator::normalizeConstantValue(const QString &value) const
{
    QString v = value.trimmed();
    if (v.compare("true", Qt::CaseInsensitive)==0) return "true";
    if (v.compare("false", Qt::CaseInsensitive)==0) return "false";
    // 科学计数法匹配：可含正负号与小数点
    static QRegularExpression sciRe("^[+-]?(?:\\d+\\.?\\d*|\\d*\\.?\\d+)[eE][+-]?\\d+$");
    if (sciRe.match(v).hasMatch()) {
        bool ok=false; double d = v.toDouble(&ok);
        if (ok) {
            // 使用最大精度避免科学计数法，再去除尾部多余0
            QString plain = QString::number(d, 'f', 15); // 15位小数
            // 去除多余尾随0与可能的点
            while (plain.contains('.') && plain.endsWith('0')) plain.chop(1);
            if (plain.endsWith('.')) plain.chop(1);
            return plain;
        }
    }
    return v;
}

void TModelAutoGenerator::normalizeConstantsMap(QMap<QString, QString> &map) const
{
    for (auto it = map.begin(); it != map.end(); ++it) {
        it.value() = normalizeConstantValue(it.value());
    }
}

bool TModelAutoGenerator::clearExistingTModel(int equipmentId)
{
    // 无数据库模式：发出信号请求清空
    if (!m_useDatabaseMode) {
        logMessage("无数据库模式：请求清空 T 模型");
        emit requestClearModel(equipmentId);
        return true;
    }

    // 数据库模式：直接清空
    QSqlQuery query(m_db);
    query.prepare("UPDATE Equipment SET TModel = '' WHERE Equipment_ID = ?");
    query.addBindValue(equipmentId);
    if (!query.exec()) {
        logMessage("清空旧 T 模型失败: " + query.lastError().text());
        return false;
    }
    return true;
}

QString TModelAutoGenerator::stripFenceWrappers(const QString &text) const
{
    QString t = text.trimmed();
    
    // 修复正则表达式：\\s* 不是 \\\\s*
    // 支持多种围栏格式：```json、```、'''json、'''
    // 捕获完整 fenced 块（开始和结束围栏）
    QRegularExpression fullFence(
        "^(?:```+|'''+)\\s*(json|JSON)?\\s*[\\r\\n]+([\\s\\S]*?)[\\r\\n]+(?:```+|'''+)\\s*$", 
        QRegularExpression::CaseInsensitiveOption
    );
    QRegularExpressionMatch m = fullFence.match(t);
    if (m.hasMatch()) {
        return m.captured(2).trimmed();
    }
    
    // 去除单侧围栏（只有开始或只有结束）
    QRegularExpression startFence("^(?:```+|'''+)\\s*(json|JSON)?\\s*[\\r\\n]*", QRegularExpression::CaseInsensitiveOption);
    QRegularExpression endFence("[\\r\\n]*(?:```+|'''+)\\s*$");
    t.remove(startFence);
    t.remove(endFence);
    
    return t.trimmed();
}

QString TModelAutoGenerator::buildPortTypePrompt(const ComponentInfo &comp)
{
    // 1. 基本器件信息
    QString prompt = QString(
        "器件信息:\n"
        "- 代号: %1\n"
        "- 名称: %2\n"
        "- 描述: %3\n\n"
    ).arg(comp.code, comp.name, comp.description);
    
    // 1.5. 添加端口描述信息（如果存在）
    if (!comp.portDescriptions.isEmpty()) {
        prompt += "功能子块描述:\n";
        for (auto it = comp.portDescriptions.constBegin(); it != comp.portDescriptions.constEnd(); ++it) {
            prompt += QString("%1：%2\n").arg(it.key(), it.value());
        }
        prompt += "\n";
    }
    
    prompt += "端口列表(JSON，portType为空表示待识别):\n";

    // 2. 构造当前端口 JSON（已有类型保留，未识别为空）
    QString portsJson = buildPortTypeJson(comp);

    // 如果为空数组，执行旧的回退策略，填充占位端口供模型推断
    QJsonDocument doc = QJsonDocument::fromJson(portsJson.toUtf8());
    bool needFallback = true;
    if (doc.isObject()) {
        QJsonArray arr = doc.object().value("ports").toArray();
        if (!arr.isEmpty()) needFallback = false;
    }
    if (needFallback) {
        QJsonArray arr;
        auto addPlaceholder = [&](const QString &fb, const QString &pn){ QJsonObject o; o["functionBlock"] = fb; o["portName"] = pn; o["portType"] = ""; arr.append(o); };
        addPlaceholder("启动回路", "IN");
        addPlaceholder("启动回路", "OUT");
        addPlaceholder("反馈回路", "IN");
        addPlaceholder("数字输出", "OUT");
        QJsonObject root; root["ports"] = arr;
        portsJson = QString::fromUtf8(QJsonDocument(root).toJson(QJsonDocument::Indented));
    }

    prompt += portsJson + "\n\n";

    // 3. 任务说明：仅补全本轮仍为空的端口类型，并且只输出新增识别条目
    prompt +=
        "任务: 根据器件描述与端口名称，推断所有 portType 为空的端口的类型(electric/hydraulic/mechanical)。\n"
        "输出要求: 只输出一个 JSON 对象，包含本轮新识别出的端口条目（即先前 portType 为空且你已填写的那些），其它已有类型的端口不要重复输出。\n"
        "输出示例:\n"
        "{\n"
        "  \"ports\": [\n"
        "    {\"functionBlock\": \"Coil\", \"portName\": \"A1\", \"portType\": \"electric\"}\n"
        "  ]\n"
        "}\n"
        "注意: 不要添加说明文字、不要输出空数组、不要包含已有类型的端口。";

    return prompt;
}

QString TModelAutoGenerator::buildInternalVarsPrompt(const ComponentInfo &comp)
{
    QString prompt = QString(
        "器件信息:\n"
        "- 代号: %1\n"
        "- 名称: %2\n"
        "- 描述: %3\n\n"
        "端口配置:\n"
    ).arg(comp.code, comp.name, comp.description);
    if (m_portConfigs.isEmpty()) {
        prompt += "(端口类型尚未识别成功，假设存在: 启动回路.IN, 启动回路.OUT, 反馈回路.IN, 数字输出.OUT)\n";
    } else {
        for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
            const PortTypeConfig &config = it.value();
            prompt += QString("- %1.%2: %3 (%4)\n")
                .arg(config.functionBlock, config.portName, config.portType, config.variables);
        }
    }

    prompt +=
        "\n请生成该器件的内部变量定义（SMT-LIB2 格式）。\n"
        "内部变量可能包括: 电阻R、液阻r、阻尼Z 等。\n"
        "示例:\n"
        "(declare-const %Name%.R Real)  ; 电阻（单分号注释）\n"
        "(assert (> %Name%.R 0))        ; 电阻大于0\n\n"
        "注意:\n"
        "- 只输出 SMT-LIB2 代码，不要包含其他说明文字\n"
        "- 普通注释用单分号(;)，不要用双分号(;;)\n";

    return prompt;
}

QString TModelAutoGenerator::buildNormalModePrompt(const ComponentInfo &comp)
{
    QString prompt = QString(
        "器件信息:\n"
        "- 代号: %1\n"
        "- 名称: %2\n"
        "- 描述: %3\n\n"
        "端口配置:\n"
    ).arg(comp.code, comp.name, comp.description);
    if (m_portConfigs.isEmpty()) {
        prompt += "(端口类型未确定，假设: START.IN, START.OUT, FEEDBACK.IN, DIGOUT.OUT)\n";
    } else {
        for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
            const PortTypeConfig &config = it.value();
            prompt += QString("- %1.%2: %3 (%4)\n")
                .arg(config.functionBlock, config.portName, config.portType, config.variables);
        }
    }

    prompt += QString("\n内部变量定义:\n%1\n").arg(m_internalVarsDef);

    prompt +=
        "\n请生成该器件的正常模式约束（SMT-LIB2 格式）。\n"
        "正常模式描述器件正常工作时端口变量和内部变量之间的关系。\n"
        "示例:\n"
        "; 欧姆定律约束（单分号注释）\n"
        "(assert (= %Name%.Coil.A1.u (+ %Name%.Coil.A2.u (* %Name%.Coil.A1.i %Name%.R))))\n"
        "; 电流非负\n"
        "(assert (>= %Name%.Coil.A1.i 0))\n\n"
        "注意:\n"
        "- 只输出 SMT-LIB2 代码，不要包含其他说明文字\n"
        "- 普通注释用单分号(;)，不要用双分号(;;)\n";

    return prompt;
}

QString TModelAutoGenerator::buildFailureModePrompt(const ComponentInfo &comp)
{
    QString prompt = QString(
        "器件信息:\n"
        "- 代号: %1\n"
        "- 名称: %2\n"
        "- 描述: %3\n\n"
        "端口配置:\n"
    ).arg(comp.code, comp.name, comp.description);
    if (m_portConfigs.isEmpty()) {
        prompt += "(端口类型未确定，假设: START.IN, START.OUT, FEEDBACK.IN, DIGOUT.OUT)\n";
    } else {
        for (auto it = m_portConfigs.constBegin(); it != m_portConfigs.constEnd(); ++it) {
            const PortTypeConfig &config = it.value();
            prompt += QString("- %1.%2: %3 (%4)\n")
                .arg(config.functionBlock, config.portName, config.portType, config.variables);
        }
    }

    prompt += QString("\n内部变量定义:\n%1\n").arg(m_internalVarsDef);
    prompt += QString("\n正常模式:\n%1\n").arg(m_normalModeDef);

    prompt +=
        "\n请生成该器件的常见故障模式（SMT-LIB2 格式）。\n"
        "故障模式描述器件发生故障时的行为，常见故障包括: 开路、短路、参数漂移等。\n"
        "每个故障模式用一个或一组 assert 定义，且一个器件的多个故障模式名称不均不能相同。\n"
        "示例:\n"
        ";;开路\n"
        "; 开路时电阻极大（单分号注释）\n"
        "(assert (> %Name%.Coil.R 1000000))\n\n"
        ";;短路\n"
        "; 短路时电阻接近零\n"
        "(assert (< %Name%.Coil.R 1))\n\n"
        "注意:\n"
        "- 只输出 SMT-LIB2 代码，不要包含其他说明文字\n"
        "- 故障名称用双分号(;;)，如 ;;开路、;;短路\n"
        "- 普通注释用单分号(;)，不要用双分号(;;)\n";

    return prompt;
}

// ========== 新增：端口类型识别辅助实现（此前声明但未实现） ==========

QString TModelAutoGenerator::canonicalKey(const QString &s) const
{
    QString r; r.reserve(s.size());
    for (QChar c : s) {
        if (c.isLetterOrNumber()) r.append(c.toLower());
    }
    return r;
}

int TModelAutoGenerator::levenshteinDistance(const QString &a, const QString &b) const
{
    const int n = a.size();
    const int m = b.size();
    if (n == 0) return m;
    if (m == 0) return n;
    QVector<int> prev(m + 1), cur(m + 1);
    for (int j = 0; j <= m; ++j) prev[j] = j;
    for (int i = 1; i <= n; ++i) {
        cur[0] = i;
        for (int j = 1; j <= m; ++j) {
            int cost = (a[i - 1] == b[j - 1]) ? 0 : 1;
            cur[j] = qMin(qMin(cur[j - 1] + 1, prev[j] + 1), prev[j - 1] + cost);
        }
        prev = cur;
    }
    return cur[m];
}

void TModelAutoGenerator::loadExistingPortTypes(int equipmentId)
{
    m_portConfigs.clear();
    
    // 无数据库模式：无需加载
    if (!m_useDatabaseMode) {
        return;
    }
    
    int containerId = resolveContainerId(equipmentId, false);
    if (containerId <= 0) return;
    QSqlQuery q(m_db);
    q.prepare("SELECT function_block, port_name, port_type, variables_json, connect_macro FROM port_config WHERE container_id=?");
    q.addBindValue(containerId);
    if (q.exec()) {
        while (q.next()) {
            PortTypeConfig cfg;
            cfg.functionBlock = q.value(0).toString();
            cfg.portName = q.value(1).toString();
            cfg.portType = q.value(2).toString();
            // 变量回填：解析数组，兼容旧格式单条包含逗号的情况
            const QString varsJson = q.value(3).toString();
            if (!varsJson.trimmed().isEmpty()) {
                QJsonDocument doc = QJsonDocument::fromJson(varsJson.toUtf8());
                if (doc.isArray()) {
                    QStringList varNames;
                    for (auto v : doc.array()) if (v.isObject()) {
                        QString nm = v.toObject().value("name").toString().trimmed();
                        if (nm.contains(',')) {
                            QStringList parts = nm.split(QRegExp("[,;，；]"), QString::SkipEmptyParts);
                            for (QString p : parts) { p = p.trimmed(); if (!p.isEmpty()) varNames << p; }
                        } else if (!nm.isEmpty()) varNames << nm;
                    }
                    cfg.variables = varNames.join(",");
                }
            }
            if (cfg.variables.trimmed().isEmpty()) cfg.variables = getDefaultVariables(cfg.portType);
            cfg.connectMacro = q.value(4).toString();
            if (cfg.connectMacro.trimmed().isEmpty()) cfg.connectMacro = getDefaultMacro(cfg.portType);
            QString key = cfg.functionBlock + "." + cfg.portName;
            m_portConfigs.insert(key, cfg);
        }
    }
}

QString TModelAutoGenerator::buildPortTypeJson(const ComponentInfo &comp)
{
    // 使用预加载端口或组件端口作为基准
    QList<QPair<QString, QString>> sourcePorts = !m_preloadedPorts.isEmpty() ? m_preloadedPorts : comp.ports;
    QJsonArray arr;
    for (const auto &p : sourcePorts) {
        QString key = p.first + "." + p.second;
        QJsonObject obj;
        obj["functionBlock"] = p.first;
        obj["portName"] = p.second;
        if (m_portConfigs.contains(key) && !m_portConfigs.value(key).portType.trimmed().isEmpty()) {
            obj["portType"] = m_portConfigs.value(key).portType;
        } else {
            obj["portType"] = ""; // 空表示待识别
        }
        arr.append(obj);
    }
    QJsonObject root; root["ports"] = arr;
    return QString::fromUtf8(QJsonDocument(root).toJson(QJsonDocument::Indented));
}

void TModelAutoGenerator::loadPortsFromDatabase(const QSqlDatabase &db, int equipmentId, QList<QPair<QString, QString>> &ports, QMap<QString, QString> *portDescriptions)
{
    ports.clear();
    if (portDescriptions) {
        portDescriptions->clear();
    }
    
    // 按照新的逻辑从 EquipmentTemplate 表加载端口和描述
    QSqlQuery query(db);
    query.prepare("SELECT SpurDT, ConnNum, ConnDesc FROM EquipmentTemplate WHERE Equipment_ID = ?");
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        qWarning() << QString("查询 EquipmentTemplate 失败: %1").arg(query.lastError().text());
        return;
    }
    
    while (query.next()) {
        QString spurDT = query.value("SpurDT").toString().trimmed();
        QString connNum = query.value("ConnNum").toString().trimmed();
        QString connDesc = query.value("ConnDesc").toString().trimmed();
        
        // 功能子块名称：优先使用 SpurDT，如果为空则使用 ConnNum
        QString functionBlock = spurDT.isEmpty() ? connNum : spurDT;
        
        if (functionBlock.isEmpty() || connNum.isEmpty()) {
            continue;
        }
        
        // 保存端口描述（如果 ConnDesc 不为空且与 ConnNum 不完全相同）
        if (portDescriptions && !connDesc.isEmpty() && connDesc != connNum) {
            portDescriptions->insert(functionBlock, connDesc);
        }
        
        // 将 ConnNum 按 ￤ 分解为多个端口
        QStringList portNames = connNum.split("￤", QString::SkipEmptyParts);
        for (const QString &portName : portNames) {
            QString trimmedPortName = portName.trimmed();
            if (!trimmedPortName.isEmpty()) {
                ports.append(qMakePair(functionBlock, trimmedPortName));
            }
        }
    }
}

void TModelAutoGenerator::loadPortConfigsForEquipment(const QSqlDatabase &db, int equipmentId, QMap<QString, PortTypeConfig> &portConfigs)
{
    portConfigs.clear();
    
    // 1. 先找到 container_id
    QSqlQuery containerQuery(db);
    containerQuery.prepare("SELECT container_id FROM equipment_containers WHERE equipment_id = ?");
    containerQuery.addBindValue(equipmentId);
    
    if (!containerQuery.exec()) {
        qWarning() << QString("查询 equipment_containers 失败: %1").arg(containerQuery.lastError().text());
        return;
    }
    
    if (!containerQuery.next()) {
        // 没有 container_id，说明还没有配置端口信息
        return;
    }
    
    int containerId = containerQuery.value(0).toInt();
    
    // 2. 使用 container_id 查询 port_config
    QSqlQuery portConfigQuery(db);
    portConfigQuery.prepare(
        "SELECT function_block, port_name, port_type, variables_json, connect_macro "
        "FROM port_config WHERE container_id = ?"
    );
    portConfigQuery.addBindValue(containerId);
    
    if (!portConfigQuery.exec()) {
        qWarning() << QString("查询 port_config 失败: %1").arg(portConfigQuery.lastError().text());
        return;
    }
    
    // 辅助函数：获取默认变量
    auto getDefaultVars = [](const QString &portType) -> QString {
        if (portType == "electric") return "i,u";
        else if (portType == "hydraulic") return "p,q";
        else if (portType == "mechanical") return "F,x";
        return "";
    };
    
    // 辅助函数：获取默认宏
    auto getDefaultMacroFunc = [](const QString &portType) -> QString {
        if (portType == "electric") return "electric-connect";
        else if (portType == "hydraulic") return "hydraulic-connect";
        else if (portType == "mechanical") return "mechanical-connect";
        return "";
    };
    
    while (portConfigQuery.next()) {
        PortTypeConfig cfg;
        cfg.functionBlock = portConfigQuery.value("function_block").toString();
        cfg.portName = portConfigQuery.value("port_name").toString();
        cfg.portType = portConfigQuery.value("port_type").toString();
        
        // 解析变量 JSON
        const QString varsJson = portConfigQuery.value("variables_json").toString();
        if (!varsJson.trimmed().isEmpty()) {
            QJsonDocument doc = QJsonDocument::fromJson(varsJson.toUtf8());
            if (doc.isArray()) {
                QStringList varNames;
                for (auto v : doc.array()) {
                    if (v.isObject()) {
                        QString nm = v.toObject().value("name").toString().trimmed();
                        if (nm.contains(',')) {
                            QStringList parts = nm.split(QRegExp("[,;，；]"), QString::SkipEmptyParts);
                            for (QString p : parts) {
                                p = p.trimmed();
                                if (!p.isEmpty()) varNames << p;
                            }
                        } else if (!nm.isEmpty()) {
                            varNames << nm;
                        }
                    }
                }
                cfg.variables = varNames.join(",");
            }
        }
        
        // 如果变量为空，使用默认变量
        if (cfg.variables.trimmed().isEmpty()) {
            cfg.variables = getDefaultVars(cfg.portType);
        }
        
        cfg.connectMacro = portConfigQuery.value("connect_macro").toString();
        if (cfg.connectMacro.trimmed().isEmpty()) {
            cfg.connectMacro = getDefaultMacroFunc(cfg.portType);
        }
        
        QString key = cfg.functionBlock + "." + cfg.portName;
        portConfigs.insert(key, cfg);
    }
    
    // 已加载端口配置（调试信息移除，避免批量处理时刷屏）
}
