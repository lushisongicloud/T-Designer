#include "tmodelautogenerator.h"
#include "widget/aimodelgeneratordialog.h"
#include "BO/function/tmodelparser.h"
#include "widget/codecheckdialog.h"
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
{
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

void TModelAutoGenerator::startAutoGeneration()
{
    // 初始化日志
    initLogFile();
    
    // 加载组件
    loadComponents();
    
    if (m_components.isEmpty()) {
        QMessageBox::information(nullptr, "提示", "没有需要处理的器件");
        emit finished();
        return;
    }
    
    // 创建并显示对话框
    m_dialog = new AiModelGeneratorDialog();
    m_dialog->setWindowModality(Qt::NonModal);
    m_dialog->show();
    
    logMessage(QString("开始自动生成，共 %1 个器件").arg(m_components.size()));
    // 端口列表预览：在第一阶段请求前先向对话框展示第一个器件的端口列表，方便用户确认
    if (m_dialog && !m_components.isEmpty()) {
        const ComponentInfo &first = m_components.first();
        QString preview = buildPortListPreview(first);
        m_dialog->appendInput("=== 端口列表预览 ===\n" + preview + "\n");
    }

    // 开始处理第一个组件
    m_currentIndex = 0;
    processNextComponent();
}

void TModelAutoGenerator::initLogFile()
{
    QString logPath = QString("tmodel_auto_gen_%1.log")
        .arg(QDateTime::currentDateTime().toString("yyyyMMdd_hhmmss"));
    
    m_logFile = new QFile(logPath);
    if (m_logFile->open(QIODevice::WriteOnly | QIODevice::Text)) {
        m_logStream = new QTextStream(m_logFile);
        m_logStream->setCodec("UTF-8");
    } else {
        qWarning() << "无法创建日志文件:" << logPath;
    }
}

void TModelAutoGenerator::loadComponents()
{
    m_components.clear();

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
            }

            // 若未预加载，则继续原有 DB 读取逻辑：端口来自 port_config 表（如果已经配置）
            // 若 port_config 为空，则尝试从已存在的模板终端表 Equipment_TemplateTerm（兼容旧数据）或 Symb2TermInfo（项目端）加载。

            if (comp.ports.isEmpty()) {
                // 优先：port_config（新建端口配置后保存）
                QSqlQuery portQuery(m_db);
                portQuery.prepare("SELECT function_block, port_name FROM port_config pc "
                                   "INNER JOIN component_container cc ON pc.container_id = cc.container_id "
                                   "WHERE cc.entity_type='equipment_template' AND cc.entity_id = ?");
                portQuery.addBindValue(comp.equipmentId);
                if (portQuery.exec()) {
                    while (portQuery.next()) {
                        comp.ports.append(qMakePair(portQuery.value(0).toString(), portQuery.value(1).toString()));
                    }
                }
            }

            // 兼容：Equipment_TemplateTerm （如果上面没拿到端口）
            if (comp.ports.isEmpty()) {
                QSqlQuery legacyPortQuery(m_db);
                legacyPortQuery.prepare("SELECT Spurr_DT, ConnNumber FROM Equipment_TemplateTerm WHERE EquipmentTemplate_ID = ? AND Spurr_DT != '' AND ConnNumber != ''");
                legacyPortQuery.addBindValue(comp.equipmentId);
                if (legacyPortQuery.exec()) {
                    while (legacyPortQuery.next()) {
                        comp.ports.append(qMakePair(legacyPortQuery.value(0).toString(), legacyPortQuery.value(1).toString()));
                    }
                }
            }

            // 暂不跳过即使没有端口的器件（用户要求：先不要跳过器件）
            logMessage(QString("端口数量: %1").arg(comp.ports.size()));
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

        // 端口（同上策略）
        QSqlQuery portQuery(m_db);
        portQuery.prepare("SELECT function_block, port_name FROM port_config pc "
                           "INNER JOIN component_container cc ON pc.container_id = cc.container_id "
                           "WHERE cc.entity_type='equipment_template' AND cc.entity_id = ?");
        portQuery.addBindValue(comp.equipmentId);
        if (portQuery.exec()) {
            while (portQuery.next()) {
                comp.ports.append(qMakePair(portQuery.value(0).toString(), portQuery.value(1).toString()));
            }
        }
        if (comp.ports.isEmpty()) {
            QSqlQuery legacyPortQuery(m_db);
            legacyPortQuery.prepare("SELECT Spurr_DT, ConnNumber FROM Equipment_TemplateTerm WHERE EquipmentTemplate_ID = ? AND Spurr_DT != '' AND ConnNumber != ''");
            legacyPortQuery.addBindValue(comp.equipmentId);
            if (legacyPortQuery.exec()) {
                while (legacyPortQuery.next()) {
                    comp.ports.append(qMakePair(legacyPortQuery.value(0).toString(), legacyPortQuery.value(1).toString()));
                }
            }
        }
        logMessage(QString("  端口数量: %1").arg(comp.ports.size()));

        // 不再跳过无端口器件（满足用户“先不要跳过器件”需求）
        m_components.append(comp);
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
    m_portConfigs.clear();
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
    
    if (m_dialog) {
        m_dialog->setStatus("识别端口类型...");
    }
    
    logMessage("阶段1: 识别端口类型");
    
    QString systemPrompt = buildSystemPrompt();
    QString userPrompt = buildPortTypePrompt(comp);
    
    if (m_dialog) {
        m_dialog->appendInput("=== 系统提示 ===\n" + systemPrompt);
        m_dialog->appendInput("\n=== 用户输入 ===\n" + userPrompt);
    }
    
    m_deepseekClient->chatCompletion(systemPrompt, userPrompt, true);
}

void TModelAutoGenerator::startInternalVarsGeneration()
{
    const ComponentInfo &comp = m_components[m_currentIndex];
    m_currentStage = Stage_InternalVars;
    m_currentReasoning.clear();
    m_currentOutput.clear();
    
    if (m_dialog) {
        m_dialog->setStatus("生成内部变量定义...");
    }
    
    logMessage("阶段2: 生成内部变量定义");
    
    QString systemPrompt = buildSystemPrompt();
    QString userPrompt = buildInternalVarsPrompt(comp);
    
    if (m_dialog) {
        m_dialog->appendInput("\n\n=== 新请求 ===\n");
        m_dialog->appendInput("=== 系统提示 ===\n" + systemPrompt);
        m_dialog->appendInput("\n=== 用户输入 ===\n" + userPrompt);
    }
    
    m_deepseekClient->chatCompletion(systemPrompt, userPrompt, true);
}

void TModelAutoGenerator::startNormalModeGeneration()
{
    const ComponentInfo &comp = m_components[m_currentIndex];
    m_currentStage = Stage_NormalMode;
    m_currentReasoning.clear();
    m_currentOutput.clear();
    
    if (m_dialog) {
        m_dialog->setStatus("生成正常模式...");
    }
    
    logMessage("阶段3: 生成正常模式");
    
    QString systemPrompt = buildSystemPrompt();
    QString userPrompt = buildNormalModePrompt(comp);
    
    if (m_dialog) {
        m_dialog->appendInput("\n\n=== 新请求 ===\n");
        m_dialog->appendInput("=== 系统提示 ===\n" + systemPrompt);
        m_dialog->appendInput("\n=== 用户输入 ===\n" + userPrompt);
    }
    
    m_deepseekClient->chatCompletion(systemPrompt, userPrompt, true);
}

void TModelAutoGenerator::startFailureModeGeneration()
{
    const ComponentInfo &comp = m_components[m_currentIndex];
    m_currentStage = Stage_FailureMode;
    m_currentReasoning.clear();
    m_currentOutput.clear();
    
    if (m_dialog) {
        m_dialog->setStatus("生成故障模式...");
    }
    
    logMessage("阶段4: 生成故障模式");
    
    QString systemPrompt = buildSystemPrompt();
    QString userPrompt = buildFailureModePrompt(comp);
    
    if (m_dialog) {
        m_dialog->appendInput("\n\n=== 新请求 ===\n");
        m_dialog->appendInput("=== 系统提示 ===\n" + systemPrompt);
        m_dialog->appendInput("\n=== 用户输入 ===\n" + userPrompt);
    }
    
    m_deepseekClient->chatCompletion(systemPrompt, userPrompt, true);
}

void TModelAutoGenerator::onReasoningDelta(const QString &delta)
{
    m_currentReasoning += delta;
    if (m_dialog) {
        m_dialog->appendReasoning(delta);
    }
}

void TModelAutoGenerator::onContentDelta(const QString &delta)
{
    m_currentOutput += delta;
    if (m_dialog) {
        m_dialog->appendOutput(delta);
    }
}

void TModelAutoGenerator::onResponseComplete(const QString &reasoning, const QString &content)
{
    logMessage("AI 响应完成");
    logMessage("思考内容: " + reasoning);
    logMessage("输出内容: " + content);
    
    m_currentReasoning = reasoning;
    m_currentOutput = content;
    
    const ComponentInfo &comp = m_components[m_currentIndex];
    
    switch (m_currentStage) {
    case Stage_PortType:
        // 解析端口类型
        if (parsePortTypeResponse(content)) {
            // 保存端口配置
            if (savePortConfigs(comp.equipmentId)) {
                logMessage("端口配置保存成功");
                // 进入下一阶段
                startInternalVarsGeneration();
            } else {
                logMessage("端口配置保存失败");
                moveToNextComponent();
            }
        } else {
            logMessage("端口类型解析失败");
            if (m_retryCount < MAX_RETRIES) {
                m_retryCount++;
                logMessage(QString("重试 %1/%2").arg(m_retryCount).arg(MAX_RETRIES));
                startPortTypeIdentification();
            } else {
                logMessage("达到最大重试次数，跳过此器件");
                moveToNextComponent();
            }
        }
        break;
        
    case Stage_InternalVars:
        m_internalVarsDef = content;
        logMessage("内部变量定义已获取");
        startNormalModeGeneration();
        break;
        
    case Stage_NormalMode:
        m_normalModeDef = content;
        logMessage("正常模式已获取");
        startFailureModeGeneration();
        break;
        
    case Stage_FailureMode:
        m_failureModeDef = content;
        logMessage("故障模式已获取");
        
        // 组装完整的 T 模型
        QString fullTModel = QString(
            ";; 端口变量（由系统自动生成）\n"
            "%PORT_VARS%\n\n"
            ";; 内部变量定义\n"
            "%1\n\n"
            ";; 正常模式\n"
            "%2\n\n"
            ";; 故障模式\n"
            "%3\n"
        ).arg(m_internalVarsDef, m_normalModeDef, m_failureModeDef);
        
        // 校验
        QString errorMsg;
        if (validateTModel(comp.equipmentId, fullTModel, errorMsg)) {
            // 保存
            if (saveTModel(comp.equipmentId, fullTModel)) {
                logMessage("T 模型生成并保存成功");
                moveToNextComponent();
            } else {
                logMessage("T 模型保存失败");
                moveToNextComponent();
            }
        } else {
            logMessage("T 模型校验失败: " + errorMsg);
            if (m_retryCount < MAX_RETRIES) {
                m_retryCount++;
                logMessage(QString("重试 %1/%2").arg(m_retryCount).arg(MAX_RETRIES));
                // 从内部变量开始重新生成
                startInternalVarsGeneration();
            } else {
                logMessage("达到最大重试次数，跳过此器件");
                moveToNextComponent();
            }
        }
        break;
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
            startInternalVarsGeneration();
            break;
        case Stage_NormalMode:
            startNormalModeGeneration();
            break;
        case Stage_FailureMode:
            startFailureModeGeneration();
            break;
        }
    } else {
        logMessage("达到最大重试次数，跳过此器件");
        moveToNextComponent();
    }
}

bool TModelAutoGenerator::parsePortTypeResponse(const QString &output)
{
    // 期望输出格式为 JSON:
    // {
    //   "ports": [
    //     {"functionBlock": "Coil", "portName": "A1", "portType": "electric"},
    //     ...
    //   ]
    // }
    
    QJsonDocument doc = QJsonDocument::fromJson(output.toUtf8());
    if (!doc.isObject()) {
        logMessage("输出不是有效的 JSON 对象");
        return false;
    }
    
    QJsonObject obj = doc.object();
    if (!obj.contains("ports")) {
        logMessage("JSON 中缺少 ports 字段");
        return false;
    }
    
    QJsonArray ports = obj["ports"].toArray();
    m_portConfigs.clear();
    
    for (const QJsonValue &val : ports) {
        if (!val.isObject()) continue;
        
        QJsonObject portObj = val.toObject();
        QString funcBlock = portObj["functionBlock"].toString();
        QString portName = portObj["portName"].toString();
        QString portType = portObj["portType"].toString();
        
        if (funcBlock.isEmpty() || portName.isEmpty() || portType.isEmpty()) {
            continue;
        }
        
        PortTypeConfig config;
        config.functionBlock = funcBlock;
        config.portName = portName;
        config.portType = portType;
        config.variables = getDefaultVariables(portType);
        config.connectMacro = getDefaultMacro(portType);
        
        QString key = funcBlock + "." + portName;
        m_portConfigs[key] = config;
    }
    
    logMessage(QString("解析到 %1 个端口配置").arg(m_portConfigs.size()));
    return !m_portConfigs.isEmpty();
}

bool TModelAutoGenerator::savePortConfigs(int equipmentId)
{
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
        
        if (query.next()) {
            // 更新
            int portConfigId = query.value(0).toInt();
            query.prepare(
                "UPDATE port_config SET port_type = ?, variables_json = ?, connect_macro = ? "
                "WHERE port_config_id = ?"
            );
            query.addBindValue(config.portType);
            query.addBindValue(QString("[{\"name\":\"%1\"}]").arg(config.variables));
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
            query.addBindValue(QString("[{\"name\":\"%1\"}]").arg(config.variables));
            query.addBindValue(config.connectMacro);
        }
        
        if (!query.exec()) {
            logMessage("保存端口配置失败: " + query.lastError().text());
            return false;
        }
    }
    
    return true;
}

bool TModelAutoGenerator::saveTModel(int equipmentId, const QString &tmodel)
{
    QSqlQuery query(m_db);
    query.prepare("UPDATE Equipment_Template SET TModel = ? WHERE Equipment_ID = ?");
    query.addBindValue(tmodel);
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        logMessage("保存 T 模型失败: " + query.lastError().text());
        return false;
    }
    
    return true;
}

bool TModelAutoGenerator::validateTModel(int equipmentId, const QString &tmodel, QString &errorMsg)
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
    qDebug().noquote() << timestampedMsg;
    
    if (m_logStream) {
        *m_logStream << timestampedMsg << "\n";
        m_logStream->flush();
    }
}

void TModelAutoGenerator::moveToNextComponent()
{
    m_currentIndex++;
    QTimer::singleShot(500, this, &TModelAutoGenerator::processNextComponent);
}

void TModelAutoGenerator::finishGeneration()
{
    logMessage("\n========== 自动生成完成 ==========");
    logMessage(QString("共处理 %1 个器件").arg(m_components.size()));
    
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
    QSqlQuery query(m_db);
    
    // 查询是否已存在
    query.prepare(
        "SELECT container_id FROM component_container "
        "WHERE entity_type = 'equipment_template' AND entity_id = ?"
    );
    query.addBindValue(equipmentId);
    
    if (query.exec() && query.next()) {
        return query.value(0).toInt();
    }
    
    if (!createIfMissing) {
        return 0;
    }
    
    // 创建新容器
    query.prepare(
        "INSERT INTO component_container (entity_type, entity_id, container_level) "
        "VALUES ('equipment_template', ?, 'component')"
    );
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        qWarning() << "创建容器失败:" << query.lastError();
        return 0;
    }
    
    return query.lastInsertId().toInt();
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
            result += QString("- 功能子块: %1, 端口: %2\n").arg(p.first, p.second);
        }
        return result.trimmed();
    }
    // 无端口时，复用 buildPortTypePrompt 的回退逻辑：尝试 TermInfo
    QSqlQuery q(m_db);
    q.prepare("SELECT DISTINCT Spurr_DT, TermNum FROM TermInfo WHERE Equipment_ID = ? AND TermNum != ''");
    q.addBindValue(comp.equipmentId);
    if (q.exec()) {
        while (q.next()) {
            QString fb = q.value(0).toString();
            QString pn = q.value(1).toString();
            if (!fb.isEmpty() && !pn.isEmpty()) {
                result += QString("- 功能子块: %1, 端口: %2\n").arg(fb, pn);
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
    return 
        "你是一个专业的测试性建模专家，精通 SMT-LIB2 语法和器件建模。\n"
        "你的任务是根据器件信息生成符合规范的 T 语言模型。\n\n"
        "基本规则:\n"
        "1. 端口类型有三种: electric(电气)、hydraulic(液压)、mechanical(机械)\n"
        "2. 电气端口变量: i(电流)、u(电压)\n"
        "3. 液压端口变量: p(压力)、q(流量)\n"
        "4. 机械端口变量: F(力)、x(位移)\n"
        "5. 使用 SMT-LIB2 语法\n"
        "6. 变量命名格式: %Name%.FunctionBlock.PortName.Variable\n"
        "7. 输出必须是有效的 JSON 格式（对于端口类型识别任务）或 SMT-LIB2 代码（对于模型生成任务）\n";
}

QString TModelAutoGenerator::buildPortTypePrompt(const ComponentInfo &comp)
{
    QString prompt = QString(
        "器件信息:\n"
        "- 代号: %1\n"
        "- 名称: %2\n"
        "- 描述: %3\n\n"
        "端口列表:\n"
    ).arg(comp.code, comp.name, comp.description);
    // 如果端口为空，尝试动态回退查询 TermInfo (旧模板) 与 Symb2TermInfo (项目侧) 补充
    if (comp.ports.isEmpty()) {
        QSqlQuery q(m_db);
        // 回退1: TermInfo 与 Equipment_ID
        q.prepare("SELECT DISTINCT Spurr_DT, TermNum FROM TermInfo WHERE Equipment_ID = ? AND TermNum != ''");
        q.addBindValue(comp.equipmentId);
        if (q.exec()) {
            while (q.next()) {
                QString fb = q.value(0).toString();
                QString pn = q.value(1).toString();
                if (!fb.isEmpty() && !pn.isEmpty()) {
                    prompt += QString("- 功能子块: %1, 端口: %2\n").arg(fb, pn);
                }
            }
        }
        // 回退2: Symb2TermInfo 需要通过 Symbol 查找，此处简化尝试直接列出逻辑端口（若以后需要可扩展）
        // 若仍为空，加入占位说明避免让大模型误判
        if (!prompt.contains("功能子块:")) {
            prompt += "(当前数据未找到端口定义，请依据描述猜测可能的端口: 启动回路输入, 反馈回路输入, 数字量信号输出)\n";
        }
    } else {
        for (const auto &port : comp.ports) {
            prompt += QString("- 功能子块: %1, 端口: %2\n").arg(port.first, port.second);
        }
    }
    
    prompt += 
        "\n请根据器件描述和端口名称，判断每个端口的类型（electric/hydraulic/mechanical）。\n"
        "输出格式为 JSON:\n"
        "{\n"
        "  \"ports\": [\n"
        "    {\"functionBlock\": \"Coil\", \"portName\": \"A1\", \"portType\": \"electric\"},\n"
        "    ...\n"
        "  ]\n"
        "}\n";
    
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
        "(declare-const %Name%.R Real) ; 电阻\n"
        "(assert (> %Name%.R 0)) ; 电阻大于0\n\n"
        "注意: 只输出 SMT-LIB2 代码，不要包含其他说明文字。\n";
    
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
        "(define-fun %Name%_normal () Bool\n"
        "  (and\n"
        "    (= %Name%.Coil.A1.u (+ %Name%.Coil.A2.u (* %Name%.Coil.A1.i %Name%.R)))\n"
        "  )\n"
        ")\n\n"
        "注意: 只输出 SMT-LIB2 代码，不要包含其他说明文字。\n";
    
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
        "每个故障模式用一个 define-fun 定义。\n"
        "示例:\n"
        "(define-fun %Name%_fault_open () Bool\n"
        "  (= %Name%.Coil.A1.i 0) ; 开路\n"
        ")\n\n"
        "(define-fun %Name%_fault_short () Bool\n"
        "  (= %Name%.Coil.A1.u %Name%.Coil.A2.u) ; 短路\n"
        ")\n\n"
        "注意: 只输出 SMT-LIB2 代码，不要包含其他说明文字。\n";
    
    return prompt;
}
