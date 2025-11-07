#include "tmodelautogenerator.h"
#include "widget/aimodelgeneratordialog.h"
#include "BO/function/tmodelparser.h"
#include "widget/codecheckdialog.h"
#include "BO/containerrepository.h"
#include "widget/containerhierarchyutils.h"
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
                startInternalVarsGeneration();
            }
        } else {
            logMessage("端口类型解析失败");
            if (m_portTypeAttempt < MAX_RETRIES-1) {
                m_portTypeAttempt++;
                startPortTypeIdentification();
            } else {
                if (!m_portConfigs.isEmpty()) savePortConfigs(comp.equipmentId);
                startInternalVarsGeneration();
            }
        }
        break; }

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

    case Stage_FailureMode: {
        m_failureModeDef = content;
        logMessage("故障模式已获取");
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
        QString errorMsg;
        if (validateTModel(comp.equipmentId, fullTModel, errorMsg)) {
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
                startInternalVarsGeneration();
            } else {
                logMessage("达到最大重试次数，跳过此器件");
                moveToNextComponent();
            }
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
    // 期望输出格式为 JSON，仅包含本轮新填写的端口（即原来 portType 为空的那些条目）
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
    // 复用系统统一的 ContainerRepository + ContainerHierarchy 逻辑，避免手写 SQL 导致列/结构不匹配
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
        "4. 机械端口变量: F(力)、x(位移或运动)\n"
        "5. 使用 SMT-LIB2 语法\n"
        "6. 变量命名格式: %Name%.PortName.Variable\n"
        "7. 输出必须是有效的 JSON 格式（对于端口类型识别任务）或 SMT-LIB2 代码（对于模型生成任务）\n";
}

QString TModelAutoGenerator::buildPortTypePrompt(const ComponentInfo &comp)
{
    // 1. 基本器件信息
    QString prompt = QString(
        "器件信息:\n"
        "- 代号: %1\n"
        "- 名称: %2\n"
        "- 描述: %3\n\n"
        "端口列表(JSON，portType为空表示待识别):\n"
    ).arg(comp.code, comp.name, comp.description);

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
            // 变量回填：如果库里有变量结构，则简单拼接 name 字段；否则用默认变量集合
            const QString varsJson = q.value(3).toString();
            if (!varsJson.trimmed().isEmpty()) {
                QJsonDocument doc = QJsonDocument::fromJson(varsJson.toUtf8());
                if (doc.isArray()) {
                    QStringList varNames; for (auto v : doc.array()) if (v.isObject()) varNames << v.toObject().value("name").toString();
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
