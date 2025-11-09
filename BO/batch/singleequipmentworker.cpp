#include "singleequipmentworker.h"
#include "../ai/tmodelautogenerator.h"
#include <QDateTime>
#include <QRegularExpression>
#include <QDebug>
#include <QThread>
#include <QSqlError>

SingleEquipmentWorker::SingleEquipmentWorker(const QString &dbConnectionName, const EquipmentInputData &inputData, QObject *parent)
    : QObject(parent)
    , m_dbConnectionName(dbConnectionName)
    , m_inputData(inputData)
    , m_generator(nullptr)
    , m_timeoutTimer(nullptr)
    , m_isFinished(false)
{
    // 初始化结果
    m_result.equipmentId = m_inputData.equipmentId;
    m_result.code = m_inputData.code;
    m_result.name = m_inputData.name;
    m_result.categoryName = m_inputData.categoryName;
    m_result.status = EquipmentProcessResult::Failed;
    m_result.elapsedSeconds = 0;
    
    // 创建超时定时器（5分钟超时）
    m_timeoutTimer = new QTimer(this);
    m_timeoutTimer->setSingleShot(true);
    m_timeoutTimer->setInterval(5 * 60 * 1000);  // 5分钟
    connect(m_timeoutTimer, &QTimer::timeout, this, &SingleEquipmentWorker::onTimeout);
}

SingleEquipmentWorker::~SingleEquipmentWorker()
{
    if (m_timeoutTimer) {
        m_timeoutTimer->stop();
    }
    if (m_generator) {
        m_generator->deleteLater();
    }
    
    // 关闭并移除线程独立的数据库连接
    if (m_threadDb.isValid() && m_threadDb.isOpen()) {
        m_threadDb.close();
    }
    if (!m_threadConnectionName.isEmpty() && QSqlDatabase::contains(m_threadConnectionName)) {
        QSqlDatabase::removeDatabase(m_threadConnectionName);
    }
}

void SingleEquipmentWorker::process()
{
    m_timer.start();
    m_isFinished = false;
    
    log(QString("========== 开始处理: %1 (%2) ==========")
        .arg(m_inputData.code, m_inputData.name));
    
    // 启动超时定时器
    m_timeoutTimer->start();
    
    // 检查是否有有效端号
    if (m_inputData.ports.isEmpty()) {
        log("器件无有效端号，跳过处理");
        m_result.status = EquipmentProcessResult::NoPorts;
        m_result.errorMessage = "无有效端号";
        m_result.elapsedSeconds = m_timer.elapsed() / 1000;
        m_timeoutTimer->stop();
        emit finished(m_result);
        return;
    }
    
    log(QString("输入数据: 端口数=%1, 已配置端口数=%2")
        .arg(m_inputData.ports.size())
        .arg(m_inputData.portConfigs.size()));
    
    // 创建 TModelAutoGenerator（无数据库模式）
    m_generator = new TModelAutoGenerator(this);
    
    // 设置组件数据（代替数据库加载）
    ComponentInfo compInfo;
    compInfo.equipmentId = m_inputData.equipmentId;
    compInfo.code = m_inputData.code;
    compInfo.name = m_inputData.name;
    compInfo.description = m_inputData.description;
    compInfo.ports = m_inputData.ports;
    m_generator->setComponentData(compInfo, m_inputData.portConfigs);
    
    // 设置为批量模式（不操作UI）
    m_generator->setBatchMode(true);
    
    // 设置日志输出（禁用文件日志，只通过信号输出）
    m_generator->setLogFileOverride("", false);  // 空路径表示不写文件
    
    // 连接信号
    connect(m_generator, &TModelAutoGenerator::logLine,
            this, &SingleEquipmentWorker::onGeneratorLogLine);
    connect(m_generator, &TModelAutoGenerator::componentFinished,
            this, &SingleEquipmentWorker::onGeneratorFinished);
    connect(m_generator, &TModelAutoGenerator::constantsExtracted,
            this, &SingleEquipmentWorker::onConstantsExtracted);
    connect(m_generator, &TModelAutoGenerator::modelGenerated,
            this, &SingleEquipmentWorker::onModelGenerated);
    connect(m_generator, &TModelAutoGenerator::streamDelta,
            this, &SingleEquipmentWorker::onStreamDelta);
    
    // 连接数据库操作请求信号（转发到 Manager）
    connect(m_generator, &TModelAutoGenerator::requestSavePortConfigs,
            this, &SingleEquipmentWorker::requestSavePortConfigs);
    connect(m_generator, &TModelAutoGenerator::requestSaveModel,
            this, &SingleEquipmentWorker::requestSaveModel);
    connect(m_generator, &TModelAutoGenerator::requestClearModel,
            this, &SingleEquipmentWorker::requestClearModel);
    
    // 开始生成
    log("启动 TModelAutoGenerator...");
    m_generator->startAutoGeneration();
}

void SingleEquipmentWorker::onGeneratorLogLine(const QString &line)
{
    // 转发日志（过滤掉时间戳，因为外层会加）
    QString cleanLine = line;
    // 移除 [yyyy-MM-dd hh:mm:ss] 前缀
    static QRegularExpression timestampRe("^\\[\\d{4}-\\d{2}-\\d{2} \\d{2}:\\d{2}:\\d{2}\\] ");
    cleanLine.remove(timestampRe);
    log(cleanLine);
}

void SingleEquipmentWorker::onGeneratorFinished(int equipmentId, const QString &code, bool success, const QString &message)
{
    Q_UNUSED(equipmentId);
    Q_UNUSED(code);
    
    // 防止重复完成
    if (m_isFinished) {
        return;
    }
    m_isFinished = true;
    
    // 停止超时定时器
    m_timeoutTimer->stop();
    
    log(QString("TModelAutoGenerator 完成: %1 - %2").arg(success ? "成功" : "失败", message));
    
    if (success) {
        m_result.status = EquipmentProcessResult::Success;
        m_result.errorMessage = "";
        
        // 无数据库模式：端口配置已通过信号请求保存到 Manager
        // 最新配置将由 Manager 在主线程处理
        
        log("处理成功");
    } else {
        m_result.status = EquipmentProcessResult::Failed;
        m_result.errorMessage = message;
        log(QString("处理失败: %1").arg(message));
    }
    
    m_result.elapsedSeconds = m_timer.elapsed() / 1000;
    emit finished(m_result);
}

void SingleEquipmentWorker::onConstantsExtracted(const QMap<QString, QString> &constants)
{
    m_result.constants = constants;
    log(QString("提取常量: %1 个").arg(constants.size()));
}

void SingleEquipmentWorker::onModelGenerated(const QString &tmodel)
{
    m_result.tmodel = tmodel;
    log(QString("生成T模型: %1 字符").arg(tmodel.length()));
}

void SingleEquipmentWorker::onStreamDelta(const QString &delta)
{
    // 直接转发流式输出
    emit streamDelta(delta);
}

void SingleEquipmentWorker::onTimeout()
{
    if (m_isFinished) {
        return;  // 已经完成，忽略超时
    }
    
    log("错误: 处理超时（5分钟无响应）");
    finishWithError("处理超时");
}

void SingleEquipmentWorker::finishWithError(const QString &errorMessage)
{
    if (m_isFinished) {
        return;
    }
    m_isFinished = true;
    
    m_timeoutTimer->stop();
    
    m_result.status = EquipmentProcessResult::Failed;
    m_result.errorMessage = errorMessage;
    m_result.elapsedSeconds = m_timer.elapsed() / 1000;
    
    log(QString("处理失败: %1").arg(errorMessage));
    
    emit finished(m_result);
}

void SingleEquipmentWorker::log(const QString &message)
{
    emit logMessage(message);
}
