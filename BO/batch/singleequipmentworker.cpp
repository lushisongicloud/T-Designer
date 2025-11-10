#include "singleequipmentworker.h"
#include "../ai/tmodelautogenerator.h"
#include <QDateTime>
#include <QRegularExpression>
#include <QDebug>
#include <QThread>
#include <QSqlError>
#include <QDir>
#include <QApplication>

SingleEquipmentWorker::SingleEquipmentWorker(const QString &dbConnectionName, const EquipmentInputData &inputData, bool enableWorkerLog, QObject *parent)
    : QObject(parent)
    , m_dbConnectionName(dbConnectionName)
    , m_inputData(inputData)
    , m_enableWorkerLog(enableWorkerLog)
    , m_generator(nullptr)
    , m_totalTimeoutTimer(nullptr)
    , m_activityTimeoutTimer(nullptr)
    , m_isFinished(false)
{
    // 初始化结果
    m_result.equipmentId = m_inputData.equipmentId;
    m_result.code = m_inputData.code;
    m_result.name = m_inputData.name;
    m_result.categoryName = m_inputData.categoryName;
    m_result.status = EquipmentProcessResult::Failed;
    m_result.elapsedSeconds = 0;
    
    // 创建总体超时定时器（5分钟）
    m_totalTimeoutTimer = new QTimer(this);
    m_totalTimeoutTimer->setSingleShot(true);
    m_totalTimeoutTimer->setInterval(5 * 60 * 1000);  // 5分钟
    connect(m_totalTimeoutTimer, &QTimer::timeout, this, &SingleEquipmentWorker::onTotalTimeout);
    
    // 创建活跃度超时定时器（30秒无流式输出）
    m_activityTimeoutTimer = new QTimer(this);
    m_activityTimeoutTimer->setSingleShot(false);  // 可重复触发
    m_activityTimeoutTimer->setInterval(30 * 1000);  // 30秒
    connect(m_activityTimeoutTimer, &QTimer::timeout, this, &SingleEquipmentWorker::onActivityTimeout);
}

SingleEquipmentWorker::~SingleEquipmentWorker()
{
    if (m_totalTimeoutTimer) {
        m_totalTimeoutTimer->stop();
        m_totalTimeoutTimer->deleteLater();
        m_totalTimeoutTimer = nullptr;
    }
    
    if (m_activityTimeoutTimer) {
        m_activityTimeoutTimer->stop();
        m_activityTimeoutTimer->deleteLater();
        m_activityTimeoutTimer = nullptr;
    }
    
    // 确保 generator 完全清理，避免向已删除对象发送信号
    if (m_generator) {
        // 断开所有信号连接，防止析构过程中发送信号
        disconnect(m_generator, nullptr, this, nullptr);
        m_generator->deleteLater();
        m_generator = nullptr;
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
    
    // 启动双重超时保护
    m_totalTimeoutTimer->start();      // 总体5分钟超时
    m_activityTimeoutTimer->start();   // 30秒无活动超时
    
    // 检查是否有有效端号
    if (m_inputData.ports.isEmpty()) {
        log("器件无有效端号，跳过处理");
        m_result.status = EquipmentProcessResult::NoPorts;
        m_result.errorMessage = "无有效端号";
        m_result.elapsedSeconds = m_timer.elapsed() / 1000;
        m_totalTimeoutTimer->stop();
        m_activityTimeoutTimer->stop();
        emit finished(m_result);
        return;
    }
    
    log(QString("输入数据: 端口数=%1, 已配置端口数=%2, 端口描述数=%3")
        .arg(m_inputData.ports.size())
        .arg(m_inputData.portConfigs.size())
        .arg(m_inputData.portDescriptions.size()));
    
    // 创建 TModelAutoGenerator（无数据库模式）
    m_generator = new TModelAutoGenerator(this);
    
    // 设置组件数据（代替数据库加载）
    ComponentInfo compInfo;
    compInfo.equipmentId = m_inputData.equipmentId;
    compInfo.code = m_inputData.code;
    compInfo.name = m_inputData.name;
    compInfo.description = m_inputData.description;
    compInfo.ports = m_inputData.ports;
    compInfo.portDescriptions = m_inputData.portDescriptions;  // 传递端口描述（ConnDesc）
    m_generator->setComponentData(compInfo, m_inputData.portConfigs);
    
    // 设置为批量模式（不操作UI）
    m_generator->setBatchMode(true);
    
    // 根据配置决定是否启用 Worker 日志文件
    if (m_enableWorkerLog) {
        // 生成带有线程ID和毫秒的唯一日志文件名
        qint64 msec = QDateTime::currentMSecsSinceEpoch();
        quintptr threadId = (quintptr)QThread::currentThreadId();
        QString logFileName = QString("worker_%1_%2_%3.log")
            .arg(m_inputData.code)
            .arg(msec)
            .arg(threadId);
        QString logFilePath = QDir(QApplication::applicationDirPath()).filePath("logs/" + logFileName);
        m_generator->setLogFileOverride(logFilePath, true);
        log(QString("Worker 日志文件: %1").arg(logFilePath));
    } else {
        // 禁用文件日志，只通过信号输出
        m_generator->setLogFileOverride("", false);
    }
    
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
    
    // 停止所有超时定时器
    if (m_totalTimeoutTimer) {
        m_totalTimeoutTimer->stop();
    }
    if (m_activityTimeoutTimer) {
        m_activityTimeoutTimer->stop();
    }
    
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
    
    // 断开 generator 的所有连接，防止后续清理时发送信号到已删除对象
    if (m_generator) {
        disconnect(m_generator, nullptr, this, nullptr);
    }
    
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
    // 收到流式输出，重置活跃度定时器
    if (m_activityTimeoutTimer && m_activityTimeoutTimer->isActive()) {
        m_activityTimeoutTimer->stop();
        m_activityTimeoutTimer->start();  // 重新开始30秒倒计时
    }
    
    // 转发流式输出
    emit streamDelta(delta);
}

void SingleEquipmentWorker::onTotalTimeout()
{
    if (m_isFinished) {
        return;  // 已经完成，忽略超时
    }
    
    log("错误: 处理总体超时（5分钟无响应）");
    finishWithError("处理超时（超过5分钟）");
}

void SingleEquipmentWorker::onActivityTimeout()
{
    if (m_isFinished) {
        return;  // 已经完成，忽略超时
    }
    
    log("错误: 流式输出超时（30秒无新数据）");
    finishWithError("流式输出超时（30秒无响应）");
}

void SingleEquipmentWorker::finishWithError(const QString &errorMessage)
{
    if (m_isFinished) {
        return;
    }
    m_isFinished = true;
    
    // 停止所有定时器
    if (m_totalTimeoutTimer) {
        m_totalTimeoutTimer->stop();
    }
    if (m_activityTimeoutTimer) {
        m_activityTimeoutTimer->stop();
    }
    
    m_result.status = EquipmentProcessResult::Failed;
    m_result.errorMessage = errorMessage;
    m_result.elapsedSeconds = m_timer.elapsed() / 1000;
    
    log(QString("处理失败: %1").arg(errorMessage));
    
    // 断开 generator 的所有连接，防止后续清理时发送信号到已删除对象
    if (m_generator) {
        disconnect(m_generator, nullptr, this, nullptr);
    }
    
    emit finished(m_result);
}

void SingleEquipmentWorker::log(const QString &message)
{
    emit logMessage(message);
}
