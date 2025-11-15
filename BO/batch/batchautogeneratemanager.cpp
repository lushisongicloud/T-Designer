#include "batchautogeneratemanager.h"
#include "../ai/tmodelautogenerator.h"  // 包含 PortTypeConfig 完整定义
#include "BO/containerrepository.h"
#include "widget/containerhierarchyutils.h"
#include <QSqlQuery>
#include <QSqlError>
#include <QDateTime>
#include <QThread>
#include <QDebug>
#include <QJsonDocument>
#include <QJsonObject>
#include <QJsonArray>
#include <QMetaObject>
#include <QCoreApplication>

BatchAutoGenerateManager::BatchAutoGenerateManager(const QSqlDatabase &db, QObject *parent)
    : QObject(parent)
    , m_connectionName(db.connectionName())  // 保存连接名而非拷贝对象
    , m_workerCount(1)
    , m_recoveredCount(0)
    , m_totalCount(0)
    , m_processedCount(0)
    , m_successCount(0)
    , m_failedCount(0)
    , m_noPortsCount(0)
    , m_skippedCount(0)
    , m_stopped(false)
    , m_lastLoadedEquipmentId(0)
    , m_totalEquipmentCount(0)
    , m_reverseOrder(false)
{
    // 注册元类型，以便在跨线程信号槽中使用
    qRegisterMetaType<EquipmentProcessResult>("EquipmentProcessResult");
    qRegisterMetaType<QMap<QString, PortTypeConfig>>("QMap<QString,PortTypeConfig>");
}

BatchAutoGenerateManager::~BatchAutoGenerateManager()
{
    stop();
    
    if (m_logFile.isOpen()) {
        m_logFile.close();
    }
}

void BatchAutoGenerateManager::start(const QString &logFilePath,
                                      bool resumeFromLog,
                                      int workerCount,
                                      bool enableWorkerLog,
                                      bool reverseOrder)
{
    m_logFilePath = logFilePath;
    m_workerCount = qMax(1, workerCount);
    m_enableWorkerLog = enableWorkerLog;
    m_reverseOrder = reverseOrder;
    m_stopped = false;

    // 每次开始前清空所有历史统计状态，确保从干净状态重新开始
    m_recoveredCount = 0;
    m_totalCount = 0;
    m_processedCount = 0;
    m_successCount = 0;
    m_failedCount = 0;
    m_noPortsCount = 0;
    m_skippedCount = 0;
    m_processedEquipmentIds.clear();
    m_skippedEquipmentIds.clear();

    // 1. 初始化日志文件
    if (!initializeLogFile(resumeFromLog)) {
        emit finished();
        return;
    }

    // 2. 如果恢复模式，解析日志文件
    if (resumeFromLog) {
        parseLogAndMarkProcessed(logFilePath);
    }
    
    // 3. 加载任务队列
    loadTaskQueue();

    // 使用Equipment表中的总器件数作为进度条分母，符合用户期望
    // 已处理器件 = 成功 + 失败 + 无端口 + 无Class_ID
    // 无Class_ID = 已处理器件中因Class_ID字段为空的器件（包括从日志恢复的和当前运行的）
    // 总器件数 = Equipment表中的总记录数
    m_totalCount = m_totalEquipmentCount;

    // 恢复模式下显示从日志加载的已处理器件信息
    // parseLogAndMarkProcessed中已将统计结果存储在m_successCount等变量中
    // 注意：m_skippedCount包含了从日志恢复的无Class_ID器件，它们也属于已处理器件
    if (resumeFromLog) {
        int recovered = m_recoveredCount;
        qInfo() << QString("[BatchManager] 从日志恢复: 共有 %1 个器件已完成处理")
            .arg(recovered);
    }
    
    if (m_taskQueue.isEmpty()) {
        qInfo() << "[BatchManager] 没有待处理的器件";
        writeLogEnd();
        emit finished();
        return;
    }
    
    qInfo() << QString("[BatchManager] 开始批量处理: 总数=%1, 待处理=%2, 无Class_ID=%3, 工作线程=%4")
        .arg(m_totalCount)
        .arg(m_taskQueue.size())
        .arg(m_skippedCount)
        .arg(m_workerCount);

    // 4. 写入日志头部
    writeLogStart();

    // 5. 记录无Class_ID的器件到日志文件（仅当前运行中因Class_ID字段为空而跳过的器件）
    writeSkippedResults();

    // 6. 创建工作线程
    m_totalTimer.start();
    createWorkers();
    
    emit started(m_totalCount);
}

void BatchAutoGenerateManager::stop()
{
    if (m_stopped) return;
    
    m_stopped = true;
    qInfo() << "[BatchManager] 停止批量处理";
    
    // 1. 先断开所有信号连接，避免在清理过程中触发回调
    for (auto worker : m_workers) {
        if (worker) {
            // 断开所有与 manager 的连接
            disconnect(worker, nullptr, this, nullptr);
        }
    }
    
    // 2. 请求所有工作线程优雅退出
    for (auto thread : m_workerThreads) {
        if (thread && thread->isRunning()) {
            thread->quit();
        }
    }
    
    // 3. 等待所有线程退出（给每个线程3秒时间）
    for (auto thread : m_workerThreads) {
        if (thread && thread->isRunning()) {
            if (!thread->wait(3000)) {  // 等待最多3秒
                qWarning() << "[BatchManager] 工作线程未能在3秒内退出，强制终止";
                thread->terminate();
                thread->wait(1000);  // 等待终止完成
            }
        }
    }
    
    // 4. 清理映射
    m_workerThreads.clear();
    m_workers.clear();
    m_workerIds.clear();
    
    // 写入停止日志
    if (m_logStream.device()) {
        m_logStream << QString("\n[%1] 批量处理被用户停止\n")
            .arg(QDateTime::currentDateTime().toString("yyyy-MM-dd HH:mm:ss"));
        m_logStream.flush();
    }
    
    // 发出完成信号，让UI恢复状态
    emit finished();
}

bool BatchAutoGenerateManager::initializeLogFile(bool resumeFromLog)
{
    if (m_logFile.isOpen()) {
        m_logFile.close();
    }
    
    m_logFile.setFileName(m_logFilePath);
    
    QIODevice::OpenMode mode = QIODevice::WriteOnly | QIODevice::Text;
    if (resumeFromLog && QFile::exists(m_logFilePath)) {
        mode |= QIODevice::Append;
    } else {
        // 新建文件，清空旧内容
        if (QFile::exists(m_logFilePath)) {
            QFile::remove(m_logFilePath);
        }
    }
    
    if (!m_logFile.open(mode)) {
        qWarning() << "[BatchManager] 无法打开日志文件:" << m_logFilePath;
        return false;
    }
    
    m_logStream.setDevice(&m_logFile);
    m_logStream.setCodec("UTF-8");
    
    return true;
}

void BatchAutoGenerateManager::parseLogAndMarkProcessed(const QString &logFilePath)
{
    QFile file(logFilePath);
    if (!file.open(QIODevice::ReadOnly | QIODevice::Text)) {
        qWarning() << "[BatchManager] 无法读取日志文件:" << logFilePath;
        return;
    }
    
    QTextStream stream(&file);
    stream.setCodec("UTF-8");

    int recoveredCount = 0;  // 从日志恢复的已处理器件数
    while (!stream.atEnd()) {
        QString line = stream.readLine().trimmed();
        if (!line.startsWith("[RESULT]")) continue;
        
        // 格式: [RESULT] equipmentId|code|name|categoryPath|status|message
        QStringList parts = line.mid(8).trimmed().split("|");
        if (parts.size() < 5) continue;
        
        bool ok;
        int equipmentId = parts[0].toInt(&ok);
        if (!ok) continue;
        
        QString status = parts[4];
        
        // 恢复所有4种已处理器件状态：success、failed、NoPorts、无Class_ID
        // 这些都是已处理器件，应该计入恢复计数
        if (status == "success" || status == "failed" || status == "NoPorts" || status == "无Class_ID") {
            m_processedEquipmentIds.insert(equipmentId);
            recoveredCount++;

            // 统计各类已处理器件数，用于进度显示
            if (status == "success") m_successCount++;
            else if (status == "failed") m_failedCount++;
            else if (status == "NoPorts") m_noPortsCount++;
            else if (status == "无Class_ID") {
                // 无Class_ID状态的器件也计入跳过
                // 这些是已处理过的无Class_ID器件，但统计上仍归类为"无Class_ID"
                m_skippedCount++;
                m_skippedEquipmentIds.insert(equipmentId);
            }
        }
    }

    file.close();

    // recoveredCount是恢复的已处理器件数（success + failed + NoPorts + 无Class_ID）
    qInfo() << QString("[BatchManager] 从日志恢复: 共有 %1 个器件已完成处理").arg(recoveredCount);
    qInfo() << QString("[BatchManager] 其中: 成功=%1, 失败=%2, 无端口=%3, 无Class_ID=%4")
        .arg(m_successCount)
        .arg(m_failedCount)
        .arg(m_noPortsCount)
        .arg(m_skippedCount);

    // 保存恢复的总数，后续用于UI显示和进度计算
    m_recoveredCount = recoveredCount;
}

void BatchAutoGenerateManager::loadTaskQueue()
{
    m_taskQueue.clear();
    m_lastLoadedEquipmentId = 0;
    
    // 查询总器件数（用于进度显示）
    // 查询总器件数
    {
        QSqlDatabase db = QSqlDatabase::database(m_connectionName);
        QSqlQuery countQuery(db);
        if (countQuery.exec("SELECT COUNT(*) FROM Equipment")) {
            if (countQuery.next()) {
                m_totalEquipmentCount = countQuery.value(0).toInt();
                qInfo() << QString("[BatchManager] 数据库总器件数: %1").arg(m_totalEquipmentCount);
            }
        }
    }
    
    // 初始加载任务，持续加载直到队列有足够任务或没有更多数据
    qInfo() << "[BatchManager] 开始初始加载任务...";
    const int targetInitialTasks = 20;  // 目标初始任务数
    const int maxLoadAttempts = 1000;   // 最多尝试加载次数，支持更多已处理器件
    int totalLoaded = 0;
    int attempts = 0;
    
    while (m_taskQueue.size() < targetInitialTasks && attempts < maxLoadAttempts) {
        int loaded = loadBatchTasks(20);
        attempts++;
        
        // loaded == -1 表示已到数据库末尾或查询失败
        if (loaded == -1) {
            qInfo() << "[BatchManager] 已到达数据库末尾或查询失败，停止加载";
            break;
        }
        
        if (loaded > 0) {
            totalLoaded += loaded;
        }
        
        // 如果本次查询有结果但加载了 0 个任务，说明全部被跳过，继续尝试下一批
        if (loaded == 0) {
            qInfo() << QString("[BatchManager] 本批次全部跳过，继续加载 (尝试 %1/%2)").arg(attempts).arg(maxLoadAttempts);
        }
    }
    
    qInfo() << QString("[BatchManager] 初始加载任务完成: %1 个器件 (尝试次数: %2)").arg(totalLoaded).arg(attempts);
    qInfo() << QString("[BatchManager] 当前队列大小: %1").arg(m_taskQueue.size());
}

int BatchAutoGenerateManager::loadBatchTasks(int batchSize)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);

    int loadedCount = 0;
    int rowCount = 0;

    QSqlQuery query(db);

    if (m_reverseOrder) {
        // 逆序遍历：从上次加载的位置往前，按 Equipment_ID 降序加载
        QString sql = QString(
            "SELECT Equipment_ID, PartCode, Name, Class_ID "
            "FROM Equipment "
            "WHERE Equipment_ID < ? "
            "ORDER BY Equipment_ID DESC "
            "LIMIT ?"
        );

        // 如果是第一次加载（m_lastLoadedEquipmentId为0），需要先获取最大ID
        if (m_lastLoadedEquipmentId == 0) {
            QSqlQuery maxIdQuery(db);
            if (maxIdQuery.exec("SELECT MAX(Equipment_ID) FROM Equipment")) {
                if (maxIdQuery.next()) {
                    m_lastLoadedEquipmentId = maxIdQuery.value(0).toInt() + 1;
                }
            }
        }

        query.prepare(sql);
        query.addBindValue(m_lastLoadedEquipmentId);
        query.addBindValue(batchSize);
    } else {
        // 升序遍历：从上次加载的位置继续，按 Equipment_ID 升序加载
        query.prepare(
            "SELECT Equipment_ID, PartCode, Name, Class_ID "
            "FROM Equipment "
            "WHERE Equipment_ID > ? "
            "ORDER BY Equipment_ID "
            "LIMIT ?"
        );
        query.addBindValue(m_lastLoadedEquipmentId);
        query.addBindValue(batchSize);
    }

    if (!query.exec()) {
        qWarning() << "[BatchManager] 加载器件任务失败:" << query.lastError().text();
        return -1;  // 返回 -1 表示查询失败
    }

    while (query.next()) {
        rowCount++;
        int equipmentId = query.value(0).toInt();
        QString classId = query.value(3).toString();  // 获取Class_ID

        // 更新加载位置
        m_lastLoadedEquipmentId = equipmentId;

        // 跳过已处理的器件
        if (m_processedEquipmentIds.contains(equipmentId)) {
            continue;
        }

        // 跳过Class_ID为空的器件（无Class_ID）
        if (classId.isEmpty()) {
            qInfo() << QString("[BatchManager] 跳过Equipment_ID %1: Class_ID为空").arg(equipmentId);
            // 记录到无Class_ID集合，待稍后统一记录到日志
            m_skippedEquipmentIds.insert(equipmentId);
            m_skippedCount++;
            continue;
        }

        EquipmentTask task;
        task.equipmentId = equipmentId;
        task.code = query.value(1).toString();
        task.name = query.value(2).toString();
        task.categoryPath = getCategoryPathInternal(equipmentId);  // 使用内部方法（已持有锁）
        task.categoryIndex = 0;  // 不再使用类别索引

        m_taskQueue.enqueue(task);
        loadedCount++;
    }

    // 如果查询返回 0 行，说明已经到达数据库末尾，返回 -1 作为标记
    if (rowCount == 0) {
        return -1;
    }

    return loadedCount;
}

bool BatchAutoGenerateManager::loadMoreTasksIfNeeded()
{
    // 当队列少于10个时，尝试加载更多
    const int QUEUE_LOW_THRESHOLD = 10;
    const int BATCH_SIZE = 20;
    const int MAX_RELOAD_ATTEMPTS = 50;  // 最多重试次数
    
    if (m_taskQueue.size() < QUEUE_LOW_THRESHOLD) {
        int attempts = 0;
        int totalLoaded = 0;
        
        // 持续尝试加载，直到队列足够或到达末尾
        while (m_taskQueue.size() < QUEUE_LOW_THRESHOLD && attempts < MAX_RELOAD_ATTEMPTS) {
            int loaded = loadBatchTasks(BATCH_SIZE);
            attempts++;
            
            // loaded == -1 表示已到数据库末尾
            if (loaded == -1) {
                qInfo() << "[BatchManager] 已到达数据库末尾，无更多器件可加载";
                return false;
            }
            
            if (loaded > 0) {
                totalLoaded += loaded;
            }
            
            // 如果本批次全部跳过但还没到末尾，继续尝试（跳过指Class_ID为空）
            if (loaded == 0) {
                qInfo() << QString("[BatchManager] 队列补充: 本批次全部跳过，继续尝试 (%1/%2)")
                    .arg(attempts).arg(MAX_RELOAD_ATTEMPTS);
            }
        }
        
        if (totalLoaded > 0) {
            qInfo() << QString("[BatchManager] 队列补充完成: 加载了 %1 个新任务，当前队列: %2")
                .arg(totalLoaded).arg(m_taskQueue.size());
            
            // 更新总数（因为可能有新加载的）
            m_totalCount = m_skippedCount + m_processedCount + m_taskQueue.size();
            
            return true;
        } else {
            qInfo() << QString("[BatchManager] 队列补充失败: 尝试了%1次，未找到新任务").arg(attempts);
            return false;
        }
    }
    
    return false;
}

QString BatchAutoGenerateManager::getCategoryPath(int equipmentId)
{
    return getCategoryPathInternal(equipmentId);
}

QString BatchAutoGenerateManager::getCategoryPathInternal(int equipmentId)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    QSqlQuery query(db);
    query.prepare("SELECT c.ClassName FROM Equipment e "
                  "JOIN Class c ON e.Class_ID = c.Class_ID "
                  "WHERE e.Equipment_ID = ?");
    query.addBindValue(equipmentId);
    
    if (query.exec() && query.next()) {
        return query.value(0).toString();
    }
    
    return "未分类";
}

void BatchAutoGenerateManager::createWorkers()
{
    for (int i = 0; i < m_workerCount; ++i) {
        startNextTask(i);
    }
}

void BatchAutoGenerateManager::startNextTask(int workerId)
{
    if (m_stopped) {
        return;
    }
    
    // 队列不足时尝试加载更多
    loadMoreTasksIfNeeded();
    
    // 从队列取任务
    if (m_taskQueue.isEmpty()) {
        // 队列为空，检查是否所有工作线程都完成
        if (m_workers.isEmpty()) {
            // 全部完成
            qInfo() << "[BatchManager] 所有任务已完成";
            writeLogEnd();
            emit finished();
        }
        return;
    }
    
    EquipmentTask task = m_taskQueue.dequeue();
    assignTaskToWorker(workerId, task);
}

void BatchAutoGenerateManager::assignTaskToWorker(int workerId, const EquipmentTask &task)
{
    // 1. 从数据库加载输入数据
    EquipmentInputData inputData = loadEquipmentInputData(task);
    
    // 2. 检查是否有有效端口（提前过滤）
    if (inputData.ports.isEmpty()) {
        
        EquipmentProcessResult result;
        result.equipmentId = task.equipmentId;
        result.code = task.code;
        result.name = task.name;
        result.categoryName = task.categoryPath;
        result.status = EquipmentProcessResult::NoPorts;
        result.errorMessage = "无有效端号";
        result.elapsedSeconds = 0;
        
        // 直接触发完成
        QMetaObject::invokeMethod(this, [this, workerId, result]() {
            // 不在这里增加m_processedCount，避免重复计数
            // 统一在onWorkerFinished中计算总处理数
            m_noPortsCount++;
            writeLogResult(result);
            emit workerFinished(workerId, result);
            emit progressUpdated(m_processedCount, m_totalCount,
                                m_successCount, m_failedCount, m_noPortsCount, m_skippedCount);
            startNextTask(workerId);
        }, Qt::QueuedConnection);
        
        return;
    }
    
    // 3. 创建新线程和Worker
    QThread *thread = new QThread(this);
    SingleEquipmentWorker *worker = new SingleEquipmentWorker(m_connectionName, inputData, m_enableWorkerLog);
    
    worker->moveToThread(thread);
    
    // 4. 连接信号（跨线程需要显式指定Qt::QueuedConnection）
    connect(thread, &QThread::started, worker, &SingleEquipmentWorker::process);
    connect(worker, &SingleEquipmentWorker::finished, this, &BatchAutoGenerateManager::onWorkerFinished, Qt::QueuedConnection);
    connect(worker, &SingleEquipmentWorker::logMessage, this, [this, workerId](const QString &msg) {
        emit workerLogMessage(workerId, msg);
    }, Qt::QueuedConnection);
    connect(worker, &SingleEquipmentWorker::streamDelta, this, [this, workerId](const QString &delta) {
        emit workerStreamDelta(workerId, delta);
    }, Qt::QueuedConnection);
    
    // 连接数据库操作请求信号
    connect(worker, &SingleEquipmentWorker::requestSavePortConfigs,
            this, &BatchAutoGenerateManager::onWorkerRequestSavePortConfigs, Qt::QueuedConnection);
    connect(worker, &SingleEquipmentWorker::requestSaveModel,
            this, &BatchAutoGenerateManager::onWorkerRequestSaveModel, Qt::QueuedConnection);
    connect(worker, &SingleEquipmentWorker::requestClearModel,
            this, &BatchAutoGenerateManager::onWorkerRequestClearModel, Qt::QueuedConnection);
    
    // 5. 清理
    connect(worker, &SingleEquipmentWorker::finished, thread, &QThread::quit);
    connect(thread, &QThread::finished, worker, &QObject::deleteLater);
    connect(thread, &QThread::finished, thread, &QObject::deleteLater);
    
    // 6. 保存映射
    m_workerThreads[workerId] = thread;
    m_workers[workerId] = worker;
    m_workerIds[worker] = workerId;
    
    emit workerStarted(workerId, task.code, task.name, task.equipmentId);
    
    // 处理事件，让 UI 有机会更新
    QCoreApplication::processEvents();
    
    // 7. 启动线程
    thread->start();
}

void BatchAutoGenerateManager::onWorkerFinished(const EquipmentProcessResult &result)
{
    // 获取工作线程ID
    SingleEquipmentWorker *worker = qobject_cast<SingleEquipmentWorker*>(sender());
    if (!worker) return;
    
    int workerId = m_workerIds.value(worker, -1);
    if (workerId < 0) return;
    
    // 先更新分类统计，再统一计算总处理数
    switch (result.status) {
        case EquipmentProcessResult::Success:
            m_successCount++;
            // 保存结果到数据库
            if (!saveEquipmentResult(result)) {
                qWarning() << QString("[Worker%1] 保存结果失败: %2").arg(workerId).arg(result.code);
            }
            break;
        case EquipmentProcessResult::Failed:
            m_failedCount++;
            break;
        case EquipmentProcessResult::NoPorts:
            m_noPortsCount++;
            break;
        case EquipmentProcessResult::Skipped:
            m_skippedCount++;
            break;
        default:
            break;
    }

    // 统一计算总处理器件数，确保与各类统计之和一致
    m_processedCount = m_successCount + m_failedCount + m_noPortsCount + m_skippedCount;
    
    // 写入日志
    writeLogResult(result);
    
    // 发送信号
    emit workerFinished(workerId, result);
    emit progressUpdated(m_processedCount, m_totalCount, 
                        m_successCount, m_failedCount, m_noPortsCount, m_skippedCount);
    
    // 处理事件，让 UI 有机会更新
    QCoreApplication::processEvents();
    
    // 清理工作线程映射
    m_workerThreads.remove(workerId);
    m_workers.remove(workerId);
    m_workerIds.remove(worker);
    
    // 启动下一个任务
    startNextTask(workerId);
}

void BatchAutoGenerateManager::writeLogStart()
{
    m_logStream << "# T-Designer Batch Auto Generate Log\n";
    m_logStream << QString("# Start Time: %1\n")
        .arg(QDateTime::currentDateTime().toString("yyyy-MM-dd HH:mm:ss"));
    m_logStream << QString("# Total Equipment: %1\n").arg(m_totalCount);
    m_logStream << QString("# Worker Count: %1\n").arg(m_workerCount);
    m_logStream << "\n";
    m_logStream.flush();
}

void BatchAutoGenerateManager::writeLogResult(const EquipmentProcessResult &result)
{
    QString timestamp = QDateTime::currentDateTime().toString("yyyy-MM-dd HH:mm:ss");
    QString statusStr = result.statusString();
    QString message = result.errorMessage.isEmpty() ? "OK" : result.errorMessage;
    
    m_logStream << QString("[RESULT] %1|%2|%3|%4|%5|%6\n")
        .arg(result.equipmentId)
        .arg(result.code)
        .arg(result.name)
        .arg(result.categoryName)
        .arg(statusStr)
        .arg(message);
    m_logStream.flush();
}

void BatchAutoGenerateManager::writeSkippedResults()
{
    if (m_skippedEquipmentIds.isEmpty()) {
        return;
    }

    // 为每个无Class_ID的器件创建EquipmentProcessResult并记录到日志
    for (int equipmentId : m_skippedEquipmentIds) {
        // 获取器件信息
        QSqlDatabase db = QSqlDatabase::database(m_connectionName);
        QSqlQuery query(db);
        query.prepare("SELECT PartCode, Name FROM Equipment WHERE Equipment_ID = ?");
        query.addBindValue(equipmentId);

        EquipmentProcessResult result;
        result.equipmentId = equipmentId;
        result.code = "";
        result.name = "";
        result.categoryName = "";
        result.status = EquipmentProcessResult::Skipped;
        result.errorMessage = "无Class_ID";

        if (query.exec() && query.next()) {
            result.code = query.value(0).toString();
            result.name = query.value(1).toString();
            result.categoryName = getCategoryPathInternal(equipmentId);
        }

        // 记录到日志
        writeLogResult(result);
    }

    qInfo() << QString("[BatchManager] 记录了 %1 个无Class_ID的器件到日志文件").arg(m_skippedEquipmentIds.size());
}

void BatchAutoGenerateManager::writeLogEnd()
{
    int elapsedSeconds = m_totalTimer.elapsed() / 1000;
    m_logStream << "\n";
    m_logStream << QString("# End Time: %1\n")
        .arg(QDateTime::currentDateTime().toString("yyyy-MM-dd HH:mm:ss"));
    m_logStream << QString("# Total Time: %1s\n").arg(elapsedSeconds);
    m_logStream << QString("# Success: %1, Failed: %2, NoPorts: %3, 无Class_ID: %4\n")
        .arg(m_successCount)
        .arg(m_failedCount)
        .arg(m_noPortsCount)
        .arg(m_skippedCount);
    m_logStream.flush();
}

// ========== 数据库操作方法 ==========

EquipmentInputData BatchAutoGenerateManager::loadEquipmentInputData(const EquipmentTask &task)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    EquipmentInputData data;
    data.equipmentId = task.equipmentId;
    data.code = task.code;
    data.name = task.name;
    data.categoryName = task.categoryPath;
    
    // 1. 查询器件描述
    QSqlQuery equipQuery(db);
    equipQuery.prepare("SELECT Desc FROM Equipment WHERE Equipment_ID = ?");
    equipQuery.addBindValue(task.equipmentId);
    if (equipQuery.exec() && equipQuery.next()) {
        data.description = equipQuery.value(0).toString();
    }
    
    // 2. 复用 TModelAutoGenerator::loadPortsFromDatabase 加载端口列表和描述
    TModelAutoGenerator::loadPortsFromDatabase(db, task.equipmentId, data.ports, &data.portDescriptions);
    
    // 3. 复用 TModelAutoGenerator::loadPortConfigsForEquipment 加载端口配置
    TModelAutoGenerator::loadPortConfigsForEquipment(db, task.equipmentId, data.portConfigs);
    
    return data;
}

bool BatchAutoGenerateManager::saveEquipmentResult(const EquipmentProcessResult &result)
{
    if (result.status != EquipmentProcessResult::Success) {
        return false;
    }
    
    // 1. 保存 T 模型
    if (!saveTModel(result.equipmentId, result.tmodel)) {
        qWarning() << "[BatchManager] 保存T模型失败:" << result.code;
        return false;
    }
    
    // 2. 保存端口配置（如果有更新）
    if (!result.updatedPortConfigs.isEmpty()) {
        int containerId = resolveContainerId(result.equipmentId);
        if (containerId <= 0) {
            qWarning() << "[BatchManager] 获取容器ID失败:" << result.code;
            return false;
        }
        
        if (!savePortConfigs(containerId, result.updatedPortConfigs)) {
            qWarning() << "[BatchManager] 保存端口配置失败:" << result.code;
            return false;
        }
    }
    
    return true;
}

bool BatchAutoGenerateManager::savePortConfigs(int containerId, 
                                                const QMap<QString, PortTypeConfig> &configs)
{
    if (configs.isEmpty()) {
        return true;
    }
    
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    QSqlQuery query(db);
    
    for (auto it = configs.constBegin(); it != configs.constEnd(); ++it) {
        const PortTypeConfig &config = it.value();
        
        // 标准化变量集合：拆分后独立存储 JSON 数组（与手动模式一致）
        QStringList varList = config.variables.split(QRegExp("[,;，；]"), QString::SkipEmptyParts);
        QJsonArray varArray;
        for (QString v : varList) {
            v = v.trimmed();
            if (!v.isEmpty()) {
                QJsonObject o;
                o["name"] = v;
                varArray.append(o);
            }
        }
        QString variablesJson = QString::fromUtf8(QJsonDocument(varArray).toJson(QJsonDocument::Compact));
        
        // 检查是否已存在（与手动模式一致）
        query.prepare(
            "SELECT port_config_id FROM port_config "
            "WHERE container_id = ? AND function_block = ? AND port_name = ?"
        );
        query.addBindValue(containerId);
        query.addBindValue(config.functionBlock);
        query.addBindValue(config.portName);
        
        if (!query.exec()) {
            qWarning() << "[BatchManager] 查询端口配置失败:" << query.lastError().text();
            continue;
        }
        
        if (query.next()) {
            // 更新已存在的记录
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
            // 插入新记录（包含 direction 和 variable_profile 字段）
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
            qWarning() << "[BatchManager] 保存端口配置失败:" << query.lastError().text();
            return false;
        }
    }
    
    return true;
}

bool BatchAutoGenerateManager::saveTModel(int equipmentId, const QString &tmodel)
{
    // 注意：此方法已废弃，实际使用 onWorkerRequestSaveModel 来保存
    // 保留此方法仅为兼容性，实际不应被调用
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    QSqlQuery query(db);
    
    // 与手动模式的 saveFullModel 一致：保存到 Equipment 表
    query.prepare("UPDATE Equipment SET TModel = ? WHERE Equipment_ID = ?");
    query.addBindValue(tmodel);
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 更新TModel失败:" << query.lastError().text();
        return false;
    }
    
    return true;
}

int BatchAutoGenerateManager::resolveContainerId(int equipmentId)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    // 使用与手动模式相同的逻辑：ContainerRepository + ContainerHierarchy
    ContainerRepository repo(db);
    if (!repo.ensureTables()) {
        qWarning() << "[BatchManager] ensureTables failed";
        return 0;
    }
    
    // 查询是否已有容器映射
    int existing = repo.componentContainerIdForEquipment(equipmentId);
    if (existing != 0) {
        return existing;
    }
    
    // 不存在则创建新容器（使用统一的容器层次结构）
    int created = ContainerHierarchy::ensureComponentContainer(repo, db, equipmentId);
    if (created == 0) {
        qWarning() << "[BatchManager] ensureComponentContainer failed for equipment" << equipmentId;
        return 0;
    }
    
    return created;
}

void BatchAutoGenerateManager::onWorkerRequestSavePortConfigs(int equipmentId, const QMap<QString, PortTypeConfig> &configs)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    if (!db.isOpen()) {
        qWarning() << "[BatchManager] 数据库未打开，无法保存端口配置";
        return;
    }
    
    int containerId = resolveContainerId(equipmentId);
    if (containerId <= 0) {
        qWarning() << "[BatchManager] 无法获取 container_id";
        return;
    }
    
    bool success = savePortConfigs(containerId, configs);
    if (!success) {
        qWarning() << "[BatchManager] 端口配置保存失败: equipmentId=" << equipmentId;
    }
}

void BatchAutoGenerateManager::onWorkerRequestSaveModel(int equipmentId, const QString &tmodel, const QMap<QString, QString> &constants)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    if (!db.isOpen()) {
        qWarning() << "[BatchManager] 数据库未打开，无法保存T模型";
        return;
    }
    
    // 1. 序列化常量为 Structure 字段格式 (name,value,unit,remark;...)
    QString structureData;
    if (!constants.isEmpty()) {
        QStringList items;
        for (auto it = constants.constBegin(); it != constants.constEnd(); ++it) {
            const QString &name = it.key();
            const QString &value = it.value();
            if (name.trimmed().isEmpty()) continue;
            items << QString("%1,%2,,").arg(name, value); // 单位与备注留空
        }
        structureData = items.join(";");
    }
    
    // 2. 保存 TModel 和 Structure
    QSqlQuery query(db);
    query.prepare("UPDATE Equipment SET TModel = :TModel, Structure = :Structure WHERE Equipment_ID = :EID");
    query.bindValue(":TModel", tmodel);
    query.bindValue(":Structure", structureData);
    query.bindValue(":EID", equipmentId);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 保存T模型和常量失败:" << query.lastError().text();
    }
}

void BatchAutoGenerateManager::onWorkerRequestClearModel(int equipmentId)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    if (!db.isOpen()) {
        qWarning() << QString("[BatchManager] Worker请求清空T模型失败: equipmentId=%1, 数据库未打开").arg(equipmentId);
        return;
    }
    
    // 同时清空 TModel 和 Structure（常量表）
    QSqlQuery query(db);
    if (!query.prepare("UPDATE Equipment SET TModel = '', Structure = '' WHERE Equipment_ID = ?")) {
        qWarning() << "[BatchManager] 清空T模型与常量prepare失败:" << query.lastError().text();
        return;
    }
    
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 清空T模型与常量exec失败:" << query.lastError().text();
    }
}
