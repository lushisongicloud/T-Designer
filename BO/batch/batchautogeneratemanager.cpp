#include "batchautogeneratemanager.h"
#include "../ai/tmodelautogenerator.h"  // 包含 PortTypeConfig 完整定义
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
    , m_totalCount(0)
    , m_processedCount(0)
    , m_successCount(0)
    , m_failedCount(0)
    , m_noPortsCount(0)
    , m_skippedCount(0)
    , m_stopped(false)
    , m_lastLoadedEquipmentId(0)
    , m_totalEquipmentCount(0)
{
    // 注册元类型，以便在跨线程信号槽中使用
    qRegisterMetaType<EquipmentProcessResult>("EquipmentProcessResult");
    qRegisterMetaType<QMap<QString, PortTypeConfig>>("QMap<QString,PortTypeConfig>");
    
    qInfo() << QString("[BatchManager] 构造函数 - 连接名: %1").arg(m_connectionName);
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
                                      int workerCount)
{
    m_logFilePath = logFilePath;
    m_workerCount = qMax(1, workerCount);
    m_stopped = false;
    
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
    
    m_totalCount = m_taskQueue.size() + m_skippedCount;
    
    if (m_taskQueue.isEmpty()) {
        qInfo() << "[BatchManager] 没有待处理的器件";
        writeLogEnd();
        emit finished();
        return;
    }
    
    qInfo() << QString("[BatchManager] 开始批量处理: 总数=%1, 待处理=%2, 已跳过=%3, 工作线程=%4")
        .arg(m_totalCount)
        .arg(m_taskQueue.size())
        .arg(m_skippedCount)
        .arg(m_workerCount);
    
    // 4. 写入日志头部
    writeLogStart();
    
    // 5. 创建工作线程
    m_totalTimer.start();
    createWorkers();
    
    emit started(m_totalCount);
}

void BatchAutoGenerateManager::stop()
{
    if (m_stopped) return;
    
    m_stopped = true;
    qInfo() << "[BatchManager] 停止批量处理";
    
    // 先断开所有信号连接，避免在清理过程中触发回调
    for (auto worker : m_workers) {
        if (worker) {
            disconnect(worker, nullptr, this, nullptr);
        }
    }
    
    // 停止所有工作线程
    for (auto thread : m_workerThreads) {
        if (thread && thread->isRunning()) {
            thread->quit();
            if (!thread->wait(3000)) {  // 等待最多3秒
                qWarning() << "[BatchManager] 工作线程未能正常退出，强制终止";
                thread->terminate();
                thread->wait();
            }
        }
    }
    
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
    
    int skippedCount = 0;
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
        
        // 只跳过 success 和 NoPorts 的器件
        if (status == "success" || status == "NoPorts") {
            m_processedEquipmentIds.insert(equipmentId);
            skippedCount++;
            
            if (status == "success") m_successCount++;
            else if (status == "NoPorts") m_noPortsCount++;
        }
    }
    
    file.close();
    
    m_skippedCount = skippedCount;
    qInfo() << QString("[BatchManager] 从日志恢复: 跳过 %1 个已完成器件").arg(skippedCount);
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
    
    // 初始加载第一批任务（loadBatchTasks 内部会加锁）
    qInfo() << "[BatchManager] 开始初始加载任务...";
    int loaded = loadBatchTasks(20);
    qInfo() << QString("[BatchManager] 初始加载任务完成: %1 个器件").arg(loaded);
    qInfo() << QString("[BatchManager] 当前队列大小: %1").arg(m_taskQueue.size());
}

int BatchAutoGenerateManager::loadBatchTasks(int batchSize)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    qInfo() << QString("[BatchManager] loadBatchTasks: batchSize=%1, lastLoadedId=%2")
        .arg(batchSize).arg(m_lastLoadedEquipmentId);
    
    int loadedCount = 0;
    
    // 从上次加载的位置继续，按 Equipment_ID 升序加载
    QSqlQuery query(db);
    query.prepare(
        "SELECT Equipment_ID, PartCode, Name, Class_ID "
        "FROM Equipment "
        "WHERE Equipment_ID > ? "
        "ORDER BY Equipment_ID "
        "LIMIT ?"
    );
    query.addBindValue(m_lastLoadedEquipmentId);
    query.addBindValue(batchSize);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 加载器件任务失败:" << query.lastError().text();
        return 0;
    }
    
    qInfo() << "[BatchManager] SQL查询执行成功，开始遍历结果...";
    
    int rowCount = 0;
    while (query.next()) {
        rowCount++;
        int equipmentId = query.value(0).toInt();
        
        // 跳过已处理的器件
        if (m_processedEquipmentIds.contains(equipmentId)) {
            m_lastLoadedEquipmentId = equipmentId;
            qInfo() << QString("[BatchManager] 跳过已处理器件: ID=%1").arg(equipmentId);
            continue;
        }
        
        EquipmentTask task;
        task.equipmentId = equipmentId;
        task.code = query.value(1).toString();
        task.name = query.value(2).toString();
        task.categoryPath = getCategoryPathInternal(equipmentId);  // 使用内部方法（已持有锁）
        task.categoryIndex = 0;  // 不再使用类别索引
        
        m_taskQueue.enqueue(task);
        m_lastLoadedEquipmentId = equipmentId;
        loadedCount++;
        
        if (loadedCount <= 3 || loadedCount == batchSize) {
            qInfo() << QString("[BatchManager] 加载任务 #%1: ID=%2, Code=%3, Name=%4")
                .arg(loadedCount).arg(equipmentId).arg(task.code).arg(task.name);
        }
    }
    
    qInfo() << QString("[BatchManager] loadBatchTasks 完成: 查询返回%1行, 加载%2个任务")
        .arg(rowCount).arg(loadedCount);
    
    return loadedCount;
}

bool BatchAutoGenerateManager::loadMoreTasksIfNeeded()
{
    // 当队列少于10个时，尝试加载更多
    const int QUEUE_LOW_THRESHOLD = 10;
    const int BATCH_SIZE = 20;
    
    if (m_taskQueue.size() < QUEUE_LOW_THRESHOLD) {
        int loaded = loadBatchTasks(BATCH_SIZE);
        if (loaded > 0) {
            qInfo() << QString("[BatchManager] 队列补充: 加载了 %1 个新任务，当前队列: %2")
                .arg(loaded).arg(m_taskQueue.size());
            
            // 更新总数（因为可能有新加载的）
            m_totalCount = m_skippedCount + m_processedCount + m_taskQueue.size();
            
            return true;
        } else {
            qInfo() << "[BatchManager] 没有更多器件可加载";
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
    qInfo() << QString("[BatchManager] createWorkers: 创建 %1 个工作线程").arg(m_workerCount);
    qInfo() << QString("[BatchManager] 当前队列大小: %1").arg(m_taskQueue.size());
    
    for (int i = 0; i < m_workerCount; ++i) {
        qInfo() << QString("[BatchManager] 启动 Worker%1...").arg(i);
        startNextTask(i);
    }
    
    qInfo() << "[BatchManager] createWorkers 完成";
}

void BatchAutoGenerateManager::startNextTask(int workerId)
{
    qInfo() << QString("[BatchManager] startNextTask: Worker%1 开始").arg(workerId);
    
    if (m_stopped) {
        qInfo() << QString("[BatchManager] Worker%1: 已停止，退出").arg(workerId);
        return;
    }
    
    qInfo() << QString("[BatchManager] Worker%1: 当前队列大小=%2").arg(workerId).arg(m_taskQueue.size());
    
    // 队列不足时尝试加载更多
    qInfo() << QString("[BatchManager] Worker%1: 检查是否需要加载更多任务...").arg(workerId);
    loadMoreTasksIfNeeded();
    
    qInfo() << QString("[BatchManager] Worker%1: 检查后队列大小=%2").arg(workerId).arg(m_taskQueue.size());
    
    // 从队列取任务
    if (m_taskQueue.isEmpty()) {
        // 队列为空，检查是否所有工作线程都完成
        if (m_workers.isEmpty()) {
            // 全部完成
            qInfo() << "[BatchManager] 所有任务已完成";
            writeLogEnd();
            emit finished();
        } else {
            qInfo() << QString("[BatchManager] 队列为空，但还有 %1 个 Worker 正在运行").arg(m_workers.size());
        }
        return;
    }
    
    EquipmentTask task = m_taskQueue.dequeue();
    qInfo() << QString("[BatchManager] Worker%1 从队列取出任务: ID=%2, Code=%3, Name=%4")
        .arg(workerId).arg(task.equipmentId).arg(task.code).arg(task.name);
    assignTaskToWorker(workerId, task);
}

void BatchAutoGenerateManager::assignTaskToWorker(int workerId, const EquipmentTask &task)
{
    qInfo() << QString("[BatchManager] assignTaskToWorker: Worker%1, 器件=%2")
        .arg(workerId).arg(task.code);
    
    // 调试：检查当前线程
    qInfo() << QString("[BatchManager] assignTaskToWorker 在线程 %1 中执行")
        .arg((quintptr)QThread::currentThreadId());
    
    // 1. 从数据库加载输入数据
    qInfo() << QString("[BatchManager] Worker%1: 开始加载器件数据...").arg(workerId);
    EquipmentInputData inputData = loadEquipmentInputData(task);
    qInfo() << QString("[BatchManager] Worker%1: 加载完成, 端口数=%2, 配置数=%3")
        .arg(workerId).arg(inputData.ports.size()).arg(inputData.portConfigs.size());
    
    // 2. 检查是否有有效端口（提前过滤）
    if (inputData.ports.isEmpty()) {
        qInfo() << QString("[Worker%1] 器件 %2 无有效端号，跳过").arg(workerId).arg(task.code);
        
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
            m_processedCount++;
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
    qInfo() << QString("[BatchManager] 创建Worker%1 - 传递连接名: %2").arg(workerId).arg(m_connectionName);
    
    QThread *thread = new QThread(this);
    SingleEquipmentWorker *worker = new SingleEquipmentWorker(m_connectionName, inputData);
    
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
    
    emit workerStarted(workerId, task.code, task.name);
    
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
    
    // 更新统计
    m_processedCount++;
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
        default:
            break;
    }
    
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

void BatchAutoGenerateManager::writeLogEnd()
{
    int elapsedSeconds = m_totalTimer.elapsed() / 1000;
    m_logStream << "\n";
    m_logStream << QString("# End Time: %1\n")
        .arg(QDateTime::currentDateTime().toString("yyyy-MM-dd HH:mm:ss"));
    m_logStream << QString("# Total Time: %1s\n").arg(elapsedSeconds);
    m_logStream << QString("# Success: %1, Failed: %2, NoPorts: %3, Skipped: %4\n")
        .arg(m_successCount)
        .arg(m_failedCount)
        .arg(m_noPortsCount)
        .arg(m_skippedCount);
    m_logStream.flush();
}

// ========== 数据库操作方法 ==========

EquipmentInputData BatchAutoGenerateManager::loadEquipmentInputData(const EquipmentTask &task)
{
    qInfo() << QString("[BatchManager] loadEquipmentInputData: ID=%1, Code=%2")
        .arg(task.equipmentId).arg(task.code);
    
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    EquipmentInputData data;
    data.equipmentId = task.equipmentId;
    data.code = task.code;
    data.name = task.name;
    data.categoryName = task.categoryPath;
    
    // 1. 查询器件描述
    qInfo() << QString("[BatchManager] 查询器件描述: ID=%1").arg(task.equipmentId);
    QSqlQuery equipQuery(db);
    equipQuery.prepare("SELECT Desc FROM Equipment WHERE Equipment_ID = ?");
    equipQuery.addBindValue(task.equipmentId);
    if (equipQuery.exec() && equipQuery.next()) {
        data.description = equipQuery.value(0).toString();
        qInfo() << QString("[BatchManager] 器件描述: %1").arg(data.description.left(50));
    } else {
        qInfo() << QString("[BatchManager] 查询器件描述失败或无数据");
    }
    
    // 2. 复用 TModelAutoGenerator::loadPortsFromDatabase 加载端口列表
    qInfo() << QString("[BatchManager] 加载端口列表: ID=%1").arg(task.equipmentId);
    TModelAutoGenerator::loadPortsFromDatabase(db, task.equipmentId, data.ports);
    qInfo() << QString("[BatchManager] 端口数量: %1").arg(data.ports.size());
    
    // 3. 复用 TModelAutoGenerator::loadPortConfigsForEquipment 加载端口配置
    qInfo() << QString("[BatchManager] 加载端口配置: ID=%1").arg(task.equipmentId);
    TModelAutoGenerator::loadPortConfigsForEquipment(db, task.equipmentId, data.portConfigs);
    qInfo() << QString("[BatchManager] 端口配置数量: %1").arg(data.portConfigs.size());
    
    qInfo() << QString("[BatchManager] loadEquipmentInputData 完成: ID=%1").arg(task.equipmentId);
    
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
        
        // 构建 variables_json
        QJsonArray varsArray;
        QStringList vars = config.variables.split(",", QString::SkipEmptyParts);
        for (const QString &var : vars) {
            QJsonObject obj;
            obj["name"] = var.trimmed();
            varsArray.append(obj);
        }
        QString varsJson = QString::fromUtf8(QJsonDocument(varsArray).toJson(QJsonDocument::Compact));
        
        // INSERT OR REPLACE
        query.prepare(
            "INSERT OR REPLACE INTO port_config "
            "(container_id, function_block, port_name, port_type, variables_json, connect_macro) "
            "VALUES (?, ?, ?, ?, ?, ?)"
        );
        query.addBindValue(containerId);
        query.addBindValue(config.functionBlock);
        query.addBindValue(config.portName);
        query.addBindValue(config.portType);
        query.addBindValue(varsJson);
        query.addBindValue(config.connectMacro);
        
        if (!query.exec()) {
            qWarning() << "[BatchManager] 保存端口配置失败:" << query.lastError().text();
            return false;
        }
    }
    
    return true;
}

bool BatchAutoGenerateManager::saveTModel(int equipmentId, const QString &tmodel)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    QSqlQuery query(db);
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
    
    // 查询是否已有容器映射
    QSqlQuery query(db);
    query.prepare("SELECT container_id FROM equipment_containers WHERE equipment_id = ?");
    query.addBindValue(equipmentId);
    
    if (query.exec() && query.next()) {
        int containerId = query.value(0).toInt();
        if (containerId > 0) {
            return containerId;
        }
    }
    
    // 不存在则创建新容器ID（简化：使用 equipment_id 作为 container_id）
    int newContainerId = equipmentId;
    
    query.prepare("INSERT OR REPLACE INTO equipment_containers (equipment_id, container_id) VALUES (?, ?)");
    query.addBindValue(equipmentId);
    query.addBindValue(newContainerId);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 创建容器映射失败:" << query.lastError().text();
        return 0;
    }
    
    return newContainerId;
}

void BatchAutoGenerateManager::onWorkerRequestSavePortConfigs(int equipmentId, const QMap<QString, PortTypeConfig> &configs)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    qInfo() << QString("[BatchManager] Worker请求保存端口配置: equipmentId=%1, 配置数=%2")
        .arg(equipmentId).arg(configs.size());
    
    if (!db.isOpen()) {
        qWarning() << "[BatchManager] 数据库未打开，无法保存端口配置";
        return;
    }
    
    int containerId = resolveContainerId(equipmentId);
    if (containerId <= 0) {
        qWarning() << "[BatchManager] 无法获取 container_id";
        return;
    }
    
    savePortConfigs(containerId, configs);
}

void BatchAutoGenerateManager::onWorkerRequestSaveModel(int equipmentId, const QString &tmodel, const QMap<QString, QString> &constants)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    qInfo() << QString("[BatchManager] Worker请求保存T模型: equipmentId=%1, 模型长度=%2, 常量数=%3")
        .arg(equipmentId).arg(tmodel.length()).arg(constants.size());
    
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
        qInfo() << QString("[BatchManager] 序列化常量数据: %1").arg(structureData);
    }
    
    // 2. 保存 TModel 和 Structure
    QSqlQuery query(db);
    query.prepare("UPDATE Equipment SET TModel = :TModel, Structure = :Structure WHERE Equipment_ID = :EID");
    query.bindValue(":TModel", tmodel);
    query.bindValue(":Structure", structureData);
    query.bindValue(":EID", equipmentId);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 保存T模型和常量失败:" << query.lastError().text();
        return;
    }
    
    qInfo() << QString("[BatchManager] T模型和常量保存成功: equipmentId=%1").arg(equipmentId);
}

void BatchAutoGenerateManager::onWorkerRequestClearModel(int equipmentId)
{
    QSqlDatabase db = QSqlDatabase::database(m_connectionName);
    
    if (!db.isOpen()) {
        qWarning() << QString("[BatchManager] Worker请求清空T模型失败: equipmentId=%1, 数据库未打开").arg(equipmentId);
        return;
    }
    
    qInfo() << QString("[BatchManager] Worker请求清空T模型与常量: equipmentId=%1").arg(equipmentId);
    
    // 同时清空 TModel 和 Structure（常量表）
    QSqlQuery query(db);
    if (!query.prepare("UPDATE Equipment SET TModel = '', Structure = '' WHERE Equipment_ID = ?")) {
        qWarning() << "[BatchManager] 清空T模型与常量prepare失败:" << query.lastError().text();
        return;
    }
    
    query.addBindValue(equipmentId);
    
    if (!query.exec()) {
        qWarning() << "[BatchManager] 清空T模型与常量exec失败:" << query.lastError().text();
    } else {
        qInfo() << QString("[BatchManager] T模型与常量清空成功: equipmentId=%1").arg(equipmentId);
    }
}
