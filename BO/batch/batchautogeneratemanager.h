#ifndef BATCHAUTOGENERATEMANAGER_H
#define BATCHAUTOGENERATEMANAGER_H

#include <QObject>
#include <QSqlDatabase>
#include <QQueue>
#include <QSet>
#include <QMap>
#include <QElapsedTimer>
#include <QFile>
#include <QTextStream>
#include <QMutex>
#include "singleequipmentworker.h"

// 器件任务信息
struct EquipmentTask {
    int equipmentId;
    QString code;
    QString name;
    QString categoryPath;
    int categoryIndex;  // 用于排序
};

// 批量自动生成管理器
class BatchAutoGenerateManager : public QObject
{
    Q_OBJECT

public:
    explicit BatchAutoGenerateManager(const QSqlDatabase &db, QObject *parent = nullptr);
    ~BatchAutoGenerateManager();

    // 开始批量处理
    void start(const QString &logFilePath, bool resumeFromLog, int workerCount = 1, bool enableWorkerLog = false);
    
    // 停止处理
    void stop();
    
    // 获取统计信息
    int getTotalCount() const { return m_totalCount; }
    int getProcessedCount() const { return m_processedCount; }
    int getSuccessCount() const { return m_successCount; }
    int getFailedCount() const { return m_failedCount; }
    int getNoPortsCount() const { return m_noPortsCount; }
    int getSkippedCount() const { return m_skippedCount; }

signals:
    void started(int totalCount);  // 开始处理
    void workerStarted(int workerId, const QString &code, const QString &name);  // 工作线程开始处理器件
    void workerLogMessage(int workerId, const QString &message);  // 工作线程日志
    void workerStreamDelta(int workerId, const QString &delta);  // 工作线程 AI 流式输出
    void workerFinished(int workerId, const EquipmentProcessResult &result);  // 工作线程完成
    void progressUpdated(int processed, int total, int success, int failed, int noPorts, int skipped);  // 进度更新
    void finished();  // 全部完成

private slots:
    void onWorkerFinished(const EquipmentProcessResult &result);
    void onWorkerRequestSavePortConfigs(int equipmentId, const QMap<QString, PortTypeConfig> &configs);
    void onWorkerRequestSaveModel(int equipmentId, const QString &tmodel, const QMap<QString, QString> &constants);
    void onWorkerRequestClearModel(int equipmentId);

private:
    QString m_connectionName;  // 数据库连接名（而非拷贝对象）
    QString m_logFilePath;
    QFile m_logFile;
    QTextStream m_logStream;
    QElapsedTimer m_totalTimer;
    
    // 队列管理
    QQueue<EquipmentTask> m_taskQueue;
    QSet<int> m_processedEquipmentIds;  // 已处理的器件ID（本次运行）
    int m_lastLoadedEquipmentId;         // 上次加载到的最大 Equipment_ID
    int m_totalEquipmentCount;           // 数据库中总器件数（用于进度显示）
    
    // 工作线程管理
    int m_workerCount;
    bool m_enableWorkerLog;  // 是否启用 Worker 详细日志文件
    QMap<int, QThread*> m_workerThreads;         // workerId -> QThread
    QMap<int, SingleEquipmentWorker*> m_workers; // workerId -> Worker
    QMap<QObject*, int> m_workerIds;             // Worker -> workerId
    
    // 统计信息
    int m_totalCount;
    int m_processedCount;
    int m_successCount;
    int m_failedCount;
    int m_noPortsCount;
    int m_skippedCount;
    
    bool m_stopped;
    
    // 初始化方法
    bool initializeLogFile(bool resumeFromLog);
    void loadTaskQueue();
    void parseLogAndMarkProcessed(const QString &logFilePath);
    
    // 队列管理
    void createWorkers();
    void startNextTask(int workerId);
    void assignTaskToWorker(int workerId, const EquipmentTask &task);
    bool loadMoreTasksIfNeeded();  // 当队列少于阈值时加载更多任务
    int loadBatchTasks(int batchSize);  // 分批加载任务
    
    // 日志记录
    void writeLogStart();
    void writeLogResult(const EquipmentProcessResult &result);
    void writeLogEnd();
    
    // 辅助方法
    QString getCategoryPath(int equipmentId);
    QString getCategoryPathInternal(int equipmentId);  // 内部方法：调用者需持有锁
    
    // 数据库操作（为Worker准备数据、保存结果）
    EquipmentInputData loadEquipmentInputData(const EquipmentTask &task);
    bool saveEquipmentResult(const EquipmentProcessResult &result);
    bool savePortConfigs(int containerId, const QMap<QString, PortTypeConfig> &configs);
    bool saveTModel(int equipmentId, const QString &tmodel);
    int resolveContainerId(int equipmentId);
};

#endif // BATCHAUTOGENERATEMANAGER_H
