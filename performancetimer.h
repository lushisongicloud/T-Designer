#ifndef PERFORMANCETIMER_H
#define PERFORMANCETIMER_H

#include <QString>
#include <QDebug>
#include <QElapsedTimer>
#include <QMap>
#include <QVector>

/**
 * @brief PerformanceTimer 类用于精确测量代码执行时间
 * 
 * 使用方法:
 * 1. 在需要测量的函数开始处创建 PerformanceTimer 对象
 * 2. 使用 checkpoint() 记录关键节点
 * 3. 析构时自动输出总时间
 * 
 * 示例:
 * PerformanceTimer timer("LoadProject");
 * // ... 一些代码 ...
 * timer.checkpoint("数据库打开完成");
 * // ... 更多代码 ...
 * timer.checkpoint("页面加载完成");
 */
class PerformanceTimer
{
public:
    /**
     * @brief 构造函数,开始计时
     * @param label 计时器标签,用于识别不同的测量点
     */
    explicit PerformanceTimer(const QString &label)
        : m_label(label)
        , m_startTime(0)
        , m_lastCheckpoint(0)
    {
        m_timer.start();
        m_startTime = m_timer.elapsed();
        m_lastCheckpoint = m_startTime;
        // 移除详细开始日志，只保留总结
    }

    /**
     * @brief 析构函数,输出总执行时间
     */
    ~PerformanceTimer()
    {
        qint64 totalTime = m_timer.elapsed() - m_startTime;
        qDebug() << QString("<<< [性能分析] %1 完成，总耗时: %2 毫秒")
                        .arg(m_label)
                        .arg(totalTime);
        
        if (!m_checkpoints.isEmpty()) {
            qDebug() << QString("--- [性能分析] %1 检查点详情:").arg(m_label);
            for (const CheckpointInfo &cp : m_checkpoints) {
                qDebug() << QString("    %1: %2 毫秒 (累计: %3 毫秒)")
                                .arg(cp.name)
                                .arg(cp.duration)
                                .arg(cp.elapsed);
            }
        }
    }

    /**
     * @brief 记录一个检查点
     * @param name 检查点名称
     * @param additionalInfo 附加信息(如数量统计)
     */
    void checkpoint(const QString &name, const QString &additionalInfo = QString())
    {
        qint64 now = m_timer.elapsed();
        qint64 duration = now - m_lastCheckpoint;
        qint64 elapsed = now - m_startTime;

        CheckpointInfo info;
        info.name = name;
        info.duration = duration;
        info.elapsed = elapsed;
        info.additionalInfo = additionalInfo;
        m_checkpoints.append(info);

        // 移除详细的checkpoint日志，只在析构时打印累计统计
        m_lastCheckpoint = now;
    }

    /**
     * @brief 获取从开始到现在的总时间
     * @return 毫秒数
     */
    qint64 elapsed() const
    {
        return m_timer.elapsed() - m_startTime;
    }

    /**
     * @brief 重置计时器
     */
    void reset()
    {
        m_checkpoints.clear();
        m_timer.restart();
        m_startTime = m_timer.elapsed();
        m_lastCheckpoint = m_startTime;
    }

private:
    struct CheckpointInfo {
        QString name;
        qint64 duration;  // 与上一个检查点的间隔
        qint64 elapsed;   // 从开始到现在的累计时间
        QString additionalInfo;
    };

    QString m_label;
    QElapsedTimer m_timer;
    qint64 m_startTime;
    qint64 m_lastCheckpoint;
    QVector<CheckpointInfo> m_checkpoints;
};

/**
 * @brief QueryPerformanceHelper 用于测量数据库查询性能
 */
class QueryPerformanceHelper
{
public:
    /**
     * @brief 记录一次查询
     * @param queryLabel 查询标签
     * @param sqlQuery SQL语句(可选)
     * @param rowCount 返回的行数(可选)
     */
    static void logQuery(const QString &queryLabel, 
                        const QString &sqlQuery = QString(), 
                        int rowCount = -1)
    {
        QString msg = QString("[数据库查询] %1").arg(queryLabel);
        if (!sqlQuery.isEmpty()) {
            msg += QString(" | SQL: %1").arg(sqlQuery.left(100));
        }
        if (rowCount >= 0) {
            msg += QString(" | 返回行数: %1").arg(rowCount);
        }
        qDebug() << msg;
    }

    /**
     * @brief 带计时的查询日志
     */
    class ScopedQueryLog
    {
    public:
        explicit ScopedQueryLog(const QString &label, const QString &sql = QString())
            : m_label(label), m_sql(sql)
        {
            m_timer.start();
            qDebug() << QString("[查询开始] %1").arg(m_label);
            if (!m_sql.isEmpty()) {
                qDebug() << QString("  SQL: %1").arg(m_sql.left(150));
            }
        }

        ~ScopedQueryLog()
        {
            qint64 elapsed = m_timer.elapsed();
            qDebug() << QString("[查询完成] %1 耗时: %2 毫秒").arg(m_label).arg(elapsed);
        }

        void setRowCount(int count)
        {
            qDebug() << QString("  返回行数: %1").arg(count);
        }

    private:
        QString m_label;
        QString m_sql;
        QElapsedTimer m_timer;
    };
};

// 便捷宏定义
#define PERF_TIMER(label) PerformanceTimer __perfTimer##__LINE__(label)
#define PERF_CHECKPOINT(name) __perfTimer##__LINE__.checkpoint(name)
#define PERF_CHECKPOINT_INFO(name, info) __perfTimer##__LINE__.checkpoint(name, info)

#endif // PERFORMANCETIMER_H
