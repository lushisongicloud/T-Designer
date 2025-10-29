#include "solverrunnable.h"

// 此处可以添加 z3Solve 函数的定义，或者确保其定义在其他合适的源文件中

SolverRunnable::SolverRunnable(const QString &code, int index, QVector<int> &excludedIndexes, QMutex &mutex)
        : m_code(code), m_index(index), m_excludedIndexes(excludedIndexes), m_mutex(mutex) {}

void SolverRunnable::run()
{
    if (!z3Solve(m_code)) {
        QMutexLocker locker(&m_mutex);
        m_excludedIndexes.append(m_index);
    }
}
