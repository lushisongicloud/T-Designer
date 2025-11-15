# 批量自动编写处理器件数量显示修复

## 问题描述

批量自动编写T语言模型功能中，已处理器件数量显示不正确：
- 界面显示的processorCount可能比实际的[RESULT]日志行数大
- 存在重复计数问题

## 问题根源

### 1. NoPorts器件重复计数
在`assignTaskToWorker()`中处理NoPorts器件时：
```cpp
// 第485行 - 第一次计数
m_processedCount++;
m_noPortsCount++;
writeLogResult(result);
emit workerFinished(workerId, result);  // 触发onWorkerFinished
```

在`onWorkerFinished()`中又被计数一次：
```cpp
// 第551行 - 第二次计数（重复了！）
m_processedCount++;
m_noPortsCount++;
```

**结果**：NoPorts器件被计算了两次。

### 2. 跳过器件未立即更新UI
跳过器件（Class_ID为空）在`loadBatchTasks()`中被计数：
```cpp
m_skippedCount++;  // 但界面不会立即更新
```

但UI进度条不会立即更新，直到第一个真正处理的器件完成。

### 3. 统计公式不一致
理论上应该是：
```
m_processedCount = m_successCount + m_failedCount + m_noPortsCount + m_skippedCount
```

但实际代码中这个公式不成立，因为有重复计数。

## 修复方案

### 修复1：移除重复计数
**文件**: `BO/batch/batchautogeneratemanager.cpp`
**函数**: `assignTaskToWorker()`

```cpp
// 修改前：
QMetaObject::invokeMethod(this, [this, workerId, result]() {
    m_processedCount++;        // ← 移除这行，避免重复计数
    m_noPortsCount++;
    writeLogResult(result);
    emit workerFinished(workerId, result);
    ...
}, Qt::QueuedConnection);

// 修改后：
QMetaObject::invokeMethod(this, [this, workerId, result]() {
    // 不在这里增加m_processedCount，避免重复计数
    // 统一在onWorkerFinished中计算总处理数
    m_noPortsCount++;
    writeLogResult(result);
    emit workerFinished(workerId, result);
    ...
}, Qt::QueuedConnection);
```

### 修复2：统一计算总处理数
**文件**: `BO/batch/batchautogeneratemanager.cpp`
**函数**: `onWorkerFinished()`

```cpp
// 修改前：
m_processedCount++;  // 手动增加
switch (result.status) {
    case EquipmentProcessResult::Success:
        m_successCount++;
        ...
    case EquipmentProcessResult::Failed:
        m_failedCount++;
        ...
    case EquipmentProcessResult::NoPorts:
        m_noPortsCount++;
        break;
}

// 修改后：
switch (result.status) {
    case EquipmentProcessResult::Success:
        m_successCount++;
        ...
    case EquipmentProcessResult::Failed:
        m_failedCount++;
        ...
    case EquipmentProcessResult::NoPorts:
        m_noPortsCount++;
        break;
    case EquipmentProcessResult::Skipped:  // 新增
        m_skippedCount++;
        break;
}

// 统一计算总处理器件数，确保与各类统计之和一致
m_processedCount = m_successCount + m_failedCount + m_noPortsCount + m_skippedCount;
```

### 修复3：立即更新UI进度
**文件**: `BO/batch/batchautogeneratemanager.cpp`
**函数**: `start()`

```cpp
// 在writeSkippedResults()后添加：
// 5. 记录跳过的器件到日志文件
writeSkippedResults();

// 6. 立即更新UI进度，显示跳过的器件（不触发workerFinished）
emit progressUpdated(m_skippedCount, m_totalCount,
                    m_successCount, m_failedCount, m_noPortsCount, m_skippedCount);

// 7. 创建工作线程
m_totalTimer.start();
createWorkers();
```

## 修复后效果

### 统计公式正确
```
m_processedCount = m_successCount + m_failedCount + m_noPortsCount + m_skippedCount
```

### 日志行数一致
- 日志文件中的`[RESULT]`行数 = `m_processedCount`
- 界面显示的已处理数 = `m_processedCount`

### 进度条正确
- 初始进度显示跳过的器件数
- 每处理一个器件，进度+1
- 进度条最大值为`m_totalCount`

## 测试建议

### 测试用例1：正常处理
1. 创建10个有效器件
2. 执行批量处理
3. 验证：进度条从0到10
4. 验证：日志中有10条[RESULT]记录

### 测试用例2：有跳过器件
1. 创建10个器件，其中3个Class_ID为空
2. 执行批量处理
3. 验证：
   - 初始进度显示：已处理=3 (跳过)，总数=10
   - 完成后进度：已处理=10，日志有10条[RESULT]记录
   - 统计：成功+失败+NoPorts=7，跳过=3

### 测试用例3：全跳过
1. 创建5个器件，全部Class_ID为空
2. 执行批量处理
3. 验证：
   - 初始进度：已处理=5，总数=5
   - 完成后：已处理=5，日志有5条[RESULT]记录
   - 统计：跳过=5

### 测试用例4：恢复模式
1. 执行测试用例2，生成日志
2. 使用相同日志恢复
3. 验证：
   - 初始进度显示：已处理=8（3跳过+5已处理），总数=10
   - 只处理剩余的2个器件

## 总结

本次修复解决了批量自动编写中处理器件数量显示不准确的问题：
- ✅ 消除重复计数
- ✅ 统一统计公式
- ✅ 正确显示跳过器件
- ✅ 日志行数与显示数量一致

修复后的统计更加准确可靠。
