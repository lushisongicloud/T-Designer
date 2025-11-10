# 诊断UI优化修复总结

## 修改日期
2025-11-10

## 问题描述与解决方案

### 问题1：诊断完成对话框弹出两遍

**原因分析：**
- `DiagnosisEngine`的`faultIsolated`信号连接到了`showDiagnosisResult()`槽函数
- `recordTestResult()`调用`displayCurrentTest()`后，`displayCurrentTest()`检测到故障隔离时也会调用`showDiagnosisResult()`
- 导致同一个诊断完成事件触发了两次`showDiagnosisResult()`调用

**解决方案：**
- 移除了`faultIsolated`信号的连接
- 仅在`displayCurrentTest()`中检测到故障隔离时调用`showDiagnosisResult()`
- 确保每次诊断完成只显示一次对话框

**修改位置：**
- `dialogdiagnoseui.cpp` 第24-34行

```cpp
// 修改前：
connect(diagnosisEngine, &DiagnosisEngine::faultIsolated, this, [this](DiagnosisTreeNode* faultNode) {
    qDebug() << "故障隔离完成:" << (faultNode ? faultNode->faultHypothesis() : "null");
    showDiagnosisResult();
});

// 修改后：
// 注意：不连接faultIsolated信号，避免重复调用showDiagnosisResult
// showDiagnosisResult会在displayCurrentTest中检测到故障隔离时调用
```

---

### 问题2：不显示"【故障隔离度】"

**原因分析：**
- 用户反馈不需要在诊断结果中显示故障隔离度百分比
- 该信息对普通用户意义不大，增加界面复杂度

**解决方案：**
- 在`showDiagnosisResult()`函数中注释掉了故障隔离度的显示行
- 保留了故障定位和处理建议的显示

**修改位置：**
- `dialogdiagnoseui.cpp` 第481-483行

```cpp
// 修改前：
if (faultNode) {
    resultText += QString("【故障定位】\n%1\n\n").arg(faultNode->faultHypothesis());
    resultText += QString("【故障隔离度】\n%1%\n\n").arg(faultNode->isolationLevel());
    if (!faultNode->comment().isEmpty()) {
        resultText += QString("【处理建议】\n%1\n\n").arg(faultNode->comment());
    }
}

// 修改后：
if (faultNode) {
    resultText += QString("【故障定位】\n%1\n\n").arg(faultNode->faultHypothesis());
    
    // 不显示故障隔离度
    // resultText += QString("【故障隔离度】\n%1%\n\n").arg(faultNode->isolationLevel());
    
    if (!faultNode->comment().isEmpty()) {
        resultText += QString("【处理建议】\n%1\n\n").arg(faultNode->comment());
    }
}
```

---

### 问题3：显示推理计算时间

**需求说明：**
- 在诊断窗口右下角显示每一步诊断的推理计算时间
- 计算公式：`推理时间 = (当前可用测试数/总测试数) × 100ms + 实际用时`
- 实时更新，让用户了解推理过程的性能

**实现方案：**

1. **添加时间统计成员变量**
   - 在`dialogDiagnoseUI`类中添加`QElapsedTimer reasoningTimer`用于计时
   - 添加`qint64 lastReasoningTime`存储最后计算的推理时间

2. **创建显示Label**
   - 在构造函数中动态创建`label_reasoning_time` Label
   - 位置设置在窗口右下角（宽140px，高20px）
   - 样式：灰色文字，9pt微软雅黑字体

3. **计时逻辑**
   - 在`displayCurrentTest()`开始时启动计时器（`reasoningTimer.start()`）
   - 在显示完测试信息后计算推理时间：
     - 获取实际用时：`actualTime = reasoningTimer.elapsed()`
     - 统计总测试数：`totalTests = getAllTestNodes().size()`
     - 计算可用测试数：`availableTests = totalTests - path.size()`
     - 计算估计时间：`estimatedTime = availableTests × 100 / totalTests`
     - 最终推理时间：`lastReasoningTime = estimatedTime + actualTime`
   - 更新Label显示

4. **响应窗口大小变化**
   - 重写`resizeEvent()`方法
   - 窗口大小改变时自动调整Label位置，保持在右下角

**修改位置：**

**dialogdiagnoseui.h:**
```cpp
// 添加头文件
#include <QElapsedTimer>

// 添加成员变量（第48-50行）
QElapsedTimer reasoningTimer;
qint64 lastReasoningTime;

// 添加方法声明（第67行）
protected:
    void resizeEvent(QResizeEvent *event) override;
```

**dialogdiagnoseui.cpp:**

1. **构造函数初始化**（第9行）
```cpp
dialogDiagnoseUI::dialogDiagnoseUI(QWidget *parent) :
    QDialog(parent),
    ui(new Ui::dialogDiagnoseUI),
    diagnosisEngine(nullptr),
    currentTreeId(0),
    lastReasoningTime(0)  // 新增
```

2. **创建推理时间Label**（第25-31行）
```cpp
// 创建推理时间显示Label（在窗口右下角）
QLabel* reasoningTimeLabel = new QLabel(this);
reasoningTimeLabel->setObjectName("label_reasoning_time");
reasoningTimeLabel->setText("推理时间: 0ms");
reasoningTimeLabel->setStyleSheet("QLabel { color: rgb(100, 100, 100); font: 9pt '微软雅黑'; }");
reasoningTimeLabel->setAlignment(Qt::AlignRight | Qt::AlignVCenter);
reasoningTimeLabel->setGeometry(this->width() - 150, this->height() - 30, 140, 20);
```

3. **resizeEvent实现**（第71-81行）
```cpp
void dialogDiagnoseUI::resizeEvent(QResizeEvent *event)
{
    QDialog::resizeEvent(event);
    
    // 更新推理时间Label的位置（保持在右下角）
    QLabel* timeLabel = this->findChild<QLabel*>("label_reasoning_time");
    if (timeLabel) {
        timeLabel->setGeometry(this->width() - 150, this->height() - 30, 140, 20);
    }
}
```

4. **displayCurrentTest中的计时逻辑**（第377-380行，第444-465行）
```cpp
void dialogDiagnoseUI::displayCurrentTest()
{
    // ...
    // 启动推理计时
    reasoningTimer.start();
    
    // ... 测试显示逻辑 ...
    
    // 计算并显示推理时间
    qint64 actualTime = reasoningTimer.elapsed();
    
    // 获取当前可用测试数量和总测试数量
    int availableTests = 0;
    int totalTests = 0;
    
    if (diagnosisEngine->getDiagnosisTree()) {
        // 统计树中的测试节点总数
        QList<DiagnosisTreeNode*> allTestNodes = diagnosisEngine->getDiagnosisTree()->getAllTestNodes();
        totalTests = allTestNodes.size();
        
        // 当前可用测试数 = 尚未执行的测试数
        QList<DiagnosisStep> path = diagnosisEngine->getDiagnosisPath();
        availableTests = totalTests - path.size();
        if (availableTests < 0) availableTests = 0;
    }
    
    // 计算推理时间：当前可用测试/总测试数量*100ms + 实际用时
    qint64 estimatedTime = (totalTests > 0) ? (availableTests * 100 / totalTests) : 0;
    lastReasoningTime = estimatedTime + actualTime;
    
    // 更新推理时间显示
    QLabel* timeLabel = this->findChild<QLabel*>("label_reasoning_time");
    if (timeLabel) {
        timeLabel->setText(QString("推理时间: %1ms").arg(lastReasoningTime));
    }
    
    qDebug() << "显示测试: node_id=" << currentTest->nodeId() 
             << ", 按钮=[" << passButtonText << "/" << failButtonText << "]"
             << ", 推理时间=" << lastReasoningTime << "ms (实际" << actualTime << "ms + 估计" << estimatedTime << "ms)";
}
```

---

## 修改文件清单

### 头文件
- `dialogdiagnoseui.h`
  - 添加 `#include <QElapsedTimer>`
  - 添加成员变量 `QElapsedTimer reasoningTimer`
  - 添加成员变量 `qint64 lastReasoningTime`
  - 添加方法声明 `void resizeEvent(QResizeEvent *event) override`

### 源文件
- `dialogdiagnoseui.cpp`
  - 构造函数：初始化`lastReasoningTime`，创建推理时间显示Label
  - 新增 `resizeEvent()` 方法实现
  - 修改构造函数：移除`faultIsolated`信号连接
  - 修改 `showDiagnosisResult()`：注释掉故障隔离度显示
  - 修改 `displayCurrentTest()`：添加推理时间计算和显示逻辑

---

## 测试验证

### 测试场景1：诊断完成对话框
1. 启动T-Designer，打开诊断界面
2. 选择任意功能开始诊断
3. 逐步执行测试直到故障定位完成
4. **预期结果**：只弹出一次"诊断完成"对话框

### 测试场景2：故障隔离度隐藏
1. 完成诊断后查看结果对话框
2. **预期结果**：对话框中不显示"【故障隔离度】"相关信息
3. 查看文本框中的诊断结果
4. **预期结果**：文本框中也不显示"【故障隔离度】"

### 测试场景3：推理时间显示
1. 开始诊断后观察窗口右下角
2. **预期结果**：显示"推理时间: Xms"字样，灰色小字
3. 每执行一个测试后
4. **预期结果**：推理时间数值更新
5. 调整窗口大小
6. **预期结果**：推理时间Label保持在右下角位置

---

## 实现细节说明

### 推理时间计算公式详解

```
推理时间 = 估计时间 + 实际用时

其中：
- 实际用时 = 从调用displayCurrentTest()到完成UI更新的真实耗时
- 估计时间 = (当前可用测试数 / 总测试数) × 100ms
- 当前可用测试数 = 总测试数 - 已执行测试数
```

**设计理念：**
- 实际用时：反映系统实际的UI渲染和数据处理时间
- 估计时间：模拟推理算法的复杂度，剩余测试越多，推理越复杂
- 100ms基准：假设每个剩余测试平均需要100ms的推理时间

**示例：**
假设诊断树有10个测试节点，当前已执行3个测试：
- 总测试数 = 10
- 已执行测试数 = 3
- 当前可用测试数 = 10 - 3 = 7
- 估计时间 = (7 / 10) × 100 = 70ms
- 如果实际用时 = 15ms
- 推理时间 = 70 + 15 = 85ms

---

## 优化建议

### 未来可能的改进
1. **推理时间优化**
   - 可以根据实际诊断数据统计，调整100ms基准值
   - 可以考虑不同测试节点的权重差异

2. **UI增强**
   - 可以添加推理时间趋势图，展示整个诊断过程的时间分布
   - 可以在诊断完成后显示总推理时间和平均推理时间

3. **性能监控**
   - 记录所有诊断会话的推理时间数据
   - 用于分析和优化诊断算法性能

---

## 相关代码引用

### DiagnosisTree类（已使用的方法）
```cpp
// 获取所有测试节点
QList<DiagnosisTreeNode*> getAllTestNodes() const;
```

### DiagnosisEngine类（已使用的方法）
```cpp
// 获取诊断树
DiagnosisTree* getDiagnosisTree() const;

// 获取诊断路径
QList<DiagnosisStep> getDiagnosisPath() const;
```

---

## 编译与部署

**编译状态：** ✅ 成功  
**编译命令：** `jom -j 20 -f Makefile.Release`  
**编译时间：** 2025-11-10  
**目标平台：** Windows (Qt 5.12.9, MSVC2017_64)

---

**总结：** 本次修复解决了诊断UI的三个关键问题，提升了用户体验和系统可观测性。所有修改已完成编译验证，可以进行功能测试。
