# 诊断系统修复说明

## 修复时间
2025年11月10日 14:39

## 问题诊断

### 根本原因
**参数语义不匹配**导致诊断引擎无法正确加载诊断树：

1. **UI层传递的是 `tree_id`**
   - `dialogDiagnoseUI::on_toolButton_start_diagnosis_clicked()` 从 `diagnosis_tree` 表加载功能列表
   - 获取的 `currentTreeId` 是诊断树的主键 `tree_id`

2. **DiagnosisEngine期望的是 `function_id`**
   - 原方法签名：`bool startDiagnosisSession(int functionId)`
   - 内部调用：`loadByFunctionId(m_database, functionId)`
   - 用 `tree_id` 作为 `function_id` 查询，导致查询失败

3. **诊断流程中断**
   - 加载失败 → `recordTestResult()` 返回 false
   - 会话状态变为 Failed → 后续操作都提示"没有活动的诊断会话"

## 修复内容

### 1. 修改 `DiagnosisEngine::startDiagnosisSession()`
**文件**: `BO/diagnosisengine.h` + `BO/diagnosisengine.cpp`

**变更**:
```cpp
// 修改前
bool startDiagnosisSession(int functionId);

// 修改后
bool startDiagnosisSession(int treeId);
```

**逻辑调整**:
```cpp
bool DiagnosisEngine::startDiagnosisSession(int treeId)
{
    // 使用新方法按 tree_id 加载
    if (!loadDiagnosisTreeById(treeId)) {
        updateSessionState(DiagnosisSessionState::Failed);
        emit diagnosisFailed("无法加载诊断树");
        return false;
    }
    
    // 从加载的树中获取 function_id
    m_functionId = m_currentTree->functionId();
    
    // ... 其余逻辑不变
}
```

### 2. 新增 `loadDiagnosisTreeById()` 方法
**文件**: `BO/diagnosisengine.h` + `BO/diagnosisengine.cpp`

**新方法**:
```cpp
private:
    bool loadDiagnosisTreeById(int treeId);
```

**实现**:
```cpp
bool DiagnosisEngine::loadDiagnosisTreeById(int treeId)
{
    m_currentTree = new DiagnosisTree();
    
    // 使用 DiagnosisTree::loadFromDatabase() 按 tree_id 加载
    if (!m_currentTree->loadFromDatabase(m_database, treeId)) {
        qDebug() << "Failed to load diagnosis tree with tree_id" << treeId;
        delete m_currentTree;
        m_currentTree = nullptr;
        return false;
    }

    // 加载完整树结构
    if (!m_currentTree->loadFullTree(m_database)) {
        qDebug() << "Failed to load full tree structure";
        delete m_currentTree;
        m_currentTree = nullptr;
        return false;
    }

    qDebug() << "Diagnosis tree loaded successfully";
    qDebug() << "Tree ID:" << m_currentTree->treeId();
    qDebug() << "Function ID:" << m_currentTree->functionId();
    qDebug() << "Total nodes:" << m_currentTree->countNodes();
    
    return true;
}
```

### 3. 保留原 `loadDiagnosisTree()` 方法
为保持向后兼容性，保留原方法供可能按 `function_id` 启动诊断的场景使用。

## 测试验证

### 预期行为（修复后）

1. **启动诊断**
   - 用户在功能列表中选择"液压泵站启动功能"
   - 点击"开始诊断"按钮
   - 系统正确加载 `tree_id=1` 的诊断树
   - 显示第一个测试："测试AC220V供电是否正常"

2. **记录测试结果**
   - 点击"电压符合"或"电压不符合"按钮
   - `recordTestResult()` 成功记录结果
   - 诊断引擎自动推荐下一个测试
   - UI显示新的测试节点

3. **上一步功能**
   - 点击"上一步"按钮
   - 诊断路径回退一步
   - UI显示前一个测试节点
   - 诊断会话保持活跃状态

4. **跳过当前测试**
   - 点击"跳过当前测试"按钮
   - 系统自动查找并推荐替代测试
   - 跳过计数增加
   - 诊断继续进行

5. **选择其他测试**
   - 点击"选择其他测试"按钮
   - 弹出对话框显示所有可选测试
   - 按推荐分数排序（成本、时间、历史数据综合评分）
   - 选择后跳转到指定测试

### 调试日志输出

修复后运行时应看到以下日志：
```
Diagnosis session started. Tree ID: 1, Function ID: 1001
Initial test node: 测试AC220V供电是否正常
Diagnosis tree loaded successfully
Tree ID: 1
Function ID: 1001
Total nodes: 19
```

如果出现错误，会看到：
```
Failed to load diagnosis tree with tree_id 1
Failed to load full tree structure
```

## 数据库验证

确认测试数据正确加载：

```sql
-- 查看诊断树
SELECT tree_id, function_id, name, root_node_id 
FROM diagnosis_tree;

-- 预期结果：
-- tree_id | function_id | name                     | root_node_id
-- --------|-------------|--------------------------|-------------
-- 1       | 1001        | 液压泵站启动功能诊断树    | 1
-- 2       | 1002        | 压力控制功能诊断树        | 20
-- 3       | 1003        | 液压油质量监测诊断树      | 33

-- 查看节点数量
SELECT tree_id, COUNT(*) as node_count, 
       SUM(CASE WHEN node_type='Test' THEN 1 ELSE 0 END) as test_count,
       SUM(CASE WHEN node_type='Fault' THEN 1 ELSE 0 END) as fault_count
FROM diagnosis_tree_node
GROUP BY tree_id;

-- 预期结果：
-- tree_id | node_count | test_count | fault_count
-- --------|------------|------------|------------
-- 1       | 19         | 5          | 8
-- 2       | 13         | 4          | 5
-- 3       | 10         | 4          | 3
```

## 后续测试步骤

### 1. 基础诊断流程测试
```
1. 启动 T-DESIGNER.exe
2. 打开项目：集中油源动力系统
3. 进入诊断界面
4. 选择"液压泵站启动功能"
5. 点击"开始诊断"
6. 验证第一个测试显示正确
7. 点击"电压符合"
8. 验证下一个测试显示
9. 继续完成诊断流程
10. 验证最终故障定位结果
```

### 2. 回退功能测试
```
1. 执行2-3个测试后
2. 点击"上一步"按钮
3. 验证回退到前一个测试
4. 再次点击测试结果按钮
5. 验证诊断继续进行
```

### 3. 跳过测试功能测试
```
1. 在任意测试节点
2. 点击"跳过当前测试"
3. 验证推荐了替代测试
4. 验证跳过计数在数据库中更新
```

### 4. 手动选择测试功能测试
```
1. 点击"选择其他测试"
2. 验证弹出对话框
3. 验证列表显示所有可选测试
4. 验证显示成本和时间估算
5. 选择一个测试
6. 验证跳转到所选测试
```

### 5. 多功能诊断测试
```
1. 完成"液压泵站启动功能"诊断
2. 返回功能选择页面
3. 选择"压力控制功能"
4. 验证新会话正常启动
5. 验证前一次诊断路径不影响新会话
```

## 已知限制

1. **UI控件动态更新**
   - 当前按钮槽函数已实现，但需要确保UI文件中控件正确命名
   - 如果UI Designer中控件名称不匹配，槽函数不会自动连接

2. **决策树可视化未实现**
   - TestManagementDialog 的 tabDecision 功能尚未实现
   - 用户无法在管理界面中编辑决策树

3. **会话持久化未完全实现**
   - diagnosis_session 表创建了，但未完全使用
   - diagnosis_step_history 表未写入数据
   - 关闭程序后诊断历史会丢失

## 编译信息

- **编译时间**: 2025/11/10 14:39:33
- **可执行文件大小**: 7.22 MB
- **编译警告**: 仅有字符编码警告（C4819），无错误
- **Qt版本**: 5.12.9
- **编译器**: MSVC 2017 64-bit

## 修改文件清单

1. `BO/diagnosisengine.h` - 新增 loadDiagnosisTreeById() 声明，修改 startDiagnosisSession() 参数
2. `BO/diagnosisengine.cpp` - 实现新方法，修复参数不匹配问题
3. `dialogdiagnoseui.cpp` - 已有代码无需修改（传递的 tree_id 参数现在能正确处理）

## 总结

此次修复解决了诊断系统的核心问题：**参数语义不匹配**。通过引入 `loadDiagnosisTreeById()` 方法，使诊断引擎能够直接使用 UI 传递的 `tree_id` 加载诊断树，而不是错误地当作 `function_id` 处理。

修复后，5个按钮的功能应该都能正常工作：
- ✅ btn_TestPass - 记录测试通过
- ✅ btn_TestFail - 记录测试失败
- ✅ BtnLastStep - 回退到上一步
- ✅ toolButton_skip_this_test - 跳过当前测试并推荐替代
- ✅ toolButton_slelct_other_test - 手动选择其他测试

请按照上述测试步骤验证功能是否完全正常。如有问题，请检查调试日志输出以定位具体原因。
