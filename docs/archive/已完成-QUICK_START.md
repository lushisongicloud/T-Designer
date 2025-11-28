**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 新诊断系统快速开始指南

## 立即验证（醒来后5分钟）

### 1. 运行程序
```powershell
cd D:\SynologyDrive\Project\T_DESIGNER\build\release
.\T-DESIGNER.exe
```

### 2. 准备测试数据（如果未迁移）
```powershell
cd D:\SynologyDrive\Project\T_DESIGNER

# 方法1：使用模板数据库（已包含3个测试功能）
copy templete\project.db MyProjects\测试项目\project.db

# 方法2：迁移现有项目数据
python tools\migrate_diagnosis_data.py "MyProjects\你的项目\project.db"
```

### 3. 临时测试方案（UI按钮未添加前）

由于UI按钮尚未在.ui文件中添加，可以使用以下方法临时测试：

#### 选项A：直接修改代码测试
在`mainwindow_diagnosis.cpp`的`displayCurrentTest()`末尾临时添加：
```cpp
// 临时测试代码 - 自动模拟Pass结果
QTimer::singleShot(3000, this, [this]() {
    recordCurrentTestResult(TestOutcome::Pass);
});
```

#### 选项B：使用调试器手动调用
1. 在Visual Studio中打开项目
2. 在`displayCurrentTest()`设置断点
3. 运行到断点后，在立即窗口执行：
   ```cpp
   ((MainWindow*)this)->recordCurrentTestResult(TestOutcome::Pass)
   ```

#### 选项C：快速添加UI按钮（推荐）
1. 在Qt Designer中打开`mainwindow.ui`
2. 找到`page_main_diagnosis`（诊断执行页面）
3. 拖拽3个QPushButton到页面
4. 设置对象名称：
   - 第1个按钮：objectName = `btnTestPass`, text = "测试通过 ✓"
   - 第2个按钮：objectName = `btnTestFail`, text = "测试失败 ✗"
   - 第3个按钮：objectName = `btnSkipTest`, text = "跳过测试 →"
5. 保存.ui文件
6. 重新编译（槽函数已实现，会自动连接）

## 完整测试流程

### 步骤1：启动程序并打开项目
1. 运行T-DESIGNER.exe
2. 打开包含测试数据的项目（templete/project.db或已迁移的项目）

### 步骤2：进入诊断页面
1. 点击主界面的"故障诊断"按钮
2. 应该看到功能列表显示3个功能：
   - 电源供电功能
   - 电机驱动功能
   - 信号采集功能

### 步骤3：开始诊断
1. 选择第一个功能："电源供电功能"
2. 点击"开始诊断"按钮
3. 预期结果：
   - 页面自动切换到测试执行页面
   - 显示第一个测试描述："测试 电源模块"

### 步骤4：执行测试
**场景A：故障路径测试**
1. 点击"测试失败"按钮
2. 预期结果：
   - 诊断完成，显示："电源模块 故障"
   - 显示诊断路径：1个测试步骤
   - 隔离度：某个数值

**场景B：正常路径测试**
1. 点击"测试通过"按钮
2. 预期结果：
   - 显示第二个测试："测试 保险丝"
3. 继续点击"测试通过"
4. 预期结果：
   - 显示第三个测试："测试 电源开关"
5. 继续点击"测试通过"
6. 预期结果：
   - 诊断完成，显示："其他故障（所有测试通过）"
   - 显示完整诊断路径：3个测试步骤

### 步骤5：验证诊断路径记录
在诊断完成页面，应该看到：
```
故障定位结果:

<故障假设内容>

隔离度: <数值>

诊断路径:
1. 测试 电源模块 -> 通过/失败
2. 测试 保险丝 -> 通过/失败
...
```

### 步骤6：重复测试
1. 返回功能选择页面
2. 选择其他功能或不同的测试结果组合
3. 验证系统行为一致

## 预期输出与日志

### 控制台日志（qDebug输出）
启动诊断时：
```
诊断会话已启动: tree_id=1 , 功能名称=电源供电功能
显示测试: node_id=2 , 描述=测试 电源模块
```

记录测试结果时：
```
用户点击: 测试失败
记录测试结果: node_id=2 , outcome=失败
故障定位: 电源模块 故障
```

### 数据库查询验证
在诊断会话中，可以查询当前状态（开发调试用）：
```sql
-- 查看当前诊断树结构
SELECT * FROM diagnosis_tree WHERE tree_id=1;

-- 查看所有节点
SELECT node_id, node_type, parent_node_id, test_description, fault_hypothesis
FROM diagnosis_tree_node
WHERE tree_id=1
ORDER BY node_id;
```

## 常见问题排查

### Q1: 点击"开始诊断"后没有反应
**可能原因：**
- DiagnosisEngine初始化失败
- 数据库连接问题
- tree_id不存在

**排查步骤：**
1. 检查控制台输出是否有错误信息
2. 验证数据库文件存在：`ls MyProjects/测试项目/project.db`
3. 检查diagnosis_tree表中是否有数据：
   ```sql
   sqlite3 MyProjects/测试项目/project.db "SELECT * FROM diagnosis_tree;"
   ```

### Q2: 功能列表为空
**可能原因：**
- diagnosis_tree表无数据
- 未执行迁移脚本

**解决方案：**
```powershell
# 执行迁移脚本
python tools/migrate_diagnosis_data.py "MyProjects/测试项目/project.db"

# 或使用测试数据
python tools/migrate_diagnosis_data.py templete/project.db
```

### Q3: UI按钮无响应
**可能原因：**
- 按钮对象名称不匹配（应为btnTestPass等）
- 信号槽未自动连接

**解决方案：**
1. 在Qt Designer中检查按钮的objectName属性
2. 确保按钮名称完全匹配：
   - `btnTestPass` (不是testPassButton)
   - `btnTestFail` (不是testFailButton)
   - `btnSkipTest` (不是skipTestButton)

### Q4: 编译错误："TestOutcome未定义"
**解决方案：**
确保mainwindow.h包含了：
```cpp
#include "BO/diagnosisengine.h"
```

TestOutcome是全局枚举，不需要类限定符。

## 性能验证

### 内存占用
正常情况下，加载10节点的诊断树应占用 < 100KB 内存。

### 响应时间
- 启动诊断会话：< 100ms
- 记录测试结果：< 50ms
- 显示下一个测试：< 50ms

如果明显超出，检查：
1. 数据库索引是否创建（tools/extend_diagnosis_tables.sql）
2. 树结构是否有循环（运行validateTree()）

## 下一步开发建议

### 优先级1：完成UI设计
- 添加3个测试结果按钮（15分钟）
- 调整测试描述显示布局（10分钟）
- 添加诊断进度指示器（可选，30分钟）

### 优先级2：清理旧代码
- 移除L2test相关函数（1小时）
- 移除征兆选择相关UI（30分钟）
- 更新用户文档（1小时）

### 优先级3：功能增强
- 支持测试跳过逻辑优化
- 添加诊断历史记录
- 导出诊断报告功能
- 支持自定义决策树编辑器

## 联系信息
遇到问题请查看：
- DIAGNOSIS_INTEGRATION_SUMMARY.md - 完整实现总结
- DIAGNOSIS_REDESIGN.md - 原始设计文档
- BO/diagnosisengine.h - API文档（注释详细）
