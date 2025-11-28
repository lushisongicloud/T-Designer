**【分类依据】本文件记录了具体的修复过程、调试分析或已过时的设计实现，作为问题解决的临时记录保留。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 故障诊断系统重构设计文档

## 1. 需求分析

### 1.1 当前系统问题
- 依赖外部L2test.exe程序进行诊断推理
- 使用旧的Function表结构，数据组织不清晰
- 诊断流程与Livingstone求解器绑定
- 需要生成xmpl/jmpl等外部文件

### 1.2 新系统目标
- **完全基于项目数据库**：仅使用diagnosis_tree和diagnosis_tree_node表
- **自包含诊断引擎**：不依赖外部程序
- **决策树驱动**：基于诊断决策树进行测试推荐和故障定位
- **简化流程**：选择功能 → 推荐测试 → 故障隔离

## 2. 数据模型设计

### 2.1 现有表结构分析

#### diagnosis_tree (诊断树)
```sql
CREATE TABLE diagnosis_tree (
    tree_id INTEGER PRIMARY KEY AUTOINCREMENT,
    container_id INTEGER NOT NULL,
    name TEXT,
    description TEXT,
    FOREIGN KEY(container_id) REFERENCES container(container_id)
);
```

#### diagnosis_tree_node (诊断树节点)
```sql
CREATE TABLE diagnosis_tree_node (
    node_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    parent_node_id INTEGER,
    test_id INTEGER,
    state_id INTEGER,
    outcome TEXT,
    comment TEXT,
    FOREIGN KEY(tree_id) REFERENCES diagnosis_tree(tree_id),
    FOREIGN KEY(parent_node_id) REFERENCES diagnosis_tree_node(node_id),
    FOREIGN KEY(test_id) REFERENCES test_definition(test_id),
    FOREIGN KEY(state_id) REFERENCES container_state(state_id)
);
```

### 2.2 需要扩展的字段

#### diagnosis_tree 扩展
```sql
ALTER TABLE diagnosis_tree ADD COLUMN function_id INTEGER;
ALTER TABLE diagnosis_tree ADD COLUMN root_node_id INTEGER;
ALTER TABLE diagnosis_tree ADD COLUMN created_time TEXT;
ALTER TABLE diagnosis_tree ADD COLUMN auto_generated INTEGER DEFAULT 1;
```

说明：
- `function_id`: 关联到待诊断的功能
- `root_node_id`: 指向根节点，便于快速访问
- `created_time`: 创建时间
- `auto_generated`: 是否自动生成

#### diagnosis_tree_node 扩展
```sql
ALTER TABLE diagnosis_tree_node ADD COLUMN node_type TEXT DEFAULT 'test';
ALTER TABLE diagnosis_tree_node ADD COLUMN test_description TEXT;
ALTER TABLE diagnosis_tree_node ADD COLUMN expected_result TEXT;
ALTER TABLE diagnosis_tree_node ADD COLUMN fault_hypothesis TEXT;
ALTER TABLE diagnosis_tree_node ADD COLUMN isolation_level INTEGER DEFAULT 0;
ALTER TABLE diagnosis_tree_node ADD COLUMN test_priority REAL DEFAULT 0.5;
```

说明：
- `node_type`: 节点类型 ('test', 'fault', 'branch')
- `test_description`: 测试描述文本
- `expected_result`: 期望结果描述
- `fault_hypothesis`: 故障假设描述
- `isolation_level`: 隔离级别 (0=未隔离, 1=部分隔离, 2=完全隔离)
- `test_priority`: 测试优先级 (0.0-1.0)

### 2.3 数据组织逻辑

```
diagnosis_tree (针对某个功能的诊断树)
    ├── root_node (根节点)
    │   ├── test_node_1 (第一个推荐测试)
    │   │   ├── outcome_pass → test_node_2
    │   │   └── outcome_fail → fault_node_1
    │   ├── test_node_2 (第二个推荐测试)
    │   │   ├── outcome_pass → fault_node_2
    │   │   └── outcome_fail → test_node_3
    │   └── ...
    └── fault_nodes (叶子节点，指向具体故障)
```

## 3. 诊断引擎设计

### 3.1 核心类结构

```cpp
// DO/diagnosistree.h
class DiagnosisTree {
public:
    int treeId;
    int containerId;
    int functionId;
    QString name;
    QString description;
    int rootNodeId;
    
    bool loadFromDatabase(int treeId);
    bool saveToDatabase();
    DiagnosisTreeNode* getRootNode();
};

// DO/diagnosistreenode.h
class DiagnosisTreeNode {
public:
    int nodeId;
    int treeId;
    int parentNodeId;
    int testId;
    int stateId;
    QString nodeType;        // 'test', 'fault', 'branch'
    QString outcome;         // 'pass', 'fail', 'unknown'
    QString testDescription;
    QString expectedResult;
    QString faultHypothesis;
    double testPriority;
    int isolationLevel;
    
    QList<DiagnosisTreeNode*> children;
    
    bool loadFromDatabase(int nodeId);
    bool saveToDatabase();
    void addChild(DiagnosisTreeNode* child);
    DiagnosisTreeNode* getChildByOutcome(const QString& outcome);
};

// BO/diagnosisengine.h
class DiagnosisEngine {
public:
    DiagnosisEngine(QSqlDatabase& db);
    
    // 加载诊断树
    bool loadDiagnosisTree(int functionId);
    
    // 获取当前推荐的测试
    DiagnosisTreeNode* getCurrentRecommendedTest();
    
    // 记录测试结果，返回下一个推荐测试或故障结论
    DiagnosisTreeNode* recordTestResult(const QString& outcome);
    
    // 重置诊断会话
    void resetSession();
    
    // 获取诊断路径
    QList<DiagnosisTreeNode*> getDiagnosisPath();
    
    // 检查是否已隔离故障
    bool isFaultIsolated();
    
private:
    QSqlDatabase& m_database;
    DiagnosisTree* m_currentTree;
    DiagnosisTreeNode* m_currentNode;
    QList<DiagnosisTreeNode*> m_diagnosisPath;
    
    void buildTreeStructure();
};
```

### 3.2 诊断流程

```
1. 用户选择功能
   ↓
2. DiagnosisEngine::loadDiagnosisTree(functionId)
   - 从数据库加载诊断树
   - 构建树形结构
   - 定位到根节点
   ↓
3. DiagnosisEngine::getCurrentRecommendedTest()
   - 返回当前节点推荐的测试
   - 显示测试描述和期望结果
   ↓
4. 用户执行测试，输入结果
   ↓
5. DiagnosisEngine::recordTestResult(outcome)
   - 根据结果遍历到子节点
   - 记录诊断路径
   - 检查是否到达叶子节点（故障结论）
   ↓
6. 判断：
   - 如果是故障节点 → 显示故障结论，结束
   - 如果是测试节点 → 返回步骤3
   - 如果无子节点 → 诊断失败，需要人工介入
```

## 4. UI改造方案

### 4.1 功能选择页面 (page_main_select_model)
保持不变，显示可诊断的功能列表。

修改点：
- 数据源改为从 `function_definition` 表获取
- 只显示有对应诊断树的功能

### 4.2 症状选择页面 → 测试执行页面
**重大改变**：不再需要"症状选择"步骤

新流程：
1. 用户选择功能后直接进入测试推荐页面
2. 系统显示当前推荐的测试
3. 用户执行测试并输入结果
4. 系统根据结果推荐下一个测试或给出故障结论

UI元素：
```
┌─────────────────────────────────────┐
│ 当前诊断功能: [功能名称]            │
├─────────────────────────────────────┤
│ 诊断步骤 1/5                        │
│                                     │
│ 推荐测试: [测试名称]                │
│ 测试说明:                           │
│ [详细的测试描述文本]                │
│                                     │
│ 期望结果:                           │
│ [期望的测试结果描述]                │
│                                     │
│ 测试结果:                           │
│ ○ 通过  ○ 失败  ○ 无法执行         │
│                                     │
│ [提交结果] [跳过此测试] [重新诊断]  │
└─────────────────────────────────────┘
```

### 4.3 诊断结果页面
显示：
- 故障结论
- 诊断路径（执行的测试序列）
- 建议的修复措施

## 5. 数据迁移方案

### 5.1 从旧Function表到新结构

旧Function表字段：
- FunctionID
- FunctionName
- ExecsList (执行器列表)
- CmdValList (控制变量列表)
- UserTest (用户测试)
- Remark

迁移策略：
1. 为每个Function创建一个diagnosis_tree记录
2. 从ExecsList和CmdValList推断可能的测试点
3. 创建简单的线性诊断树（每个执行器一个测试节点）
4. 手动或半自动优化诊断树结构

### 5.2 迁移脚本设计

```python
# tools/migrate_diagnosis_data.py
import sqlite3

def migrate_function_to_diagnosis_tree(db_path):
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    # 1. 读取所有Function记录
    cursor.execute("SELECT * FROM Function")
    functions = cursor.fetchall()
    
    for func in functions:
        func_id, func_name, execs_list, cmd_list, user_test, remark = func
        
        # 2. 创建diagnosis_tree记录
        cursor.execute("""
            INSERT INTO diagnosis_tree (container_id, name, description, function_id)
            VALUES (?, ?, ?, ?)
        """, (1, f"诊断树-{func_name}", remark, func_id))
        
        tree_id = cursor.lastrowid
        
        # 3. 创建根节点
        cursor.execute("""
            INSERT INTO diagnosis_tree_node (tree_id, node_type, test_description)
            VALUES (?, 'branch', '开始诊断')
        """, (tree_id,))
        
        root_node_id = cursor.lastrowid
        
        # 4. 为每个执行器创建测试节点
        if execs_list:
            execs = execs_list.split(',')
            parent_id = root_node_id
            
            for i, exec_name in enumerate(execs):
                # 创建测试节点
                cursor.execute("""
                    INSERT INTO diagnosis_tree_node 
                    (tree_id, parent_node_id, node_type, test_description, test_priority)
                    VALUES (?, ?, 'test', ?, ?)
                """, (tree_id, parent_id, f"测试 {exec_name}", 1.0 - i*0.1))
                
                test_node_id = cursor.lastrowid
                
                # 创建故障节点作为叶子
                cursor.execute("""
                    INSERT INTO diagnosis_tree_node 
                    (tree_id, parent_node_id, node_type, outcome, fault_hypothesis, isolation_level)
                    VALUES (?, ?, 'fault', 'fail', ?, 2)
                """, (tree_id, test_node_id, f"{exec_name} 故障"))
                
                # 下一个测试节点
                cursor.execute("""
                    INSERT INTO diagnosis_tree_node 
                    (tree_id, parent_node_id, node_type, outcome)
                    VALUES (?, ?, 'branch', 'pass')
                """, (tree_id, test_node_id))
                
                parent_id = cursor.lastrowid
        
        # 5. 更新root_node_id
        cursor.execute("""
            UPDATE diagnosis_tree SET root_node_id = ? WHERE tree_id = ?
        """, (root_node_id, tree_id))
    
    conn.commit()
    conn.close()
```

## 6. 实施计划

### Phase 1: 数据模型 (2小时)
- [ ] 扩展diagnosis_tree表字段
- [ ] 扩展diagnosis_tree_node表字段
- [ ] 创建数据模型类 (DiagnosisTree, DiagnosisTreeNode)
- [ ] 编写单元测试

### Phase 2: 诊断引擎 (3小时)
- [ ] 实现DiagnosisEngine类
- [ ] 实现树加载和遍历逻辑
- [ ] 实现测试推荐算法
- [ ] 实现诊断路径跟踪
- [ ] 编写单元测试

### Phase 3: UI改造 (2小时)
- [ ] 修改功能选择逻辑
- [ ] 重构测试执行页面
- [ ] 实现诊断结果显示
- [ ] 移除L2test相关代码

### Phase 4: 数据迁移 (1小时)
- [ ] 编写迁移脚本
- [ ] 测试迁移结果
- [ ] 生成示例诊断树

### Phase 5: 集成测试 (1小时)
- [ ] 端到端测试完整诊断流程
- [ ] 性能测试
- [ ] Bug修复

### Phase 6: 文档和清理 (1小时)
- [ ] 更新用户文档
- [ ] 清理旧代码
- [ ] 代码审查

总计：约10小时工作量

## 7. 风险和缓解措施

### 7.1 数据完整性风险
**风险**：迁移过程中数据丢失或损坏
**缓解**：
- 迁移前备份数据库
- 提供回滚机制
- 详细的迁移日志

### 7.2 功能兼容性风险
**风险**：新系统无法完全替代旧系统功能
**缓解**：
- 分阶段实施，保留旧代码作为fallback
- 充分的回归测试
- 用户反馈收集机制

### 7.3 性能风险
**风险**：复杂诊断树加载和遍历可能较慢
**缓解**：
- 实现树节点缓存
- 延迟加载子树
- 数据库索引优化

## 8. 成功标准

1. ✓ 完全不依赖外部L2test.exe程序
2. ✓ 只使用项目数据库中的两个表
3. ✓ 诊断流程简化为：选择功能 → 执行测试 → 故障定位
4. ✓ 代码可维护性提升
5. ✓ 响应时间 < 1秒
6. ✓ 旧数据成功迁移
