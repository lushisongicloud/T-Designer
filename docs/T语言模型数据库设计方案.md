# T语言模型数据库设计方案

## 1. 背景与需求

### 参考实现
- **T-Solver**: 使用XML格式存储故障模式（`<common>`, `<fault>`, `<name>`, `<describe>`, `<p>`）
- **Model.db**: component表存储元件的SMT模型和故障信息
- **T-Designer**: 需要存储T语言模型并支持z3求解器

### 求解场景
1. **增量求解**: 添加/修改约束后重新求解
2. **完整求解**: 求解整个系统模型
3. **约束完整性检查**: 验证单个功能的约束是否完整
4. **变量可行解范围求解**: 确定变量的取值范围
5. **离线求解**: 预计算和缓存求解结果

## 2. 当前Equipment表结构（project.db）

### 现有T语言相关字段
```sql
TVariable    VARCHAR(1000)  -- 当前未使用
TModel       VARCHAR(2000)  -- 当前存储整个T语言模型文本
TModelDiag   VARCHAR(2000)  -- 当前未使用
Structure    VARCHAR(2000)  -- 当前存储常量CSV：常量名,值,单位,备注;...
```

### 局限性
1. **字段容量不足**: VARCHAR(2000)对复杂模型太小
2. **数据未结构化**: 整个模型存储为一个大文本，难以单独访问各部分
3. **不支持故障模式管理**: 无法单独查询/修改特定故障模式
4. **缺少版本控制**: 无编译缓存和版本管理

## 3. 推荐方案：混合存储

### 3.1 Equipment表字段调整

保留向后兼容性，扩展字段容量：

```sql
-- 扩展现有字段
TVariable    TEXT  -- 端口变量定义（编译前）
TModel       TEXT  -- 内部变量定义 + 正常模式（编译前）
TModelDiag   TEXT  -- 故障模式（编译前，见下文格式）
Structure    TEXT  -- 常量定义（CSV格式，向后兼容）

-- 新增编译结果缓存字段
TVariableCompiled     TEXT  -- 端口变量定义（编译后，替换占位符）
TModelCompiled        TEXT  -- 内部变量定义 + 正常模式（编译后）
TModelDiagCompiled    TEXT  -- 所有故障模式（编译后，XML或JSON）
CompileVersion        INTEGER DEFAULT 0  -- 编译版本号，用于缓存失效
ComponentName         VARCHAR(200)  -- 元件实例名（用于编译时替换%Name%）
```

### 3.2 故障模式存储格式（TModelDiag字段）

#### 格式选择：XML（兼容T-Solver）

```xml
<failuremodes>
  <common>
    <!-- 公共约束（可能有多个公共块，按出现顺序） -->
    <block>
      <content>
        (assert (= 0 (+ %Name%.Cmd.A1.i %Name%.Cmd.A2.i)))
        (assert (= 122 (* %Name%.Cmd.H.q %Name%.Cmd.H.p)))
      </content>
      <scope>1,2</scope>  <!-- 作用于故障模式索引：故障模式名a(1), 故障模式名c(2) -->
    </block>
    <block>
      <content>
        (assert (= 100 (+ %Name%.Cmd.A1.i %Name%.Cmd.A2.i)))
        (assert (= 200 (+ %Name%.Cmd.A2.i %Name%.Cmd.A2.i)))
      </content>
      <scope>3,4</scope>  <!-- 作用于故障模式索引：故障模式名f(3), 故障模式名k(4) -->
    </block>
  </common>
  
  <unknownfault>
    <p>0.0000001</p>  <!-- 未知故障概率 -->
  </unknownfault>
  
  <fault id="1">
    <name>故障模式名a</name>
    <describe>
      (assert (= 10 (* %Name%.Cmd.A1.i %Name%.Cmd.A1.u)))
      (assert (= 20 (* %Name%.Cmd.A2.i %Name%.Cmd.A2.u)))
    </describe>
    <p>0.00001</p>  <!-- 故障概率 -->
    <severity>3</severity>  <!-- 严重度1-5 -->
    <remark>备注信息</remark>
  </fault>
  
  <fault id="2">
    <name>故障模式名c</name>
    <describe>
      (assert (= %常量3% (* %Name%.Cmd.A1.i %Name%.Cmd.A1.u)))
      (assert (= %常量4% (* %Name%.Cmd.A2.i %Name%.Cmd.A2.u)))
    </describe>
    <p>0.00002</p>
    <severity>2</severity>
    <remark></remark>
  </fault>
  
  <!-- 更多故障模式... -->
</failuremodes>
```

#### 替代格式：JSON（更现代）

```json
{
  "commonBlocks": [
    {
      "content": "(assert (= 0 (+ %Name%.Cmd.A1.i %Name%.Cmd.A2.i)))\n(assert (= 122 (* %Name%.Cmd.H.q %Name%.Cmd.H.p)))",
      "scope": [1, 2]
    },
    {
      "content": "(assert (= 100 (+ %Name%.Cmd.A1.i %Name%.Cmd.A2.i)))\n(assert (= 200 (+ %Name%.Cmd.A2.i %Name%.Cmd.A2.i)))",
      "scope": [3, 4]
    }
  ],
  "unknownFault": {
    "probability": 0.0000001
  },
  "faults": [
    {
      "id": 1,
      "name": "故障模式名a",
      "describe": "(assert (= 10 (* %Name%.Cmd.A1.i %Name%.Cmd.A1.u)))\n(assert (= 20 (* %Name%.Cmd.A2.i %Name%.Cmd.A2.u)))",
      "probability": 0.00001,
      "severity": 3,
      "remark": "备注信息"
    }
  ]
}
```

**推荐使用XML格式**，因为：
- 与T-Solver兼容
- 方便迁移现有代码
- Qt有良好的XML支持（QDomDocument）

### 3.3 编译流程

```
用户编辑T语言模型（UI）
    ↓
保存到 TVariable, TModel, TModelDiag（原始文本）
    ↓
点击"编译"按钮
    ↓
TModelParser解析（检查语法）
    ↓
替换占位符：%Name% → ComponentName, %常量% → Structure值
    ↓
生成XML/JSON格式的编译结果
    ↓
保存到 *Compiled 字段，CompileVersion++
    ↓
（可选）在UI显示编译结果（TModelCompileDisplayDialog）
```

### 3.4 z3求解流程

```
系统功能分析
    ↓
收集相关元件的 *Compiled 字段
    ↓
根据连线生成端口连接约束（connect2e/3e等）
    ↓
组装完整SMT模型
    ↓
调用z3求解器
    ↓
  ├─ 增量求解：基于上次的solver上下文
  ├─ 完整求解：新建solver上下文
  ├─ 约束检查：check-sat
  └─ 范围求解：optimize或多次check-sat
    ↓
解析结果并呈现
```

## 4. 内存数据结构设计

### 4.1 TModelParser（当前实现）

```cpp
class TModelParser {
    QString m_portVariables;        // 端口变量定义
    QString m_internalVariables;    // 内部变量定义
    QString m_normalMode;           // 正常模式约束
    QList<FailureMode> m_failureModes;  // 故障模式列表
    
    struct FailureMode {
        QString name;         // 故障模式名称
        QString description;  // 故障特有约束
        QString commonPart;   // 公共约束
    };
};
```

### 4.2 扩展为ComponentModel（建议新增）

```cpp
class ComponentModel {
public:
    // 基本信息
    int equipmentId;
    QString componentName;      // 实例名（如 ACT-1）
    QString componentType;      // 类型（如 电磁阀）
    
    // T语言模型（原始）
    QString portVariablesRaw;
    QString internalVariablesRaw;
    QString normalModeRaw;
    QList<FailureModeRaw> failureModesRaw;
    
    // 常量定义
    QMap<QString, ConstantDef> constants;
    struct ConstantDef {
        QString name;
        QString value;
        QString unit;
        QString remark;
    };
    
    // 编译结果（缓存）
    QString portVariablesCompiled;
    QString internalVariablesCompiled;
    QString normalModeCompiled;
    QList<FailureModeCompiled> failureModesCompiled;
    int compileVersion;
    
    // 故障模式
    struct FailureModeRaw {
        QString name;
        QString description;
        QString commonPart;  // 关联的公共块
    };
    
    struct FailureModeCompiled {
        QString name;
        QString fullConstraints;  // 公共约束 + 特有约束（已编译）
        double probability;
        int severity;
        QString remark;
    };
    
    // 方法
    bool compile();  // 编译：替换占位符
    bool validate(); // 验证：SMT语法检查
    QString toXml(); // 导出为XML（存储到数据库）
    bool fromXml(const QString& xml);  // 从XML加载
};
```

### 4.3 SystemModel（用于z3求解）

```cpp
class SystemModel {
public:
    QString systemName;
    QList<ComponentModel> components;
    QList<ConnectionConstraint> connections;
    
    struct ConnectionConstraint {
        QString portA;  // 如 ACT-1.Cmd.A1
        QString portB;  // 如 POWER.OUT
        QString domain; // electric/hydraulic/mechanical
        QString macro;  // connect2e/3e/4e
    };
    
    // z3求解方法
    QString generateFullSMT();  // 生成完整SMT-LIB2代码
    QString generateIncrementalSMT(const QStringList& changedComponents);
    
    bool solve(SolverContext* ctx);
    bool checkConstraints(const QString& functionName);
    QMap<QString, QPair<double,double>> getVariableRanges(const QStringList& vars);
};
```

## 5. 实施步骤

### Phase 1: 数据库迁移（当前阶段）
1. ✅ 使用Structure字段存储常量（CSV格式）
2. ✅ TModel字段存储完整T语言文本
3. ⏳ 生成编译结果到显示对话框

### Phase 2: 结构化存储（下一阶段）
1. 扩展Equipment表字段（添加*Compiled字段）
2. 实现XML序列化/反序列化
3. 故障模式独立管理UI（添加/删除/编辑故障模式）
4. 添加故障概率、严重度字段

### Phase 3: z3集成（后续）
1. 创建ComponentModel和SystemModel类
2. 实现连接约束自动生成
3. 集成z3求解器API
4. 实现增量求解和缓存

### Phase 4: 高级功能
1. 约束完整性检查
2. 变量范围求解（优化问题）
3. 离线求解和结果缓存
4. 诊断决策树生成

## 6. 兼容性考虑

### 与T-Solver的兼容性
- 使用相同的XML格式存储故障模式
- FailureMode类保持相同的接口（name, describe, probability）
- 支持unknownfault概念

### 向后兼容性
- Structure字段保持CSV格式
- TModel字段继续存储完整文本（用于备份和手工编辑）
- 编译结果存储在新字段，不影响现有功能

## 7. 性能优化

### 编译缓存
- 使用CompileVersion追踪变更
- 只在常量或模型变更时重新编译
- 编译结果存储在*Compiled字段

### 求解优化
- 增量求解：只更新变更的约束
- 并行求解：多个故障模式可并行检查
- 结果缓存：常见场景的求解结果缓存到数据库

## 8. 安全性

### 数据验证
- SMT语法检查（防止注入）
- 常量值类型检查
- 故障概率范围检查（0-1）

### 版本控制
- CompileVersion追踪编译状态
- 变更日志（可选，未来扩展）
