**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 连接宏族（Connection Macro Family）概念说明

## 概述

**连接宏族（Connection Macro Family）**是为支持不同端口数量连接而设计的宏管理机制。一个宏族包含支持不同端口数量（arity）的多个连接宏，系统根据连接点的实际端口数量自动选择合适的宏并展开为SMT约束。

## 设计动机

在T-Designer中，元件之间的连接点可能有2个、3个、4个甚至更多端口相连。传统的单一连接宏（如connect2e）无法适应这种多样性：

- **问题1**：如果只配置connect2e，遇到3个端口相连时无法处理
- **问题2**：如果为每个端口数都单独配置宏，用户选择繁琐且容易出错
- **问题3**：端口配置与实际连接脱节，需要在两处分别维护

**解决方案**：引入宏族概念，将支持不同端口数的宏组织成族，用户配置时选择宏族（如"electric-connect"），系统在生成连接约束时根据实际端口数自动选择对应的宏（如3个端口时自动选择connect3e）。

## 宏族结构

### 数据库表设计

```sql
CREATE TABLE port_connect_macro_family (
    family_id INTEGER PRIMARY KEY AUTOINCREMENT,
    family_name TEXT NOT NULL UNIQUE,
    domain TEXT NOT NULL,
    description TEXT,
    is_builtin INTEGER DEFAULT 0,
    macros_json TEXT NOT NULL,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP
);
```

### 字段说明

- **family_name**: 宏族名称，唯一标识一个宏族（如"electric-connect"）
- **domain**: 领域分类（electric/hydraulic/mechanical/other）
- **description**: 宏族的文字描述
- **is_builtin**: 是否为内置宏族（1=内置，0=自定义）
  - 内置宏族不可删除，确保系统基本功能
  - 自定义宏族可由用户添加和删除
- **macros_json**: JSON数组，存储宏族中的多个宏定义
- **created_at**: 创建时间戳

### macros_json格式

```json
[
    {
        "arity": 2,
        "macro_name": "connect2e",
        "expansion": "(assert (= (+ {0}.i {1}.i) 0))\n(assert (= {0}.u {1}.u))"
    },
    {
        "arity": 3,
        "macro_name": "connect3e",
        "expansion": "(assert (= (+ {0}.i {1}.i {2}.i) 0))\n(assert (= {0}.u {1}.u))\n(assert (= {1}.u {2}.u))"
    },
    {
        "arity": 4,
        "macro_name": "connect4e",
        "expansion": "(assert (= (+ {0}.i {1}.i {2}.i {3}.i) 0))\n(assert (= {0}.u {1}.u))\n(assert (= {1}.u {2}.u))\n(assert (= {2}.u {3}.u))"
    }
]
```

## 内置宏族

系统提供三个内置宏族，对应电气、液压、机械三种领域：

### 1. electric-connect（电气连接宏族）

- **领域**: electric
- **变量**: i（电流）、u（电压）
- **约束原理**: 基尔霍夫定律
  - 电流守恒：Σi = 0
  - 电压等势：所有端口u相等
- **包含的宏**:
  - connect2e: 2端口连接
  - connect3e: 3端口连接
  - connect4e: 4端口连接

**示例**：
```smt
; connect2e(A, B) 展开为：
(assert (= (+ A.i B.i) 0))
(assert (= A.u B.u))

; connect3e(A, B, C) 展开为：
(assert (= (+ A.i B.i C.i) 0))
(assert (= A.u B.u))
(assert (= B.u C.u))
```

### 2. hydraulic-connect（液压连接宏族）

- **领域**: hydraulic
- **变量**: q（流量）、p（压力）
- **约束原理**: 流体力学定律
  - 流量守恒：Σq = 0
  - 压力等势：所有端口p相等
- **包含的宏**:
  - connect2h: 2端口连接
  - connect3h: 3端口连接
  - connect4h: 4端口连接

**示例**：
```smt
; connect2h(A, B) 展开为：
(assert (= (+ A.q B.q) 0))
(assert (= A.p B.p))
```

### 3. mechanical-connect（机械连接宏族）

- **领域**: mechanical
- **变量**: F（力）、v/n/x（速度/转速/位移，选其一）
- **约束原理**: 力学定律
  - 力守恒：ΣF = 0
  - 速度/转速/位移等势：所有端口v/n/x相等
- **包含的宏**:
  - connect2m: 2端口连接
  - connect3m: 3端口连接
  - connect4m: 4端口连接

**示例**：
```smt
; connect2m(A, B) 使用速度v，展开为：
(assert (= (+ A.F B.F) 0))
(assert (= A.v B.v))
```

## 宏族的使用流程

### 1. 端口配置阶段

在"元件属性"或"本地物料库"的端口配置界面中：

1. 用户在tableTerm表格中右键选择"配置端口"
2. 打开PortConfigEditDialog对话框
3. 选择端口类型（电气/液压/机械）
4. 系统自动填充默认变量集和默认宏族：
   - 电气 → i,u + electric-connect
   - 液压 → p,q + hydraulic-connect
   - 机械 → F,x + mechanical-connect
5. 用户可选择其他可用的宏族或保持默认
6. 配置保存到port_config表

### 2. 连接生成阶段

在生成系统SMT模型时：

1. 系统分析CAD连线，识别连接点及其连接的端口
2. 统计每个连接点上的端口数量（arity）
3. 查询相关端口的port_config配置，获取选择的宏族名称
4. 从port_connect_macro_family表读取宏族的macros_json
5. 根据连接点的arity从宏族中选择对应的宏
6. 将宏展开为SMT约束（替换占位符{0}, {1}, ...为实际端口变量）
7. 将生成的约束写入系统SMT的connect_block

**示例**：

假设连接点有3个端口：KA1.Coil.A1、KA1.Coil.A2、L1.1，且都配置为electric-connect宏族：

1. 识别arity=3
2. 从electric-connect宏族中选择connect3e宏
3. 获取expansion模板：
   ```
   (assert (= (+ {0}.i {1}.i {2}.i) 0))
   (assert (= {0}.u {1}.u))
   (assert (= {1}.u {2}.u))
   ```
4. 替换占位符：
   ```smt
   (assert (= (+ KA1.Coil.A1.i KA1.Coil.A2.i L1.1.i) 0))
   (assert (= KA1.Coil.A1.u KA1.Coil.A2.u))
   (assert (= KA1.Coil.A2.u L1.1.u))
   ```

### 3. 宏族管理

在PortConfigEditDialog中：

- **查看宏族**：表格显示所有可用宏族（内置+自定义），包括宏族名称、领域、支持的端口数、描述
- **添加宏族**：点击"添加宏族"按钮（当前显示待实现提示）
  - 未来将支持用户定义宏族名称、领域、多个arity的宏定义
- **删除宏族**：点击"删除宏族"按钮
  - 内置宏族（is_builtin=1）不可删除，系统会提示
  - 自定义宏族可删除，删除前会确认
- **选择宏族**：从下拉列表选择宏族应用到当前端口配置

## 自定义宏族

用户可创建自定义宏族以支持特殊连接语义：

### 使用场景

1. **非标准物理量**：如热流、光强等非电/液/机领域
2. **特殊约束关系**：不是简单的守恒+等势，而是更复杂的关系
3. **混合连接**：同一连接点包含多种类型的变量

### 创建步骤（未来功能）

1. 点击"添加宏族"按钮
2. 填写宏族基本信息：
   - 宏族名称（唯一）
   - 领域（可选择或自定义）
   - 描述信息
3. 定义宏集合：
   - 对每个支持的arity，定义宏名和展开模板
   - 展开模板使用{0}, {1}, {2}, ...作为端口占位符
4. 验证宏定义的正确性
5. 保存到数据库（is_builtin=0）

### 示例：热传导连接宏族

```json
{
    "family_name": "thermal-connect",
    "domain": "thermal",
    "description": "热传导连接宏族",
    "is_builtin": 0,
    "macros_json": [
        {
            "arity": 2,
            "macro_name": "connect2t",
            "expansion": "(assert (= (+ {0}.Q {1}.Q) 0))\n(assert (= {0}.T {1}.T))"
        }
    ]
}
```
其中：
- Q: 热流量（热功率）
- T: 温度

## 实现文件

### 数据库脚本
- `tools/init_builtin_macro_families.py`: 初始化内置宏族

### UI组件
- `widget/portconfigeditdialog.h/cpp/ui`: 端口配置编辑对话框
  - loadAvailableMacros(): 加载可用宏族列表
  - onAddMacroFamily(): 添加自定义宏族（待完善）
  - onDeleteMacroFamily(): 删除自定义宏族

### 业务逻辑
- `BO/behavior/ConnectSugarGenerator.*` (未来实现): 连接宏生成器
  - 输入：连接点信息、端口配置
  - 输出：SMT连接约束

## 技术要点

### 宏族选择算法

```python
def select_macro(macro_family_json, arity):
    """从宏族中选择匹配arity的宏"""
    macros = json.loads(macro_family_json)
    for macro in macros:
        if macro['arity'] == arity:
            return macro
    # 如果没有精确匹配，可以选择最接近的或报错
    raise ValueError(f"宏族中不支持{arity}个端口的连接")
```

### 宏展开算法

```python
def expand_macro(expansion_template, port_list):
    """展开宏模板为实际SMT约束"""
    result = expansion_template
    for i, port in enumerate(port_list):
        result = result.replace(f"{{{i}}}", port)
    return result
```

### 多相数组支持

对于三相电等数组端口（使用`(Array Int Real)`类型），宏展开需要对每一相分别处理：

```smt
; connect2e(3P, A, B) 应展开为对3个相位分别约束：
(assert (= (+ (select A.i 0) (select B.i 0)) 0))
(assert (= (select A.u 0) (select B.u 0)))
(assert (= (+ (select A.i 1) (select B.i 1)) 0))
(assert (= (select A.u 1) (select B.u 1)))
(assert (= (+ (select A.i 2) (select B.i 2)) 0))
(assert (= (select A.u 2) (select B.u 2)))
```

## 与现有代码的关系

### 数据流

```
[元件属性/本地物料库]
    ↓ tableTerm右键菜单
[PortConfigEditDialog] ← port_connect_macro_family表
    ↓ 保存配置
[port_config表] ← 存储选择的宏族名称
    ↓ 系统建模时读取
[ConnectSugarGenerator] ← 根据arity选择宏
    ↓ 生成约束
[system_smt.connect_block]
```

### 相关表结构

```
port_config:
    - port_config_id (主键)
    - component_container_id
    - func_block (功能子块代号)
    - port_name (端口名称)
    - port_type (electric/hydraulic/mechanical/other)
    - direction (input/output/bidirectional)
    - variable_profile (default/custom)
    - variables_json (变量列表JSON)
    - connect_macro (宏族名称) ← 存储宏族名而非单个宏名
    - created_at
    - updated_at

port_connect_macro_family:
    - family_id (主键)
    - family_name (宏族名称，唯一)
    - domain (领域)
    - description (描述)
    - is_builtin (是否内置)
    - macros_json (宏定义JSON数组)
    - created_at
```

## 优势与扩展性

### 优势

1. **简化用户配置**：用户只需选择宏族，无需关心具体端口数
2. **提高系统灵活性**：支持任意端口数的连接，只需在宏族中定义
3. **统一管理**：内置宏族确保基本功能，自定义宏族支持扩展
4. **易于维护**：修改连接逻辑只需更新宏族定义，无需修改代码

### 扩展方向

1. **宏族继承**：支持宏族之间的继承关系
2. **宏族版本管理**：支持宏族的版本控制和升级
3. **宏族导入导出**：支持宏族定义的导入导出，便于共享
4. **宏族验证工具**：提供工具验证宏定义的正确性和完备性
5. **可视化宏编辑器**：提供图形化界面编辑宏族定义

## 参考文档

- `docs/port_config_fixes_summary.md`: 端口配置功能修复总结
- `docs/phase2_implementation_summary.md`: Phase 2实现总结
- `AGENTS.md`: 开发指南（根目录）
- `README.md`: 项目总体说明
- `ToDoList.md`: Phase 4连接语法糖生成任务

## 版本历史

- **v1.0** (2025-10-30): 初始版本，定义连接宏族概念，实现内置宏族和基本管理功能
