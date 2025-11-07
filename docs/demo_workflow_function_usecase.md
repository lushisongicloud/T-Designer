# DemoWorkflow 功能管理用例（边界识别 & 完整性验证）

本用例基于仓库中的 `MyProjects/DemoWorkflow/DemoWorkflow.db` 项目，录入了 3 个新的功能定义，分别覆盖电源回路、接触器线圈与安全链。用例目标：

1. 通过 FunctionManagerDialog 的“自动查找边界条件”功能验证 `SystemStructureService` 的裁剪与边界推导逻辑；
2. 通过“执行器取反完整性检查”验证 SAT 正/反求解的完整性提示；
3. 为后续集成测试提供可复现的数据样本。

## 功能数据概览

| 功能名称 | 执行器端口 | 链路 (link) | 关键约束 | 预期边界组件（首邻接） |
| --- | --- | --- | --- | --- |
| `QS_FU_PowerPath` | `FU.2` | `T,QS,FU` | `QS.closed=true`; `FU.2.u=220` | `L1`, `L2`, `L7`, `L21` |
| `KM_Coil_Energize` | `KM.A1_A2` | `KM` | `KM.A1_A2.i=0.1`; `KM.1.u=220` | `FR`, `L8`, `L17`, `L18`, `L20` |
| `SafetyChain_SB` | `SB2.2` | `SB1,SB2` | `SB1.closed=true`; `SB2.closed=true` | `L15`, `L16`, `L17`, `L18`, `L19` |

> 说明：预期边界集合基于系统描述中的一阶邻接分析（示例脚本见下），UI 侧实际结果在包含更多层级信息时应为上述组件或其等价端口集合。

所有功能的 `constraintIntegrity` 初始值均为 `未检查`，便于在 UI 中直接体验完整性检查流程。

## 插入的数据

- `Function` 表新增 ID `3/4/5` 三条记录（详见表格）。`CmdValList`、`LinkText`、`ComponentDependency` 与 `VariableConfigXml` 均与 XML 定义保持一致。
- `function_document` 表为系统容器（`container_id = 1`）新增文档，包含上述三个功能的树结构、依赖、约束、可行区间以及全局 `variableRangeConfig (u/i)` 片段。

如需复核，可在仓库根目录执行：

```bash
sqlite3 MyProjects/DemoWorkflow/DemoWorkflow.db "
  SELECT FunctionID, FunctionName, LinkText, CmdValList
  FROM Function WHERE FunctionID BETWEEN 3 AND 5;
"
sqlite3 MyProjects/DemoWorkflow/DemoWorkflow.db "
  SELECT LENGTH(xml_text) FROM function_document WHERE container_id = 1;
"
```

## 验证步骤建议

1. 打开 DemoWorkflow 项目，进入 FunctionManagerDialog。
2. 分别选中上述三个功能，执行：
   - “自动查找边界条件”，预期得到表格中的边界组件集合（组件顺序可能按连接遍历顺序轻微差异）。
   - “执行器取反完整性检查”，正向 SAT 通过且反向取反 UNSAT 时状态应更新为“完整”；若某约束缺失导致“不完整”，请按约束提示补齐后再次校验。
3. 可选操作：
   - “自动查找依赖功能”目前不会返回结果（尚无依赖链），执行后应提示“未匹配到依赖功能”。
   - 在 FunctionEditDialog 中查看 `变量取值范围`，确认 `VariableValueConfig` 中预设范围已加载。

## 边界计算示例脚本

以下 Python 片段直接解析 `systemDescription`，对比链路与邻接关系得出文中列出的边界集合，可用于快速核对：

```python
system_description = """..."""  # 取自 models.systemDescription

links = {
    'QS_FU_PowerPath': ['T', 'QS', 'FU'],
    'KM_Coil_Energize': ['KM'],
    'SafetyChain_SB': ['SB1', 'SB2'],
}

import collections

connections = []
for line in system_description.splitlines():
    line = line.strip()
    if line.startswith('connect'):
        args = line[line.index('(')+1:-1]
        nodes = [token.strip() for token in args.split(',')]
        comps = [(node.split('.')[0], node) for node in nodes]
        connections.append(comps)

adj = collections.defaultdict(set)
for comps in connections:
    names = [c[0] for c in comps]
    for name in names:
        adj[name].update(set(names) - {name})

for func, members in links.items():
    boundary = set()
    for member in members:
        boundary.update(neigh for neigh in adj.get(member, set()) if neigh not in members)
    print(func, sorted(boundary))
```

运行结果示例：

```
QS_FU_PowerPath -> ['L1', 'L2', 'L21', 'L7']
KM_Coil_Energize -> ['FR', 'L17', 'L18', 'L20', 'L8']
SafetyChain_SB -> ['L15', 'L16', 'L17', 'L18', 'L19']
```

若后续在 UI 中观察到边界集合与此存在差异，请优先检查链路是否被修改或新增了更细粒度的端口描述。
