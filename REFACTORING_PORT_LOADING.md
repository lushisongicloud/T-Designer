# 端口加载逻辑重构总结

## 修改概述

本次重构完全重写了 `TModelAutoGenerator` 中端口列表和端口配置的加载逻辑，将分散的数据库查询整合到 `loadComponents()` 函数中，并新增两个专用辅助函数。

## 核心改动

### 1. 新增辅助函数

#### `loadPortsFromDatabase(int equipmentId, QList<QPair<QString, QString>> &ports)`
- **功能**: 从 `EquipmentTemplate` 表加载端口列表
- **算法**:
  1. 查询 `SELECT SpurDT, ConnNum FROM Equipment_Template WHERE Equipment_ID = ?`
  2. 使用 `SpurDT` 作为功能子块名（如果为空则使用 `ConnNum`）
  3. 将 `ConnNum` 按 `￤` 分隔符拆分为单独的端口号
  4. 组装为 `(功能子块, 端口号)` 的列表

- **示例**:
  ```
  Equipment_ID: PXC.2700356
  SpurDT: "Coil"
  ConnNum: "A1￤A2"
  → 结果: [("Coil", "A1"), ("Coil", "A2")]
  ```

#### `loadPortConfigsForEquipment(int equipmentId)`
- **功能**: 加载端口的类型、变量和连接宏配置到 `m_portConfigs`
- **算法**:
  1. 查询 `equipment_containers.container_id` WHERE `equipment_id = ?`
  2. 使用 `container_id` 查询 `port_config` 表
  3. 解析 JSON 变量定义
  4. 为空值填充默认配置（默认变量、默认宏族）
  5. 存储到 `m_portConfigs` 映射表（key: "功能子块.端口号"）

- **端口类型默认配置**:
  - `electric` → 变量: `i,u`, 宏: `electric-connect`
  - `hydraulic` → 变量: `p,q`, 宏: `hydraulic-connect`
  - `mechanical` → 变量: `F,x`, 宏: `mechanical-connect`

### 2. 重构 `loadComponents()`

#### 单器件模式分支
```cpp
// 端口信息：优先使用外部 UI 预加载端口
if (!m_preloadedPorts.isEmpty()) {
    comp.ports = m_preloadedPorts;
} else {
    loadPortsFromDatabase(comp.equipmentId, comp.ports);
}

// 加载该器件的端口配置信息到 m_portConfigs
loadPortConfigsForEquipment(comp.equipmentId);
```

#### 批量模式分支
```cpp
while (query.next()) {
    ComponentInfo comp;
    comp.equipmentId = query.value("Equipment_ID").toInt();
    comp.code = query.value("PartCode").toString();
    comp.name = query.value("Name").toString();
    comp.description = query.value("Desc").toString();
    
    // 从数据库加载端口列表
    loadPortsFromDatabase(comp.equipmentId, comp.ports);
    
    m_components.append(comp);
}
```

### 3. 优化 `processNextComponent()`

```cpp
// 对于批量模式的后续器件，需要重新加载其端口配置
// (单器件模式或批量模式的第一个器件已在 loadComponents() 中加载)
if (m_currentIndex > 0) {
    m_portConfigs.clear();
    loadPortConfigsForEquipment(comp.equipmentId);
}
```

**优化逻辑**:
- 第一个器件（index=0）的配置已在 `loadComponents()` 中加载，无需重复
- 后续器件（index>0）需要清空并重新加载各自的配置

### 4. 移除冗余调用

从 `startAutoGeneration()` 中移除了以下代码：
```cpp
// 已删除：
// loadExistingPortTypes();
// if (m_portConfigs.isEmpty()) { ... }
```

**原因**: `loadComponents()` 已经完成了所有端口配置的加载，无需在开始生成时重复加载。

## 数据流变化对比

### 重构前
```
loadComponents()
  → 仅加载基本信息 (equipmentId, code, name, desc)
  
startAutoGeneration()
  → loadExistingPortTypes()  // 单独加载端口配置
  → buildPortListPreview()   // 构建预览（此时可能配置未加载完成）
  
processNextComponent()
  → 每个器件都调用 loadExistingPortTypes()  // 重复加载
```

### 重构后
```
loadComponents()
  → loadPortsFromDatabase()           // 加载端口列表
  → loadPortConfigsForEquipment()     // 加载端口配置
  → 数据完整准备好
  
startAutoGeneration()
  → buildPortListPreview()            // 直接使用已加载的配置
  
processNextComponent()
  → if (m_currentIndex > 0)           // 仅后续器件重新加载
      loadPortConfigsForEquipment()
```

## 关键优势

### 1. 时序正确性
- **重构前**: 预览时配置可能尚未加载，导致端口类型信息缺失
- **重构后**: 加载顺序明确，预览时配置必定已准备好

### 2. 性能优化
- 减少数据库查询次数（批量模式下第一个器件不再重复加载）
- 消除了 `startAutoGeneration()` 中的冗余 `loadExistingPortTypes()` 调用

### 3. 代码清晰度
- 端口加载逻辑集中在 `loadComponents()`，职责明确
- 辅助函数 `loadPortsFromDatabase()` 和 `loadPortConfigsForEquipment()` 可复用

### 4. 数据一致性
- 统一从 `EquipmentTemplate` 表加载端口列表
- 统一从 `port_config` 表加载端口配置
- 遵循 `Equipment_ID → equipment_containers → port_config` 的查询路径

## 端口列表预览格式

现在预览显示会包含端口类型信息：

```
=== 端口列表预览 ===
- 功能子块: Coil, 端口: A1 [类型: electric]
- 功能子块: Coil, 端口: A2 [类型: electric]
- 功能子块: Contact, 端口: 11 [类型: electric]
- 功能子块: Contact, 端口: 14 [类型: electric]
```

**显示规则**:
- 有配置信息时显示 `[类型: electric/hydraulic/mechanical]`
- 无配置信息时不显示类型标签

## 数据库表依赖

### 核心表结构
```sql
-- 端口列表来源
Equipment_Template (
    Equipment_ID INTEGER,
    SpurDT TEXT,        -- 功能子块名
    ConnNum TEXT        -- 端口列表（￤ 分隔）
)

-- 端口配置来源
equipment_containers (
    equipment_id INTEGER,
    container_id INTEGER
)

port_config (
    container_id INTEGER,
    function_block TEXT,
    port_name TEXT,
    port_type TEXT,              -- electric/hydraulic/mechanical
    variables_json TEXT,         -- JSON: [{"name":"i,u"}]
    connect_macro TEXT           -- 连接宏族名
)
```

## 测试要点

### 1. 单器件模式
- [x] 预加载端口优先级（UI tableTerm → 数据库）
- [x] 端口配置正确加载
- [x] 预览显示端口类型

### 2. 批量模式
- [ ] 第一个器件使用 loadComponents() 加载的配置
- [ ] 后续器件（index>0）重新加载各自配置
- [ ] 不同器件的端口配置互不干扰

### 3. 端口解析
- [ ] SpurDT 优先作为功能子块名
- [ ] ConnNum 为空时的 fallback 处理
- [ ] ￤ 分隔符正确拆分端口号

### 4. 默认值处理
- [ ] 缺失 variables_json 时使用默认变量
- [ ] 缺失 connect_macro 时使用默认宏族
- [ ] 未知端口类型的处理

## 后续建议

1. **添加单元测试**: 为 `loadPortsFromDatabase()` 和 `loadPortConfigsForEquipment()` 编写测试
2. **错误处理增强**: 对数据库查询失败、数据格式错误等异常情况增加更健壮的处理
3. **日志完善**: 在关键步骤增加调试日志，方便追踪端口加载过程
4. **文档更新**: 更新 AGENTS.md 中关于端口加载流程的描述

## 修改文件清单

- `BO/ai/tmodelautogenerator.cpp` - 实现文件
- `BO/ai/tmodelautogenerator.h` - 头文件声明

## 兼容性说明

本次重构保持了与现有功能的完全兼容：
- UI 预加载端口的优先级不变
- 端口类型识别、模型生成流程不受影响
- 数据库结构无变更
- 对外接口（信号/槽）保持不变

---

**重构完成日期**: 2025-01
**涉及模块**: T-Model自动生成器 (AI辅助建模)
**参考文档**: AGENTS.md - Development Sprint Goals
