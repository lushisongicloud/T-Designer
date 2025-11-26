# T-Designer 代码审查与差距分析报告

## 执行日期
2025-11-26

## 审查目标
根据 README.md 中的开发周期目标，本次审查重点检查当前 master 分支的代码实现状态，特别是针对以下功能流程的完成度：

1. 在项目中插入器件（器件模型含 SMT 语言描述的 T 语言模型） - **已基本实现**
2. 在 CAD 图中绘制功能子块 - **已基本实现**
3. 在 CAD 图中器件端口间建立连接 - **已基本实现**
4. 构建系统描述 - **部分实现，存在重大缺口**
5. 构建系统的功能描述 - **部分实现，存在重大缺口**
6. 查看 D 矩阵/自动生成 D 矩阵 - **框架已实现，但集成不完整**

## 一、数据库结构审查

### 1.1 已完成的数据库表结构

#### 模板数据库 (templete/project.db)
已建立以下关键表：

- **component_smt**: 元件 SMT 模型存储
  - 支持 equipment_id 和 container_id 双重索引
  - 包含语法状态和端口签名字段
  - ✅ 结构完整

- **system_smt**: 系统级 SMT 模型存储
  - def_block: 组件定义块
  - connect_block: 连接语句块
  - raw_block: 原生 SMT 块
  - ✅ 结构完整

- **port_config**: 端口配置表
  - 支持端口类型、变量集、连接宏配置
  - ✅ 结构完整

- **port_connect_macro_family**: 连接宏族表
  - 支持内置宏族（electric/hydraulic/mechanical）
  - 支持用户自定义宏族
  - ✅ 结构完整，已有内置数据

- **function_definition**: 功能定义表
  - 支持层次化功能定义
  - ✅ 结构完整

- **function_dependency**: 功能依赖关系表
  - ✅ 结构完整

- **function_io**: 功能输入输出表
  - ✅ 结构完整

- **dmatrix_meta**: D矩阵元数据表
  - ✅ 结构完整

#### 现有项目数据库对比
- **test.db**: 包含完整的新表结构，包括 container 相关表
- **DemoSystem.db**: 仅有 function_bindings 表，**缺少新表结构**
- ⚠️ **问题**: 示例项目数据库结构不统一，需要迁移脚本

### 1.2 传统元件表 (Equipment)
- TModel 字段存储 T 语言模型（VARCHAR(2000)）
- TModelDiag 字段用于诊断模型
- ✅ ref/LdMainData.db 中已有 13,860 个元件的 T 模型
- ✅ MyProjects/test.db 中的元件也包含 T 模型

### 1.3 数据迁移状况
- ⚠️ **缺口**: component_smt 表当前为空（test.db 中 COUNT=0）
- ⚠️ **缺口**: system_smt 表当前为空（test.db 中 COUNT=0）
- ⚠️ **缺口**: function_definition 表当前为空（test.db 中 COUNT=0）
- ✅ port_config 表有数据（15 条记录）
- ✅ port_connect_macro_family 表有内置宏族（3 个）

## 二、元件建模与编辑功能审查

### 2.1 元件属性对话框 (dialogUnitAttr)

#### 已实现功能 ✅
1. **T 语言模型编辑**
   - QsciEdit 控件用于编辑 TModel 字段
   - 保存到 Equipment.TModel 字段
   - 文件位置：dialogUnitAttr.cpp:182, 737, 789

2. **T 语言模型校验** (on_BtnValidateTModel_clicked)
   - 语法校验（通过 TModelCheckService）
   - 端口一致性校验
   - 占位符替换与验证
   - 从 port_config 表读取端口配置
   - 支持电气/液压/机械端口类型
   - 文件位置：dialogUnitAttr.cpp:1492-1666

3. **端口配置集成** (通过右键菜单)
   - tableTerm 表格增加"变量"列（第3列）
   - 右键菜单"配置端口"打开 PortConfigEditDialog
   - 右键菜单"删除配置"删除端口配置
   - getPortVariables() 方法从 port_config 读取变量
   - 文件位置：dialogUnitAttr.cpp:2068-2149

4. **端口变量自动生成**
   - TModelHelper::generatePortVariablesFromTable()
   - TModelHelper::updatePortVariablesInTModel()
   - 文件位置：dialogUnitAttr.cpp:2312-2321

5. **故障模式管理**
   - 从 T 语言模型自动提取故障模式
   - TModelHelper::autoFillFaultModesFromTModel()
   - 文件位置：dialogUnitAttr.cpp:1486

6. **容器关联**
   - m_componentContainerId 字段正确设置和使用
   - copyPortConfigAndMacrosFromLibrary() 支持端口配置复制
   - 文件位置：dialogUnitAttr.cpp:759, 866

#### 存在的缺口 ⚠️
1. **component_smt 表未使用**
   - 当前仍保存到 Equipment.TModel（2000字符限制）
   - 未使用 component_smt 表（无字符限制，支持版本管理）
   - **建议**: 迁移到 component_smt 表，保留 TModel 字段兼容性

2. **端口配置 UI 不够直观**
   - 端口配置通过右键菜单操作，用户可能不易发现
   - tableTerm 的"变量"列信息密度较高
   - **建议**: 考虑在端口行内联编辑或增加可视化提示

3. **连接宏族管理 UI 缺失**
   - PortConfigEditDialog 中选择宏族，但没有宏族管理界面
   - 无法查看/编辑/添加自定义宏族
   - **建议**: 增加宏族管理对话框

### 2.2 本地物料库 (dialogsymbols / dialogsymbolattribute)

#### 当前状况 ❌
- **dialogsymbolattribute**: 未找到 T 语言模型编辑相关代码
- **dialogsymbolattribute**: 未找到端口配置集成代码
- **dialogsymbolattribute**: 未找到 T 语言校验相关代码

#### 重大缺口 ⚠️
1. **本地物料库缺少 T 语言模型编辑功能**
   - 无法在模板库中编辑 T 语言模型
   - 无法在模板库中配置端口
   - 无法在模板库中校验 T 语言

2. **代码复用不足**
   - dialogUnitAttr 的功能未复用到 dialogsymbolattribute
   - 违反了 README.md 第3点："编辑、修改内容大同小异，要尽量复用代码"

#### 推荐改进方案
1. **共享 T 语言编辑组件**
   - 提取 TModelEditPanel 公共组件
   - dialogUnitAttr 和 dialogsymbolattribute 都使用该组件
   - 统一校验逻辑

2. **共享端口配置组件**
   - PortConfigEditDialog 已存在，可直接复用
   - 需要在 dialogsymbolattribute 中集成

## 三、系统描述构建功能审查

### 3.1 系统描述生成 (mainwindow_project.cpp)

#### 已实现功能 ✅
1. **DEF 块生成** (selectSystemUnitStripLineInfo)
   - 从 Equipment 表读取元件信息
   - 生成 "MARK NAME(param=value)" 格式
   - 文件位置：mainwindow_project.cpp:3500-3530

2. **连接语句生成** (buildAutoConnectionsFromCad)
   - 从 JXB 表读取连线信息
   - 根据等电位号分组端口
   - 生成 connect2e/connect3e 语句
   - 文件位置：mainwindow_project.cpp:3382-3450

3. **系统描述显示**
   - textEditSystemDiscription 控件显示完整系统描述
   - 格式：DEF BEGIN...DEF END + 连接语句
   - LoadProjectSystemDescription() 自动生成

#### 存在的重大缺口 ⚠️

##### 1. 未使用 system_smt 表
- **当前**: 系统描述仅存在于 textEditSystemDiscription 控件中
- **期望**: 系统描述应保存到 system_smt 表（def_block, connect_block, raw_block）
- **影响**: 
  - 系统描述无法持久化
  - 无法版本管理
  - 无法与功能管理、D矩阵集成

##### 2. 连接宏选择不智能
- **当前**: buildAutoConnectionsFromCad 硬编码使用 connect2e/connect3e
- **期望**: 根据端口配置中的宏族和端口类型自动选择
  - 电气端口 → 从 electric-connect 宏族选择
  - 液压端口 → 从 hydraulic-connect 宏族选择
  - 机械端口 → 从 mechanical-connect 宏族选择
- **影响**: 无法支持液压、机械系统建模

##### 3. 缺少 SystemModelAssembler
- **期望**: 应有专门的 BO/behavior/systemmodelassembler.{h,cpp}
- **功能**: 
  - 从 container 层面组装系统描述
  - 读取元件 SMT（优先 component_smt 表，降级到 Equipment.TModel）
  - 读取端口配置（port_config 表）
  - 根据连线信息和端口类型生成连接语句
  - 保存到 system_smt 表

##### 4. 缺少 ConnectSugarGenerator
- **期望**: 应有专门的 BO/behavior/connectsugargenerator.{h,cpp}
- **功能**:
  - 根据端口类型和数量选择连接宏
  - 从 port_connect_macro_family 读取宏族定义
  - 自动展开为 SMT 约束
  - 支持多相数组（select .i[0/1/2]）

##### 5. 元件级容器行为适配器缺失
- **期望**: 应有 BO/container/containerbehavioradapter.{h,cpp}
- **功能**:
  - 从实体元件读取功能子块（端口）
  - 从实体元件读取 SMT 模型
  - 从 port_config 读取端口配置
  - 生成容器级接口描述
  - 生成容器级 SMT（直接继承单元件）

### 3.2 代码位置与调用链
```
mainwindow_project.cpp:LoadProjectSystemDescription()
  ↓
selectSystemUnitStripLineInfo() // 生成 DEF 块
buildAutoConnectionsFromCad()   // 生成 CONNECT 块
  ↓
ui->textEditSystemDiscription->setText() // 仅显示，未持久化
```

**缺少的调用链**:
```
[应有] mainwindow_project.cpp:LoadProjectSystemDescription()
  ↓
SystemModelAssembler::buildFromProject()
  ↓
  - ContainerBehaviorAdapter::getComponentSmt() // 读取元件 SMT
  - ConnectSugarGenerator::generate()           // 生成连接语句
  - SystemModelAssembler::save()                // 保存到 system_smt 表
  ↓
ui->textEditSystemDiscription->setText()       // 从 system_smt 读取显示
```

## 四、功能管理功能审查

### 4.1 功能管理对话框 (widget/functionmanagerdialog.*)

#### 已实现功能 ✅
1. **功能仓库** (FunctionRepository)
   - 从 function_definition 表读写功能
   - 支持层次化功能定义
   - 文件位置：BO/function/functionrepository.{h,cpp}

2. **功能管理对话框**
   - 入口：mainwindow_units.cpp:on_BtnFunctionManage_clicked()
   - 基于 function_definition 表的 CRUD 操作
   - 文件位置：widget/functionmanagerdialog.{h,cpp}

3. **链路与依赖**
   - 支持链路定义（link）
   - 支持功能依赖（parent_function_id）
   - 自动依赖识别（onAutoDependency）

4. **约束完整性检查**
   - onCheckIntegrity 功能
   - 正向/反向执行器约束 SAT 检查

5. **离线求解结果**
   - 支持离线求解结果缓存
   - onAddOffline/onRemoveOffline/onSaveOffline

#### 存在的重大缺口 ⚠️

##### 1. 功能文档 (function_document) 表未使用
- **当前**: 数据保存在 function_definition, function_dependency, function_io 等多个表
- **期望**: 应支持 functions_xml 存储（参考 T-Solver）
  - 完整的功能树结构
  - 链路、依赖、约束、属性、离线结果
  - 变量范围配置
- **影响**: 
  - 缺少统一的功能文档格式
  - 难以导入/导出功能定义
  - 与 T-Solver 格式不兼容

##### 2. 系统结构服务未完整集成
- **期望**: SystemStructureService 应提供完整的裁剪能力
- **当前**: 文件存在（BO/function/systemstructureservice.{h,cpp}）
- **缺口**: 
  - 未见边界条件自动识别的完整实现
  - 未见链路裁剪后的系统描述持久化
  - 与 FunctionManagerDialog 集成不充分

##### 3. 变量范围配置 UI 缺失
- **期望**: 应有"变量取值范围"编辑对话框（参考 T-Solver）
- **当前**: function_variable_config.{h,cpp} 和 variable_range_config.{h,cpp} 存在
- **缺口**: 
  - FunctionManagerDialog 中未见"变量取值范围"按钮
  - 未见 FunctionVariableValueDialog 集成
  - 无法编辑变量类型/范围/SAT 样本

##### 4. 功能与系统描述脱节
- **当前**: 
  - FunctionManagerDialog 需要传入 systemDescription 字符串
  - systemDescription 来自 textEditSystemDiscription
  - 没有从 system_smt 表读取
- **影响**:
  - 功能管理依赖手动维护的系统描述文本
  - 系统描述更新后功能管理不同步
  - 缺少自动化集成

##### 5. 功能完整性检查实现不完整
- **当前**: onCheckIntegrity 存在
- **缺口**:
  - 未见执行器变量取反逻辑
  - 未见 SAT/UNSAT 结果的详细反馈
  - 未见约束完整性状态写回 function_definition

### 4.2 功能管理调用链

**当前调用链**:
```
mainwindow_units.cpp:on_BtnFunctionManage_clicked()
  ↓
FunctionManagerDialog(db, containerId, systemDescription, systemEntity)
  ↓
FunctionRepository::loadAll() // 从 function_definition 读取
  ↓
[用户编辑]
  ↓
FunctionRepository::save() // 保存到 function_definition
```

**缺少的调用链**:
```
[应有] FunctionManagerDialog::onAutoBoundary()
  ↓
SystemStructureService::cropSystemDescription(link)
  ↓
SystemStructureService::identifyBoundaryVariables()
  ↓
[自动填充边界条件到约束列表]

[应有] FunctionManagerDialog::onCheckIntegrity()
  ↓
FunctionAnalysisService::checkConstraintCompleteness()
  ↓
  - 正向求解（执行器 = expected）
  - 反向求解（执行器 != expected）
  ↓
FunctionRepository::updateIntegrityStatus()

[应有] FunctionManagerDialog::onEditVariableRanges()
  ↓
FunctionVariableValueDialog::exec()
  ↓
VariableRangeConfig::save() // 保存到 function_document
```

## 五、D 矩阵功能审查

### 5.1 D 矩阵构建器 (testability/d_matrix_builder.*)

#### 已实现功能 ✅
1. **D 矩阵构建器核心**
   - DMatrixBuilder 类完整实现
   - 支持故障收集（功能故障、元件模式故障）
   - 支持测试收集（功能测试、模式测试、信号测试）
   - 支持可检测性计算（detectability）
   - 文件位置：testability/d_matrix_builder.{h,cpp}

2. **D 矩阵查看器**
   - DMatrixViewerDialog 完整实现
   - 支持导出 CSV
   - 支持保存/另存为元数据
   - 支持故障/测试选择
   - 文件位置：widget/dmatrixviewerdialog.{h,cpp,ui}

3. **D 矩阵服务**
   - DMatrixService 提供构建和持久化能力
   - 保存到 dmatrix_meta 表
   - 文件位置：mainwindow_diagnosis.cpp:3820-3890

4. **入口集成**
   - 入口：mainwindow_diagnosis.cpp:on_BtnViewDMatrix_clicked()
   - 连接 systemEntity
   - 支持重新构建

#### 存在的缺口 ⚠️

##### 1. 测试/故障维度信息不完整
- **当前**: 仅支持基本的故障定义和测试定义
- **期望**: 应支持扩展维度（参考 README.md）
  - **测试维度**: 复杂性、费用、时间、成功率、备注
  - **故障维度**: 先验概率、影响严重度、备注
- **影响**: 
  - 无法进行成本优化的测试优选
  - 无法基于概率进行诊断优先级排序

##### 2. 与 function_definition 集成不完整
- **当前**: DMatrixBuilder::setFunctionInfoMap() 需要手动传入
- **期望**: 应自动从 function_definition 表读取
- **影响**: 功能管理和 D 矩阵脱节

##### 3. 与 system_smt 集成不完整
- **当前**: 依赖 systemDescription 字符串参数
- **期望**: 应从 system_smt 表读取系统描述
- **影响**: 系统描述更新后 D 矩阵不同步

##### 4. D 矩阵元数据存储不规范
- **当前**: 元数据保存为 JSON 文件 + dmatrix_meta 表记录
- **期望**: 应该扩展 dmatrix_meta 表字段或使用关联表
  - test_definition 表存储测试详细信息
  - fault_definition 表存储故障详细信息
  - test_fault_coverage 表存储覆盖关系
- **影响**: 难以查询和分析 D 矩阵数据

##### 5. 测试管理界面集成不完整
- **当前**: DMatrixViewerDialog 独立于测试管理界面
- **期望**: 应在测试管理对话框的"依赖矩阵"tab 中集成
- **影响**: 
  - 用户需要在多个窗口间切换
  - 测试优选、指标预计功能未连接

### 5.2 测试管理 (dialogtestreport / dialogusertest)

#### 审查发现
- dialogtestreport.cpp: 传统测试报告对话框
- dialogusertest.cpp: 用户测试对话框
- ⚠️ 未找到"依赖矩阵"tab 集成 DMatrixViewerDialog 的代码
- ⚠️ 测试优选、测试性指标预计功能与 D 矩阵数据未连接

#### 推荐改进
1. **在测试管理对话框中嵌入 DMatrixViewerDialog**
   - 作为"依赖矩阵"tab 页
   - 或作为子对话框

2. **连接测试优选功能**
   - 从 D 矩阵数据读取覆盖关系
   - 使用扩展的测试维度信息（费用、时间等）
   - 实现贪心/遗传算法优选

3. **连接测试性指标预计**
   - 从 D 矩阵计算故障检测率
   - 从 D 矩阵计算故障隔离率
   - 按容器层次汇总指标

## 六、容器层功能审查

### 6.1 容器数据模型 (BO/container/*)

#### 已实现功能 ✅
1. **容器仓库** (containerrepository.*)
   - container 表 CRUD
   - container_hierarchy 层次关系
   - ensureTables() 确保表存在

2. **容器数据** (containerdata.*)
   - ContainerEntity 数据对象
   - 支持层次化管理

3. **行为聚合器** (behavioraggregator.*)
   - 存在文件，功能待确认

#### 存在的重大缺口 ⚠️

##### 1. ContainerBehaviorAdapter 缺失
- **期望**: 元件级容器作为实体元件的封装和代理
- **功能**:
  - 从实体元件读取功能子块（端口）
  - 从实体元件读取 SMT 模型
  - 从 port_config 读取端口配置
  - 生成容器级接口描述
  - 生成容器级 SMT（直接继承）
- **影响**: 无法在容器层面进行 SMT 建模和分析

##### 2. equipment_containers 表未充分使用
- **当前**: test.db 中该表存在
- **缺口**: 
  - 未见自动为插入元件创建元件级容器的代码
  - 未见容器与实体元件的双向关联维护

##### 3. container_interface / container_state 系列表未使用
- **当前**: 数据库中这些表存在但为空
- **期望**: 应记录容器的接口定义和状态
- **影响**: 容器行为模型不完整

##### 4. 容器层 SMT 模型未实现
- **期望**: component_smt.container_id 应记录容器的 SMT 模型
- **当前**: component_smt 表中 container_id 字段未使用
- **影响**: 无法为高层容器（子系统、系统）建立 SMT 模型

### 6.2 推荐的容器集成方案

#### 方案概述
根据 README.md 第9点，本阶段开发应"基于容器层面，将新增的 SMT 建模、功能管理等逻辑主要实现在容器层面"。

#### 实现步骤
1. **创建 ContainerBehaviorAdapter**
   ```cpp
   // 文件：BO/container/containerbehavioradapter.{h,cpp}
   class ContainerBehaviorAdapter {
   public:
       // 从实体元件读取并生成容器 SMT
       QString getContainerSmt(int containerId, const QSqlDatabase &db);
       
       // 从实体元件读取并生成容器接口
       QList<PortInfo> getContainerPorts(int containerId, const QSqlDatabase &db);
       
       // 保存容器 SMT 到 component_smt 表
       bool saveContainerSmt(int containerId, const QString &smt, const QSqlDatabase &db);
   };
   ```

2. **自动创建元件级容器**
   ```cpp
   // 位置：mainwindow.cpp 或元件插入代码
   void MainWindow::onEquipmentInserted(int equipmentId) {
       ContainerRepository repo(T_ProjectDatabase);
       // 检查是否已有容器
       int containerId = repo.getContainerByEquipment(equipmentId);
       if (containerId == 0) {
           // 创建元件级容器
           ContainerEntity entity;
           entity.setName(getEquipmentName(equipmentId));
           entity.setLevel("component");
           containerId = repo.create(entity);
           // 关联元件和容器
           repo.linkEquipment(containerId, equipmentId);
       }
       // 使用 ContainerBehaviorAdapter 生成容器 SMT
       ContainerBehaviorAdapter adapter;
       QString smt = adapter.getContainerSmt(containerId, T_ProjectDatabase);
       adapter.saveContainerSmt(containerId, smt, T_ProjectDatabase);
   }
   ```

3. **集成到系统描述构建**
   ```cpp
   // 文件：BO/behavior/systemmodelassembler.cpp
   QString SystemModelAssembler::buildDefBlock() {
       QStringList defLines;
       ContainerRepository repo(m_db);
       QList<ContainerEntity> components = repo.fetchByLevel("component");
       ContainerBehaviorAdapter adapter;
       
       for (const ContainerEntity &comp : components) {
           // 读取容器 SMT（而非直接读 Equipment.TModel）
           QString smt = adapter.getContainerSmt(comp.id(), m_db);
           // 生成 DEF 行
           defLines.append(generateDefLine(comp, smt));
       }
       return "DEF BEGIN\n" + defLines.join("\n") + "\nDEF END";
   }
   ```

## 七、代码复用问题

### 7.1 重复代码识别

#### 问题1: dialogUnitAttr vs dialogsymbolattribute
- **重复内容**: T 语言模型编辑、校验、端口配置
- **当前**: dialogUnitAttr 有完整实现，dialogsymbolattribute 无
- **违反**: README.md 第3点关于代码复用的要求

#### 问题2: 功能管理界面碎片化
- **重复内容**: 功能编辑逻辑
- **当前**: FunctionManagerDialog, SelectFunctionDialog (T-Solver), dialogfunctionmanage
- **建议**: 统一到 FunctionManagerDialog，逐步替换旧界面

#### 问题3: 系统描述生成逻辑分散
- **重复内容**: DEF 块生成、连接语句生成
- **当前**: mainwindow_project.cpp 中的内联代码
- **建议**: 提取到 SystemModelAssembler

### 7.2 推荐的代码重构

#### 重构1: 提取 T 语言编辑面板
```cpp
// 新文件：widget/tmodeleditpanel.{h,cpp,ui}
class TModelEditPanel : public QWidget {
public:
    void load(int equipmentId, const QSqlDatabase &db);
    void loadFromLibrary(int libraryEquipmentId, const QSqlDatabase &libraryDb);
    bool save();
    bool validate();
    
private:
    QsciScintilla *m_editor;
    SmtSyntaxChecker m_syntaxChecker;
    TModelValidator m_validator;
};

// 在 dialogUnitAttr 中使用
m_tmodelPanel = new TModelEditPanel(this);
layout->addWidget(m_tmodelPanel);

// 在 dialogsymbolattribute 中使用（相同代码）
m_tmodelPanel = new TModelEditPanel(this);
layout->addWidget(m_tmodelPanel);
```

#### 重构2: 统一端口配置界面
```cpp
// 已存在：widget/portconfigeditdialog.{h,cpp,ui}
// 需要：确保在两个对话框中都可用

// dialogUnitAttr.cpp
void DialogUnitAttr::onConfigurePort() {
    PortConfigEditDialog dialog(T_ProjectDatabase, m_componentContainerId, this);
    dialog.exec();
}

// dialogsymbolattribute.cpp（待添加）
void DialogSymbolAttribute::onConfigurePort() {
    PortConfigEditDialog dialog(LibraryDatabase, m_componentContainerId, this);
    dialog.exec();
}
```

#### 重构3: 系统描述生成服务
```cpp
// 新文件：BO/behavior/systemmodelassembler.{h,cpp}
class SystemModelAssembler {
public:
    SystemModelAssembler(const QSqlDatabase &db);
    
    // 从项目数据库构建系统描述
    bool buildFromProject(int containerId);
    
    // 生成 DEF 块
    QString buildDefBlock();
    
    // 生成 CONNECT 块
    QString buildConnectBlock();
    
    // 保存到 system_smt 表
    bool save(int containerId);
    
private:
    QSqlDatabase m_db;
    ContainerBehaviorAdapter m_adapter;
    ConnectSugarGenerator m_generator;
};
```

## 八、待实现功能清单（按优先级排序）

### P0 - 阻塞性缺口（必须先完成）

1. **SystemModelAssembler 实现**
   - 位置：BO/behavior/systemmodelassembler.{h,cpp}
   - 依赖：ContainerBehaviorAdapter, ConnectSugarGenerator
   - 输出：system_smt 表数据
   - 预计工作量：3-5天

2. **ContainerBehaviorAdapter 实现**
   - 位置：BO/container/containerbehavioradapter.{h,cpp}
   - 功能：从实体元件读取 SMT，保存到 component_smt
   - 预计工作量：2-3天

3. **ConnectSugarGenerator 实现**
   - 位置：BO/behavior/connectsugargenerator.{h,cpp}
   - 功能：根据端口配置和宏族生成连接语句
   - 预计工作量：2-3天

4. **自动创建元件级容器**
   - 位置：mainwindow.cpp 或元件插入逻辑
   - 触发：元件插入时自动创建容器
   - 关联：equipment_containers 表
   - 预计工作量：1-2天

### P1 - 功能完整性（核心功能）

5. **本地物料库 T 语言编辑集成**
   - 位置：dialogsymbolattribute.cpp
   - 复用：TModelEditPanel
   - 预计工作量：2-3天

6. **功能管理与 system_smt 集成**
   - 修改：FunctionManagerDialog
   - 改为从 system_smt 读取系统描述
   - 预计工作量：1-2天

7. **变量范围配置 UI**
   - 位置：widget/functionvariablevaluedialog.{h,cpp,ui}
   - 集成：FunctionManagerDialog
   - 预计工作量：2-3天

8. **边界条件自动识别完善**
   - 位置：BO/function/systemstructureservice.cpp
   - 改进：identifyBoundaryVariables 实现
   - 集成：FunctionManagerDialog::onAutoBoundary
   - 预计工作量：2-3天

9. **约束完整性检查完善**
   - 位置：FunctionManagerDialog::onCheckIntegrity
   - 改进：执行器取反、SAT/UNSAT 反馈、状态写回
   - 预计工作量：2-3天

### P2 - D 矩阵增强（分析能力）

10. **D 矩阵扩展维度实现**
    - 修改：testability/d_matrix_builder.*
    - 新增：test_definition, fault_definition 表字段
    - 预计工作量：2-3天

11. **D 矩阵与测试管理集成**
    - 修改：dialogtestreport 或创建新对话框
    - 集成：DMatrixViewerDialog 作为 tab
    - 连接：测试优选、指标预计功能
    - 预计工作量：3-5天

12. **D 矩阵数据持久化改进**
    - 改进：dmatrix_meta 表或新增关联表
    - 支持：高效查询和分析
    - 预计工作量：1-2天

### P3 - 用户体验优化

13. **连接宏族管理界面**
    - 位置：widget/macrofamilymanagerdialog.{h,cpp,ui}
    - 功能：查看/添加/编辑/删除宏族
    - 预计工作量：2-3天

14. **端口配置 UI 优化**
    - 改进：tableTerm 内联编辑或可视化提示
    - 预计工作量：1-2天

15. **T 语言编辑面板提取**
    - 位置：widget/tmodeleditpanel.{h,cpp,ui}
    - 复用：dialogUnitAttr, dialogsymbolattribute
    - 预计工作量：2-3天

### P4 - 工具与脚本

16. **数据库迁移脚本**
    - 位置：tools/db_migrate_project.py
    - 功能：新表创建、数据迁移、版本升级
    - 预计工作量：1-2天

17. **SMT 批量校验脚本**
    - 位置：tools/validate_smt_snippets.py
    - 功能：扫描工程/库，生成校验报告
    - 预计工作量：1天

18. **演示项目生成脚本**
    - 位置：tools/generate_demo_project.py
    - 功能：创建完整的演示工程
    - 预计工作量：2-3天

## 九、总结与建议

### 9.1 总体评估

#### 已完成部分（约40%）
- ✅ 数据库表结构设计完整
- ✅ 端口配置基础设施就绪
- ✅ T 语言编辑与校验（元件属性）
- ✅ 功能管理基础框架
- ✅ D 矩阵构建器和查看器
- ✅ 容器数据模型

#### 部分实现（约30%）
- ⚠️ 系统描述生成（DEF/CONNECT 块生成，但未持久化）
- ⚠️ 功能管理（基础 CRUD，但缺少变量范围、边界识别）
- ⚠️ D 矩阵集成（独立对话框，但未与测试管理连接）

#### 未实现部分（约30%）
- ❌ ContainerBehaviorAdapter
- ❌ SystemModelAssembler
- ❌ ConnectSugarGenerator
- ❌ 本地物料库 T 语言编辑
- ❌ 变量范围配置 UI
- ❌ D 矩阵扩展维度
- ❌ 测试管理集成

### 9.2 关键阻塞点

1. **系统描述未持久化到 system_smt 表**
   - 影响：功能管理、D 矩阵都无法稳定工作
   - 优先级：P0

2. **容器行为适配器缺失**
   - 影响：无法在容器层面进行 SMT 建模
   - 违反：README.md 第9点的容器层优先原则
   - 优先级：P0

3. **连接宏选择不智能**
   - 影响：无法支持液压、机械系统
   - 优先级：P0

4. **本地物料库功能缺失**
   - 影响：无法维护模板库的 T 语言模型
   - 违反：README.md 第3点的代码复用原则
   - 优先级：P1

5. **功能管理与系统描述脱节**
   - 影响：功能分析依赖手动维护的文本
   - 优先级：P1

### 9.3 实施路线图建议

#### 第一阶段（2-3周）：打通核心流程
1. 实现 ContainerBehaviorAdapter（3天）
2. 实现 ConnectSugarGenerator（3天）
3. 实现 SystemModelAssembler（5天）
4. 自动创建元件级容器（2天）
5. 修改 LoadProjectSystemDescription 使用 SystemModelAssembler（1天）

**里程碑**: 系统描述可持久化到 system_smt 表

#### 第二阶段（2-3周）：完善功能管理
1. 功能管理从 system_smt 读取（2天）
2. 变量范围配置 UI（3天）
3. 边界条件自动识别完善（3天）
4. 约束完整性检查完善（3天）
5. 本地物料库 T 语言编辑集成（3天）

**里程碑**: 功能管理完整可用

#### 第三阶段（2-3周）：D 矩阵集成
1. D 矩阵扩展维度（3天）
2. D 矩阵数据持久化改进（2天）
3. D 矩阵与测试管理集成（5天）
4. 测试优选算法实现（5天）

**里程碑**: D 矩阵与测试管理闭环

#### 第四阶段（1-2周）：优化与工具
1. 连接宏族管理界面（3天）
2. T 语言编辑面板提取（3天）
3. 数据库迁移脚本（2天）
4. 演示项目生成（2天）

**里程碑**: 用户体验完善，工具齐备

### 9.4 风险与缓解

#### 风险1: Z3 求解性能
- **表现**: 大规模系统 SAT 求解超时
- **缓解**: 
  - 链路裁剪减小求解空间
  - 增量求解会话复用
  - 设置合理的超时时间
  - SAT 结果缓存

#### 风险2: 数据迁移复杂度
- **表现**: 现有项目数据库结构不一致
- **缓解**:
  - 提供完整的迁移脚本
  - 保留 Equipment.TModel 字段兼容性
  - 分阶段迁移，先新增后替换

#### 风险3: 代码侵入性
- **表现**: 修改现有代码可能引入 bug
- **缓解**:
  - 遵循"容器层优先、最小侵入"原则
  - 充分测试
  - 保留旧代码路径作为降级方案

#### 风险4: 学习曲线
- **表现**: 用户不熟悉新功能
- **缓解**:
  - 完善文档和使用指南
  - 提供演示项目
  - 渐进式替换旧界面

### 9.5 质量保证建议

1. **单元测试**
   - SmtSyntaxChecker
   - TModelValidator
   - ConnectSugarGenerator
   - SystemModelAssembler

2. **集成测试**
   - 元件插入 → 容器创建 → SMT 生成
   - 连线 → 连接语句生成 → 系统描述
   - 功能定义 → 边界识别 → 完整性检查
   - 功能定义 → D 矩阵构建 → 测试优选

3. **端到端测试**
   - 完整的演示项目流程
   - 覆盖电气、液压、机械系统

4. **性能测试**
   - 大规模系统（100+ 元件）的描述生成
   - 复杂系统（50+ 功能）的 D 矩阵构建
   - SAT 求解超时处理

### 9.6 文档需求

1. **用户文档**
   - 端口配置操作指南
   - T 语言模型编写规范
   - 功能管理使用手册
   - D 矩阵分析流程

2. **开发文档**
   - 系统架构说明
   - 数据库设计文档
   - 模块接口文档
   - 扩展开发指南

3. **迁移文档**
   - 数据库升级步骤
   - 现有项目迁移指南
   - 兼容性说明

## 十、附录

### 10.1 关键文件清单

#### 数据库
- templete/project.db: 项目模板数据库
- ref/LdMainData.db: 元件库数据库
- ref/Model.db: T-Solver 模型数据库

#### 业务对象层 (BO)
- BO/componententity.*: 元件实体
- BO/systementity.*: 系统实体
- BO/containerrepository.*: 容器仓库
- BO/container/containerdata.*: 容器数据
- BO/container/behavioraggregator.*: 行为聚合器
- BO/function/functionrepository.*: 功能仓库
- BO/function/SmtSyntaxChecker.*: SMT 语法检查器 ✅
- BO/function/tmodelvalidator.*: T 模型校验器 ✅
- BO/function/systemstructureservice.*: 系统结构服务 ⚠️
- BO/function/functionanalysisservice.*: 功能分析服务 ⚠️

#### 界面层 (widget / dialog*)
- widget/functionmanagerdialog.*: 功能管理对话框 ⚠️
- widget/dmatrixviewerdialog.*: D 矩阵查看器 ✅
- widget/portconfigeditdialog.*: 端口配置编辑对话框 ✅
- dialogUnitAttr.*: 元件属性对话框 ✅
- dialogsymbolattribute.*: 符号属性对话框（库） ❌
- dialogtestreport.*: 测试报告对话框 ⚠️

#### 测试性分析 (testability)
- testability/d_matrix_builder.*: D 矩阵构建器 ✅
- testability/smt_facade.*: SMT 门面 ✅
- testability/testability_types.h: 类型定义 ✅

#### 主窗口
- mainwindow.cpp: 主窗口
- mainwindow_project.cpp: 项目相关功能 ⚠️
- mainwindow_units.cpp: 元件相关功能 ⚠️
- mainwindow_diagnosis.cpp: 诊断相关功能 ⚠️

#### 工具脚本 (tools)
- （缺失）db_migrate_project.py: 数据库迁移脚本
- （缺失）validate_smt_snippets.py: SMT 批量校验
- （缺失）generate_demo_project.py: 演示项目生成

### 10.2 数据库表依赖关系

```
Equipment (传统)
  ├─ TModel (T 语言模型)
  ├─ TModelDiag (诊断模型)
  └─ 功能子块相关表

container (新)
  ├─ container_id (主键)
  ├─ equipment_containers (关联表)
  └─ container_hierarchy (层次)

component_smt (新)
  ├─ equipment_id (外键 → Equipment)
  ├─ container_id (外键 → container)
  └─ smt_text (SMT 模型)

system_smt (新)
  ├─ container_id (外键 → container)
  ├─ def_block (DEF 块)
  ├─ connect_block (CONNECT 块)
  └─ raw_block (RAW 块)

port_config (新)
  ├─ container_id (外键 → container)
  ├─ function_block (功能子块)
  ├─ port_name (端口名)
  ├─ port_type (端口类型)
  ├─ variables_json (变量集 JSON)
  └─ connect_macro (连接宏)

port_connect_macro_family (新)
  ├─ family_id (主键)
  ├─ family_name (宏族名)
  ├─ domain (领域：electric/hydraulic/mechanical)
  ├─ is_builtin (是否内置)
  └─ macros_json (宏定义 JSON)

function_definition (新)
  ├─ function_id (主键)
  ├─ container_id (外键 → container)
  ├─ parent_function_id (父功能)
  ├─ name (功能名)
  └─ ...

function_dependency (新)
  ├─ function_id (外键 → function_definition)
  └─ depends_on_function_id (外键 → function_definition)

function_io (新)
  ├─ function_id (外键 → function_definition)
  ├─ variable_name (变量名)
  ├─ io_type (输入/输出/执行器)
  └─ ...

dmatrix_meta (新)
  ├─ container_id (外键 → container)
  ├─ json_text (元数据 JSON)
  ├─ csv_path (CSV 路径)
  └─ ...
```

### 10.3 参考资料
- README.md: 总体目标和开发要求
- ToDoList.md: 详细任务分解
- ref/T-Solver/README.md: T-Solver 建模原理
- ref/T-Solver/widget/*: T-Solver 界面参考
- ref/T-Solver/BO/*: T-Solver 业务逻辑参考
- ref/T-Solver/testability/*: T-Solver D 矩阵参考

---

**报告完成日期**: 2025-11-26
**审查人**: AI Code Review Agent
**下次审查建议**: 完成第一阶段（ContainerBehaviorAdapter + SystemModelAssembler）后
