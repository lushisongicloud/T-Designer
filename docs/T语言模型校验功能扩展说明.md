# T语言模型校验功能扩展说明

## 概述

本次修改扩展了T语言模型的"校验"功能，将原有的端口一致性校验扩展为包含6项完整校验的综合检查系统。新校验功能在"本地物料库"和"元件属性"两处对话框中统一实现，完全复用代码逻辑。

## 修改范围

### 核心文件修改

1. **BO/function/tmodelvalidator.h** - 扩展校验器接口
   - 新增 `TModelValidationContext` 结构体，包含校验所需的上下文信息：
     - `componentName`: 器件名称
     - `constants`: 常量表（常量名 -> 值）
     - `faultModeProbabilities`: 故障模式概率表（故障模式名 -> 概率）
   - 扩展 `TModelValidationResult` 结构体，新增 `warnings` 字段
   - 更新 `validate()` 方法签名，增加可选的 `context` 参数

2. **BO/function/tmodelvalidator.cpp** - 实现6项校验逻辑
   - 引入 `tmodelparser.h` 以使用 `TModelParser::extractConstants()`
   - 实现器件名称占位符检查（校验1）
   - 实现常量定义检查（校验2）
   - 实现模型结构完整性检查（校验4）
   - 实现故障模式概率检查（校验5，作为warning）
   - 保留原有端口变量一致性检查（校验3）
   - SMT语法检查（校验6）由 `SmtSyntaxChecker` 处理（已存在）

3. **BO/function/tmodelcheckservice.h/.cpp** - 更新服务接口
   - 更新 `run()` 方法签名，增加可选的 `context` 参数
   - 扩展结果处理逻辑，区分错误(error)和警告(warning)
   - 更新摘要信息格式，显示错误和警告数量

4. **dialogunitmanage.cpp** - 本地物料库集成
   - 更新 `performTModelValidation()` 方法
   - 收集器件名称（从 `EdUnitCode`）
   - 收集常量表格数据（从 `tableWidgetStructure`）
   - 收集故障模式概率（从 `tableRepairInfo`）
   - 构建 `TModelValidationContext` 并传递给校验服务

5. **dialogUnitAttr.cpp** - 元件属性集成
   - 更新 `on_BtnValidateTModel_clicked()` 方法
   - 收集器件名称（从 `EdUnitTag`）
   - 收集常量表格数据（从 `tableWidgetStructure`）
   - 收集故障模式概率（从 `tableRepairInfo`）
   - 构建 `TModelValidationContext` 并传递给校验服务
   - **注意**：使用原始模型文本（`rawModelText`）而非替换后的文本进行校验

## 6项校验内容详解

### 1. 器件名称占位符检查
- **目的**：确保T语言模型使用通用占位符而非具体器件名
- **检查内容**：
  - 模型中应包含 `%Name%` 占位符
  - 不应直接使用具体器件名称（如 `KM1.Coil.A1.i`）
- **错误级别**：Error
- **示例错误**：
  - "T语言模型中应使用 %Name% 作为器件名称占位符"
  - "T语言模型中不应直接使用具体器件名称 \"KM1\"，请使用 %Name% 占位符"

### 2. 常量定义检查
- **目的**：确保所有使用的常量都在常量表格中有定义
- **检查内容**：
  - 提取T语言模型中所有 `%常量名%` 形式的占位符（排除 `%Name%`）
  - 验证每个常量是否在常量表格中存在
- **错误级别**：Error
- **示例错误**：
  - "常量 \"internalResistance\" 在T语言模型中使用但未在常量表格中定义"

### 3. 端口变量定义一致性检查（原有功能保留）
- **目的**：确保端口变量声明与端口配置信息一致
- **检查内容**：
  - 端口变量的类型（电气/液压/机械）
  - 变量名称（i/u、p/q、F+v|n|x）
  - 声明的完整性
- **错误级别**：Error/Warning
- **示例错误**：
  - "缺少声明: Coil.A1.i"
  - "未匹配的端口变量: %Name%.Unknown.port.x"

### 4. 模型结构完整性检查
- **目的**：确保T语言模型包含必需的结构部分
- **检查内容**：
  - 是否包含 `;;端口变量定义` 部分且不为空
  - 是否包含 `;;正常模式` 部分且不为空
  - 统计故障模式数量（仅作提示）
- **错误级别**：Warning
- **示例警告**：
  - "缺少 \";;端口变量定义\" 部分或该部分为空"
  - "缺少 \";;正常模式\" 部分或该部分为空"

### 5. 故障模式概率检查
- **目的**：提醒用户为故障模式定义概率
- **检查内容**：
  - 从T语言模型中提取所有故障模式名称
  - 验证每个故障模式是否在维修信息表格中有概率定义
- **错误级别**：Warning（非强制）
- **示例警告**：
  - "故障模式 \"broken\" 的概率未在维修信息表格中定义"

### 6. SMT语法检查
- **目的**：使用Z3验证SMT语法正确性
- **检查内容**：
  - 通过 `SmtSyntaxChecker` 调用Z3解析器
  - 捕获并格式化Z3返回的错误信息
  - 提供行号和列号定位
- **错误级别**：Error
- **示例错误**：
  - "line 15 column 3: unexpected token"

## 数据流程

### 本地物料库（dialogunitmanage）

```
用户点击"校验"按钮
  ↓
performTModelValidation()
  ↓
收集上下文数据：
  - 器件名称（EdUnitCode）
  - 常量表格（tableWidgetStructure）
  - 故障模式概率（tableRepairInfo）
  - 端口配置（port_config表）
  - 端口列表（tableTerm）
  ↓
构建TModelValidationContext
  ↓
调用 TModelCheckService::run(this, modelText, ports, context)
  ↓
SmtSyntaxChecker::check() - Z3语法校验
  ↓
TModelValidator::validate() - 综合校验
  ↓
CodeCheckDialog - 显示结果
```

### 元件属性（dialogUnitAttr）

```
用户点击"校验"按钮
  ↓
on_BtnValidateTModel_clicked()
  ↓
收集上下文数据：
  - 器件名称（EdUnitTag）
  - 常量表格（tableWidgetStructure）
  - 故障模式概率（tableRepairInfo）
  - 端口配置（port_config表）
  - 端口列表（tableTerm）
  ↓
构建TModelValidationContext
  ↓
调用 TModelCheckService::run(this, rawModelText, ports, context)
  （注意：使用原始模型文本，不是替换后的）
  ↓
SmtSyntaxChecker::check() - Z3语法校验
  ↓
TModelValidator::validate() - 综合校验
  ↓
CodeCheckDialog - 显示结果
```

## 关键设计决策

### 1. 使用上下文结构体
引入 `TModelValidationContext` 结构体作为可选参数，而非修改多个方法签名。这样做的好处：
- 向后兼容：不传context时使用默认值，原有调用代码无需修改
- 可扩展：未来添加新的校验项只需扩展context结构体
- 清晰：所有校验所需的数据集中在一个结构中

### 2. 区分Error和Warning
- **Error**：阻碍模型正常使用的问题，必须修复
  - 器件名称错误
  - 常量未定义
  - 端口变量不一致
  - SMT语法错误
- **Warning**：建议修复但不强制的问题
  - 缺少可选部分
  - 故障模式概率未定义

### 3. 校验顺序
1. 首先进行SMT语法校验，如果失败则立即返回（后续校验无意义）
2. 然后执行其他5项校验，收集所有错误和警告
3. 最后统一显示结果

### 4. 原始文本 vs 替换后文本
- **本地物料库**：直接使用原始模型文本
- **元件属性**：也使用原始模型文本（而非替换后的preparedModel）
- **原因**：校验的目的是检查模板的正确性，应检查占位符的使用是否规范

## 校验结果显示

### 摘要信息格式
- 无警告时：`共检查端号 X 个，错误 Y 条`
- 有警告时：`共检查端号 X 个，错误 Y 条，警告 Z 条`

### 结果列表
使用 `CodeCheckDialog` 显示，每条结果包含：
- **级别**：错误/警告/提示
- **位置**：行号:列号（如果适用）
- **信息**：具体的错误或警告描述

### 颜色编码
- **错误（Error）**：红色 (200, 45, 45)
- **警告（Warning）**：橙色 (200, 140, 35)
- **提示（Info）**：默认颜色

## 测试建议

### 测试场景1：器件名称检查
```smt
;; 错误：未使用%Name%占位符
(declare-fun KM1.Coil.A1.i () Real)

;; 正确：使用%Name%占位符
(declare-fun %Name%.Coil.A1.i () Real)
```

### 测试场景2：常量定义检查
```smt
;; 在常量表格中定义：Resistance = 2200

;; 错误：使用未定义的常量
(assert (= %Name%.value (* %UnknownConstant% %Name%.current)))

;; 正确：使用已定义的常量
(assert (= %Name%.value (* %Resistance% %Name%.current)))
```

### 测试场景3：模型结构检查
```smt
;; 完整结构示例
;;端口变量定义
(declare-fun %Name%.Coil.A1.i () Real)
(declare-fun %Name%.Coil.A1.u () Real)

;;内部变量定义
(declare-fun %Name%.internalResistance () Real)

;;正常模式
(assert (= %Name%.Coil.A1.u (* %Name%.internalResistance %Name%.Coil.A1.i)))

;;故障模式
;;公共开始
(assert (= 0 %Name%.Coil.A1.i))
;;故障模式名broken
(assert (= 0 %Name%.Coil.A1.u))
```

### 测试场景4：故障模式概率检查
在维修信息表格中：
| 故障模式 | 概率 | 维修方案 | 资源 |
|---------|------|---------|------|
| broken  | 0.01 | 更换     | 备件 |

T语言模型中：
```smt
;;故障模式名broken
;; 正确：在维修信息中有定义

;;故障模式名not_defined_fault
;; 警告：在维修信息中未定义
```

### 测试场景5：端口变量一致性
端口配置中为 `Coil.A1` 设置：
- 类型：electric
- 变量：i, u

T语言模型中：
```smt
;; 正确
(declare-fun %Name%.Coil.A1.i () Real)
(declare-fun %Name%.Coil.A1.u () Real)

;; 错误：缺少u的声明
(declare-fun %Name%.Coil.A1.i () Real)

;; 错误：使用了未配置的变量
(declare-fun %Name%.Coil.A1.p () Real)
```

## 向后兼容性

### API兼容性
- `TModelValidator::validate()` 保持向后兼容：context参数有默认值
- `TModelCheckService::run()` 保持向后兼容：context参数有默认值
- 现有调用代码如果不传context，校验功能会降级为只执行端口一致性检查

### 行为变化
- 原有的端口一致性校验逻辑完全保留
- 新增的校验项只在提供context时才执行
- 校验结果的显示格式略有变化（增加了警告计数）

## 后续改进建议

1. **行号定位增强**
   - 为常量检查、器件名称检查提供行号定位
   - 需要在TModelParser中记录每个占位符的位置信息

2. **批量修复建议**
   - 提供"自动修复"功能，一键修复常见错误
   - 例如：自动将具体器件名替换为%Name%占位符

3. **校验规则配置**
   - 允许用户选择启用/禁用特定校验项
   - 允许配置警告级别（error/warning/info）

4. **离线批量校验**
   - 提供Python脚本批量校验多个元件的T语言模型
   - 生成HTML格式的校验报告

5. **智能提示**
   - 在编辑T语言模型时实时提示错误
   - 集成到QsciScintilla编辑器的错误标记功能

## 总结

本次修改成功将T语言模型的校验功能从单一的端口一致性检查扩展为包含6项检查的综合校验系统：

✅ 1. 器件名称占位符检查
✅ 2. 常量定义检查  
✅ 3. 端口变量一致性检查（原有功能）
✅ 4. 模型结构完整性检查
✅ 5. 故障模式概率检查
✅ 6. SMT语法检查（SmtSyntaxChecker）

核心特点：
- **统一实现**：本地物料库和元件属性完全复用代码
- **清晰分级**：区分Error和Warning，合理引导用户修复
- **向后兼容**：现有代码无需修改，新功能通过可选参数启用
- **易于扩展**：通过TModelValidationContext可轻松添加新的校验项

代码已准备就绪，可以进行编译和测试。
