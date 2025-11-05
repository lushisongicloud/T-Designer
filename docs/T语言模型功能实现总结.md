# T语言模型功能实现总结

## 实现内容

本次开发完成了T语言模型在T-Designer中的集成，主要包括：

### 1. 核心类创建

#### TModelParser (BO/function/tmodelparser.h/.cpp)
- 解析T语言模型文本，识别特殊注释行标记：
  - `;;端口变量定义`
  - `;;内部变量定义`
  - `;;正常模式`
  - `;;故障模式`
  - `;;公共开始` / `;;公共结束`
  - `;;"故障模式名"`
- 支持多组公共块
- 提供compile方法展开占位符（%Name%、%常量%）

#### TModelCompileDisplayDialog (widget/tmodelcompiledisplaydialog.h/.cpp)
- 显示编译后的完整SMT描述
- 4个标签页分别显示：
  1. 端口变量定义
  2. 内部变量定义
  3. 正常模式
  4. 故障模式（每个故障模式一个子标签页）

### 2. 界面改造

#### tableWidgetStructure表格
- **原功能**：显示编译后的enum变量（Livingstone遗留）
- **新功能**：常量管理表
  - 4列：常量名、值、单位、备注
  - 列宽：前3列100px，最后一列自适应
  - 选择模式：按行选择，支持多选（ExtendedSelection）
  - 可双击编辑所有单元格

#### 右键菜单
- **常量名列**：插入常量名到T语言模型（自动添加%%）
- **其他位置**：
  - 新增：添加空行
  - 删除：支持批量删除，多于1个时二次确认

### 3. 编译功能

#### "编译"按钮行为
1. 使用TModelParser解析T语言模型
2. 收集tableWidgetStructure中的常量映射
3. 替换%Name%为实际器件代号
4. 替换%常量%为实际值
5. 展开故障模式公共约束
6. 弹出TModelCompileDisplayDialog显示结果

### 4. 数据持久化

#### 存储方案
- **表**：Equipment表（本地物料库用T_LibDatabase，项目用T_ProjectDatabase）
- **字段**：Structure字段（复用现有字段）
- **格式**：`常量名1,值1,单位1,备注1;常量名2,值2,单位2,备注2;...`

#### 加载/保存逻辑
- `loadConstants(QString)`: 从Structure字段加载常量到表格
- `saveConstants()`: 从表格保存常量到Structure字段
- 在on_tableWidgetUnit_clicked（dialogunitmanage）和UpdateUIInfo（dialogUnitAttr）中调用loadConstants
- 在on_BtnApply_clicked（dialogunitmanage）和on_BtnOk_clicked（dialogUnitAttr）中调用saveConstants

### 5. 两处界面集成

#### 本地物料库（dialogunitmanage）
- 窗口标题："数据库管理"
- 入口：主界面导航栏 → 数据管理 → 本地物料库
- 数据库：T_LibDatabase
- 完整功能：✓

#### 元件属性（dialogUnitAttr）
- 窗口标题："元件属性"
- 入口：项目导航器 → 元件tab → 右键菜单 → 元件属性
- 数据库：T_ProjectDatabase
- 完整功能：✓

### 6. 代码复用

两处界面共享以下实现：
- TModelParser类（解析逻辑）
- TModelCompileDisplayDialog类（显示逻辑）
- loadConstants/saveConstants/validateConstantName方法（几乎完全一致）
- showConstantsContextMenu/onAddConstant/onDeleteConstants/onInsertConstantName槽函数（完全一致）

## T语言模型示例

```smt
;;端口变量定义
(declare-fun %Name%.Cmd.A1.i () Real) 
(declare-fun %Name%.Cmd.A1.u () Real)
(declare-fun %Name%.H.p () Real) 
(declare-fun %Name%.H.q () Real)

;;内部变量定义
(declare-fun %Name%.internalResistance () Real)
(declare-fun %Name%.flowGain () Real)

;;正常模式
(assert (= %Name%.flowGain %常量1%))
(assert (= %Name%.internalResistance %常量2%))

;;故障模式
;;公共开始
(assert (= 0 (+ %Name%.Cmd.A1.i %Name%.Cmd.A2.i)))
;;"故障模式名a"
(assert (= 10 (* %Name%.Cmd.A1.i %Name%.Cmd.A1.u)))
;;"故障模式名b"
(assert (= %常量3% (* %Name%.Cmd.A1.i %Name%.Cmd.A1.u)))
;;公共结束
```

## 测试要点

### 功能测试
1. **常量管理**
   - [ ] 添加常量（右键菜单"新增"）
   - [ ] 编辑常量（双击单元格）
   - [ ] 删除常量（右键菜单"删除"，验证批量删除二次确认）
   - [ ] 插入常量名到编辑器（右键常量名列）

2. **T语言模型编译**
   - [ ] 解析包含端口变量、内部变量、正常模式、故障模式的模型
   - [ ] 正确替换%Name%占位符
   - [ ] 正确替换%常量%占位符
   - [ ] 正确展开公共约束到各故障模式
   - [ ] 编译结果对话框显示4部分内容

3. **数据持久化**
   - [ ] 保存常量到数据库（点击"应用"或"确定"）
   - [ ] 从数据库加载常量（选择器件/元件）
   - [ ] 验证常量格式正确（逗号、分号分隔）

4. **两处界面一致性**
   - [ ] 本地物料库和元件属性界面布局一致
   - [ ] 功能行为完全一致
   - [ ] 数据格式兼容

### 边界测试
- [ ] 空常量名处理（保存时跳过）
- [ ] 特殊字符处理（逗号、分号、百分号）
- [ ] 大量常量性能（100+行）
- [ ] T语言模型解析错误处理
- [ ] 常量未定义时的编译行为

## 修改的文件清单

### 新增文件
- `BO/function/tmodelparser.h`
- `BO/function/tmodelparser.cpp`
- `widget/tmodelcompiledisplaydialog.h`
- `widget/tmodelcompiledisplaydialog.cpp`

### 修改文件
- `T_DESIGNER.pro` - 添加新文件到构建系统
- `dialogunitmanage.h` - 添加常量管理相关方法声明
- `dialogunitmanage.cpp` - 实现常量管理、编译功能
- `dialogUnitAttr.h` - 添加常量管理相关方法声明
- `dialogUnitAttr.cpp` - 实现常量管理、编译功能

## 下一步工作

1. **编译项目**：验证代码无语法错误
2. **功能测试**：按上述测试要点逐项验证
3. **Bug修复**：根据测试结果修复问题
4. **用户验收**：提供测试版本给用户试用

## 注意事项

1. **数据库字段复用**：Structure字段原本用于存储Livingstone的enum变量，现改为存储常量信息。如果有旧数据，需要手动清理或迁移。

2. **T语言模型校验**：当前实现的是编译展开功能，尚未集成SMT语法校验和端口一致性校验（这部分由TModelValidator和TModelCheckService负责，可后续集成）。

3. **常量引用检查**：编译时不会检查T语言模型中引用的常量是否都已定义，未定义的常量会保持`%常量名%`格式。

4. **公共块作用域**：公共块会累积拼接到后续所有故障模式，直到遇到"公共结束"标记。如果没有"公共结束"，则作用到文件末尾。

5. **多故障模式命名**：故障模式名通过`;;"名称"`标记，名称中的引号必须是英文双引号。
