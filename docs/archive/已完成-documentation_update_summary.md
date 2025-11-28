**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# 文档更新总结 - 连接宏族概念

## 更新日期
2025年10月30日

## 更新背景

在本次对话中，我们确定了**连接宏族（Connection Macro Family）**的概念：一个宏族包含支持不同端口数量（arity）的多个连接宏（如electric-connect包含connect2e、connect3e、connect4e），系统根据连接点的实际端口数量自动选择合适的宏。这一设计解决了单一连接宏无法适应多样化连接场景的问题。

为确保所有开发人员基于统一的概念进行后续开发，本次更新将连接宏族概念系统性地融入到所有相关文档中。

## 更新的文档清单

### 1. 根目录文档

#### README.md
**更新位置**: 实现要点第2条和第5条

**主要变更**:
- 将"可以仿照T-Solver中使用连接函数connect2e、connect3e..."改为"系统采用连接宏族概念"
- 详细说明三个内置宏族（electric-connect、hydraulic-connect、mechanical-connect）
- 强调系统自动根据连接点端口数选择合适的宏
- 更新端口配置说明，包括宏族选择和管理功能
- 说明数据存储在port_config和port_connect_macro_family两个表中

**关键内容**:
```markdown
系统采用**连接宏族（Connection Macro Family）**概念：一个宏族包含支持不同端口数量的多个连接宏，系统根据连接点的实际端口数量自动选择合适的宏。内置三个宏族：
- **electric-connect**（电气连接宏族）：包含 connect2e（2端口连接）、connect3e（3端口连接）、connect4e（4端口连接）等
- **hydraulic-connect**（液压连接宏族）：包含 connect2h、connect3h、connect4h等
- **mechanical-connect**（机械连接宏族）：包含 connect2m、connect3m、connect4m等
```

#### AGENTS.md
**更新位置**: 
- 新增"Connection Macro Family Concept"章节
- 更新"Port/Variable Naming Rules"章节
- 更新"Cad → SMT Connection Sugar"章节
- 更新"Development Sprint Goals"章节

**主要变更**:
- 新增完整的宏族概念说明章节，包括宏族定义、内置宏族、自定义宏族、数据结构、自动选择逻辑
- 说明宏族数据存储在port_connect_macro_family表
- 强调宏的展开式存储在macros_json字段
- 更新开发目标，从"使用connect2e/3e"改为"使用连接宏族，系统自动选择合适的宏"

**关键内容**:
```markdown
## Connection Macro Family Concept
- **Macro Family（宏族）**: 一组支持不同端口数量（arity）的连接宏，系统根据连接点的实际端口数自动选择合适的宏。
- **内置宏族**（存储在 port_connect_macro_family 表，is_builtin=1）：
  - `electric-connect`: 包含 connect2e/3e/4e 等，生成电流守恒（Σi=0）+ 电压等势（u相等）约束
  ...
- **自动选择逻辑**: 在生成系统连接约束时，根据连接点的端口数量从配置的宏族中选择对应arity的宏并展开为SMT约束。
```

#### ToDoList.md
**更新位置**: Phase 2和Phase 4任务说明

**主要变更**:
- Phase 2增加连接宏族支持说明：
  - 数据库表结构（port_connect_macro_family）
  - 内置宏族列表
  - 宏族管理功能（添加/删除）
  - 自动选择逻辑
- Phase 4重写为基于宏族的实现：
  - 实现连接宏族管理
  - 根据连接点端口数自动选择宏
  - 宏族的macros_json格式说明

**关键内容**:
```markdown
- **连接宏族支持**：
  - 数据库表：port_connect_macro_family（family_name, domain, description, is_builtin, macros_json）
  - 内置宏族：electric-connect（包含connect2e/3e/4e）、hydraulic-connect、mechanical-connect
  - 端口配置时选择宏族名称，系统在生成连接时根据端口数自动选择对应宏
```

### 2. 子目录AGENTS.md文档

#### widget/AGENTS.md
**更新位置**: "本周期重点"章节中的"功能子块 → 端口配置"部分

**主要变更**:
- 完整描述宏族管理界面功能
- 说明宏族的查看、添加、删除操作
- 强调内置宏族不可删除
- 详细说明宏族概念和自动选择逻辑
- 说明数据存储在两个表中

**关键内容**:
```markdown
- 管理连接宏族（添加自定义宏族、删除自定义宏族，内置宏族不可删除）
- 宏族概念：
  - 宏族是一组支持不同端口数量的连接宏集合
  - 系统根据连接点的实际端口数量自动选择合适的宏
  - 内置宏族（is_builtin=1）包括：electric-connect、hydraulic-connect、mechanical-connect
  - 用户可创建自定义宏族支持特殊连接语义
```

#### BO/AGENTS.md
**更新位置**: "本周期重点"章节中的"端口/变量体系与连接语法糖"部分

**主要变更**:
- 将标题从"连接语法糖"改为"连接宏族"
- 详细说明宏族概念和结构
- 说明宏族的数据存储格式（macros_json）
- 强调根据arity自动选择宏的逻辑
- 说明连接生成器的工作原理

**关键内容**:
```markdown
- **连接宏族概念**：一个宏族包含支持不同端口数量的多个连接宏，系统根据连接点的实际端口数自动选择合适的宏：
  - electric-connect宏族：包含connect2e（2端口）、connect3e（3端口）、connect4e（4端口）等
  ...
- 宏族的macros_json字段存储多个宏定义：`[{arity:2, macro_name:"connect2e", expansion:"..."}, ...]`
- 提供连接生成器：...根据连接点上的端口数量从配置的宏族中自动选择对应arity的宏...
```

#### tools/AGENTS.md
**更新位置**: "现有脚本"章节

**主要变更**:
- 新增init_builtin_macro_families.py脚本说明
- 详细描述脚本目的、输入输出、宏族结构、使用场景

**关键内容**:
```markdown
- `init_builtin_macro_families.py`：初始化内置连接宏族到项目数据库
  - 目的：创建port_connect_macro_family表并插入三个内置宏族
  - 宏族结构：family_name, domain, description, is_builtin, macros_json, created_at
  - 使用场景：新建项目时确保宏族表已初始化、升级现有项目数据库、修复或重置内置宏族定义
```

### 3. 新增专题文档

#### docs/connection_macro_family_concept.md
**文档类型**: 新建

**内容概要**:
这是一份完整的连接宏族概念说明文档，包括：

1. **概述与设计动机**: 解释为什么需要宏族概念
2. **宏族结构**: 数据库表设计、字段说明、JSON格式
3. **内置宏族**: 详细说明三个内置宏族及其展开规则
4. **使用流程**: 端口配置阶段、连接生成阶段、宏族管理
5. **自定义宏族**: 使用场景、创建步骤、示例
6. **实现文件**: 列出相关的代码文件和职责
7. **技术要点**: 宏族选择算法、宏展开算法、多相数组支持
8. **优势与扩展性**: 设计优势和未来扩展方向
9. **参考文档**: 相关文档链接

**文档价值**:
- 为后续开发提供完整的概念参考
- 为添加自定义宏族功能提供设计指导
- 为实现ConnectSugarGenerator提供算法参考

## 更新一致性保证

所有文档更新保持以下一致性：

1. **术语统一**: 
   - 使用"连接宏族"而非"连接宏"或"连接函数"
   - 使用"arity"表示端口数量
   - 使用"宏展开"表示宏到SMT约束的转换

2. **概念一致**:
   - 宏族包含多个不同arity的宏
   - 系统自动根据连接点端口数选择宏
   - 内置宏族不可删除，自定义宏族可删除

3. **数据结构一致**:
   - port_connect_macro_family表存储宏族
   - macros_json字段存储宏定义数组
   - 每个宏定义包含arity、macro_name、expansion

4. **三个内置宏族**:
   - electric-connect (电气)
   - hydraulic-connect (液压)
   - mechanical-connect (机械)

## 后续开发建议

基于更新后的文档，后续开发应：

1. **实现"添加宏族"完整功能**
   - 创建AddMacroFamilyDialog对话框
   - 支持用户定义宏族名称、领域、多个arity的宏定义
   - 参考docs/connection_macro_family_concept.md中的"自定义宏族"章节

2. **实现ConnectSugarGenerator**
   - 位置：BO/behavior/ConnectSugarGenerator.{h,cpp}
   - 功能：根据连接点信息和端口配置生成SMT约束
   - 参考docs/connection_macro_family_concept.md中的"技术要点"章节

3. **测试宏族功能**
   - 测试内置宏族的正确性
   - 测试添加/删除自定义宏族
   - 测试不同arity的自动选择逻辑
   - 测试宏展开的正确性

4. **完善文档**
   - 在docs/port_variable_rules.md中补充宏族展开规则
   - 更新用户手册说明宏族的使用方法
   - 添加宏族管理的操作截图

## 检查清单

- [x] README.md更新完成
- [x] AGENTS.md更新完成
- [x] ToDoList.md更新完成
- [x] widget/AGENTS.md更新完成
- [x] BO/AGENTS.md更新完成
- [x] tools/AGENTS.md更新完成
- [x] 创建connection_macro_family_concept.md专题文档
- [x] 所有文档术语和概念保持一致
- [x] 提供后续开发建议

## 总结

通过本次系统性的文档更新，连接宏族概念已成为T-Designer项目的核心设计之一。所有相关文档都已更新以反映这一概念，为后续开发提供了统一的指导。开发人员可以基于这些文档进行：

- 端口配置UI的完善（添加宏族功能）
- 连接生成器的实现（ConnectSugarGenerator）
- 宏族管理功能的扩展（导入/导出、版本管理等）
- 测试用例的编写

所有更新遵循"先文档、后代码"的原则，确保设计清晰、实现有据可依。
