# T-Designer 脚本归档目录

## 归档说明

本次归档共移动了 **61个脚本文件** 到archive目录，并根据功能和使用状态添加了分类前缀：

- **已完成**：记录已完成的工作、实现了特定功能或作为有用工具保留的脚本
- **已过时**：记录具体的调试过程、一次性修复或临时性问题解决方案的脚本

## 归档统计

### 按分类统计

- **已完成类脚本**: 30个
- **已过时类脚本**: 31个
- **总计**: 61个脚本文件

### 按来源统计

- 根目录：11个脚本（10个Python + 1个bat）
- tools目录：49个脚本（Python）
- ref目录：1个脚本（Python）
- tests目录：1个脚本（shell）

## 归档文件清单

### 已完成类脚本（30个）

**数据库工具**：
- `已完成-add_missing_indexes.py` - 为数据库添加缺失索引
- `已完成-check_diagnosis_db.py` - 检查诊断数据库完整性
- `已完成-update_template_db.py` - 更新项目模板数据库
- `已完成-init_builtin_macro_families.py` - 初始化内置连接宏族

**代码工具**：
- `已完成-fix_encoding_newlines.py` - 修复代码文件编码和换行格式
- `已完成-test_performance.bat` - 性能测试脚本

**数据生成与迁移**：
- `已完成-migrate_diagnosis_data.py` - 故障诊断数据迁移脚本
- `已完成-create_diagnosis_tables.py` - 创建诊断表结构
- `已完成-extend_diagnosis_system.py` - 扩展诊断系统
- `已完成-db_migrate_project.py` - 项目数据库迁移
- `已完成-clean_ldmaindata_chars.py` - 清理LdMainData字符

**诊断功能生成**：
- `已完成-generate_10_diagnosis_functions.py` - 生成10个液压系统诊断功能
- `已完成-generate_improved_diagnosis_functions.py` - 生成改进的诊断功能
- `已完成-generate_winch_diagnosis_complete.py` - 生成完整绞车诊断功能
- `已完成-generate_winch_diagnosis_functions.py` - 生成绞车诊断功能
- `已完成-generate_winch_diagnosis_functions_fixed.py` - 生成修复版绞车诊断功能
- `已完成-setup_oil_power_system_diagnosis.py` - 设置液压动力系统诊断
- `已完成-expand_diagnosis_trees_14to16.py` - 扩展功能14-16诊断树
- `已完成-expand_diagnosis_trees_6to16.py` - 扩展功能6-16诊断树
- `已完成-expand_diagnosis_trees_9to13.py` - 扩展功能9-13诊断树
- `已完成-adjust_fault_14to16.py` - 调整功能14-16故障分布
- `已完成-adjust_fault_distribution_9to13.py` - 调整功能9-13故障分布
- `已完成-adjust_test_costs.py` - 调整测试成本
- `已完成-final_adjust.py` - 最终调整
- `已完成-final_adjust_16.py` - 最终调整（功能16）

**项目数据初始化**：
- `已完成-seed_curated_project.py` - 初始化精选项目
- `已完成-seed_curated_project-3000.py` - 初始化精选项目（3000版本）
- `已完成-seed_dual_winch_project.py` - 初始化双绞车项目

**T-Solver工具**：
- `已完成-dump_function_xml.py` - 导出function XML（从ref/T-Solver/scripts/）
- `已完成-target_wrapper.sh` - 测试包装脚本（从tests/）

### 已过时类脚本（31个）

**临时调试脚本**：
- `已过时-check_db.py` - 检查port_config表结构
- `已过时-check_container_id1.py` - 检查container_id=1
- `已过时-find_system_container.py` - 查找系统级容器
- `已过时-compare_container_id1.py` - 比较两个数据库的container_id
- `已过时-check_macro_table.py` - 检查port_connect_macro表
- `已过时-fix_column_numbers.py` - 修复dialogUnitAttr.cpp中的列号
- `已过时-test_sql.py` - 测试SQL语句占位符

**数据库验证脚本**：
- `已过时-check_all_branch_nesting.py` - 检查所有分支嵌套
- `已过时-check_diagnosis_integrity.py` - 检查诊断完整性
- `已过时-check_diagnosis_schema.py` - 检查诊断schema
- `已过时-check_node_499_issue.py` - 检查节点499问题
- `已过时-check_nodes_499_502.py` - 检查节点499-502
- `已过时-check_tables.py` - 检查数据库表
- `已过时-check_tree7.py` - 检查树7

**验证脚本**：
- `已过时-verify_branch_nesting_fix.py` - 验证分支嵌套修复
- `已过时-verify_diagnosis_trees.py` - 验证诊断树
- `已过时-verify_tree_9_detailed.py` - 验证树9详细信息
- `已过时-verify_trees_14to16_quality.py` - 验证树14-16质量
- `已过时-verify_trees_9to13_quality.py` - 验证树9-13质量

**调试和测试脚本**：
- `已过时-debug_split_logic.py` - 调试分割逻辑
- `已过时-test_diagnosis_tree_loading.py` - 测试诊断树加载
- `已过时-test_diagnosis_ui.py` - 测试诊断UI
- `已过时-test_json_format.py` - 测试JSON格式
- `已过时-test_new_format.py` - 测试新格式
- `已过时-test_new_parse.py` - 测试新解析
- `已过时-test_qstring_format.py` - 测试QString格式
- `已过时-test_repairinfo_format.py` - 测试维修信息格式

**修复脚本**：
- `已过时-fix_node_format.py` - 修复节点格式
- `已过时-fix_node_format2.py` - 修复节点格式2
- `已过时-fix_partcode_prefix.py` - 修复部件代码前缀

**其他**：
- `已过时-show_equipment_schema.py` - 显示设备schema
- `已过时-deepseek_tmodel_rewriter.py` - DeepSeek TModel重写器

## 归档依据

### 已完成类脚本

这些脚本记录了：
1. **有用的工具**：如代码格式化、性能测试、数据库检查等工具脚本
2. **一次性数据生成**：为特定项目或功能生成诊断数据的脚本
3. **数据库初始化**：初始化内置数据或迁移数据的脚本
4. **功能实现**：实现了特定系统功能的脚本

这些脚本对理解系统或未来类似工作可能有参考价值。

### 已过时类脚本

这些脚本记录了：
1. **临时调试过程**：为定位特定问题而编写的调试脚本
2. **一次性修复**：针对特定问题的一次性修复脚本
3. **数据验证**：验证特定数据正确性的临时脚本
4. **问题定位**：用于分析特定问题的诊断脚本

这些脚本已完成其历史使命，作为问题解决过程记录保留。

## 数据库结构分析

通过分析 `./ref/LdMainData.db` 和 `./templete/project.db` 两个数据库，我们了解到：

**LdMainData.db（模板库）**：
- 主要包含 EquipmentTemplate、container、port_config 等模板数据
- 用于定义标准和可重用的组件模板

**project.db（项目数据库）**：
- 包含完整的项目数据：Equipment、Symbol、JXB（连线）等
- 诊断系统相关表：diagnosis_tree、diagnosis_tree_node、test_definition 等
- 端口配置：port_config、port_connect_macro_family（连接宏族）
- 系统建模：models、parameters、system_smt 等

这些脚本大部分都是为了支持这些数据结构的初始化、验证、迁移和调试工作。

## 后续建议

1. **保留已完成类脚本**：这些脚本在类似项目或功能开发时可能有参考价值
2. **可清理已过时类脚本**：如果确认不再需要，可考虑删除以节省空间
3. **参考而非依赖**：这些脚本仅作历史参考，当前开发应以最新代码和文档为准

## 创建时间

2025年11月27日

