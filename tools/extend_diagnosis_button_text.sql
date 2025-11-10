-- ============================================================================
-- 诊断系统按钮文本字段扩展脚本
-- ============================================================================
-- 功能：为 diagnosis_tree_node 表添加自定义按钮文本字段
-- 日期：2025-11-10
-- 说明：支持动态设置测试结果按钮的文本，提升用户体验
-- ============================================================================

-- 为 diagnosis_tree_node 表添加按钮文本字段
ALTER TABLE diagnosis_tree_node ADD COLUMN pass_button_text TEXT DEFAULT '是';
ALTER TABLE diagnosis_tree_node ADD COLUMN fail_button_text TEXT DEFAULT '否';

-- 验证新字段
.print "verification check: pass_button_text and fail_button_text columns added"
PRAGMA table_info(diagnosis_tree_node);

-- 使用示例说明
.print ""
.print "================================================================"
.print "字段说明："
.print "- pass_button_text: 测试通过按钮的文本（如：'正常'、'亮'、'>18V'、'导通'）"
.print "- fail_button_text: 测试失败按钮的文本（如：'异常'、'不亮'、'<18V'、'不导通'）"
.print ""
.print "更新现有数据示例："
.print "UPDATE diagnosis_tree_node SET pass_button_text='电压正常', fail_button_text='电压异常' WHERE node_id=2;"
.print "UPDATE diagnosis_tree_node SET pass_button_text='指示正常', fail_button_text='指示异常' WHERE node_id=5;"
.print "================================================================"
