-- 故障诊断系统数据库扩展脚本
-- 日期: 2025-11-10
-- 目的: 扩展diagnosis_tree和diagnosis_tree_node表以支持自包含的诊断引擎

-- ======================================
-- 1. 扩展 diagnosis_tree 表
-- ======================================

-- 添加功能ID关联
ALTER TABLE diagnosis_tree ADD COLUMN function_id INTEGER;

-- 添加根节点ID引用
ALTER TABLE diagnosis_tree ADD COLUMN root_node_id INTEGER;

-- 添加创建时间
ALTER TABLE diagnosis_tree ADD COLUMN created_time TEXT DEFAULT CURRENT_TIMESTAMP;

-- 添加是否自动生成标志
ALTER TABLE diagnosis_tree ADD COLUMN auto_generated INTEGER DEFAULT 1;

-- ======================================
-- 2. 扩展 diagnosis_tree_node 表
-- ======================================

-- 添加节点类型 ('test', 'fault', 'branch')
ALTER TABLE diagnosis_tree_node ADD COLUMN node_type TEXT DEFAULT 'test';

-- 添加测试描述
ALTER TABLE diagnosis_tree_node ADD COLUMN test_description TEXT;

-- 添加期望结果描述
ALTER TABLE diagnosis_tree_node ADD COLUMN expected_result TEXT;

-- 添加故障假设描述
ALTER TABLE diagnosis_tree_node ADD COLUMN fault_hypothesis TEXT;

-- 添加隔离级别 (0=未隔离, 1=部分隔离, 2=完全隔离)
ALTER TABLE diagnosis_tree_node ADD COLUMN isolation_level INTEGER DEFAULT 0;

-- 添加测试优先级 (0.0-1.0)
ALTER TABLE diagnosis_tree_node ADD COLUMN test_priority REAL DEFAULT 0.5;

-- ======================================
-- 3. 创建索引以提升性能
-- ======================================

-- 为diagnosis_tree创建索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_function_id 
    ON diagnosis_tree(function_id);

CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_container_id 
    ON diagnosis_tree(container_id);

-- 为diagnosis_tree_node创建索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_tree_id 
    ON diagnosis_tree_node(tree_id);

CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_parent_id 
    ON diagnosis_tree_node(parent_node_id);

CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_type 
    ON diagnosis_tree_node(node_type);

-- ======================================
-- 4. 创建视图便于查询
-- ======================================

-- 创建诊断树完整信息视图
CREATE VIEW IF NOT EXISTS v_diagnosis_tree_full AS
SELECT 
    dt.tree_id,
    dt.container_id,
    dt.function_id,
    dt.name AS tree_name,
    dt.description AS tree_description,
    dt.root_node_id,
    dt.created_time,
    dt.auto_generated,
    fd.name AS function_name,
    fd.description AS function_description,
    c.name AS container_name
FROM diagnosis_tree dt
LEFT JOIN function_definition fd ON dt.function_id = fd.function_id
LEFT JOIN container c ON dt.container_id = c.container_id;

-- 创建诊断节点完整信息视图
CREATE VIEW IF NOT EXISTS v_diagnosis_node_full AS
SELECT 
    dtn.node_id,
    dtn.tree_id,
    dtn.parent_node_id,
    dtn.test_id,
    dtn.state_id,
    dtn.node_type,
    dtn.outcome,
    dtn.comment,
    dtn.test_description,
    dtn.expected_result,
    dtn.fault_hypothesis,
    dtn.isolation_level,
    dtn.test_priority,
    td.name AS test_name,
    td.description AS test_detail_description,
    cs.name AS state_name,
    cs.state_type
FROM diagnosis_tree_node dtn
LEFT JOIN test_definition td ON dtn.test_id = td.test_id
LEFT JOIN container_state cs ON dtn.state_id = cs.state_id;

-- ======================================
-- 5. 验证脚本
-- ======================================

-- 检查diagnosis_tree表结构
SELECT 'diagnosis_tree表结构验证:' AS verification;
PRAGMA table_info(diagnosis_tree);

-- 检查diagnosis_tree_node表结构
SELECT 'diagnosis_tree_node表结构验证:' AS verification;
PRAGMA table_info(diagnosis_tree_node);

-- 检查索引
SELECT 'diagnosis_tree索引验证:' AS verification;
SELECT name FROM sqlite_master 
WHERE type='index' AND tbl_name='diagnosis_tree';

SELECT 'diagnosis_tree_node索引验证:' AS verification;
SELECT name FROM sqlite_master 
WHERE type='index' AND tbl_name='diagnosis_tree_node';
