-- 诊断系统数据库扩展脚本
-- 用途：支持回退、跳过测试、测试推荐等高级功能

-- ==============================================
-- 1. 扩展 diagnosis_tree_node 表
-- ==============================================
-- 注意：SQLite的ALTER TABLE ADD COLUMN不支持所有约束，需要分别执行

-- 检查是否已有这些列，避免重复添加
-- 添加跳过计数
-- ALTER TABLE diagnosis_tree_node ADD COLUMN skip_count INTEGER DEFAULT 0;

-- 添加跳过原因  
-- ALTER TABLE diagnosis_tree_node ADD COLUMN skip_reason TEXT;

-- 添加替代测试列表（JSON数组，存储node_id）
-- ALTER TABLE diagnosis_tree_node ADD COLUMN alternative_tests TEXT;

-- 添加成本估算
-- ALTER TABLE diagnosis_tree_node ADD COLUMN cost_estimate REAL DEFAULT 0.0;

-- 添加时间估算（分钟）
-- ALTER TABLE diagnosis_tree_node ADD COLUMN duration_estimate REAL DEFAULT 0.0;

-- 添加检测故障列表（JSON数组，存储故障描述）
-- ALTER TABLE diagnosis_tree_node ADD COLUMN detectable_faults TEXT;

-- 添加隔离故障列表（JSON数组，存储故障描述）
-- ALTER TABLE diagnosis_tree_node ADD COLUMN isolatable_faults TEXT;

-- 由于SQLite限制，使用Python脚本动态检查并添加列

-- ==============================================
-- 2. 创建 diagnosis_session 表（诊断会话记录）
-- ==============================================

CREATE TABLE IF NOT EXISTS diagnosis_session (
    session_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    function_id INTEGER,
    start_time TEXT NOT NULL,
    end_time TEXT,
    session_state TEXT NOT NULL CHECK(session_state IN ('NotStarted', 'InProgress', 'Completed', 'Failed', 'Cancelled')),
    fault_node_id INTEGER,
    total_steps INTEGER DEFAULT 0,
    total_duration REAL DEFAULT 0.0,  -- 总耗时（分钟）
    user_id TEXT,
    session_notes TEXT,  -- 会话备注
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
    FOREIGN KEY (fault_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE SET NULL
);

-- 创建索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_session_tree_id ON diagnosis_session(tree_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_session_state ON diagnosis_session(session_state);
CREATE INDEX IF NOT EXISTS idx_diagnosis_session_start_time ON diagnosis_session(start_time);

-- ==============================================
-- 3. 创建 diagnosis_step_history 表（诊断步骤历史）
-- ==============================================

CREATE TABLE IF NOT EXISTS diagnosis_step_history (
    step_id INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id INTEGER NOT NULL,
    step_number INTEGER NOT NULL,
    node_id INTEGER NOT NULL,
    test_outcome TEXT NOT NULL CHECK(test_outcome IN ('Unknown', 'Pass', 'Fail', 'Skip')),
    timestamp TEXT NOT NULL,
    user_comment TEXT,
    duration REAL DEFAULT 0.0,  -- 单步耗时（分钟）
    can_rollback INTEGER DEFAULT 1 CHECK(can_rollback IN (0, 1)),
    previous_step_id INTEGER,  -- 指向前一步的ID，用于构建回退链
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (session_id) REFERENCES diagnosis_session(session_id) ON DELETE CASCADE,
    FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE,
    FOREIGN KEY (previous_step_id) REFERENCES diagnosis_step_history(step_id) ON DELETE SET NULL
);

-- 创建索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_step_session_id ON diagnosis_step_history(session_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_step_node_id ON diagnosis_step_history(node_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_step_timestamp ON diagnosis_step_history(timestamp);

-- ==============================================
-- 4. 创建 test_recommendation_pool 表（测试推荐池）
-- ==============================================

CREATE TABLE IF NOT EXISTS test_recommendation_pool (
    recommendation_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    node_id INTEGER NOT NULL,
    alternative_node_ids TEXT,  -- JSON数组：可替代的测试节点ID列表
    recommendation_score REAL DEFAULT 0.0,  -- 推荐分数 (0-100)
    recommendation_reason TEXT,  -- 推荐理由
    is_active INTEGER DEFAULT 1 CHECK(is_active IN (0, 1)),
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
    FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE
);

-- 创建索引
CREATE INDEX IF NOT EXISTS idx_test_recommendation_tree_id ON test_recommendation_pool(tree_id);
CREATE INDEX IF NOT EXISTS idx_test_recommendation_node_id ON test_recommendation_pool(node_id);
CREATE INDEX IF NOT EXISTS idx_test_recommendation_score ON test_recommendation_pool(recommendation_score DESC);

-- ==============================================
-- 5. 创建统计视图
-- ==============================================

-- 测试执行统计视图
CREATE VIEW IF NOT EXISTS v_test_execution_stats AS
SELECT 
    n.node_id,
    n.tree_id,
    n.test_description,
    COUNT(DISTINCT h.session_id) as execution_count,
    SUM(CASE WHEN h.test_outcome = 'Pass' THEN 1 ELSE 0 END) as pass_count,
    SUM(CASE WHEN h.test_outcome = 'Fail' THEN 1 ELSE 0 END) as fail_count,
    SUM(CASE WHEN h.test_outcome = 'Skip' THEN 1 ELSE 0 END) as skip_count,
    AVG(h.duration) as avg_duration,
    MAX(h.timestamp) as last_executed
FROM diagnosis_tree_node n
LEFT JOIN diagnosis_step_history h ON n.node_id = h.node_id
WHERE n.node_type = 'Test'
GROUP BY n.node_id;

-- 诊断会话统计视图
CREATE VIEW IF NOT EXISTS v_diagnosis_session_stats AS
SELECT 
    s.tree_id,
    COUNT(*) as total_sessions,
    SUM(CASE WHEN s.session_state = 'Completed' THEN 1 ELSE 0 END) as completed_sessions,
    SUM(CASE WHEN s.session_state = 'Failed' THEN 1 ELSE 0 END) as failed_sessions,
    AVG(s.total_steps) as avg_steps,
    AVG(s.total_duration) as avg_duration
FROM diagnosis_session s
GROUP BY s.tree_id;

-- ==============================================
-- 6. 插入示例推荐数据（可选）
-- ==============================================

-- 为现有测试节点初始化推荐分数
-- INSERT INTO test_recommendation_pool (tree_id, node_id, recommendation_score, recommendation_reason)
-- SELECT tree_id, node_id, test_priority * 10, '基于初始优先级的推荐分数'
-- FROM diagnosis_tree_node
-- WHERE node_type = 'Test'
-- ON CONFLICT DO NOTHING;

-- ==============================================
-- 7. 数据验证
-- ==============================================

-- 检查扩展字段是否添加成功
-- PRAGMA table_info(diagnosis_tree_node);

-- 检查新表是否创建成功
-- SELECT name FROM sqlite_master WHERE type='table' AND name LIKE 'diagnosis_%';

-- 检查视图是否创建成功
-- SELECT name FROM sqlite_master WHERE type='view' AND name LIKE 'v_%';
