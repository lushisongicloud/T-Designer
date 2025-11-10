-- 诊断系统基础表创建脚本
-- 用途：创建诊断决策树所需的所有基础表

-- ==============================================
-- 1. 创建 diagnosis_tree 表（诊断树）
-- ==============================================

CREATE TABLE IF NOT EXISTS diagnosis_tree (
    tree_id INTEGER PRIMARY KEY AUTOINCREMENT,
    container_id INTEGER,
    function_id INTEGER,
    name TEXT NOT NULL,
    description TEXT,
    root_node_id INTEGER,
    created_time TEXT DEFAULT CURRENT_TIMESTAMP,
    auto_generated INTEGER DEFAULT 1,
    FOREIGN KEY (container_id) REFERENCES container(container_id) ON DELETE CASCADE,
    FOREIGN KEY (function_id) REFERENCES Function(FunctionID) ON DELETE CASCADE,
    FOREIGN KEY (root_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE SET NULL
);

-- ==============================================
-- 2. 创建 diagnosis_tree_node 表（诊断树节点）
-- ==============================================

CREATE TABLE IF NOT EXISTS diagnosis_tree_node (
    node_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    parent_node_id INTEGER DEFAULT 0,
    test_id INTEGER,
    state_id INTEGER,
    outcome TEXT,
    comment TEXT,
    node_type TEXT DEFAULT 'Test' CHECK(node_type IN ('Test', 'Fault', 'Branch')),
    test_description TEXT,
    expected_result TEXT,
    fault_hypothesis TEXT,
    isolation_level INTEGER DEFAULT 0,
    test_priority REAL DEFAULT 0.5,
    pass_button_text TEXT DEFAULT '是',
    fail_button_text TEXT DEFAULT '否',
    skip_count INTEGER DEFAULT 0,
    skip_reason TEXT,
    alternative_tests TEXT,
    cost_estimate REAL DEFAULT 0.0,
    duration_estimate REAL DEFAULT 0.0,
    detectable_faults TEXT,
    isolatable_faults TEXT,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
    FOREIGN KEY (parent_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE,
    FOREIGN KEY (test_id) REFERENCES test_definition(test_id) ON DELETE SET NULL,
    FOREIGN KEY (state_id) REFERENCES container_state(state_id) ON DELETE SET NULL
);

-- ==============================================
-- 3. 创建 Function 表（如果不存在）
-- ==============================================

CREATE TABLE IF NOT EXISTS Function (
    FunctionID INTEGER PRIMARY KEY,
    FunctionName TEXT NOT NULL,
    ExecsList TEXT,
    CmdValList TEXT,
    UserTest TEXT,
    Remark TEXT
);

-- ==============================================
-- 4. 创建索引
-- ==============================================

-- diagnosis_tree 索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_function_id ON diagnosis_tree(function_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_container_id ON diagnosis_tree(container_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_root_node ON diagnosis_tree(root_node_id);

-- diagnosis_tree_node 索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_tree_id ON diagnosis_tree_node(tree_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_parent_id ON diagnosis_tree_node(parent_node_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_type ON diagnosis_tree_node(node_type);
CREATE INDEX IF NOT EXISTS idx_diagnosis_tree_node_test_id ON diagnosis_tree_node(test_id);

-- ==============================================
-- 5. 创建诊断会话相关表
-- ==============================================

CREATE TABLE IF NOT EXISTS diagnosis_session (
    session_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    function_id INTEGER,
    start_time TEXT NOT NULL,
    end_time TEXT,
    session_state TEXT NOT NULL CHECK(session_state IN ('NotStarted', 'InProgress', 'Completed', 'Failed', 'Cancelled')) DEFAULT 'NotStarted',
    fault_node_id INTEGER,
    total_steps INTEGER DEFAULT 0,
    total_duration REAL DEFAULT 0.0,
    user_id TEXT,
    session_notes TEXT,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
    FOREIGN KEY (fault_node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE SET NULL
);

CREATE TABLE IF NOT EXISTS diagnosis_step_history (
    step_id INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id INTEGER NOT NULL,
    step_number INTEGER NOT NULL,
    node_id INTEGER NOT NULL,
    test_outcome TEXT NOT NULL CHECK(test_outcome IN ('Unknown', 'Pass', 'Fail', 'Skip')) DEFAULT 'Unknown',
    timestamp TEXT NOT NULL,
    user_comment TEXT,
    duration REAL DEFAULT 0.0,
    can_rollback INTEGER DEFAULT 1 CHECK(can_rollback IN (0, 1)),
    previous_step_id INTEGER,
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (session_id) REFERENCES diagnosis_session(session_id) ON DELETE CASCADE,
    FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE,
    FOREIGN KEY (previous_step_id) REFERENCES diagnosis_step_history(step_id) ON DELETE SET NULL
);

CREATE TABLE IF NOT EXISTS test_recommendation_pool (
    recommendation_id INTEGER PRIMARY KEY AUTOINCREMENT,
    tree_id INTEGER NOT NULL,
    node_id INTEGER NOT NULL,
    alternative_node_ids TEXT,
    recommendation_score REAL DEFAULT 0.0,
    recommendation_reason TEXT,
    is_active INTEGER DEFAULT 1 CHECK(is_active IN (0, 1)),
    created_at TEXT DEFAULT CURRENT_TIMESTAMP,
    updated_at TEXT DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY (tree_id) REFERENCES diagnosis_tree(tree_id) ON DELETE CASCADE,
    FOREIGN KEY (node_id) REFERENCES diagnosis_tree_node(node_id) ON DELETE CASCADE
);

-- 会话表索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_session_tree_id ON diagnosis_session(tree_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_session_state ON diagnosis_session(session_state);
CREATE INDEX IF NOT EXISTS idx_diagnosis_session_start_time ON diagnosis_session(start_time);

-- 步骤历史表索引
CREATE INDEX IF NOT EXISTS idx_diagnosis_step_session_id ON diagnosis_step_history(session_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_step_node_id ON diagnosis_step_history(node_id);
CREATE INDEX IF NOT EXISTS idx_diagnosis_step_timestamp ON diagnosis_step_history(timestamp);

-- 推荐池索引
CREATE INDEX IF NOT EXISTS idx_test_recommendation_tree_id ON test_recommendation_pool(tree_id);
CREATE INDEX IF NOT EXISTS idx_test_recommendation_node_id ON test_recommendation_pool(node_id);
CREATE INDEX IF NOT EXISTS idx_test_recommendation_score ON test_recommendation_pool(recommendation_score DESC);

-- ==============================================
-- 6. 创建统计视图
-- ==============================================

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
-- 完成
-- ==============================================

SELECT '诊断系统基础表创建完成' AS result;
