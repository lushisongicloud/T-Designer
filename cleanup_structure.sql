-- ============================================================================
-- T-Designer 项目结构清理脚本
-- 目的：清理ProjectStructure表中的重复节点和空白节点
-- 日期：2024-11-12
-- ============================================================================

-- 启用外键约束
PRAGMA foreign_keys = ON;

-- 开始事务
BEGIN TRANSACTION;

-- ============================================================================
-- 第1步：记录要删除的节点及其子节点
-- ============================================================================

-- 创建临时表记录空白节点及其设备/连线
DROP TABLE IF EXISTS temp_blank_nodes;
CREATE TEMPORARY TABLE temp_blank_nodes AS
SELECT DISTINCT e.ProjectStructure_ID, e.DT as equipment_name
FROM Equipment e
WHERE e.ProjectStructure_ID IN (
    1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016,
    1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028,
    1029, 1030, 1032, 1033, 1034, 1035
);

-- ============================================================================
-- 第2步：重新关联设备到正确的父节点
-- ============================================================================

-- 将控制柜下的空白节点设备重新关联到控制柜（1004）
UPDATE Equipment
SET ProjectStructure_ID = 1003
WHERE ProjectStructure_ID IN (
    1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016,
    1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028,
    1029, 1030
);

-- 将液压站下的空白节点设备重新关联到液压站（1031）
UPDATE Equipment
SET ProjectStructure_ID = 1031
WHERE ProjectStructure_ID IN (1032, 1033, 1034, 1035);

-- ============================================================================
-- 第3步：重新关联连线到正确的父节点
-- ============================================================================

-- 将空白节点下的连线重新关联到液压站（1031）
UPDATE JXB
SET ProjectStructure_ID = 1031
WHERE ProjectStructure_ID IN (1032, 1033, 1034, 1035);

-- ============================================================================
-- 第4步：重新关联Symbol到正确的父节点
-- ============================================================================

-- 将空白节点下的Symbol重新关联到控制柜（1004）
UPDATE Symbol
SET ProjectStructure_ID = 1003
WHERE ProjectStructure_ID IN (
    1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016,
    1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028,
    1029, 1030
);

-- 将空白节点下的Symbol重新关联到液压站（1031）
UPDATE Symbol
SET ProjectStructure_ID = 1031
WHERE ProjectStructure_ID IN (1032, 1033, 1034, 1035);

-- ============================================================================
-- 第5步：删除空白的位置节点
-- ============================================================================

-- 删除空白的位置节点（控制柜下）
DELETE FROM ProjectStructure
WHERE ProjectStructure_ID IN (
    1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016,
    1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028,
    1029, 1030
);

-- 删除空白的位置节点（液压站下）
DELETE FROM ProjectStructure
WHERE ProjectStructure_ID IN (1032, 1033, 1034, 1035);

-- ============================================================================
-- 第6步：删除重复的高层节点
-- ============================================================================

-- 删除重复的"油源动力系统"节点（1002，保留1003）
DELETE FROM ProjectStructure
WHERE ProjectStructure_ID = 1002;

-- 删除重复的"集中油源动力系统"节点（1047，保留1001）
DELETE FROM ProjectStructure
WHERE ProjectStructure_ID = 1047;

-- ============================================================================
-- 第7步：更新sequence表（如果存在）
-- ============================================================================

UPDATE sqlite_sequence
SET seq = (SELECT MAX(ProjectStructure_ID) FROM ProjectStructure)
WHERE name = 'ProjectStructure';

-- ============================================================================
-- 提交事务
-- ============================================================================

COMMIT TRANSACTION;

-- ============================================================================
-- 验证结果
-- ============================================================================

-- 显示清理后的结构
.output stdout
SELECT '============================================';
SELECT '清理后的ProjectStructure表结构：';
SELECT '============================================';

SELECT ProjectStructure_ID, Structure_ID, Structure_INT, Parent_ID
FROM ProjectStructure
ORDER BY Parent_ID, Structure_INT;

-- 检查重复的高层名称
SELECT '============================================';
SELECT '检查重复的高层名称：';
SELECT '============================================';

SELECT Structure_INT, COUNT(*) as count
FROM ProjectStructure
WHERE Parent_ID = 0 OR Parent_ID = 1
GROUP BY Structure_INT
HAVING COUNT(*) > 1;

-- 检查空白节点
SELECT '============================================';
SELECT '检查空白节点数量：';
SELECT '============================================';

SELECT COUNT(*) as blank_count
FROM ProjectStructure
WHERE Structure_INT IS NULL OR Structure_INT = '';

-- 显示设备分布
SELECT '============================================';
SELECT '设备分布统计：';
SELECT '============================================';

SELECT ps.Structure_INT, COUNT(e.Equipment_ID) as equipment_count
FROM ProjectStructure ps
LEFT JOIN Equipment e ON ps.ProjectStructure_ID = e.ProjectStructure_ID
GROUP BY ps.ProjectStructure_ID, ps.Structure_INT
ORDER BY equipment_count DESC;

-- 显示清理后的连线分布
SELECT '============================================';
SELECT '连线分布统计（前20条）：';
SELECT '============================================';

SELECT ps.Structure_INT, COUNT(j.JXB_ID) as connection_count
FROM ProjectStructure ps
LEFT JOIN JXB j ON ps.ProjectStructure_ID = j.ProjectStructure_ID
GROUP BY ps.ProjectStructure_ID, ps.Structure_INT
ORDER BY connection_count DESC
LIMIT 20;

SELECT '============================================';
SELECT '数据库清理完成！';
SELECT '============================================';
