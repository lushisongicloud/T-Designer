-- 简化版清理脚本 - 直接删除重复节点和空白节点

-- 禁用外键检查
PRAGMA foreign_keys = OFF;

-- 开始事务
BEGIN IMMEDIATE TRANSACTION;

-- 步骤1：删除重复的节点（这些节点没有子节点，可以安全删除）
DELETE FROM ProjectStructure WHERE ProjectStructure_ID = 1002;  -- 重复的"油源动力系统"
DELETE FROM ProjectStructure WHERE ProjectStructure_ID = 1047;  -- 重复的"集中油源动力系统"

-- 步骤2：直接删除空白的位置节点
-- 这些节点是叶子节点，没有子项目结构
DELETE FROM ProjectStructure
WHERE Structure_INT IS NULL OR Structure_INT = ''
  AND ProjectStructure_ID IN (
    1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016,
    1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028,
    1029, 1030, 1032, 1033, 1034, 1035
  );

-- 更新自增序列
UPDATE sqlite_sequence
SET seq = (SELECT MAX(ProjectStructure_ID) FROM ProjectStructure)
WHERE name = 'ProjectStructure';

-- 提交事务
COMMIT;

-- 启用外键检查
PRAGMA foreign_keys = ON;

-- 验证结果
SELECT '=== 清理完成 ===';
SELECT 'ProjectStructure记录数：';
SELECT COUNT(*) FROM ProjectStructure;

SELECT '空白节点数：';
SELECT COUNT(*) FROM ProjectStructure WHERE Structure_INT IS NULL OR Structure_INT = '';
