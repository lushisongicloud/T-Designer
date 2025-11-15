-- 修复直接关联到高层节点的数据
-- 问题：326条连线和203个设备直接关联到高层节点1003（油源动力系统）
-- 解决：创建"网络"位置节点，或重新分配到现有位置

-- 查看当前的高层节点结构
-- SELECT * FROM ProjectStructure WHERE Parent_ID = 1003;

-- 方案：创建"网络"位置节点
INSERT INTO ProjectStructure (Structure_ID, Structure_INT, Parent_ID)
VALUES (5, '网络', 1003);

-- 获取新插入的ProjectStructure_ID
-- 注意：这里需要先查询ID，然后更新数据

-- 临时方案：分配到控制柜（因为网络设备更接近控制系统）
-- 注意：这里我们选择重新分配到控制柜1004
UPDATE Equipment
SET ProjectStructure_ID = 1004
WHERE ProjectStructure_ID = 1003;

UPDATE JXB
SET ProjectStructure_ID = 1004
WHERE ProjectStructure_ID = 1003;

-- 验证更新结果
SELECT '更新后的设备分布：';
SELECT ps.Structure_INT, COUNT(e.Equipment_ID) as equipment_count
FROM ProjectStructure ps
LEFT JOIN Equipment e ON ps.ProjectStructure_ID = e.ProjectStructure_ID
GROUP BY ps.ProjectStructure_ID, ps.Structure_INT
ORDER BY equipment_count DESC;

SELECT '更新后的连线分布：';
SELECT ps.Structure_INT, COUNT(j.JXB_ID) as connection_count
FROM ProjectStructure ps
LEFT JOIN JXB j ON ps.ProjectStructure_ID = j.ProjectStructure_ID
GROUP BY ps.ProjectStructure_ID, ps.Structure_INT
ORDER BY connection_count DESC;
