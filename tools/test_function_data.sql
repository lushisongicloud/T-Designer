-- 为测试数据迁移脚本创建示例Function数据

INSERT INTO Function (FunctionID, FunctionName, ExecsList, CmdValList, Remark) VALUES
(1, '电源供电功能', '电源模块, 保险丝, 电源开关', 'Power.state=ON', '检测电源供电是否正常'),
(2, '电机驱动功能', '电机驱动器, 电机, 传感器', 'Motor.speed=100', '检测电机驱动功能'),
(3, '信号采集功能', '传感器1, AD转换器, 信号处理模块', 'Signal.enabled=TRUE', '检测信号采集功能');

-- 验证插入
SELECT * FROM Function;
