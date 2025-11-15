@echo off
echo ========================================
echo T-Designer 性能测试脚本
echo ========================================
echo.

echo 正在启动程序...
cd /d D:\SynologyDrive\Project\T_DESIGNER\build\release

REM 启动程序
start /wait T-DESIGNER.exe

echo.
echo 测试完成！
echo 请查看控制台输出的 PerformanceTimer 日志
echo.
pause
