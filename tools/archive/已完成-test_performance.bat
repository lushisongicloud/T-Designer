# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

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
