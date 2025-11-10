# AGENTS 指南 — tests（测试）

本文件适用于 `tests/` 目录。使用 Qt Test 框架为关键业务与模型编写单元/集成测试。

## 组织与命名
- 建议命名：`bo_<area>_test.cpp`、`do_<type>_test.cpp`、`widget_<model>_test.cpp`。
- `tests.pro` 管理测试目标；添加新测试时同步更新 `T_DESIGNER.pro`（或在 `tests/tests.pro` 中聚合）。

## 本周期测试重点
- SMT 校验：
  - 语法错误定位；未声明/多余变量；端口与变量不一致的报错与修复建议。
  - 正/反例用例集；边界输入（空模型、极大模型、中文标识）。
- 连接生成：
  - CAD→`connect2e/3e`、`connect2h/3h`、`connect2m/3m` 展开正确；1P/3P 数组索引展开；KCL/KVL 等式正确性。
- 功能管理：
  - 链路合并/裁剪规则；依赖功能三元组展开；边界条件去重与补全。
- D 矩阵：
  - 生成、合并、过滤与权重策略；扩展维度（测试/故障）读写一致性；与既有流程兼容性。
- 容器层：
  - 元件级容器的接口/行为代理与 SMT/功能数据视图正确性。

## 运行与环境
- 推荐在 out-of-source 构建目录运行测试；可使用 Qt Creator Test 功能或直接执行测试二进制。
- 若测试依赖示例数据，请引用 `MyProjects/` 下的项目 db 副本；避免修改 `templete/project.db` 与 `ref/Model.db`。

---
简述：以小而全的用例覆盖新引入的 SMT/功能/D 矩阵关键路径，优先保障容器层与 BO 服务的稳定性。

