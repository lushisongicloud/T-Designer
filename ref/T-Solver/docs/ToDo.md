# 测试性建模（D矩阵）总体方案与ToDo

## 一、总体目标与产出
- 输入：系统SMT模型（器件模型、系统连接、功能模型）。
- 输出：D矩阵（测试×故障的0/1相关性），附元数据（测试/故障清单、语义、生成日志）。
- 原理：在现有SMT建模与Z3求解基础上，按“定量模型 + 逻辑可满足性”构建相关性判定。对每个候选测试t、每个故障f，利用SMT判定“t是否必然检测到f”。

## 二、技术路线与关键判定
- 故障集F：分为两类
  - 功能故障F_func（本期实现）：每个功能对应一个故障，定义为“输入满足要求但功能执行器不满足期望输出”。
    - 构造：对功能f，取其“输入约束”（一般变量、边界条件、依赖功能展开后的约束），再与功能执行器的否定约束¬Actuator(f)合取，得到故障场景M_fault_func(f)。
  - 器件故障F_comp（预留接口，后续实现）：来自器件库`failuremode`的已知故障模式（组件名+故障模式）。
- 测试集T：自动生成 + 人工维护，三类测试：
  1) 信号类测试（Signal）：端口u/i/压力/流量等的“规范判定”P_t。规范可来自：
     - 正常模型推导（优先）：对变量v做区间可达性检查（多次SAT + 二分逼近）得到[lo, hi]，形成P_t：lo≤v≤hi（含容差）。
     - 规范库/模板（备选）：沿用`MainWindow::obsTemplates`作为初始阈值。
  2) 功能类测试（Function）：由功能的“功能执行器”约束生成P_t（例如`M.M1.act=true`）。
  3) 故障模式测试（Mode）：直接针对“某组件处于某故障模式”的判定P_t（正常判别/特定模式）。
- 相关性判定（默认“必然检测”语义）：
  - 正常无误报：UNSAT(M_normal ∧ Inputs ∧ Fail_t)。
  - 故障必失败：UNSAT(M_fault_x(f) ∧ Inputs ∧ P_t)，其中x∈{func,comp}；当前实现为func。
  - 两者均满足，则D[t,f]=1；否则0。Fail_t为P_t的逻辑否定（复用`negateRange`等逻辑）。
- Inputs：功能/边界条件集合。来自功能链路裁剪（`SystemStructure`）与`boundaryComponentList`；若无功能上下文，则使用全局输入边界或默认环境。

## 三、架构与新模块
- 新增`testability/`：
  - `d_matrix_builder.h/.cpp`：
    - `collectFunctionFaults()`：从`functionInfoMap`提取每个功能的输入约束与执行器，形成功能故障定义。
    - `collectComponentFaults()`：预留（遍历组件已知故障模式）。
    - `collectTests()`：
      - `collectSignalTests(SystemStructure&)`：枚举端口变量，按上文规则生成P_t；支持模板与自动区间推导两种来源。
      - `collectFunctionTests(functionInfoMap)`：提取“功能执行器”约束为P_t。
      - `collectModeTests()`：为每个故障模式生成P_t（正常判别/特定模式）。
    - `detectability(Test t, Fault f, InputSet)`：封装两次UNSAT判定（见上式）。
    - `buildDMatrix()`：并行/串行计算D矩阵；产出CSV/JSON。
  - `smt_facade.h/.cpp`：
    - 基于`SystemEntity::prepareModel`流水线复用变量/连接/正常约束拼装；
    - 提供`buildNormalCode()`、`buildFaultCode(f)`（移除组件正常约束、叠加f的`describe`）、`addTestPredicate(P_t)`；
    - `isSat(code)`：复用`z3Solve`或独立封装；支持超时/日志。
- 导出：`docs/DMatrix/<model>_<timestamp>.csv`，首行列名为故障；首列行为测试；同时输出`metadata.json`（来源、参数、计时、判定模式）。

## 四、重点与难点拆解
1) 自动规范推导（Signal测试阈值）
- 目标：从正常模型自动推导变量可达区间[lo, hi]。
- 方法：对目标变量v，用二分+可满足性：
  - 求上界：设b初值（模板或逐级放大），检查SAT(M_normal ∧ v≥b)。若UNSAT则收缩；SAT则增大b；直至收敛。
  - 求下界同理（v≤b）。
- 产物：P_t为lo≤v≤hi（容差ε），Fail_t为取反；
- 验收：在已知电路（如README案例）上得到合理区间且能区分典型故障（如FU熔断）。

2) Fault注入与裁剪
- 目标：注入单一已知故障模式并保证模型自洽、最小裁剪。
- 方法：功能故障：重用`SystemStructure`按功能链路裁剪；以功能输入约束+¬Actuator(f)构造M_fault_func；
        器件故障（预留）：移除组件正常约束、加入fault describe。
- 验收：注入“FU左位熔断”时，能重建模型且SAT判定稳定。

3) 判定语义与性能
- 目标：必然检测（UNSAT判定）与存在性检测（SAT判定）可切换；并行化加速。
- 方法：`detectability()`加参数`mode in {guaranteed, exists}`；用线程池批量跑Z3；设置超时、缓存子式。
- 验收：示例电机启停系统100+组合在可接受时间内完成。

## 五、实现计划（可检验ToDo）
- P0 基础设施
  - [x] 新建`testability/`目录与CMake/Pro集成；
  - [x] `smt_facade`封装：`buildNormalCode()/buildFaultCode()/isSat()`；
  - [x] 针对README中的示例系统编写最小演示：能对单一测试/故障给出判定（手工P_t）。
- P1 测试/故障采集
  - [x] `collectFunctionFaults()`：遍历`functionInfoMap`生成功能故障定义（输入约束、执行器约束）。
  - [x] `collectFunctionTests()`：从`functionInfoMap`抽取执行器约束为测试P_t；
  - [x] `collectSignalTests()`：从`SystemStructure`端口清单生成端口变量列表（u/i/p/f等）。
- P2 规范推导与取反
  - [x] 数值取反与比较生成：复用`negateRange`和`creatObsEntity`生成P_t/Fail_t；
  - [x] 区间推导器：二分+SAT，得到[lo,hi]；
  - [x] 兼容数组端口（1P/3P）：对(select v i)逐相推导阈值；
  - [x] 容差策略与默认模板回退。
- P3 D矩阵构建与导出
  - [x] `detectability()`实现（guaranteed/exists模式）；
  - [x] `buildDMatrix()`：并发计算、超时与缓存；
  - [x] 导出CSV与metadata，路径`docs/DMatrix/`。
- P4 UI与配置
  - [x] 在主界面新增“生成D矩阵”入口与保存路径对话框；
  - [x] 高级选项：判定模式、超时、是否使用自动规范推导/模板。
  - [x] 新增“D矩阵查看器”窗口（QTableView+自定义模型）：
        - 行=故障（f1..fN），列=测试（t1..tM）；单元为0/1，默认用小方块/颜色指示，减少文本；
            - 仅使用QAbstractTableModel，避免QTableWidget逐格对象，保障10k×300规模；
            - 悬停tooltip：表头/单元格展示测试/故障全名与描述；
            - 导出：当前视图导出CSV；
            - 性能：分页/虚拟滚动（可选）。

## 六、代码落地建议
- 新文件建议：
  - `testability/d_matrix_builder.h/.cpp`
  - `testability/smt_facade.h/.cpp`
  - 如需：`testability/test_definitions.h`（Test/Fault结构体定义）
- 与现有代码衔接：
  - 解析与裁剪：重用`SystemStructure`；
  - 变量与模板：重用`SystemEntity::obsVarsMap/obsTemplates`；
  - 数值逻辑：重用`negateRange`与`creatObsEntity`生成断言；
  - Z3求解：重用`z3Solve`，增加超时与异常处理。

## 八、数据结构与数据库设计（UI/持久化）
- 内存结构
  - `struct TestDef {int id; QString code; QString name; QString type; QString predicate;}`
  - `struct FuncFault {int id; QString code; QString name; QString functionName; QStringList inputConstraints; QString actuatorVar; QString actuatorVal;}`
  - `QVector<QBitArray> dRows;` // 每行（故障）一个bitset，列索引为测试；10k×300≈0.36MB。
  - `QVector<TestDef> tests; QVector<FuncFault> faults; QHash<QString,int> code2row/code2col`。
- 数据库表（扩展Model.db）
  - `tests(id INTEGER PRIMARY KEY, code TEXT UNIQUE, name TEXT, type TEXT, predicate TEXT, meta TEXT)`
  - `func_faults(id INTEGER PRIMARY KEY, code TEXT UNIQUE, name TEXT, function TEXT, meta TEXT)`
  - `d_matrix_rows(fault_id INTEGER, bitrow BLOB, PRIMARY KEY(fault_id))`
  - `FOREIGN KEY`指向各自表；另建索引便于检索。
- UI模型
  - `class DMatrixModel : public QAbstractTableModel`：按bit访问；`headerData()`返回`tN/fN`，并设置`Qt::ToolTipRole`为全名；
  - 过滤/定位：`QSortFilterProxyModel`或自定义接口`setFocusRow/Col`；
  - 委托`QStyledItemDelegate`画点/色块，避免文本绘制开销。
