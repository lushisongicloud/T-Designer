**【分类依据】本文件记录了已完成的工作、最终报告或实现总结，作为历史成果保留供后续参考。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# T-Designer Current-State Snapshot (Function, Containers, D-Matrix, T-Language)

## 1. Function Management Flow
### Entry Points & Data Path
- **UI entry**: `MainWindow::on_BtnFunctionManage_clicked()` opens `widget/functionmanagerdialog`. Symbol tree context menu also offers “创建功能” leading to `FunctionEditDialog`.
- **Storage**: relational tables (`Function`, `function_bindings`) managed by `BO/function/functionrepository`. Columns include Exec lists, link text, dependencies, persistent flag, fault probability.
- **Auto analysis**: `FunctionAnalysisService::analyzeSymbol` derives default function name, exec list, simple link (`GetLinkRoadBySymbol`). No SAT or variable range computation.
- **Editing UI**: `FunctionEditDialog` allows manual inputs/exec selection, fault probability, simple dependencies. No XML-based structure, no constraint integrity checker, no variable range dialog.

### Gaps vs T-Solver
- Missing XML storage for `link`, `dependency`, `constraint`, `variableRangeConfig`, `offlineSolveResult`.
- No reuse of `SystemStructure` to crop models; only text fields persisted.
- No SAT-based integrity check or actuator inversion steps.
- Function selection UI (`FunctionManagerDialog`) lists functions but lacks tree/ dependency visualization.

## 2. Container Layer Interface
- **Repository**: `BO/containerrepository` ensures tables (`Container`, `ContainerHierarchy`, `ContainerComponentLink` etc.) and CRUD operations.
- **Data model**: `ContainerEntity`, `ContainerData` (JSON for ports, behavior, tests, analysis). Behavior stored as `behaviorSmt` string and JSON spec with normal/fault modes.
- **UI**: `widget/containertreedialog`, `containermodel`, `containerhierarchyutils` handle creation, parenting, ensuring components have containers.
- **Integration status**: Containers maintain port lists/behavior in JSON but not tied to SMT variables or auto-generated from components. No direct link to function or D-matrix builders.

### Observations
- Container behavior uses JSON; no standard SMT-LIB per port. `behaviorSmt` field exists but not auto-populated from component T-language.
- Aggregation utilities (`BehaviorAggregator`, `TestGeneratorService`) operate on current JSON; limited or no awareness of T-Solver semantics.

## 3. D-Matrix Implementation & UI
- **Builder**: `BO/test/diagnosticmatrixbuilder` builds coverage from `GeneratedTest.detectableFaults`/`isolatableFaults`. No solver invocation.
- **UI**: `widget/testmanagementdialog` (依赖矩阵 tab) displays `tableMatrix` (检测/隔离 bool). Additional views: target allocation, prediction, candidate tests, decision tree using heuristic scoring. No CSV/JSON export nor enable toggles.
- **Test definitions**: `BO/test/testgeneratorservice` synthesizes tests from container behavior/ports; outputs detection/ isolation lists but no variable ranges or solver-backed detectability.

### Gaps vs T-Solver
- Lacks detectability computation using SAT (no normalSat/faultSat states, guaranteed vs exists modes).
- No viewer like `ref/T-Solver/widget/dmatrixviewerdialog` (vertical headers, enable toggles, metadata save).
- No storage for D-matrix metadata/CSV; results transient in memory.
- Extended dimensions (complexity, cost, time, success rate, notes, fault severity) absent.

## 4. T-Language Validation & Code Checking
- **Validator**: `BO/function/tmodelvalidator` checks `%MARK%.port.i/u` declarations/assert usage; only electrical variables. Reports missing declarations, undefined variables, unused ports.
- **UI triggers**: `DialogUnitAttr::on_BtnValidateTModel_clicked()` collects `Symb2TermInfo` ports and uses validator; same button label “校验端口映射”.
- **Syntax check**: `widget/codecheckdialog` + `CodeChecker` still target legacy DEF syntax (PORT_DEF, VARIATE). SMT parsing not employed.
- **Coverage gaps**: No SMT-LIB syntax validation, no support for hydraulic `.p/.q` or mechanical `.F/.v/.n/.x`. Arrays (`select`) ignored. No cross-check with container port config.

## 5. Candidate Reuse Points & Required Replacements
| Area | Existing Component | Reuse? | Required Replacement / Extension |
| --- | --- | --- | --- |
| Function storage | `FunctionRepository` (relational) | Partial | Introduce XML storage for rich definitions; keep repo for migration/lookup. |
| Function UI | `FunctionManagerDialog`, `FunctionEditDialog` | Partial | Rebuild manager to embed T-Solver features (dependency tree, integrity check, variable ranges). Edit dialog to adopt new panels. |
| Auto analysis | `FunctionAnalysisService` | Extend | Hook into new SystemStructure-based crop and SAT functions. |
| Container data | `ContainerData` JSON ports/behavior | Extend | Map JSON to new port variable sets; auto-populate `behaviorSmt`. |
| D-matrix builder | `DiagnosticMatrixBuilder` | Limited | Replace core with T-Solver `DMatrixBuilder`; retain wrapper for compatibility. |
| D-matrix UI | `TestManagementDialog` tables | Replace | Integrate `DMatrixViewerDialog` for visualization; keep existing priority/decision tree panels with new data source. |
| T-language validator | `tmodelvalidator`, `CodeChecker` | Extend/Replace | Expand validator for SMT variables; add new syntax checker using Z3 parse. |

## 6. Notable Dependencies
- **common.cpp**: functions `GetLinkRoadBySymbol`, etc., used by function analysis & container utilities.
- **tests/test_workflow_core.cpp**: demonstrates container/test generation workflow (current features baseline).
- **docs/**: legacy requirements (hierarchical modeling) align with container JSON approach but predate SMT integration.

## 7. Risks / Migration Notes
- Existing projects store function data only in `Function` table → migration needed to XML/SMT.
- Container behavior JSON may conflict once SMT-led modeling introduced; need compatibility mode.
- Test generation currently deterministic; transitioning to solver-based detectability may change outcomes users expect.
- Validator updates must avoid false positives on legacy `.f`/`.M` before migration scripts run.

