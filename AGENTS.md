# Repository Guidelines

## Project Structure & Module Organization
- Root: `T_DESIGNER.pro`; sources (`.cpp/.h`) and Qt UI forms (`.ui`) live in root and subfolders.
- Main window logic is split across `mainwindow.cpp` (bootstrap) and feature-focused files `mainwindow_project.cpp`, `mainwindow_units.cpp`, `mainwindow_diagnosis.cpp`; keep new functionality in the closest matching unit.
- Modules: `widget/` (custom controls & dialogs), `BO/` (business objects — see `behavior/`, `container/`, `function/`, `test/` submodules), `DO/` (data objects).
- Resources: `image.qrc`, icons (e.g., `T_DESIGNER.ico`).
- Data/Templates:
  - `MyProjects/` 收录现有的 T-Designer 示例工程（如 `双电机拖曳收放装置/`、`DemoSystem/`），但要特别注意`DemoSystem/`项目使用 Livingstone 求解器与专用 T 语言描述，整体流程已跑通，可用于理解端口连线、变量定义与诊断流程；在实现新功能时请参考其概念，但逐步迁移到通用 SMT 描述与 `z3` 求解器。
  - `ref/` 提供离线校验用数据库：`LdMainData.db`（运行环境 `C:/TBD/data/LdMainData.db` 的镜像，用于对照实体元器件库）、`Model.db`（现还暂未整合到 T-Designer 的工作流程中来，其中包含实体元件、系统的 SMT 描述，以及系统功能的描述与组织，配套代码见 `./ref/T-Solver/BO/systementity.cpp`、`./ref/T-Solver/widget/selectfunctiondialog.cpp`）。查看sqlite的db文件可以直接使用sqlite3命令
  - `templete/project.db` 是新建工程时的模板，已包含统一的层次/功能/测试表；如需调整工程库结构，请先在目标项目的同名 db 文件上验证，评审通过后再更新模板。
- Tests: add under `tests/` when introduced (see below).

## Build, Test, and Development Commands
- The `axcontainer` module is not available in WSL/Linux environments (Windows-specific ActiveX technology)

- Full project compilation and execution is **not possible** in WSL

- Only limited development tasks can be performed:

  - Run `qmake` to generate Makefiles
  - Compile individual `.cpp`/`.h` files that don't depend on `axcontainer`
  - Check for syntax errors and basic compilation issues in isolated files

  ```bash
  mkdir buildInWSL && cd buildInWSL
  qmake ..\T_DESIGNER.pro
  make -j specific_target.o
  ```

## Coding Style & Naming Conventions
- Language: C++ (Qt 5.12). Indentation 4 spaces, UTF-8; Unix line endings (LF).
- Naming: Classes PascalCase (e.g., `DialogConnectAttr`); methods/variables lowerCamelCase; macros/constants ALL_CAPS.
- Files: header/source paired and same base name; UI files mirror class (e.g., `dialogconnectattr.ui`).
- Formatting: use `clang-format` (Qt style); keep consistent across files.

## Commit & Pull Request Guidelines
- Commits: Conventional Commits recommended, e.g., `feat(widget): add codecheckdialog`, `fix(BO): null check in worker`.
- PRs: clear description, link issues, include screenshots for UI changes, and list build/verification steps.

## Security & Configuration Tips
- Do not commit sensitive config or local paths. 在 `ref/` 内的数据库副本上对比/验证（优先使用 `ref/project.db` 或 `ref/Model.db`），避免直接改动入库模板或示例。
- 运行时实际加载 `C:/TBD/data/LdMainData.db`；仓库中的 `ref/LdMainData.db` 仅供参考，更新实体库逻辑时应考虑同步策略。
- Runtime deps: Qt, SQLite (`sqlitedatabase.*`), optional Z3 (`z3solverthread.*`). Ensure required DLLs are in `PATH`.

## Agent-Specific Instructions
- Scope: this file applies repo-wide. Prefer small, reversible changes; avoid unrelated refactors.
- Do not edit generated files (e.g., `ui_*.h`).
- When adding/removing sources, update `T_DESIGNER.pro` accordingly.
- Put helper scripts in `tools/` or repo root and document purpose.
- When using Chinese text in code, do not use `tr()` or `QStringLiteral`; use double-quoted string literals (e.g., "中文文本") or `QString("中文文本")`.

## Development Sprint Goals — T‑Solver Integration
- Deeply integrate T‑Solver modeling, function management, and D‑matrix into T‑Designer; keep legacy D‑matrix workflows compatible (测试优选、测试性指标预计、诊断决策树等)。
- Migrate component "元件T语言" to SMT‑LIB2; align SMT port names with 元件属性中“功能子块”的端号与类型（电气/液压/机械）。
- Auto‑generate system port connections from CAD netlist using `connect2e/3e`, `connect2h/3h`, `connect2m/3m` sugar that expand to KCL/KVL‑style SMT constraints.
- Unify edit flows between “本地物料库”与“元件属性”：复用同一校验与持久化逻辑，避免双处维护。
- Add SMT model validator: 语法校验 + 端口与变量一致性校验；在两处界面统一复用。
- Extend port configuration UI to set port type and default/custom variable sets（i/u, p/q, F+v|n|x；允许用户自定义变量与 connect 函数族）。
- Store SMT for components/systems and function definitions only in project DB（项目同名 db）；模板调整遵循“先项目验证、后模板更新、提供 tools 迁移脚本”。
- Rebuild System Function Management per T‑Solver：链路自动从连线推断，可编辑确认；依赖/边界条件裁剪与求解前准备按 T‑Solver 规则。
- Rebuild Test Management → 依赖矩阵：UI/交互与数据结构对齐 T‑Solver 的 `dmatrixviewerdialog` 实现，并扩展测试/故障维度信息（复杂性、费用、时间、成功率、备注；概率、严重度、备注等）。
- Implement at container level first：元件级容器代理单一实体元件的接口/行为；将新 SMT 建模、功能管理与 D‑矩阵逻辑尽量落在容器与 BO 层，减少对实体元件内部侵入。

## Port/Variable Naming Rules
- Electrical: `.i` current, `.u` voltage；Hydraulic: `.p` pressure, `.q` flow；Mechanical: `.F` force, `.v`/`.n`/`.x`（选其一）。
- Example relay KA1 with Coil(A1|A2) and Contact(11|14|12): declare variables `KA1.Coil.A1.i/u`, `KA1.Coil.A2.i/u`, `KA1.Contact.11.i/u`, `KA1.Contact.14.i/u`, `KA1.Contact.12.i/u`.
- Support default and custom variable sets per port type；user‑defined connect functions are allowed and must expand to valid SMT constraints.

## Cad → SMT Connection Sugar
- `connect2e(A,B)`: `(assert (= (+ A.i B.i) 0))` + `(assert (= A.u B.u))`.
- `connect3e(A,B,C)`: Σi=0 + equal potential; similarly for `h`/`m` with appropriate variables.
- Multi‑phase arrays: `connect2e(3P, A,B)` expands per phase using `(select X.i 0/1/2)`.

## Database Expectations (Project DB only)
- Persist: component templates and instances SMT, system DEF/connect/raw SMT, functions (link/dependency/constraints/offline results), D‑matrix data.
- Validation workflow: project DB first; once stable, update `templete/project.db` via `tools/` migration script.

## Testing Focus This Sprint
- SMT syntax and port consistency validator（正/反例）。
- Netlist→SMT connection generation correctness（电/液/机 & 2/3 端）。
- Function management（链路裁剪、依赖展开、边界补全）。
- D‑matrix builder/viewer data integrity and UI interactions.
