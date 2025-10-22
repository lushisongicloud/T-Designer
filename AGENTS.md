# Repository Guidelines

## Project Structure & Module Organization
- Root: `T_DESIGNER.pro`; sources (`.cpp/.h`) and Qt UI forms (`.ui`) live in root and subfolders.
- Main window logic is split across `mainwindow.cpp` (bootstrap) and feature-focused files `mainwindow_project.cpp`, `mainwindow_units.cpp`, `mainwindow_diagnosis.cpp`; keep new functionality in the closest matching unit.
- Modules: `widget/` (custom controls & dialogs), `BO/` (business objects — see `behavior/`, `container/`, `function/`, `test/` submodules), `DO/` (data objects).
- Resources: `image.qrc`, icons (e.g., `T_DESIGNER.ico`).
- Data/Templates:
  - `MyProjects/` 收录现有的 T-Designer 示例工程（如 `DemoSystem/`），这些项目使用 Livingstone 求解器与专用 T 语言描述，整体流程已跑通，可用于理解端口连线、变量定义与诊断流程；在实现新功能时请参考其概念，但逐步迁移到通用 SMT 描述与 `z3` 求解器。
  - `ref/` 提供离线校验用数据库：`LdMainData.db`（运行环境 `C:/TBD/data/LdMainData.db` 的镜像，用于对照实体元器件库）、`Model.db`（包含实体元、系统、功能的 SMT 描述，配套代码见 `systementity.cpp`、`selectfunctiondialog.cpp`），以及其他实验数据。
  - `templete/project.db` 是新建工程时的模板；如需调整工程库结构，请先在目标项目的 `project.db` 上验证，评审通过后再更新模板并同步示例工程。
- Tests: add under `tests/` when introduced (see below).

## Build, Test, and Development Commands
- Out-of-source build (Windows, MinGW):
  ```bat
  mkdir build && cd build
  qmake ..\T_DESIGNER.pro
  mingw32-make -j
  ```
- MSVC toolchain: replace `mingw32-make` with `nmake`.
- Qt Creator: open `T_DESIGNER.pro`, choose Kit, then Run.
- Run: exe appears in `build\debug\` or `build\release\`.
- Clean: from the build dir run `make clean` or delete `build/`.

## Coding Style & Naming Conventions
- Language: C++ (Qt 5.12). Indentation 4 spaces, UTF-8 with BOM; preserve existing line endings (CRLF on Windows is fine).
- Naming: Classes PascalCase (e.g., `DialogConnectAttr`); methods/variables lowerCamelCase; macros/constants ALL_CAPS.
- Files: header/source paired and same base name; UI files mirror class (e.g., `dialogconnectattr.ui`).
- Formatting: use `clang-format` (Qt or Google style); keep consistent across files.

## Testing Guidelines
- Framework: Qt Test. Place tests in `tests/` with names like `something_test.cpp`.
- Scope: cover key business logic and interactions of custom widgets.
- Run: add test target(s) to `.pro`, build, then execute produced test binaries.

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
- 调整 T-Designer 工程数据库结构时：① 在工程目录的 `project.db` 上迭代验证；② 评审通过后更新 `templete/project.db`；③ 视需要同步更新 `MyProjects/` 中的示例工程并记录迁移步骤。
- All project source files use **UTF-8 with BOM** encoding format. 所有项目源文件必须保存为 UTF-8 with BOM 编码。
- When using Chinese text in code, do not use `tr()` or `QStringLiteral`; use double-quoted string literals (e.g., `"中文文本"`) or `QString("中文文本")`. 在代码中直接书写中文时，请不要调用 `tr()` 或 `QStringLiteral`，应直接使用双引号字符串（例如 `"中文"`）或 `QString("中文")`。
