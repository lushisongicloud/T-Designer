# Repository Guidelines

## Project Structure & Module Organization
- Root: `T_DESIGNER.pro`; sources (`.cpp/.h`) and Qt UI forms (`.ui`) live in root and subfolders.
- Modules: `widget/` (custom controls & dialogs), `BO/` (business objects), `DO/` (data objects).
- Resources: `image.qrc`, icons (e.g., `T_DESIGNER.ico`).
- Data/Tools: `Model.db` (sample data), `generate_file_tree.py` (dev helper).
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
- Language: C++ (Qt 5). Indentation 4 spaces, UTF-8 with BOM; preserve existing line endings (CRLF on Windows is fine).
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
- Do not commit sensitive config or local paths. `Model.db` is demo-only; avoid destructive writes.
- Runtime deps: Qt, SQLite (`sqlitedatabase.*`), optional Z3 (`z3solverthread.*`). Ensure required DLLs are in `PATH`.

## Agent-Specific Instructions
- Scope: this file applies repo-wide. Prefer small, reversible changes; avoid unrelated refactors.
- Do not edit generated files (e.g., `ui_*.h`).
- When adding/removing sources, update `T_DESIGNER.pro` accordingly.
- Put helper scripts in `tools/` or repo root and document purpose.
- All project source files use **UTF-8 with BOM** encoding format. 所有项目源文件必须保存为 UTF-8 with BOM 编码。
- When using Chinese text in code, do not use `tr()` or `QStringLiteral`; use double-quoted string literals (e.g., `"中文文本"`) or `QString("中文文本")`. 在代码中直接书写中文时，请不要调用 `tr()` 或 `QStringLiteral`，应直接使用双引号字符串（例如 `"中文"`）或 `QString("中文")`。
