# Repository Guidelines

## Project Structure & Modules
- Root app: `main.cpp`, `mainwindow.*` (Qt Widgets UI), `Model.db` (SQLite).
- UI: `widget/` (dialogs, e.g., `selectfunctiondialog.*`, `mycombobox.*`), `.ui` forms.
- Domain logic: `BO/` (business objects—solver orchestration), `DO/` (data objects—component, model, parameter).
- Algorithms/infra: `graphadjlist.*`, `solverrunnable.*`, `z3solverthread.*`.
- Docs: `docs/` (technical notes), `README.md`.
- Reference code: `ref/` (legacy or examples). The `build/` folder is generated.

## Build, Test, and Development
- Recommended: Open `T-Solver.pro` in Qt Creator (Qt 5.12.x). Configure a Desktop kit.
- Command line (qmake):
  - Windows (MSVC): `qmake T-Solver.pro && nmake`
  - MinGW: `qmake T-Solver.pro && mingw32-make`
- Z3 setup: Place headers at `include/z3/` and library at `lib/libz3.lib` (or update `.pro` accordingly).
- Runtime: Ensure `Model.db` is present in repo root.
- CMake file is minimal and not maintained—prefer qmake/Qt Creator.

## Coding Style & Naming
- C++17/Qt style, 4-space indentation, no tabs.
- Classes: PascalCase (e.g., `SelectFunctionDialog`); methods/variables: camelCase.
- Signals/slots: Qt conventions; UI slots follow `on_<widget>_<signal>` (e.g., `on_btn_OfflineSolve_clicked`).
- Keep `.h/.cpp/.ui` co-located; avoid unrelated refactors in feature PRs.
- Encoding: UTF-8 for source and docs.

## Testing Guidelines
- No formal unit tests yet. Use manual validation:
  - Launch app, open “选择待诊断的功能” dialog.
  - Load/edit functions, run “检查约束完整性/离线求解”，确认结果表与高亮逻辑。
- If adding tests, prefer Qt Test (QTest). Name tests `tests/<module>_test.cpp` and integrate via qmake.

## Commit & Pull Requests
- Commits: concise, imperative (Chinese or English), e.g., `修复: 依赖功能展开取反逻辑` or `feat(ui): add boundary condition prompt`.
- PRs: include purpose, linked issues, build/run notes, and screenshots/GIFs for UI changes.
- Scope small and focused; include docs updates when changing behavior.

## Security & Configuration Tips
- Do not commit secrets. DB is local sample (`Model.db`).
- Verify Z3 and Qt paths are local; prefer relative paths or environment-configured kits.

