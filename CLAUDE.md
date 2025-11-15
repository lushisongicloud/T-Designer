# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**T-Designer** is a Qt-based CAD/electrical design software with integrated system modeling, diagnosis, and T-Solver functionality. The project includes:

- **CAD Design Tools**: Electrical schematic design with symbols, connections, and components
- **System Modeling**: SMT-based system modeling using T-Solver integration
- **Diagnosis Engine**: Fault diagnosis with decision trees and test management
- **Model/View Architecture**: Recent migration from QStandardItemModel to Qt Model/View for performance

## Architecture Overview

### Three-Layer Architecture

The project follows a strict **layered architecture** with clear boundaries and dependencies:

#### 1. DO Layer (Data Objects) - `DO/` directory
**Role**: Pure data structures and minimal behaviors
- **Responsibilities**:
  - Domain data models (components, systems, connections, etc.)
  - Value semantics, equality, serialization
  - No UI, database, or business logic dependencies
- **Dependencies**: QtCore only (QString, QVector, QMap, std::*)
- **Key Components**:
  - `component.*` - Component entity structures
  - `model.*` - System model data
  - `parameter.*` - Parameter definitions
  - `containerentity.h` - Container data snapshot

#### 2. BO Layer (Business Objects) - `BO/` directory
**Role**: Business logic, service orchestration, data access
- **Responsibilities**:
  -封装业务规则与用例编排
  - Data persistence and repository patterns
  - Integration with external systems (Z3 solver)
  - Domain-specific algorithms (SMT validation, D-matrix generation)
- **Dependencies**:
  - DO layer
  - QtCore/QtSql
  - No direct UI dependencies
- **Submodules**:
  - `container/` - Container management and aggregation
  - `behavior/` - Algorithms and utilities (Z3 simplification, etc.)
  - `function/` - Function repository and analysis services
  - `test/` - D-matrix and diagnostic services
- **Key Components**:
  - `containerrepository.*` - Data access abstraction
  - `functionrepository.*` - Function management
  - `diagnosticmatrixbuilder.*` - D-matrix generation
  - `tmodelvalidator.*` - SMT validation

#### 3. Widget Layer (UI) - `widget/` directory
**Role**: User interface and interaction
- **Responsibilities**:
  - UI presentation and user interaction
  - Input validation and user feedback
  - Model/View integration
- **Dependencies**:
  - Qt Widgets
  - BO layer services (via clear interfaces)
  - No direct database access
- **Key Components**:
  - Custom dialogs (40+ classes)
  - Model classes (QAbstractItemModel derivatives)
  - Main window modules (`mainwindow_*.cpp`)

### Core Components

#### 4. Main Application (`mainwindow.cpp`, `mainwindow.h`)
- Central application window and event handling
- Project loading and management (`LoadProject()` in `mainwindow_project.cpp`)
- Unit/Equipment management (`mainwindow_units.cpp`)
- Diagnosis UI (`mainwindow_diagnosis.cpp`)
- **Note**: MainWindow logic split across feature-focused files

#### 5. Data Models (`projectdatamodel.h/cpp`)
- **ProjectDataModel**: In-memory project data cache
  - Structures (高层/Position hierarchy)
  - Equipments (Device instances)
  - Symbols (Functional blocks)
  - Connections (Wiring information)
  - Pages (Drawing sheets)
- **Performance**: Loads 5000+ records in <100ms
- **API**: Provides O(1) hash-based queries via manager classes

#### 6. Qt Model/View Components
- **EquipmentTreeModel** (`equipmenttreemodel.h/cpp`): Hierarchical device tree
- **EquipmentTableModel** (`equipmenttablemodel.h/cpp`): Device table view
- **ConnectionTreeModel** (`connectiontreemodel.h/cpp`): Connection tree (by line number)
- **ConnectionByUnitTreeModel** (`connectionbyunittreemodel.h/cpp`): Connection tree (by equipment)
- All inherit from `QAbstractItemModel` or `QAbstractTableModel`

#### 7. Dialogs (`dialog*.cpp`)
- 40+ dialog classes for various UI interactions
- Component management, symbol attributes, terminal configuration
- Function management, test management, diagnosis UI

#### 8. Graphics System (`bqgraphics*.cpp`)
- Custom graphics items and scenes for CAD drawing
- Integration withMxDraw library for DWG support

### Key Design Patterns

1. **Layer Separation**: DO/BO/Widget with clear dependencies
2. **Repository Pattern**: Data access abstraction
3. **Model/View Separation**: Data separated from UI, enabling multiple views
4. **Manager Pattern**: `EquipmentManager`, `SymbolManager`, `ConnectionManager` etc.
5. **In-Memory Caching**: `ProjectDataCache` for fast data access
6. **Performance Timer**: `performancetimer.h` for performance tracking

## T-Solver Integration (Current Sprint Focus)

### Overview
Deep integration of T-Solver modeling, function management, and D-matrix into T-Designer while maintaining legacy compatibility.

### Migration Strategy: Livingstone → SMT/Z3

#### Port/Variable Naming Rules
**Electrical**: `.i` current, `.u` voltage
**Hydraulic**: `.p` pressure, `.q` flow
**Mechanical**: `.F` force, `.x` displacement (optional `.v` velocity, `.n` angular)

Example relay KA1:
```cpp
KA1.Coil.A1.i/u, KA1.Coil.A2.i/u,
KA1.Contact.11.i/u, KA1.Contact.14.i/u, KA1.Contact.12.i/u
```

#### Connection Macro Family Concept
A **Macro Family** is a set of connection macros supporting different port counts (arity). The system automatically selects the appropriate macro based on actual port count.

**Built-in Macro Families** (stored in `port_connect_macro_family`, `is_builtin=1`):
- `electric-connect`: Contains connect2e/3e/4e, generates KCL (Σi=0) + equal potential (u相等)
- `hydraulic-connect`: Contains connect2h/3h/4h, generates flow conservation (Σq=0) + equal pressure
- `mechanical-connect`: Contains connect2m/3m/4m, generates force conservation (ΣF=0) + equal displacement

**Macro Family Data Structure**:
```json
{
  "family_name": "electric-connect",
  "domain": "electric",
  "macros_json": [
    {"arity": 2, "macro_name": "connect2e", "expansion": "..."},
    {"arity": 3, "macro_name": "connect3e", "expansion": "..."}
  ]
}
```

#### CAD → SMT Connection Sugar
Connection macros expand from macro family definitions:
- `connect2e(A,B)`: `(assert (= (+ A.i B.i) 0))` + `(assert (= A.u B.u))`
- `connect3e(A,B,C)`: Σi=0 + equal potential
- Multi-phase arrays: `connect2e(3P, A,B)` expands per phase using `(select X.i 0/1/2)`

### SMT Validation & Port Consistency
**Validation Service** (`tmodelvalidator.*`):
1. **SMT Syntax Check**: Parse and validate SMT-LIB2 syntax
2. **Port/Variable Consistency**: Verify variables match port schema
3. **Shared Service**: Used by both "本地物料库" and "元件属性" UI

**Interface**:
```cpp
ValidationResult validateComponentSmt(const QString& smt, const PortSchema& schema);
```

Returns: Syntax errors, undeclared variables, missing variables, port/variable conflicts

### Function Management (BO/function)
**Reference**: `ref/T-Solver/README.md`

**Capabilities**:
- Link generation from CAD netlist (auto-generated, user-confirmable)
- Dependency chain resolution (device/function triplets)
- Boundary condition completion
- Offline solution caching (`offlineSolveResult`)

**Data Storage** (project DB only):
- Function definitions (tree structure, link, dependency, constraints)
- Attributes (Persistent|NotPersistent, prior probability)
- Variable ranges and sample configurations

### D-Matrix (BO/test)
**Alignment**: T-Solver's `dmatrixviewerdialog` implementation

**Extended Dimensions**:
- **Test**: Complexity, cost, time, success rate, notes
- **Fault**: Probability, severity, notes

**Services**: Generation, merging, filtering, weighted calculation (compatible with existing workflows)

### Container-First Implementation (BO/container)
- Component-level containers proxy single entity component interfaces/behaviors
- New SMT/function/testability logic placed at container and aggregator layer
- Reduces intrusion into entity components

**Container Data** (from DO/containerentity.h):
- SMT variable namespace construction (e.g., `K1.Coil.A1.i`)
- Functional block/port settings from entity components
- SMT/function/testability data views

## Building the Project

### Prerequisites
- Qt 5.12+ (Qt Creator recommended)
- Visual Studio 2019/2022 or MinGW
- QScintilla2 library
- Z3 SMT Solver library (included in `lib/`)
- SQLite3

### Build Commands

```bash
# Using qmake
qmake T_DESIGNER.pro
make -j4  # or nmake on Windows

# In Qt Creator
# 1. Open T_DESIGNER.pro
# 2. Choose Kit (Desktop Qt 5.12.x MSVC2019 64-bit)
# 3. Build (Ctrl+B)
# 4. Run (Ctrl+R)
```

**Note**: The `axcontainer` module is Windows-specific (ActiveX). Full compilation not possible in WSL/Linux environments.

### Output
- Executable: `build/release/T-DESIGNER.exe`
- Dependencies automatically copied during build

## Database & Schema Management

### Database Locations
- **Template**: `templete/project.db` - For new projects
- **Reference**: `ref/LdMainData.db` (offline mirror), `ref/Model.db` (SMT samples)
- **Project-specific**: `MyProjects/<ProjectName>/<ProjectName>.db`
- **Runtime**: `C:/TBD/data/LdMainData.db` (local component library)

### Key Tables
- `ProjectStructure` - Hierarchical structure (高层/Position)
- `Equipment` - Device instances
- `Symbol` - Functional blocks (linked to Equipment)
- `JXB` - Connections/wiring
- `Page` - Drawing pages
- `diagnosis_tree*` - Diagnosis engine tables
- `port_config` - Port configurations (type, variables)
- `port_connect_macro_family` - Connection macro families
- `function_*` - Function management tables
- `dmatrix_*` - D-matrix tables

### Database Change Workflow
**Critical**: Follow "Project First, Template Later" principle:

1. **Validate in Project DB**:
   - Make changes in `MyProjects/<Project>/<Project>.db`
   - Test functionality thoroughly
   - Ensure backward compatibility

2. **Update Template** (only after validation):
   - Use `tools/` migration scripts
   - Update `templete/project.db`
   - Version changes (schema_version table)

3. **Never** modify `templete/project.db` or `ref/*.db` directly

### Database Scripts (tools/)
- `update_template_db.py` - Apply validated changes to template
- `init_builtin_macro_families.py` - Initialize connection macro families
- `migrate_project_db.py` - Apply schema changes to existing projects
- `validate_smt_snippets.py` - Batch validate SMT components
- `export_dmatrix_csv.py` - D-matrix import/export

## Code Style Guidelines

### Naming Conventions
- **Classes**: PascalCase (`EquipmentTreeModel`)
- **Functions/Variables**: camelCase (`loadProjectData()`)
- **Member variables**: `m_` prefix (`m_projectDataModel`)
- **Constants**: UPPER_CASE
- **Qt types**: QString, QVector, QHash, QMap

### Formatting
- **Indentation**: 4 spaces
- **Encoding**: UTF-8 with BOM
- **Line endings**: Unix LF
- **Formatter**: `clang-format` (Qt style)
- **File pairing**: Header and source with same base name

### String Handling
- **Chinese text**: Use double-quoted strings or `QString("中文")`, **NOT** `tr()` or `QStringLiteral`
- **English**: Use `tr()` for UI strings
- **Literal constants**: Avoid in code; use constants

### File Organization
```
Source files: Root directory
  ├── *.cpp/*.h - Implementation and headers
  ├── mainwindow.cpp - Bootstrap
  ├── mainwindow_*.cpp - Feature modules
  └── *.ui - Qt Designer forms

Subdirectories:
  ├── BO/ - Business objects
  ├── DO/ - Data objects
  ├── widget/ - UI controls
  ├── tests/ - Test suites
  ├── tools/ - Scripts and utilities
  ├── MyProjects/ - Sample projects
  └── ref/ - Reference materials
```

## Layer-Specific Guidelines

### DO Layer (Data Objects)
**Focus**: Pure data structures with minimal behavior

**Principles**:
- Lightweight and value semantics
- Copy/move semantics clearly defined (Rule of Five if needed)
- No invariants violations (construct valid)
- Optional fields use `std::optional<T>`
- Provide `operator==` and `qHash` for QSet/QHash
- Serialization: `toJson()`/`fromJson()` if needed

**Prohibited**:
- UI/Widget dependencies
- Direct database access
- Business logic or thread operations

### BO Layer (Business Objects)
**Focus**: Business logic and service orchestration

**Principles**:
- Case-oriented interfaces
- Clear method naming and responsibility division
- Avoid singletons and global mutable state
- Prefer dependency injection
- Asynchronous operations for long tasks (QThread/QRunnable/QtConcurrent)
- Signal/slot for results
- Distinguish "no data" vs "failure" (std::optional + error codes)

**Prohibited**:
- Qt Widgets dependencies
- Blocking UI thread

**Key Components**:
- `containerrepository.*` - Data loading and persistence
- `behavioraggregator.*` - Container business logic
- `functionrepository.*` - Function management
- `diagnosticmatrixbuilder.*` - D-matrix services

### Widget Layer (UI)
**Focus**: User interface and interaction

**Principles**:
- Use Qt Designer for `.ui` files
- Complex data uses QAbstractItemModel
- Clear Role and data() contract
- User actions → signals or BO calls
- Async results via signals (no cross-thread widget access)

**Prohibited**:
- Complex business logic in UI
- Long blocking operations
- Generated files (`ui_*.h`)

**Performance**:
- Delegate heavy tasks to BO Workers
- Use `beginResetModel()/endResetModel()` for batch updates
- UI thread only for light operations

## Testing Strategy

### Testing Framework
- **Qt Test** framework for all tests
- **Location**: `tests/` directory

### Test Naming Convention
- `bo_<area>_test.cpp` - BO layer tests
- `do_<type>_test.cpp` - DO layer tests
- `widget_<model>_test.cpp` - Widget/Model tests

### Current Sprint Testing Focus

**SMT Validation**:
- Syntax error detection and localization
- Undeclared/extra variables
- Port/variable inconsistency reporting
- Positive/negative test cases
- Edge cases (empty models, oversized models, Chinese identifiers)

**Connection Generation**:
- CAD → `connect2e/3e`, `connect2h/3h`, `connect2m/3m` expansion
- Multi-phase arrays (1P/3P) index expansion
- KCL/KVL equation correctness

**Function Management**:
- Link merge/pruning rules
- Dependency function triplet expansion
- Boundary condition deduplication and completion

**D-Matrix**:
- Generation, merge, filtering, weighted strategies
- Extended dimensions (test/fault) read/write consistency
- Legacy workflow compatibility

**Container Layer**:
- Component-level container proxy correctness
- SMT/function/data view accuracy

### Running Tests
```bash
# In out-of-source build directory
make test                # Run all tests
# Or use Qt Creator Test panel
```

### Test Data
- Reference sample projects in `MyProjects/`
- Copy project DBs for testing (don't modify templates)
- Use `ref/Model.db` for SMT reference

## Development Workflow

### Recent Major Changes

1. **Model/View Migration** (2024)
   - Converted from QStandardItemModel/QTableWidget to Qt Model/View
   - Performance improvement: 171s → 2s load time
   - Affected files: `equipmenttreemodel.*`, `equipmenttablemodel.*`, `connectiontreemodel.*`, `connectionbyunittreemodel.*`

2. **ProjectDataModel Optimization**
   - In-memory caching of all project data
   - Eliminated N+1 SQL query problems
   - 43,000+ SQL queries → 0 queries for UI loading

3. **T-Solver Integration** (Current Sprint)
   - SMT-LIB2 migration from Livingstone T-language
   - Function management system overhaul
   - D-matrix enhancement
   - Container-first architecture

### Adding New Features

#### 1. Adding a New Model/View Component
1. Create header: `mynewmodel.h`
2. Create implementation: `mynewmodel.cpp`
3. Inherit from `QAbstractItemModel` or appropriate base class
4. Implement required methods: `rowCount()`, `columnCount()`, `index()`, `parent()`, `data()`
5. Add to `T_DESIGNER.pro` SOURCES/HEADERS
6. Initialize in `MainWindow::InitXXXXX()`

#### 2. Adding New Business Logic (BO Layer)
1. Design DO data structures first
2. Implement BO repository/service
3. Write unit tests (Qt Test)
4. Create widget integration (if needed)
5. Update project documentation

#### 3. Database Schema Changes
1. **Validate in Project**: Modify `MyProjects/<Project>/<Project>.db`
2. **Test Thoroughly**: Verify functionality and backward compatibility
3. **Create Migration Script**: `tools/migrate_<version>.py`
4. **Update Template**: Use `update_template_db.py` after review
5. **Update Documentation**: Record changes and migration steps

### Commit & Pull Request Guidelines

**Conventional Commits**:
```
feat(widget): add port configuration dialog
fix(BO): null check in function repository
docs: update T-Solver integration guide
```

**PR Requirements**:
- Clear description with screenshots for UI changes
- Link to related issues
- List build/verification steps
- Include test coverage for new features

**Prohibited**:
- Modifying generated files (`ui_*.h`)
- Committing sensitive configs or local paths
- Unrelated refactoring

## Performance Optimization

### Current Performance Metrics
- **Load time**: < 2 seconds (large projects >5000 devices)
- **Tree expansion**: < 100ms
- **UI operations**: 0 SQL queries (pure in-memory)

### Performance Best Practices
1. **Avoid SQL in loops** - Pre-load data instead
2. **Use QHash for lookups** - O(1) instead of O(n)
3. **Cache expensive operations** - Structure queries, symbol lookups
4. **Use PerformanceTimer** - Measure before optimizing

### PerformanceTimer Usage
```cpp
PerformanceTimer timer("MyOperation");
// ... code to measure ...
timer.checkpoint("Checkpoint 1");
// ... more code ...
qDebug() << "Total time:" << timer.elapsed() << "ms";
```

### Debugging Performance Issues
```cpp
// Check model is set
if (!ui->treeViewUnits->model()) {
    qWarning() << "Model not set!";
}

// Verify data loading
qDebug() << m_projectDataModel->getStatistics();

// Add checkpoints
timer.checkpoint("Before tree rebuild");
m_equipmentTreeModel->rebuild();
timer.checkpoint("After tree rebuild");
```

## Key Files Reference

### High-Traffic Files
- `mainwindow_project.cpp` - Project loading logic
- `mainwindow_units.cpp` - Equipment/tree operations
- `projectdatamodel.cpp` - Data model implementation
- `equipmenttreemodel.cpp` - Device tree model
- `connectiontreemodel.cpp` - Connection tree model
- `connectionbyunittreemodel.cpp` - Connection-by-unit tree

### T-Solver Integration Files
- `BO/systementity.*` - System modeling
- `BO/function/*` - Function management services
- `BO/test/*` - D-matrix and diagnostic services
- `ref/T-Solver/README.md` - T-Solver reference

### Database Files
- `sqlitedatabase.cpp` - Database connection management
- `projectdatacache.h/cpp` - Caching layer
- `templete/project.db` - New project template
- `tools/*.py` - Database migration scripts

### Configuration Files
- `T_DESIGNER.pro` - Qt project configuration
- `mainwindow.ui` - Main window UI layout
- `image.qrc` - Application resources

## Known Issues & Limitations

### Historical Issues (Resolved)
- ~~N+1 SQL queries in equipment tree~~ - Fixed with Model/View
- ~~QTableWidget performance~~ - Migrated to QTableView
- ~~ConnectionManager column mismatch~~ - Fixed with dynamic column detection

### Current Considerations
- Large projects (>10,000 devices) may need virtual scrolling
- Z3 solver performance depends on model complexity
- Some legacy SQL code remains (search for "QSqlQuery")
- WSL/Linux development limited (Windows-specific axcontainer module)

### Migration Notes
- **Livingstone → T-Solver**: DemoSystem project uses Livingstone for understanding; new features migrate to SMT/Z3
- **Legacy D-matrix**: Maintain compatibility with existing workflows
- **Database Changes**: Always validate in project DB before template updates

## Security & Configuration

### Security Best Practices
- Do not commit sensitive configurations or credentials
- Use `ref/` database copies for validation (not runtime data)
- Runtime loads `C:/TBD/data/LdMainData.db`; mirror in `ref/LdMainData.db` for reference
- Ensure required DLLs (Qt, SQLite, Z3) are in PATH

### Environment Configuration
- Qt 5.12+ installed and configured
- Visual Studio 2019/2022 or MinGW for compilation
- QScintilla2 for syntax highlighting
- Z3 SMT Solver library (included)

## Tips for Development

### Finding Related Code
```bash
# Find all files using a specific manager
grep -r "equipmentMgr->" --include="*.cpp" .

# Find SQL queries
grep -r "QSqlQuery" --include="*.cpp" . | head -20

# Find T-Solver related code
grep -r "connect2e\|connect3e" --include="*.cpp" .
```

### Debugging SQL Issues
- Check `sqlitedatabase.cpp` for connection management
- Use `UI_DATA_ACCESS_ANALYSIS.md` for common anti-patterns
- Verify queries run in project DB first

### Understanding Layer Boundaries
- **DO**: "What is the data?" - Pure structures
- **BO**: "How do we process it?" - Business logic
- **Widget**: "How do we show it?" - Presentation

### Common Development Tasks

#### Adding Port Configuration
1. Update DO layer: Add port/variable structures
2. Implement BO: Port config repository and validator
3. Create widget: PortConfigEditDialog
4. Add tests: Validation logic, UI interactions
5. Update database: Port config tables

#### Implementing SMT Validation
1. DO: Define validation result structures
2. BO: Implement TModelValidator with SMT parser
3. Widget: Add "Validate" button to editors
4. Tests: Positive/negative cases, edge cases

#### Creating Function Management UI
1. BO: FunctionRepository and analysis services
2. Widget: Function management dialog
3. Integration: CAD netlist → function links
4. Tests: Link generation, dependency resolution

## Future Roadmap

### Completed (2024)
- ✅ Model/View migration for equipment views
- ✅ Model/View migration for connection views
- ✅ ProjectDataModel in-memory caching
- ✅ Performance optimization (171s → 2s)
- ✅ T-Solver integration architecture

### Current Sprint (In Progress)
- 🔄 SMT-LIB2 migration from Livingstone
- 🔄 Unified SMT validation service
- 🔄 Port configuration UI
- 🔄 Function management overhaul
- 🔄 D-matrix enhancement
- 🔄 Connection macro families

### Planned Enhancements
- EquipmentTreeFilterProxy (advanced filtering)
- ConnectionTreeFilterProxy (connection filtering)
- Virtual scrolling for ultra-large projects
- Background data loading
- Incremental model updates
- Container-level virtual scrolling

## Documentation References

### Internal Documentation
- `README.md` - T-Solver integration and system modeling
- `ToDo-LoadProject.md` - Performance optimization status
- `FINAL_PERFORMANCE_OPTIMIZATION_REPORT.md` - Model/View migration results
- `DIAGNOSIS_README.md` - Diagnosis engine documentation
- `EQUIPMENT_TREE_PERFORMANCE_OPTIMIZATION.md` - Equipment tree optimization
- `DIAGNOSIS_INTEGRATION_SUMMARY.md` - Complete diagnosis implementation
- `CONNECTION_BY_UNIT_MODEL_REPORT.md` - Connection tree model details
- `MEMORY_MODEL_IMPLEMENTATION.md` - In-memory model design

### Module-Specific Documentation (AGENTS.md)
- `/AGENTS.md` - Repository-wide guidelines
- `/BO/AGENTS.md` - Business objects layer
- `/DO/AGENTS.md` - Data objects layer
- `/widget/AGENTS.md` - UI/Widget layer
- `/tests/AGENTS.md` - Testing strategy
- `/tools/AGENTS.md` - Scripts and tools
- `/MyProjects/AGENTS.md` - Example projects
- `/ref/AGENTS.md` - Reference materials

### Performance Documentation
- `PERFORMANCE_OPTIMIZATION_RESULT.md` - Overall metrics
- `PERFORMANCE_DEBUG_GUIDE.md` - Analysis methods
- `UI_DATA_ACCESS_ANALYSIS.md` - SQL anti-patterns

### T-Solver References
- `ref/T-Solver/README.md` - Core T-Solver documentation
- `ref/Model.db` - SMT samples and structures
- `MyProjects/DemoSystem/` - Legacy Livingstone example

## Support Resources

### Qt Documentation
- [Qt Model/View Programming](https://doc.qt.io/qt-5/model-view-programming.html)
- [QAbstractItemModel](https://doc.qt.io/qt-5/qabstractitemmodel.html)
- [Qt Test Framework](https://doc.qt.io/qt-5/qttest.html)

### External Dependencies
- **Qt Framework**: Core GUI framework
- **QScintilla2**: Syntax highlighting editor component
- **Z3 Solver**: SMT solver for T-Solver integration
- **MxDraw**: CAD drawing library
- **SQLite3**: Database engine

### Tools
- **Qt Creator**: Recommended IDE
- **clang-format**: Code formatting
- **qmake**: Build system
- **sqlite3**: Database CLI (for inspection)

---

**Last Updated**: 2025-11-12
**Major Version**: 2.1 (T-Solver Integration)
**Sprint Focus**: T-Solver Deep Integration
