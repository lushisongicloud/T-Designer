**【分类依据】本文件记录了具体的修复过程、调试分析或已过时的设计实现，作为问题解决的临时记录保留。具体分类原因与依据请参考: docs/archive/MOVED_DOCUMENTS_SUMMARY.md**

# Database Unification & Testability Schema

## Objectives
- Replace the multi-database layout (`project.db` + ad-hoc `Model.db`) with a single project database that stores topology, component models, hierarchical containers, functions, and test assets.
- Provide durable storage for the functional and testability workflow defined in `docs/本开发周期的功能总要求.txt`, including hierarchical aggregation, SMT-based behaviour definitions, automatic test generation, D-matrix storage, and diagnostic decision trees.
- Preserve backward compatibility with the existing electrical design data until UI/business logic is migrated.

## Existing Assets
| Origin | Purpose | Notes |
|--------|---------|-------|
| `templete/project.db` | Electrical设计 baseline (Equipment, Page, Symbol…) + unified schema. | Includes container/function/test tables seeded via `tools/update_template_db.py`. |
| `DemoProjectBuilder` | Generates DemoWorkflow project. | Copies template `.db` and seeds normalized + legacy (`containers`) data for compatibility. |
| `MyProjects/DemoSystem` | Livingstone-based reference project. | Proves end-to-end diagnostic flow. |
| `ref/Model.db` | SMT-oriented component/system/function samples. | Data model used by `systementity.cpp` / `selectfunctiondialog.cpp`. |

## Unified Schema Overview
The single project database keeps legacy CAD data, imports the `Model.db` structures, and introduces new normalized tables to satisfy the functional workflow.

### Reused Tables
- `ProjectStructure`, `Equipment`, `Symbol`, `Symb2TermInfo`, `Page`, `JXB`, `Function`, … (legacy)
- `components`, `parameters`, `models` (from former `Model.db`)

### New Core Tables
| Table | Purpose | Key Fields / Relationships |
|-------|---------|----------------------------|
| `container` | Typed hierarchical nodes (system, subsystem, LRU, …, component). | `container_id` PK, `project_structure_id` FK (`ProjectStructure`), `level` (enum), `source_equipment_id` FK (`Equipment`), `fault_analysis_depth`, `description`. |
| `container_hierarchy` | Parent/child relationships between containers. | (`parent_id`, `child_id`) PK, cascaded deletes. |
| `container_component` | Many-to-many mapping between containers and `Equipment`. | (`container_id`, `equipment_id`) PK. |
| `container_interface` | Ports exposed by containers. | `interface_id` PK, `direction`, `signal_category`, optional inheritance, FK→`container`. |
| `container_interface_binding` | Binds interfaces to physical symbols / terminals / connections. | Links to `Equipment`, `Terminal`, `ConnectLine`. |
| `container_state` | Behaviour states (normal & faults). | `state_type` (`normal`,`fault`,`unknown`), `derived_from_children`, probability, analysis scope. |
| `container_state_behavior` | SMT/TL snippets for a state. | `representation` column stores `'smt2'`, `'tl'`, `'json'` etc. |
| `container_state_interface` | Constraints per interface per state. | References `container_state` & `container_interface`. |

### Functional Definition Tables
| Table | Purpose |
|-------|---------|
| `function_definition` | User-defined or auto-generated functions tied to a container. |
| `function_io` | Inputs/outputs/assumptions associated with either container interfaces or virtual signals. |
| `function_dependency` | Dependency graph between functions (`requires`, `enables`, etc.). |

### Testability Tables
| Table | Purpose |
|-------|---------|
| `test_definition` | Signal/function/fault-mode tests (auto-generated flag, estimates). |
| `test_fault_coverage` | D-matrix entries: relation of tests to fault states (`detect`, `isolate`, `observe`). |
| `test_constraint` | Cost/time/complexity/resource constraints per test. |
| `analysis_requirement` | Target metrics (detection rate, isolation rate) per container level. |
| `analysis_constraint` | Global constraints applied when selecting candidate tests. |
| `test_plan_candidate` / `test_plan_candidate_item` | Stores optimisation results as candidate test sets. |
| `diagnosis_tree` / `diagnosis_tree_node` | Persist generated diagnostic decision trees. |

### Additional Support Tables
- `interface_signal_template` (optional): canonical signal definitions (voltage, pressure).
- `metric_definition`: metadata for metrics stored in JSON blobs (future-proofing).

### Enumerations
| Enum | Values |
|------|--------|
| `container.level` | `system`, `subsystem`, `lru`, `sru`, `module`, `submodule`, `component`. |
| `container_state.state_type` | `normal`, `fault`, `unknown`. |
| `container_state_behavior.representation` | `smt2`, `tl`, `json`, `text`. |
| `function_io.io_type` | `input`, `output`, `parameter`, `assumption`. |
| `test_definition.test_type` | `signal`, `function`, `fault-mode`. |
| `test_fault_coverage.coverage_type` | `detect`, `isolate`, `observe`. |

## Data Flow Highlights
1. **Project creation**  
   - Copy `templete/project.db` (already contains schema + seed rows).  
   - Demo builder seeds `container`/`function`/`test` rows instead of embedding JSON blobs.
2. **Hierarchical modelling**  
   - Component placement auto-creates a `container` row (`level='component'`, `source_equipment_id` set).  
   - Aggregation UI manages `container_hierarchy`, `container_component`, and derived `container_state` records.  
   - Interface roll-up stored in `container_interface` + `container_state_interface`.
3. **Functional definition**  
   - Functions tie back to container interfaces via `function_io`.  
   - Dependencies recorded in `function_dependency`; supports implicit input propagation per requirement 2.
4. **Automatic test generation**  
   - Signal tests: create `test_definition` with `test_type='signal'` + `interface_id`.  
   - Function tests: `test_type='function'`, reference `function_id`.  
   - Fault-mode tests: `test_type='fault-mode'`, reference `state_id`.  
   - Coverage matrix stored in `test_fault_coverage`.
5. **Testability analysis**  
   - Requirements gathered in `analysis_requirement`.  
   - Constraints persisted in `analysis_constraint` & per-test `test_constraint`.  
   - Candidate optimisation writes `test_plan_candidate` and linking rows.  
   - Decision tree results persisted in `diagnosis_tree_node`.

## Migration Strategy
1. **Schema evolution**  
   - Idempotent `CREATE TABLE IF NOT EXISTS` statements.  
   - Add indices on FK columns (`container.project_structure_id`, `test_definition.container_id`, etc.).  
   - Enable `PRAGMA foreign_keys = ON`.
2. **Data import**  
   - Copy `components`, `parameters`, `models` from legacy `Model.db` into template during build step.  
   - Populate `container` / `container_state` etc. for sample DemoWorkflow using conversion helpers.
3. **Compatibility**  
   - Retain legacy `containers` table (JSON) for interim UI usage; backfill new tables from it.  
   - Introduce sync routines to keep both representations aligned until UI migrates.  
   - Update `SQliteDatabase` to read/write unified tables.

## Follow-Up Work
- Refactor BO/DO layers (`ContainerRepository`, `systementity`, `SelectFunctionDialog`) to target the normalized schema.  
- Extend new tables with auditing metadata (timestamps, authors) once workflows stabilise.  
- Define stored views (e.g., `view_testability_matrix`) to simplify reporting queries.  
- Automate validation with unit tests under `tests/` once schema refactor is wired into code paths.

## Implementation Status (Current Sprint)
- ✅ Template database refreshed via `tools/update_template_db.py`; ships with SMT models (`components`, `parameters`, `models`) and empty normalized tables.  
- ✅ `DemoProjectBuilder` now copies `templete/project.db` and seeds demo data into both legacy JSON columns and the new normalized tables.  
- ✅ Runtime loader (`mainwindow_project.cpp`) opens the unified `.db`; `SQliteDatabase` handles unique connections and works against the same file.  
- ✅ `ContainerRepository` mirrors CRUD operations into `container`, `container_hierarchy`, and `container_component` to keep normalized data in sync.  
- ⏳ Business logic/UI still consume legacy JSON payloads; next steps will migrate readers/writers to normalized structures and expose new function/test tables.
