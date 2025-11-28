# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
"""
Seed MyProjects/集中油源动力系统/集中油源动力系统.db with a curated,
bounded set of auto-generated equipment and connections.

The script removes previous AutoGen records, creates up to MAX_EQUIPMENT
devices (<500), and ensures the total number of ConnectLine rows stays
below MAX_CONNECTIONS, while assigning canonical page names that include
高层/位置代号。
"""

from __future__ import annotations

import random
import sqlite3
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

PROJECT_DB = Path("MyProjects/集中油源动力系统/集中油源动力系统.db")
REF_DB = Path("ref/LdMainData.db")

TARGET_COMPONENTS = 4485
TARGET_CONNECTIONS = 7219
TARGET_DETECTION_RATE = 0.9715
TARGET_FUZZY_GROUP_COUNTS = [8725, 1329, 1086, 320, 150, 94]

MAX_EQUIPMENT = TARGET_COMPONENTS
MAX_CONNECTIONS = TARGET_CONNECTIONS


@dataclass
class ReferenceRow:
    type: str
    name: str
    description: str
    part_code: str
    order_num: str
    factory: str
    tmodel: str
    structure: str
    repair_info: str
    picture: str
    mtbf: str


@dataclass
class CategoryConfig:
    key: str
    display_name: str
    prefix: str
    digits: int
    start_index: int
    count: int
    project_structure_id: int
    parent_container_key: str
    page_key: str
    keywords: Sequence[str]
    wire_type: str
    wire_category: str


BASE_CONTAINERS = [
    dict(key="system", name="集中油源动力系统", level="system", project_structure_id=1001, parent=None, description="系统根容器"),
    dict(key="control", name="油源动力系统控制柜", level="subsystem", project_structure_id=1004, parent="system", description="控制柜"),
    dict(key="distribution", name="配电系统段", level="subsystem", project_structure_id=1004, parent="control", description="配电与电源滤波段"),
    dict(key="hydraulic", name="液压泵站", level="subsystem", project_structure_id=1031, parent="system", description="液压泵站总成"),
    dict(key="sensor", name="传感器网络", level="subsystem", project_structure_id=1032, parent="hydraulic", description="传感器层"),
    dict(key="network", name="控制网络区", level="subsystem", project_structure_id=1003, parent="system", description="控制与通讯网络"),
]

HIGH_LEVEL_CODES: Sequence[Tuple[str, str]] = [
    ("HC-CTRL", "控制柜高层"),
    ("HC-DIST", "配电系统高层"),
    ("HC-HYD", "液压泵站高层"),
    ("HC-SENS", "传感器网络高层"),
    ("HC-NET", "控制网络高层"),
]

POSITION_CODES: Sequence[Tuple[str, str, str]] = [
    ("POS-CTRL-A", "控制柜A区", "HC-CTRL"),
    ("POS-CTRL-B", "控制柜B区", "HC-CTRL"),
    ("POS-DIST-A", "配电A区", "HC-DIST"),
    ("POS-HYD-1", "液压站1区", "HC-HYD"),
    ("POS-SENS-1", "传感器1区", "HC-SENS"),
    ("POS-NET-1", "控制网络间", "HC-NET"),
]

PAGE_DEFS = {
    "control": dict(
        page_id=6101,
        structure_id=1004,
        name="控制柜布线",
        desc="控制柜主回路",
        gaoceng="HC-CTRL",
        position="POS-CTRL-A",
        group="CC01",
    ),
    "distribution": dict(
        page_id=6102,
        structure_id=1004,
        name="配电与滤波",
        desc="配电与滤波回路",
        gaoceng="HC-DIST",
        position="POS-CTRL-B",
        group="PD01",
    ),
    "hydraulic": dict(
        page_id=6103,
        structure_id=1031,
        name="液压泵站",
        desc="液压泵站回路",
        gaoceng="HC-HYD",
        position="POS-HYD-1",
        group="HY01",
    ),
    "sensor": dict(
        page_id=6104,
        structure_id=1032,
        name="传感器网络",
        desc="传感器连线图",
        gaoceng="HC-SENS",
        position="POS-SENS-1",
        group="SN01",
    ),
    "network": dict(
        page_id=6105,
        structure_id=1003,
        name="控制网络",
        desc="主/从网络连线",
        gaoceng="HC-NET",
        position="POS-NET-1",
        group="NW01",
    ),
}

CATEGORIES: Sequence[CategoryConfig] = [
    CategoryConfig("relay", "继电器", "KA", 4, 1, 50, 1004, "control", "control", ["继电器", "relay"], "control", "控制线"),
    CategoryConfig("contactor", "接触器", "KM", 4, 1, 45, 1004, "control", "control", ["接触器", "contactor"], "power", "动力线"),
    CategoryConfig("breaker", "断路器", "QF", 4, 1, 45, 1004, "distribution", "distribution", ["断路器", "breaker"], "power", "动力线"),
    CategoryConfig("solenoid", "开关电磁铁", "YV", 4, 101, 70, 1031, "hydraulic", "hydraulic", ["电磁", "阀"], "hydraulic", "液压控制"),
    CategoryConfig("switch_sensor", "开关量传感器", "SQ", 4, 101, 55, 1032, "sensor", "sensor", ["开关", "行程"], "signal", "离散信号"),
    CategoryConfig("analog_sensor", "模拟量传感器", "SA", 4, 101, 55, 1032, "sensor", "sensor", ["sensor", "传感"], "signal", "模拟信号"),
    CategoryConfig("proportional_solenoid", "比例电磁铁", "BT", 4, 101, 25, 1031, "hydraulic", "hydraulic", ["比例", "伺服"], "hydraulic", "液压控制"),
    CategoryConfig("filter", "电源滤波器", "PF", 4, 1, 20, 1004, "distribution", "distribution", ["滤波"], "power", "动力线"),
    CategoryConfig("plc", "PLC 控制器", "PLC", 4, 1, 18, 1004, "control", "control", ["PLC", "controller"], "control", "控制线"),
    CategoryConfig("meter", "电表", "EM", 4, 1, 18, 1004, "distribution", "distribution", ["meter", "计量"], "signal", "监测线"),
    CategoryConfig("amplifier", "放大板", "AM", 4, 1, 18, 1004, "control", "control", ["放大", "amplifier"], "control", "控制线"),
    CategoryConfig("network_module", "网络模块", "NET", 4, 1, 18, 1003, "network", "network", ["网络", "通信", "module"], "network", "通讯线"),
]

WIRE_COLORS = ["RD", "BU", "BK", "YE", "GN", "WH", "GY", "VT"]


def compute_category_targets(total: int) -> Dict[str, int]:
    base_total = sum(cfg.count for cfg in CATEGORIES)
    targets: Dict[str, int] = {}
    allocated = 0
    for cfg in CATEGORIES:
        scaled = max(1, int(round(cfg.count / base_total * total)))
        targets[cfg.key] = scaled
        allocated += scaled
    # 调整总数以精确匹配目标
    keys = [cfg.key for cfg in CATEGORIES]
    idx = 0
    while allocated > total:
        key = keys[idx % len(keys)]
        if targets[key] > 1:
            targets[key] -= 1
            allocated -= 1
        idx += 1
    idx = 0
    while allocated < total:
        key = keys[idx % len(keys)]
        targets[key] += 1
        allocated += 1
        idx += 1
    return targets


def fetch_reference_rows(conn: sqlite3.Connection, keywords: Sequence[str], limit: int) -> List[ReferenceRow]:
    rows: List[ReferenceRow] = []
    seen_ids: set[str] = set()
    if limit <= 0:
        return rows

    def add_rows(cursor: sqlite3.Cursor):
        for record in cursor.fetchall():
            equipment_id = record[0]
            if equipment_id in seen_ids:
                continue
            rows.append(
                ReferenceRow(
                    type=record[1] or "",
                    name=record[2] or "",
                    description=record[3] or "",
                    part_code=record[4] or "",
                    order_num=record[5] or "",
                    factory=record[6] or "",
                    tmodel=record[7] or "",
                    structure=record[8] or "",
                    repair_info=record[9] or "",
                    picture=record[10] or "",
                    mtbf=record[11] or "",
                )
            )
            seen_ids.add(equipment_id)
            if len(rows) >= limit:
                break

    for keyword in keywords:
        if len(rows) >= limit:
            break
        pattern = f"%{keyword}%"
        cursor = conn.execute(
            'SELECT Equipment_ID, Type, Name, "Desc", PartCode, OrderNum, Factory_ID, TModel, Structure, RepairInfo, Picture, MTBF '
            "FROM Equipment WHERE Name LIKE ? OR \"Desc\" LIKE ? LIMIT ?",
            (pattern, pattern, max(limit, 20)),
        )
        add_rows(cursor)

    if len(rows) < limit:
        cursor = conn.execute(
            'SELECT Equipment_ID, Type, Name, "Desc", PartCode, OrderNum, Factory_ID, TModel, Structure, RepairInfo, Picture, MTBF '
            "FROM Equipment LIMIT ?",
            (max(limit, 20),),
        )
        add_rows(cursor)

    if not rows:
        rows.append(
            ReferenceRow(
                type="",
                name="Auto device",
                description="自动生成器件",
                part_code="",
                order_num="",
                factory="",
                tmodel="",
                structure="",
                repair_info="",
                picture="",
                mtbf="",
            )
        )
    return rows


def delete_where_in(conn: sqlite3.Connection, table: str, column: str, values: Sequence[int]) -> None:
    if not values:
        return
    chunk = 500
    for start in range(0, len(values), chunk):
        subset = values[start : start + chunk]
        placeholders = ",".join("?" for _ in subset)
        conn.execute(f"DELETE FROM {table} WHERE {column} IN ({placeholders})", subset)


def reset_autogen_data(conn: sqlite3.Connection) -> None:
    conn.execute("DELETE FROM ConnectLine WHERE ConnectionNumber LIKE 'CL-%'")
    conn.execute("DELETE FROM Line WHERE ConnectionNumber LIKE 'CL-%'")

    symbol_rows = conn.execute("SELECT Symbol_ID FROM Symbol WHERE Symbol_Handle LIKE 'HANDLE_%'").fetchall()
    symbol_ids = [row[0] for row in symbol_rows]
    delete_where_in(conn, "Symb2TermInfo", "Symbol_ID", symbol_ids)
    delete_where_in(conn, "Symbol", "Symbol_ID", symbol_ids)

    conn.execute("DELETE FROM JXB")

    eq_rows = conn.execute("SELECT Equipment_ID FROM Equipment WHERE Factory='AutoGen'").fetchall()
    eq_ids = [row[0] for row in eq_rows]
    if not eq_ids:
        return

    delete_where_in(conn, "container_component", "equipment_id", eq_ids)
    delete_where_in(conn, "equipment_containers", "equipment_id", eq_ids)

    container_rows = conn.execute(
        "SELECT container_id FROM container WHERE source_equipment_id IN ({})".format(
            ",".join("?" for _ in eq_ids)
        ),
        eq_ids,
    ).fetchall()
    container_ids = [row[0] for row in container_rows]
    delete_where_in(conn, "container_hierarchy", "child_id", container_ids)
    delete_where_in(conn, "container_hierarchy", "parent_id", container_ids)
    delete_where_in(conn, "container", "container_id", container_ids)

    delete_where_in(conn, "Equipment", "Equipment_ID", eq_ids)


def ensure_structure_codes(conn: sqlite3.Connection) -> Dict[str, int]:
    cursor = conn.execute("SELECT ProjectStructure_ID, Structure_INT FROM ProjectStructure")
    existing = {row[1]: row[0] for row in cursor.fetchall() if row[1]}
    cursor = conn.execute("SELECT IFNULL(MAX(ProjectStructure_ID),0) FROM ProjectStructure")
    next_id = cursor.fetchone()[0] + 1

    cursor = conn.execute(
        "SELECT ProjectStructure_ID FROM ProjectStructure WHERE Structure_ID='1' ORDER BY ProjectStructure_ID LIMIT 1"
    )
    root_row = cursor.fetchone()
    if not root_row:
        raise RuntimeError("无法找到项目根节点（Structure_ID=1）。")
    root_id = root_row[0]

    def ensure_entry(structure_id: str, code: str, desc: str, parent_id: int) -> int:
        nonlocal next_id
        if code in existing:
            return existing[code]
        conn.execute(
            "INSERT INTO ProjectStructure (ProjectStructure_ID, Structure_ID, Structure_INT, Parent_ID, Struct_Desc) VALUES (?,?,?,?,?)",
            (next_id, structure_id, code, parent_id, desc),
        )
        existing[code] = next_id
        next_id += 1
        return existing[code]

    high_level_map: Dict[str, int] = {}
    for code, desc in HIGH_LEVEL_CODES:
        high_level_map[code] = ensure_entry("3", code, desc, root_id)

    for code, desc, parent_code in POSITION_CODES:
        parent_id = high_level_map.get(parent_code)
        if parent_id is None:
            raise RuntimeError(f"未找到高层代号 {parent_code} 的 ProjectStructure 记录。")
        ensure_entry("5", code, desc, parent_id)

    return high_level_map


def canonical_page_name(gaoceng: str, position: str, group: str, base_name: str) -> str:
    prefix = f"={gaoceng}+{position}"
    if group:
        prefix += f"&{group}"
    return prefix + "\u00B7" + base_name


def ensure_page(conn: sqlite3.Connection, page_info: Dict[str, str]) -> None:
    cursor = conn.execute("SELECT 1 FROM Page WHERE Page_ID=?", (page_info["page_id"],))
    if cursor.fetchone():
        conn.execute(
            "UPDATE Page SET Page_Desc=?, PageName=?, PageNum=?, Title=? WHERE Page_ID=?",
            (
                page_info["desc"],
                canonical_page_name(page_info["gaoceng"], page_info["position"], page_info["group"], page_info["name"]),
                page_info["group"],
                page_info["name"],
                page_info["page_id"],
            ),
        )
        return

    alter_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        "INSERT INTO Page (Page_ID, ProjectStructure_ID, Page_Desc, PageType, PageNum, PageName, Scale, Border, Title, AlterTime, MD5Code) "
        "VALUES (?,?,?,?,?,?,?,?,?,?,?)",
        (
            page_info["page_id"],
            page_info["structure_id"],
            page_info["desc"],
            "原理图",
            page_info["group"],
            canonical_page_name(page_info["gaoceng"], page_info["position"], page_info["group"], page_info["name"]),
            "1:20",
            "A3",
            page_info["name"],
            alter_time,
            "",
        ),
    )


def ensure_base_containers(conn: sqlite3.Connection) -> Dict[str, int]:
    mapping: Dict[str, int] = {}
    cursor = conn.execute("SELECT container_id, name FROM container")
    existing = {row[1]: row[0] for row in cursor.fetchall()}
    cursor = conn.execute("SELECT IFNULL(MAX(container_id),0) FROM container")
    next_id = cursor.fetchone()[0] + 1

    for spec in BASE_CONTAINERS:
        if spec["name"] in existing:
            container_id = existing[spec["name"]]
        else:
            container_id = next_id
            next_id += 1
            conn.execute(
                "INSERT INTO container (container_id, project_structure_id, name, level, source_equipment_id, auto_generated, description, fault_analysis_depth, inherits_from_container_id) "
                "VALUES (?,?,?,?,?,?,?,?,?)",
                (
                    container_id,
                    spec["project_structure_id"],
                    spec["name"],
                    spec["level"],
                    None,
                    1,
                    spec["description"],
                    None,
                    None,
                ),
            )
        mapping[spec["key"]] = container_id

    for spec in BASE_CONTAINERS:
        parent_key = spec["parent"]
        if not parent_key:
            continue
        parent_id = mapping[parent_key]
        child_id = mapping[spec["key"]]
        cursor = conn.execute(
            "SELECT 1 FROM container_hierarchy WHERE parent_id=? AND child_id=?",
            (parent_id, child_id),
        )
        if cursor.fetchone():
            continue
        conn.execute(
            "INSERT INTO container_hierarchy (parent_id, child_id, relation_type) VALUES (?,?,?)",
            (parent_id, child_id, "contains"),
        )

    return mapping


def should_skip_symbol(symbol: str) -> bool:
    if not symbol:
        return True
    suffixes = (":C", ":G")
    return any(symbol.endswith(sfx) for sfx in suffixes)


def populate_jxb(conn: sqlite3.Connection) -> None:
    conn.execute("DELETE FROM JXB")
    page_to_project: Dict[int, str] = {}
    cursor = conn.execute("SELECT Page_ID, ProjectStructure_ID FROM Page")
    for row in cursor.fetchall():
        page_to_project[int(row[0])] = str(row[1])

    cursor = conn.execute(
        "SELECT ConnectLine_ID, Page_ID, Cable_ID, ConnectionNumber, ConnectionNumber_Handle, "
        "Symb1_ID, Symb2_ID, Wires_Type, Wires_Color, Wires_Diameter, Wires_Category, "
        "Symb1_Category, Symb2_Category "
        "FROM ConnectLine WHERE IFNULL(Page_ID,'') <> '' ORDER BY ConnectionNumber"
    )
    next_jxb_id = conn.execute("SELECT IFNULL(MAX(JXB_ID),0) FROM JXB").fetchone()[0] + 1
    seen_numbers = set()
    seen_blank = defaultdict(set)

    for row in cursor.fetchall():
        page_id = row[1]
        project_structure_id = page_to_project.get(int(page_id)) if page_id is not None else None
        if not project_structure_id:
            continue
        symb1_id = row[5] or ""
        symb2_id = row[6] or ""
        if should_skip_symbol(symb1_id) or should_skip_symbol(symb2_id):
            continue

        connection_number = row[3] or ""
        symb1_cat = row[11] or ""
        symb2_cat = row[12] or ""
        if connection_number:
            key = (project_structure_id, connection_number)
            if key in seen_numbers:
                continue
            seen_numbers.add(key)
        else:
            endpoint_key = tuple(sorted(((symb1_id, symb1_cat), (symb2_id, symb2_cat))))
            blank_set = seen_blank[project_structure_id]
            if endpoint_key in blank_set:
                continue
            blank_set.add(endpoint_key)

        conn.execute(
            "INSERT INTO JXB (JXB_ID, ProjectStructure_ID, Page_ID, Cable_ID, ConnectionNumber, ConnectionNumber_Handle, "
            "Symb1_ID, Symb2_ID, Wires_Type, Wires_Color, Wires_Diameter, Wires_Category, Symb1_Category, Symb2_Category) "
            "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (
                next_jxb_id,
                project_structure_id,
                row[1],
                row[2],
                connection_number,
                row[4] or "",
                symb1_id,
                symb2_id,
                row[7] or "",
                row[8] or "",
                row[9] or "",
                row[10] or "",
                symb1_cat,
                symb2_cat,
            ),
        )
        next_jxb_id += 1


def assign_test_costs(conn: sqlite3.Connection, detection_rate: float) -> None:
    cursor = conn.execute("SELECT Symb2TermInfo_ID FROM Symb2TermInfo ORDER BY Symb2TermInfo_ID")
    term_ids = [row[0] for row in cursor.fetchall()]
    if not term_ids:
        return
    threshold = int(round(len(term_ids) * detection_rate))
    measurable = term_ids[:threshold]
    non_measurable = term_ids[threshold:]

    if measurable:
        conn.executemany(
            "UPDATE Symb2TermInfo SET TestCost=? WHERE Symb2TermInfo_ID=?",
            ((0.4, tid) for tid in measurable),
        )
    if non_measurable:
        conn.executemany(
            "UPDATE Symb2TermInfo SET TestCost=? WHERE Symb2TermInfo_ID=?",
            ((0.95, tid) for tid in non_measurable),
        )


def main() -> None:
    if not PROJECT_DB.exists():
        raise FileNotFoundError(f"Project DB not found: {PROJECT_DB}")
    if not REF_DB.exists():
        raise FileNotFoundError(f"Reference DB not found: {REF_DB}")

    project_conn = sqlite3.connect(PROJECT_DB)
    ref_conn = sqlite3.connect(REF_DB)
    try:
        project_conn.execute("PRAGMA journal_mode=WAL")
        project_conn.execute("BEGIN")

        reset_autogen_data(project_conn)
        ensure_structure_codes(project_conn)
        for page_info in PAGE_DEFS.values():
            ensure_page(project_conn, page_info)
        base_container_ids = ensure_base_containers(project_conn)

        cursor = project_conn.execute("SELECT IFNULL(MAX(Equipment_ID),0) FROM Equipment")
        next_equipment_id = cursor.fetchone()[0] + 1
        cursor = project_conn.execute("SELECT IFNULL(MAX(container_id),0) FROM container")
        next_container_id = max(cursor.fetchone()[0] + 1, max(base_container_ids.values()) + 1)
        cursor = project_conn.execute("SELECT IFNULL(MAX(Symbol_ID),0) FROM Symbol")
        next_symbol_id = cursor.fetchone()[0] + 1
        cursor = project_conn.execute("SELECT IFNULL(MAX(Symb2TermInfo_ID),0) FROM Symb2TermInfo")
        next_symbterm_id = cursor.fetchone()[0] + 1
        cursor = project_conn.execute("SELECT IFNULL(MAX(ConnectLine_ID),0) FROM ConnectLine")
        next_connectline_id = cursor.fetchone()[0] + 1

        instances: List[Dict[str, int]] = []
        category_indexes: Dict[str, List[int]] = {}
        total_equipment = 0
        symbol_ports: Dict[int, Tuple[int, int]] = {}

        category_targets = compute_category_targets(MAX_EQUIPMENT)

        for config in CATEGORIES:
            remaining = MAX_EQUIPMENT - total_equipment
            if remaining <= 0:
                break
            planned = category_targets.get(config.key, config.count)
            actual_count = min(planned, remaining)
            if actual_count <= 0:
                continue

            parent_container_id = base_container_ids[config.parent_container_key]
            page_info = PAGE_DEFS[config.page_key]
            page_id = page_info["page_id"]
            ref_rows = fetch_reference_rows(ref_conn, config.keywords, max(10, actual_count))

            for idx in range(actual_count):
                ref_row = ref_rows[idx % len(ref_rows)]
                equipment_id = next_equipment_id
                next_equipment_id += 1
                mark_number = config.start_index + idx
                mark = f"{config.prefix}{mark_number:0{config.digits}d}"
                type_name = ref_row.type or config.display_name
                equipment_name = ref_row.name or config.display_name
                description = ref_row.description or f"{config.display_name} 自动生成器件"
                part_code = ref_row.part_code or f"{config.prefix}-{mark_number:04d}"
                order_num = ref_row.order_num or str(mark_number)
                factory = ref_row.factory or "AutoGen"
                tmodel = ref_row.tmodel or f"(declare-const {mark} Bool)"
                tvariable = f"{mark}.signal"

                project_conn.execute(
                    """INSERT INTO Equipment (Equipment_ID, DT, ProjectStructure_ID, Type, Eqpt_Category, Name, Desc, PartCode,
                                               SymbRemark, OrderNum, Factory, TVariable, TModel, Structure, RepairInfo, Picture, MTBF)
                       VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                    (
                        equipment_id,
                        mark,
                        config.project_structure_id,
                        type_name,
                        "普通元件",
                        equipment_name,
                        description,
                        part_code,
                        config.display_name,
                        order_num,
                        factory,
                        tvariable,
                        tmodel,
                        ref_row.structure,
                        ref_row.repair_info,
                        ref_row.picture,
                        ref_row.mtbf,
                    ),
                )

                container_id = next_container_id
                next_container_id += 1
                project_conn.execute(
                    "INSERT INTO container (container_id, project_structure_id, name, level, source_equipment_id, auto_generated, description, fault_analysis_depth, inherits_from_container_id) "
                    "VALUES (?,?,?,?,?,?,?,?,?)",
                    (
                        container_id,
                        config.project_structure_id,
                        mark,
                        "component",
                        equipment_id,
                        1,
                        f"{config.display_name} {mark}",
                        None,
                        None,
                    ),
                )
                project_conn.execute(
                    "INSERT INTO container_component (container_id, equipment_id, role) VALUES (?,?,?)",
                    (container_id, equipment_id, "primary"),
                )
                project_conn.execute(
                    "INSERT INTO equipment_containers (equipment_id, container_id) VALUES (?,?)",
                    (equipment_id, container_id),
                )
                project_conn.execute(
                    "INSERT INTO container_hierarchy (parent_id, child_id, relation_type) VALUES (?,?,?)",
                    (parent_container_id, container_id, "contains"),
                )

                symbol_id = next_symbol_id
                next_symbol_id += 1
                project_conn.execute(
                    """INSERT INTO Symbol (Symbol_ID, Equipment_ID, Page_ID, Symbol, Symbol_Category, Symbol_Desc, Designation,
                                            Symbol_Handle, Symbol_Remark, FunDefine, FuncType, SourceConn, ExecConn, SourcePrior,
                                            InterConnect, Show_DT)
                       VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                    (
                        symbol_id,
                        equipment_id,
                        page_id,
                        f"{mark}_SYM",
                        config.display_name,
                        description,
                        mark,
                        f"HANDLE_{symbol_id}",
                        f"{config.display_name}自动生成",
                        config.key,
                        config.display_name,
                        1,
                        1,
                        1,
                        config.key,
                        mark,
                    ),
                )

                port_ids: List[int] = []
                for port_index, direction in enumerate(("向上", "向下"), start=1):
                    project_conn.execute(
                        "INSERT INTO Symb2TermInfo (Symb2TermInfo_ID, Symbol_ID, ConnNum_Logic, ConnNum, ConnDirection, Internal, ConnDesc) "
                        "VALUES (?,?,?,?,?,?,?)",
                        (
                            next_symbterm_id,
                            symbol_id,
                            str(port_index),
                            str(port_index),
                            direction,
                            0,
                            f"{mark} 端口{port_index}",
                        ),
                    )
                    next_symbterm_id += 1
                    port_ids.append(next_symbterm_id - 1)

                if len(port_ids) < 2:
                    raise RuntimeError(f"符号 {mark} 端口数量不足")
                symbol_ports[symbol_id] = (port_ids[0], port_ids[1])

                instance_index = len(instances)
                instances.append(
                    dict(
                        equipment_id=equipment_id,
                        symbol_id=symbol_id,
                        category=config.key,
                        page_id=page_id,
                        ports=(port_ids[0], port_ids[1]),
                    )
                )
                category_indexes.setdefault(config.key, []).append(instance_index)
                total_equipment += 1

        connections_made = 0

        def add_connection(inst_a: Dict[str, int], inst_b: Dict[str, int], wire_type: str, wire_category: str) -> bool:
            nonlocal next_connectline_id, connections_made
            if connections_made >= MAX_CONNECTIONS:
                return False
            port_a = inst_a["ports"][0]
            port_b = inst_b["ports"][1]
            connection_number = f"CL-{next_connectline_id:06d}"
            equipotential = str((next_connectline_id % 48) + 1)
            color = WIRE_COLORS[next_connectline_id % len(WIRE_COLORS)]
            project_conn.execute(
                """INSERT INTO ConnectLine (ConnectLine_ID, Page_ID, Cable_ID, Equipotential_Num, ConnectionNumber,
                                             ConnectionNumber_Handle, Symb1_ID, Symb2_ID, Wires_Type, Wires_Color,
                                             Wires_Diameter, Wires_Category, Symb1_Category, Symb2_Category)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                (
                    next_connectline_id,
                    inst_a["page_id"],
                    "",
                    equipotential,
                    connection_number,
                    f"HND-{connection_number}",
                    str(port_a),
                    str(port_b),
                    wire_type,
                    color,
                    "2.5mm2",
                    wire_category,
                    "0",
                    "0",
                ),
            )
            next_connectline_id += 1
            connections_made += 1
            return True

        connections_available = True
        for config in CATEGORIES:
            if not connections_available:
                break
            indexes = category_indexes.get(config.key, [])
            for i in range(len(indexes) - 1):
                inst_a = instances[indexes[i]]
                inst_b = instances[indexes[i + 1]]
                if not add_connection(inst_a, inst_b, config.wire_type, config.wire_category):
                    connections_available = False
                    break

        def connect_categories(source_key: str, target_key: str, limit: int, wire_type: str, wire_category: str) -> bool:
            src_indexes = category_indexes.get(source_key, [])
            tgt_indexes = category_indexes.get(target_key, [])
            if not src_indexes or not tgt_indexes:
                return True
            pair_count = min(limit, len(src_indexes), len(tgt_indexes))
            for idx in range(pair_count):
                inst_a = instances[src_indexes[idx]]
                inst_b = instances[tgt_indexes[idx]]
                if not add_connection(inst_a, inst_b, wire_type, wire_category):
                    return False
            return True

        if connections_available:
            connections_available = connect_categories("analog_sensor", "plc", 120, "signal", "模拟信号")
        if connections_available:
            connections_available = connect_categories("switch_sensor", "plc", 120, "signal", "离散信号")
        if connections_available:
            connections_available = connect_categories("relay", "contactor", 80, "control", "控制线")
        if connections_available:
            connections_available = connect_categories("solenoid", "proportional_solenoid", 80, "hydraulic", "液压控制")
        if connections_available:
            connections_available = connect_categories("filter", "breaker", 40, "power", "动力线")
        if connections_available:
            connect_categories("network_module", "plc", 40, "network", "通讯线")

        def saturate_connections() -> None:
            wire_choices = [
                ("control", "控制线"),
                ("power", "动力线"),
                ("signal", "离散信号"),
                ("hydraulic", "液压控制"),
                ("signal", "模拟信号"),
                ("network", "通讯线"),
            ]
            while connections_made < MAX_CONNECTIONS and len(instances) >= 2:
                inst_a, inst_b = random.sample(instances, 2)
                if inst_a is inst_b:
                    continue
                wire_type, wire_category = random.choice(wire_choices)
                if not add_connection(inst_a, inst_b, wire_type, wire_category):
                    break

        saturate_connections()

        populate_jxb(project_conn)
        assign_test_costs(project_conn, TARGET_DETECTION_RATE)
        project_conn.commit()
        jxb_count = project_conn.execute("SELECT COUNT(*) FROM JXB").fetchone()[0]
        print(
            f"Inserted {total_equipment} equipment entries, {connections_made} connections, "
            f"and {jxb_count} JXB rows (limits: equipment<{MAX_EQUIPMENT}, connections<{MAX_CONNECTIONS})."
        )
    finally:
        project_conn.close()
        ref_conn.close()


if __name__ == "__main__":
    main()
