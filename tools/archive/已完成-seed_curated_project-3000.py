# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
"""
Populate MyProjects/集中油源动力系统/集中油源动力系统.db with
large volumes of devices and connections seeded from ref/LdMainData.db.
"""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

PROJECT_DB = Path("MyProjects/集中油源动力系统/集中油源动力系统.db")
REF_DB = Path("ref/LdMainData.db")


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

PAGE_DEFS = {
    "control": dict(page_id=6001, structure_id=1004, name="控制柜布线", desc="控制柜主回路"),
    "distribution": dict(page_id=6002, structure_id=1004, name="配电与滤波", desc="配电与滤波回路"),
    "hydraulic": dict(page_id=6003, structure_id=1031, name="液压泵站", desc="液压泵站回路"),
    "sensor": dict(page_id=6004, structure_id=1032, name="传感器网络", desc="传感器连线图"),
    "network": dict(page_id=6005, structure_id=1003, name="控制网络", desc="主/从网络连线"),
}

CATEGORIES: Sequence[CategoryConfig] = [
    CategoryConfig("relay", "继电器", "KA", 2, 1, 350, 1004, "control", "control", ["继电器", "relay"], "control", "控制线"),
    CategoryConfig("contactor", "接触器", "KM", 2, 1, 250, 1004, "control", "control", ["接触器", "contactor"], "power", "动力线"),
    CategoryConfig("breaker", "断路器", "QF", 2, 1, 250, 1004, "distribution", "distribution", ["断路器", "breaker"], "power", "动力线"),
    CategoryConfig("solenoid", "开关电磁铁", "YV", 3, 101, 700, 1031, "hydraulic", "hydraulic", ["电磁", "阀"], "hydraulic", "液压控制"),
    CategoryConfig("switch_sensor", "开关量传感器", "SQ", 3, 101, 650, 1032, "sensor", "sensor", ["开关", "行程", "limit"], "signal", "离散信号"),
    CategoryConfig("analog_sensor", "模拟量传感器", "SA", 3, 101, 650, 1032, "sensor", "sensor", ["sensor", "传感"], "signal", "模拟信号"),
    CategoryConfig("proportional_solenoid", "比例电磁铁", "BT", 3, 101, 250, 1031, "hydraulic", "hydraulic", ["比例", "伺服"], "hydraulic", "液压控制"),
    CategoryConfig("filter", "电源滤波器", "PF", 2, 1, 100, 1004, "distribution", "distribution", ["滤波"], "power", "动力线"),
    CategoryConfig("plc", "PLC 控制器", "PLC", 2, 1, 80, 1004, "control", "control", ["PLC", "controller"], "control", "控制线"),
    CategoryConfig("meter", "电表", "EM", 2, 1, 80, 1004, "distribution", "distribution", ["meter", "计量"], "signal", "监测线"),
    CategoryConfig("amplifier", "放大板", "AM", 2, 1, 80, 1004, "control", "control", ["放大", "amplifier"], "control", "控制线"),
    CategoryConfig("network_module", "网络模块", "NET", 2, 1, 80, 1003, "network", "network", ["网络", "通信", "module"], "network", "通讯线"),
]

WIRE_COLORS = ["RD", "BU", "BK", "YE", "GN", "WH", "GY", "VT"]


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
            (pattern, pattern, limit * 2),
        )
        add_rows(cursor)

    if len(rows) < limit:
        cursor = conn.execute(
            'SELECT Equipment_ID, Type, Name, "Desc", PartCode, OrderNum, Factory_ID, TModel, Structure, RepairInfo, Picture, MTBF '
            "FROM Equipment LIMIT ?",
            (limit * 2,),
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


def ensure_page(conn: sqlite3.Connection, page_id: int, structure_id: int, name: str, desc: str) -> None:
    cursor = conn.execute("SELECT 1 FROM Page WHERE Page_ID=?", (page_id,))
    if cursor.fetchone():
        return
    alter_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    conn.execute(
        "INSERT INTO Page (Page_ID, ProjectStructure_ID, Page_Desc, PageType, PageNum, PageName, Scale, Border, Title, AlterTime, MD5Code) "
        "VALUES (?,?,?,?,?,?,?,?,?,?,?)",
        (page_id, structure_id, desc, "原理图", page_id, name, "1:20", "A3", name, alter_time, ""),
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

    # ensure hierarchy
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

        for page in PAGE_DEFS.values():
            ensure_page(project_conn, page["page_id"], page["structure_id"], page["name"], page["desc"])
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

        ref_cache: Dict[str, List[ReferenceRow]] = {}
        instances: List[Dict[str, int]] = []
        category_indexes: Dict[str, List[int]] = {}

        for config in CATEGORIES:
            ref_rows = fetch_reference_rows(ref_conn, config.keywords, max(10, min(100, config.count // 2)))
            ref_cache[config.key] = ref_rows

        for config in CATEGORIES:
            parent_container_id = base_container_ids[config.parent_container_key]
            page_id = PAGE_DEFS[config.page_key]["page_id"]
            reference_rows = ref_cache[config.key]
            if not reference_rows:
                raise RuntimeError(f"No reference data for {config.key}")

            for idx in range(config.count):
                ref_row = reference_rows[idx % len(reference_rows)]
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

                instance_index = len(instances)
                instances.append(
                    dict(
                        equipment_id=equipment_id,
                        symbol_id=symbol_id,
                        category=config.key,
                        page_id=page_id,
                    )
                )
                category_indexes.setdefault(config.key, []).append(instance_index)

        def add_connection(inst_a: Dict[str, int], inst_b: Dict[str, int], wire_type: str, wire_category: str) -> None:
            nonlocal next_connectline_id
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
                    f"{inst_a['symbol_id']}:1",
                    f"{inst_b['symbol_id']}:2",
                    wire_type,
                    color,
                    "2.5mm2",
                    wire_category,
                    "component",
                    "component",
                ),
            )
            next_connectline_id += 1

        for config in CATEGORIES:
            indexes = category_indexes.get(config.key, [])
            for i in range(len(indexes) - 1):
                inst_a = instances[indexes[i]]
                inst_b = instances[indexes[i + 1]]
                add_connection(inst_a, inst_b, config.wire_type, config.wire_category)

        def connect_categories(source_key: str, target_key: str, limit: int, wire_type: str, wire_category: str) -> None:
            src_indexes = category_indexes.get(source_key, [])
            tgt_indexes = category_indexes.get(target_key, [])
            if not src_indexes or not tgt_indexes:
                return
            pair_count = min(limit, len(src_indexes), len(tgt_indexes))
            for idx in range(pair_count):
                inst_a = instances[src_indexes[idx]]
                inst_b = instances[tgt_indexes[idx]]
                add_connection(inst_a, inst_b, wire_type, wire_category)

        connect_categories("analog_sensor", "plc", 200, "signal", "模拟信号")
        connect_categories("switch_sensor", "plc", 200, "signal", "离散信号")
        connect_categories("relay", "contactor", 200, "control", "控制线")
        connect_categories("solenoid", "proportional_solenoid", 200, "hydraulic", "液压控制")
        connect_categories("filter", "breaker", 80, "power", "动力线")
        connect_categories("network_module", "plc", 80, "network", "通讯线")

        project_conn.commit()
        total_equipment = len(instances)
        total_connections = next_connectline_id - 1
        print(f"Inserted {total_equipment} equipment entries and {total_connections} connections.")
    finally:
        project_conn.close()
        ref_conn.close()


if __name__ == "__main__":
    main()
