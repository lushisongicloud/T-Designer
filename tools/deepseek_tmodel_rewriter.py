#!/usr/bin/env python3
"""
Bulk T-model rewriting helper using DeepSeek's chat API.

Features
--------
- Iterates equipment records from the component library (default: ref/LdMainData.db).
- Skips items without description or defined ports.
- For each equipment, requests DeepSeek (model `deepseek-chat`) to:
    * Assign port types / variable lists / connection macros.
    * Produce updated T-language sections (port vars → internal vars → normal mode → fault modes).
- Applies updates into the database (Equipment.TModel + port_config entries) with automatic rollback on failure.
- Runs optional post-update validation via external command (set TMODEL_VALIDATOR_CMD env).
- Retries each equipment up to 3 times, feeding validator errors back to the LLM.
- Supports multi-threaded execution (default 2 workers).
- Persists progress to a JSONL log file and supports resume.

Usage
-----
    python tools/deepseek_tmodel_rewriter.py \
        --db ref/LdMainData.db \
        --threads 2 \
        --log logs/deepseek_tmodel.log \
        --resume

Prerequisites
-------------
- Environment variable `DEEPSEEK_API_KEY` must be set.
- Optional: `TMODEL_VALIDATOR_CMD` for invoking an existing validator, e.g.
      export TMODEL_VALIDATOR_CMD="tools/tmodel_validator_cli --equipment"

Notes
-----
- Network connectivity is required to reach DeepSeek.
- Adjust prompts as needed to adapt to your T-language conventions.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import logging
import os
import re
import sqlite3
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import requests


DEESEEK_API_URL = "https://api.deepseek.com/chat/completions"
DEFAULT_MODEL = "deepseek-chat"
DEFAULT_THREADS = 2
DEFAULT_MAX_RETRIES = 3
DEFAULT_TIMEOUT = 45
DEFAULT_LOG = "deepseek_tmodel.log"


def slugify_component_tag(name: str, fallback: str) -> str:
    """Generate a safe identifier (ASCII) for variable naming."""
    base = re.sub(r"[^A-Za-z0-9]", "_", name.strip())
    base = re.sub(r"_+", "_", base).strip("_")
    if not base:
        base = str(fallback)
    return base


def chunk_ports(term_num: str) -> List[str]:
    """Split a TermNum string (supports 'A1|A2' form)."""
    if not term_num:
        return []
    parts = [p.strip() for p in re.split(r"[|、，,;/]+", term_num) if p.strip()]
    return parts or [term_num.strip()]


@dataclass
class PortRecord:
    block: str
    port: str
    description: str


@dataclass
class EquipmentRecord:
    equipment_id: str
    name: str
    spec: str
    description: str
    tmodel: str
    container_id: Optional[int]
    ports: List[PortRecord] = field(default_factory=list)


class ResumeTracker:
    """Track completed items via a JSONL log file."""

    def __init__(self, log_path: Path, resume: bool):
        self.log_path = log_path
        self.resume = resume
        self._lock = threading.Lock()
        self.completed: Dict[str, str] = {}
        if resume and log_path.exists():
            self._load_existing()

    def _load_existing(self) -> None:
        try:
            with self.log_path.open("r", encoding="utf-8") as f:
                for line in f:
                    try:
                        entry = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    status = entry.get("status")
                    equip_id = entry.get("equipment_id")
                    if status == "success" and equip_id is not None:
                        self.completed[str(equip_id)] = "success"
        except OSError as exc:
            logging.warning("Unable to load resume log: %s", exc)

    def mark(self, equipment_id: str, status: str, message: str) -> None:
        record = {
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "equipment_id": equipment_id,
            "status": status,
            "message": message,
        }
        with self._lock:
            with self.log_path.open("a", encoding="utf-8") as f:
                f.write(json.dumps(record, ensure_ascii=False) + "\n")
            if status == "success":
                self.completed[str(equipment_id)] = "success"

    def is_completed(self, equipment_id: str) -> bool:
        return str(equipment_id) in self.completed


class DeepSeekClient:
    """Thin wrapper around DeepSeek chat completions."""

    def __init__(self, api_key: str, model: str = DEFAULT_MODEL, timeout: int = DEFAULT_TIMEOUT):
        self.api_key = api_key
        self.model = model
        self.timeout = timeout

    def chat(self, system_prompt: str, user_prompt: str) -> str:
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }
        payload = {
            "model": self.model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            "temperature": 0.2,  # 较低温度以提高T语言生成的准确性和一致性
        }
        response = requests.post(
            DEESEEK_API_URL,
            headers=headers,
            json=payload,
            timeout=self.timeout,
        )
        if response.status_code != 200:
            raise RuntimeError(f"DeepSeek HTTP {response.status_code}: {response.text}")
        data = response.json()
        try:
            return data["choices"][0]["message"]["content"]
        except (KeyError, IndexError) as exc:
            raise RuntimeError(f"Unexpected DeepSeek response: {data}") from exc


def build_system_prompt(component_tag: str) -> str:
    return (
        "You are an expert T-language engineer working on T-Designer. "
        "Respond ONLY with JSON matching the requested schema. "
        "Mandatory sections: port definitions, internal variables, normal mode, fault modes. "
        f"Use '{component_tag}' as the component identifier when composing variable names."
    )


def build_user_prompt(equipment: EquipmentRecord, component_tag: str, previous_error: Optional[str]) -> str:
    ports_summary = []
    for port_record in equipment.ports:
        ports_summary.append(
            {
                "block": port_record.block,
                "port": port_record.port,
                "description": port_record.description or "",
            }
        )
    payload = {
        "task": {
            "goal": "Assign port types, variables, and rewrite the T-language model.",
            "sections_order": ["port_variables", "internal_variables", "normal_mode", "fault_modes"],
            "rules": {
                "port_types": {
                    "electric": ["i", "u"],
                    "hydraulic": ["p", "q"],
                    "mechanical": ["F", "v/n/x (choose one appropriate)"],
                },
                "macros": {
                    "electric": "electric-connect",
                    "hydraulic": "hydraulic-connect",
                    "mechanical": "mechanical-connect",
                },
                "fault_modes": {
                    "requirements": [
                        "Include at least open_circuit or short_circuit when relevant.",
                        "Each fault mode entry must identify the condition and resulting equations.",
                    ]
                },
                "formatting": {
                    "json_only": True,
                    "string_fields": "Return each T-language section as multiline strings.",
                },
            },
        },
        "component": {
            "id": equipment.equipment_id,
            "tag": component_tag,
            "name": equipment.name,
            "spec": equipment.spec,
            "description": equipment.description,
            "ports": ports_summary,
            "existing_tmodel_excerpt": equipment.tmodel[:6000] if equipment.tmodel else "",
        },
        "response_schema": {
            "ports": [
                {
                    "block": "string",
                    "port": "string",
                    "port_type": "electric|hydraulic|mechanical",
                    "variables": ["list", "of", "fully.qualified.variables"],
                    "connect_macro": "string",
                }
            ],
            "t_model": {
                "port_section": "string",
                "internal_variables": "string",
                "normal_mode": "string",
                "fault_modes": [
                    {
                        "name": "string",
                        "logic": "string",
                    }
                ],
            },
        },
    }
    if previous_error:
        payload["prior_feedback"] = previous_error[:4000]

    return json.dumps(payload, ensure_ascii=False, indent=2)


def parse_deepseek_response(raw: str) -> Dict:
    raw = raw.strip()
    if raw.startswith("```"):
        # Strip Markdown fences if present.
        raw = re.sub(r"^```(?:json)?", "", raw)
        raw = re.sub(r"```$", "", raw).strip()
    try:
        return json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"DeepSeek did not return valid JSON: {exc}\nRaw response:\n{raw}") from exc


def assemble_tmodel_text(component_tag: str, data: Dict) -> str:
    t_model = data.get("t_model", {})
    fault_modes = t_model.get("fault_modes", [])
    fault_lines = []
    for fm in fault_modes:
        name = fm.get("name", "").strip() or "unnamed_fault"
        logic = fm.get("logic", "").strip()
        fault_lines.append(f"# {name}\n{logic}".rstrip())
    parts = [
        "# 更新端口变量",
        t_model.get("port_section", "").strip(),
        "# 内部变量定义",
        t_model.get("internal_variables", "").strip(),
        "# 正常模式",
        t_model.get("normal_mode", "").strip(),
        "# 故障模式",
        "\n\n".join(fault_lines).strip(),
    ]
    final_text = "\n\n".join(part for part in parts if part)
    return final_text


def run_validator(equipment_id: str, tmodel_text: str) -> Tuple[bool, str]:
    validator_cmd = os.environ.get("TMODEL_VALIDATOR_CMD")
    if not validator_cmd:
        # Validator not configured; treat as success.
        return True, "Validator command not configured; skipping."

    import shlex
    import subprocess

    cmd = shlex.split(validator_cmd) + [str(equipment_id)]
    try:
        proc = subprocess.run(
            cmd,
            input=tmodel_text,
            text=True,
            capture_output=True,
            timeout=60,
        )
    except Exception as exc:  # pylint: disable=broad-except
        return False, f"Validator execution failed: {exc}"

    output = "\n".join(filter(None, [proc.stdout.strip(), proc.stderr.strip()]))
    success = proc.returncode == 0
    return success, output or ("Validation succeeded." if success else "Validation failed without message.")


class EquipmentProcessor:
    def __init__(
        self,
        db_path: Path,
        client: DeepSeekClient,
        resume_tracker: ResumeTracker,
        max_retries: int,
    ):
        self.db_path = db_path
        self.client = client
        self.resume = resume_tracker
        self.max_retries = max_retries
        self._db_lock = threading.Lock()

    def process(self, equipment: EquipmentRecord) -> None:
        if self.resume.is_completed(equipment.equipment_id):
            logging.info("Skipping equipment %s (already completed).", equipment.equipment_id)
            return

        logging.info("Processing equipment %s (%s).", equipment.equipment_id, equipment.name)
        component_tag = slugify_component_tag(equipment.name or equipment.spec, equipment.equipment_id)
        last_error = None

        for attempt in range(1, self.max_retries + 1):
            try:
                system_prompt = build_system_prompt(component_tag)
                user_prompt = build_user_prompt(equipment, component_tag, last_error)
                raw_reply = self.client.chat(system_prompt, user_prompt)
                data = parse_deepseek_response(raw_reply)
            except Exception as exc:  # pylint: disable=broad-except
                last_error = f"Request/parse error on attempt {attempt}: {exc}"
                logging.warning("%s", last_error)
                time.sleep(3)
                continue

            try:
                self._apply_update(equipment, data, component_tag)
            except Exception as exc:  # pylint: disable=broad-except
                last_error = f"Update error on attempt {attempt}: {exc}"
                logging.warning("%s", last_error)
                time.sleep(3)
                continue

            self.resume.mark(equipment.equipment_id, "success", f"Updated in attempt {attempt}")
            logging.info("Finished equipment %s.", equipment.equipment_id)
            return

        self.resume.mark(equipment.equipment_id, "failed", last_error or "Unknown failure")
        logging.error("Failed equipment %s after %s attempts. Last error: %s",
                      equipment.equipment_id, self.max_retries, last_error)

    # --- internals -----------------------------------------------------

    def _apply_update(self, equipment: EquipmentRecord, data: Dict, component_tag: str) -> None:
        ports = data.get("ports")
        if not isinstance(ports, list) or not ports:
            raise ValueError("Missing or empty 'ports' section in response.")

        tmodel_text = assemble_tmodel_text(component_tag, data)
        if not tmodel_text.strip():
            raise ValueError("Generated T-model text is empty.")

        # Prepare DB updates
        conn = sqlite3.connect(self.db_path, timeout=30)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA foreign_keys = ON;")
        conn.execute("PRAGMA journal_mode = WAL;")
        try:
            with self._db_lock:
                self._update_database(conn, equipment, ports, tmodel_text)
        finally:
            conn.close()

    def _update_database(
        self,
        conn: sqlite3.Connection,
        equipment: EquipmentRecord,
        ports: Sequence[Dict],
        tmodel_text: str,
    ) -> None:
        if equipment.container_id is None:
            raise ValueError("Equipment missing container mapping; cannot update port_config.")

        # Snapshot existing data for rollback.
        cur = conn.cursor()
        cur.execute(
            "SELECT port_config_id, function_block, port_name, port_type, variables_json, connect_macro "
            "FROM port_config WHERE container_id = ?",
            (equipment.container_id,),
        )
        previous_ports = cur.fetchall()

        cur.execute(
            "SELECT TModel FROM Equipment WHERE Equipment_ID = ?",
            (equipment.equipment_id,),
        )
        previous_tmodel_row = cur.fetchone()
        previous_tmodel = previous_tmodel_row["TModel"] if previous_tmodel_row else None

        # Apply new definitions.
        try:
            cur.execute("BEGIN IMMEDIATE")
            cur.execute("DELETE FROM port_config WHERE container_id = ?", (equipment.container_id,))
            insert_sql = (
                "INSERT INTO port_config "
                "(container_id, function_block, port_name, port_type, direction, variable_profile, variables_json, connect_macro) "
                "VALUES (?, ?, ?, ?, 'bidirectional', 'default', ?, ?)"
            )
            for item in ports:
                block = item.get("block") or "DEFAULT"
                port_name = item.get("port")
                port_type = item.get("port_type")
                variables = item.get("variables")
                macro = item.get("connect_macro") or ""

                if not (port_name and port_type and isinstance(variables, list) and variables):
                    raise ValueError(f"Incomplete port definition: {item}")

                variables_json = json.dumps([{"name": v} for v in variables], ensure_ascii=False)
                cur.execute(
                    insert_sql,
                    (equipment.container_id, block, port_name, port_type, variables_json, macro),
                )

            cur.execute(
                "UPDATE Equipment SET TModel = ?, CodeUpdatedTime = ? WHERE Equipment_ID = ?",
                (tmodel_text, time.strftime("%Y-%m-%d %H:%M:%S"), equipment.equipment_id),
            )
            conn.commit()
        except Exception:
            conn.rollback()
            raise

        # Run validator (after commit so external tools can read updated data).
        success, diagnostics = run_validator(equipment.equipment_id, tmodel_text)
        if not success:
            logging.warning("Validator failed for %s: %s", equipment.equipment_id, diagnostics)
            # Revert to previous state.
            try:
                cur.execute("BEGIN IMMEDIATE")
                cur.execute("DELETE FROM port_config WHERE container_id = ?", (equipment.container_id,))
                insert_sql = (
                    "INSERT INTO port_config "
                    "(port_config_id, container_id, function_block, port_name, port_type, direction, variable_profile, variables_json, connect_macro) "
                    "VALUES (?, ?, ?, ?, ?, 'bidirectional', 'default', ?, ?)"
                )
                for row in previous_ports:
                    cur.execute(
                        insert_sql,
                        (
                            row["port_config_id"],
                            equipment.container_id,
                            row["function_block"],
                            row["port_name"],
                            row["port_type"],
                            row["variables_json"],
                            row["connect_macro"],
                        ),
                    )
                cur.execute(
                    "UPDATE Equipment SET TModel = ?, CodeUpdatedTime = ? WHERE Equipment_ID = ?",
                    (previous_tmodel or "", time.strftime("%Y-%m-%d %H:%M:%S"), equipment.equipment_id),
                )
                conn.commit()
            except Exception:  # pylint: disable=broad-except
                conn.rollback()
                logging.exception("Failed to rollback updates for equipment %s.", equipment.equipment_id)
            raise ValueError(f"Validator error: {diagnostics}")

        logging.debug("Validator passed for %s: %s", equipment.equipment_id, diagnostics)


def fetch_equipment_records(conn: sqlite3.Connection) -> List[EquipmentRecord]:
    sql = """
    SELECT
        e.Equipment_ID,
        e.Name,
        IFNULL(e.Spec, '') AS Spec,
        IFNULL(e.Desc, '') AS Description,
        IFNULL(e.TModel, '') AS TModel,
        ec.container_id
    FROM Equipment e
    LEFT JOIN equipment_containers ec ON ec.equipment_id = e.Equipment_ID
    ORDER BY e.Equipment_ID
    """
    records: List[EquipmentRecord] = []
    for row in conn.execute(sql):
        description = (row["Description"] or "").strip()
        if not description:
            continue
        equipment = EquipmentRecord(
            equipment_id=str(row["Equipment_ID"]),
            name=row["Name"] or "",
            spec=row["Spec"] or "",
            description=description,
            tmodel=row["TModel"] or "",
            container_id=row["container_id"],
        )
        equipment.ports = fetch_ports(conn, equipment.equipment_id)
        if not equipment.ports:
            continue
        records.append(equipment)
    return records


def fetch_ports(conn: sqlite3.Connection, equipment_id: str) -> List[PortRecord]:
    sql = """
    SELECT TermNum, IFNULL(TermDesc, '') AS TermDesc
    FROM TermInfo
    WHERE Equipment_ID = ?
    """
    ports: List[PortRecord] = []
    for row in conn.execute(sql, (equipment_id,)):
        term_num = row["TermNum"]
        if not term_num:
            continue
        block_ports = chunk_ports(term_num)
        for port in block_ports:
            ports.append(
                PortRecord(
                    block=term_num,
                    port=port,
                    description=row["TermDesc"],
                )
            )
    return ports


def setup_logging(log_file: Optional[Path]) -> None:
    log_handlers = [logging.StreamHandler()]
    if log_file:
        log_handlers.append(logging.FileHandler(log_file, encoding="utf-8"))
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
        handlers=log_handlers,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Rewrite equipment T-models via DeepSeek API.")
    parser.add_argument("--db", type=Path, default=Path("ref/LdMainData.db"), help="Path to equipment SQLite database.")
    parser.add_argument("--threads", type=int, default=DEFAULT_THREADS, help="Number of worker threads (default: 2).")
    parser.add_argument("--log", type=Path, default=Path(DEFAULT_LOG), help="Progress log file (JSONL).")
    parser.add_argument("--resume", action="store_true", help="Resume from existing log file.")
    parser.add_argument("--max-retries", type=int, default=DEFAULT_MAX_RETRIES, help="Attempts per equipment.")
    parser.add_argument("--request-log", type=Path, help="Optional detailed request/response log file.")
    return parser.parse_args()


def main() -> None:
    args = parse_args()

    api_key = os.environ.get("DEEPSEEK_API_KEY")
    if not api_key:
        raise SystemExit("Environment variable DEEPSEEK_API_KEY is not set.")

    if not args.db.exists():
        raise SystemExit(f"Database not found: {args.db}")

    args.log.parent.mkdir(parents=True, exist_ok=True)
    if args.request_log:
        args.request_log.parent.mkdir(parents=True, exist_ok=True)

    setup_logging(args.request_log)
    resume_tracker = ResumeTracker(args.log, args.resume)
    client = DeepSeekClient(api_key=api_key)
    processor = EquipmentProcessor(args.db, client, resume_tracker, args.max_retries)

    with sqlite3.connect(args.db) as conn:
        conn.row_factory = sqlite3.Row
        equipments = fetch_equipment_records(conn)

    logging.info("Loaded %d equipment entries with descriptions and ports.", len(equipments))
    if not equipments:
        return

    # Thread pool execution
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.threads)) as executor:
        futures = [executor.submit(processor.process, equipment) for equipment in equipments]
        for future in concurrent.futures.as_completed(futures):
            try:
                future.result()
            except Exception as exc:  # pylint: disable=broad-except
                logging.error("Unhandled exception: %s", exc)

    logging.info("Processing complete.")


if __name__ == "__main__":
    main()
