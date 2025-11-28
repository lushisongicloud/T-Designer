# 【分类依据】本脚本记录了已完成的工作、实现了特定功能或作为有用的工具保留。
# 具体分类原因与依据请参考: tools/archive/README.md
#

#!/usr/bin/env python3
"""
Batch-adjust testing costs in a project DB by assigning random values that
follow a user-provided proportion (e.g. percentage of low-cost measurable ports).
"""

from __future__ import annotations

import argparse
import random
import shutil
import sqlite3
from pathlib import Path
from typing import Iterable, Sequence, Tuple

DEFAULT_LOW_RANGE = (0.15, 0.55)
DEFAULT_HIGH_RANGE = (0.8, 1.1)
DEFAULT_CLUSTER = 0.0


def parse_range(value: str) -> Tuple[float, float]:
    try:
        lo_str, hi_str = value.split(",", 1)
        lo = float(lo_str.strip())
        hi = float(hi_str.strip())
    except Exception as exc:  # noqa: BLE001
        raise argparse.ArgumentTypeError(f"无法解析区间: {value}") from exc
    if lo == hi:
        raise argparse.ArgumentTypeError("区间上下限不能相同。")
    if lo > hi:
        lo, hi = hi, lo
    if lo < 0 or hi < 0:
        raise argparse.ArgumentTypeError("测试代价需为非负值。")
    return lo, hi


def chunked(seq: Sequence[int], size: int) -> Iterable[Sequence[int]]:
    for start in range(0, len(seq), size):
        yield seq[start : start + size]


def assign_random_costs(
    conn: sqlite3.Connection,
    ids: Sequence[int],
    rng: Tuple[float, float],
    rnd: random.Random,
) -> None:
    if not ids:
        return
    low, high = rng
    sql = "UPDATE Symb2TermInfo SET TestCost=? WHERE Symb2TermInfo_ID=?"
    for batch in chunked(ids, 500):
        values = [(rnd.uniform(low, high), sid) for sid in batch]
        conn.executemany(sql, values)


def load_term_ids(conn: sqlite3.Connection) -> Sequence[int]:
    cursor = conn.execute("SELECT Symb2TermInfo_ID FROM Symb2TermInfo ORDER BY Symb2TermInfo_ID")
    return [row[0] for row in cursor.fetchall()]


def backup_db(src: Path, dst: Path) -> None:
    if dst.exists():
        dst.unlink()
    shutil.copy2(src, dst)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("db", type=Path, help="工程数据库文件路径（.db）")
    parser.add_argument(
        "--ratio",
        type=float,
        default=0.9,
        help="分配到低测试代价值域的端口比例，0~1，默认 0.9。",
    )
    parser.add_argument(
        "--low-range",
        type=parse_range,
        default="{},{}".format(*DEFAULT_LOW_RANGE),
        help=f"可测端口测试代价随机区间，默认 {DEFAULT_LOW_RANGE[0]}~{DEFAULT_LOW_RANGE[1]}。",
    )
    parser.add_argument(
        "--high-range",
        type=parse_range,
        default="{},{}".format(*DEFAULT_HIGH_RANGE),
        help=f"不可测端口测试代价随机区间，默认 {DEFAULT_HIGH_RANGE[0]}~{DEFAULT_HIGH_RANGE[1]}。",
    )
    parser.add_argument("--seed", type=int, help="随机种子，指定后结果可复现。")
    parser.add_argument(
        "--high-cluster",
        type=float,
        default=DEFAULT_CLUSTER,
        help="高测试代价端口的聚集程度（0~1）。0=完全随机，1=全部集中成连续段。",
    )
    parser.add_argument(
        "--no-backup",
        action="store_true",
        help="默认会在同目录生成 .bak 备份，指定后跳过备份。",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="仅输出统计信息，不改写数据库。",
    )
    parser.add_argument(
        "--backup-name",
        type=Path,
        help="自定义备份文件名称（可包含路径）。未指定时使用 <db>.bak。",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    db_path: Path = args.db
    if not db_path.exists():
        raise FileNotFoundError(f"未找到数据库文件: {db_path}")
    if not 0 <= args.ratio <= 1:
        raise ValueError("ratio 需介于 0 与 1 之间。")
    if not 0 <= args.high_cluster <= 1:
        raise ValueError("high-cluster 需介于 0 与 1 之间。")

    low_range = args.low_range if isinstance(args.low_range, tuple) else parse_range(args.low_range)  # type: ignore[truthy-bool]
    high_range = args.high_range if isinstance(args.high_range, tuple) else parse_range(args.high_range)  # type: ignore[truthy-bool]
    rnd = random.Random(args.seed)

    if not args.no_backup:
        backup_name = args.backup_name or db_path.with_suffix(db_path.suffix + ".bak")
        backup_db(db_path, backup_name)
        print(f"[备份] 已创建备份: {backup_name}")

    conn = sqlite3.connect(db_path)
    try:
        ordered_ids = load_term_ids(conn)
        total = len(ordered_ids)
        if not total:
            print("Symb2TermInfo 表为空，未做任何调整。")
            return

        shuffled_ids = ordered_ids[:]
        rnd.shuffle(shuffled_ids)
        low_target = int(round(total * args.ratio))
        high_target = total - low_target

        clustered_high = min(high_target, max(0, int(round(high_target * args.high_cluster))))
        high_id_set = set()
        if clustered_high > 0:
            block_len = clustered_high
            start = 0
            if total > block_len:
                start = rnd.randint(0, total - block_len)
            cluster_slice = ordered_ids[start : start + block_len]
            high_id_set.update(cluster_slice)

        remaining_high = high_target - len(high_id_set)
        if remaining_high > 0:
            available = [sid for sid in shuffled_ids if sid not in high_id_set]
            if remaining_high > len(available):
                remaining_high = len(available)
            high_id_set.update(available[:remaining_high])

        high_ids = list(high_id_set)
        low_ids = [sid for sid in ordered_ids if sid not in high_id_set]
        actual_high = len(high_ids)
        actual_low = len(low_ids)
        rnd.shuffle(low_ids)
        rnd.shuffle(high_ids)

        print(
            f"[统计] 端口总数 {total}，低代价值域 {actual_low}，高代价 {actual_high} "
            f"(ratio={args.ratio:.3f})"
        )
        if clustered_high:
            print(
                f"[聚集] 其中 {clustered_high} 个高代价端口集中成连续段 "
                f"(cluster={args.high_cluster:.3f})"
            )
        print(f"[区间] 低代价范围 {low_range[0]:.3f}~{low_range[1]:.3f}，高代价范围 {high_range[0]:.3f}~{high_range[1]:.3f}")

        if args.dry_run:
            print("[Dry-Run] 仅输出统计，不写入数据库。")
            return

        assign_random_costs(conn, low_ids, low_range, rnd)
        assign_random_costs(conn, high_ids, high_range, rnd)
        conn.commit()
        print("[完成] 已随机更新所有端口测试代价。")
    finally:
        conn.close()


if __name__ == "__main__":
    main()
