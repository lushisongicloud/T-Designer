#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
将当前目录及子目录中的 .cpp / .h 文件：
1) 从 UTF-8 with BOM 转为 UTF-8（移除 BOM）
2) 将换行统一为 Unix 风格 LF（\n）

用法：
  python3 fix_encoding_newlines.py            # 处理当前目录
  python3 fix_encoding_newlines.py /path/src  # 处理指定目录
  python3 fix_encoding_newlines.py -n         # 试运行（不写回）
  python3 fix_encoding_newlines.py -v         # 输出更详细日志
"""

from pathlib import Path
import argparse
import sys

UTF8_BOM = b"\xef\xbb\xbf"
TARGET_EXTS = {".cpp", ".h"}  # 仅按需求处理这两种后缀（大小写不敏感）
SKIP_DIRS = {".git"}          # 可按需增加：{"build", "out", ...}

def should_process(path: Path) -> bool:
    if not path.is_file():
        return False
    ext = path.suffix.lower()
    return ext in TARGET_EXTS

def normalize_newlines(data: bytes) -> bytes:
    # 先把 CRLF -> LF，再把孤立的 CR -> LF
    data = data.replace(b"\r\n", b"\n")
    data = data.replace(b"\r", b"\n")
    return data

def process_file(path: Path, dry_run: bool = False, verbose: bool = False):
    original = path.read_bytes()

    had_bom = original.startswith(UTF8_BOM)
    content = original[3:] if had_bom else original

    normalized = normalize_newlines(content)
    changed = had_bom or (normalized != original)

    if changed and not dry_run:
        path.write_bytes(normalized)

    if changed and verbose:
        ops = []
        if had_bom:
            ops.append("移除BOM")
        if normalized != (original[3:] if had_bom else original):
            ops.append("换行=>LF")
        print(f"[修改] {path} ({'，'.join(ops)})")
    elif verbose:
        print(f"[保持] {path}")

    return had_bom, normalized != (original[3:] if had_bom else original), changed

def walk_and_process(root: Path, dry_run: bool = False, verbose: bool = False):
    bom_removed = 0
    nl_fixed = 0
    modified = 0
    processed = 0

    for p in root.rglob("*"):
        # 跳过指定目录
        if p.is_dir() and p.name in SKIP_DIRS:
            # rglob 不能直接跳过子树，这里只在文件层判断
            continue
        if should_process(p):
            processed += 1
            had_bom, had_nl_change, changed = process_file(p, dry_run, verbose)
            bom_removed += int(had_bom)
            nl_fixed += int(had_nl_change)
            modified += int(changed)

    return processed, bom_removed, nl_fixed, modified

def main():
    parser = argparse.ArgumentParser(description="将 .cpp/.h 从 UTF-8 with BOM 转为 UTF-8 并统一换行到 LF。")
    parser.add_argument("root", nargs="?", default=".", help="扫描根目录（默认：当前目录）")
    parser.add_argument("-n", "--dry-run", action="store_true", help="试运行：不写回文件，只统计/预览")
    parser.add_argument("-v", "--verbose", action="store_true", help="输出每个文件的处理结果")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    if not root.exists():
        print(f"路径不存在：{root}", file=sys.stderr)
        sys.exit(1)

    processed, bom_removed, nl_fixed, modified = walk_and_process(
        root, dry_run=args.dry_run, verbose=args.verbose
    )

    mode = "试运行" if args.dry_run else "实际写入"
    print("\n==== 处理完成 ====")
    print(f"模式：{mode}")
    print(f"根目录：{root}")
    print(f"扫描文件数：{processed}")
    print(f"移除 BOM：{bom_removed}")
    print(f"规范换行(LF)：{nl_fixed}")
    print(f"实际修改文件数：{modified}")

if __name__ == "__main__":
    main()
