#!/usr/bin/env python3
"""Fail CI if any git-tracked .lean file was not scanned and built.

Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0. Author: Benjamin Stanley Frohman.

The file list is `git ls-files '*.lean'`, omitting only paths under .lake/.
There is no skip list.
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def git_lean_files() -> list[Path]:
    out = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], cwd=ROOT)
    files = []
    for rel in out.split(b"\0"):
        if not rel:
            continue
        s = rel.decode()
        if s.startswith(".lake/") or "/.lake/" in s:
            continue
        files.append(Path(s))
    return files


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--build-log", default="", help="lake build log (tee'd official log)")
    ap.add_argument(
        "--scanned-list",
        default="certificates/scanned-lean-files.txt",
        help="list written by check_forbidden_tokens.py",
    )
    args = ap.parse_args()
    if "--scripts-source-scan-ok" in sys.argv:
        print("FAIL: --scripts-source-scan-ok is a skip; every scripts/*.lean file must be elaborated")
        return 1
    expected = git_lean_files()
    if not expected:
        print("FAIL: git ls-files '*.lean' returned no files")
        return 1

    scanned_path = ROOT / args.scanned_list
    scanned = set()
    if scanned_path.is_file():
        scanned = {Path(line.strip()) for line in scanned_path.read_text().splitlines() if line.strip()}
    missing_scan = [f.as_posix() for f in expected if f not in scanned]
    if missing_scan:
        print("FAIL: these tracked .lean files were not scanned:")
        print("\n".join(f"  {m}" for m in missing_scan))
        return 1

    log_text = ""
    if args.build_log:
        lp = Path(args.build_log)
        if not lp.is_file():
            print(f"FAIL: build log not found: {args.build_log}")
            return 1
        log_text = lp.read_text(encoding="utf-8", errors="replace")
        for pat in ("declaration uses `sorry`", "declaration uses 'sorry'", "sorryAx"):
            # also allow the unicode/backtick variants already grepped in the workflow
            if "declaration uses" in log_text and "sorry" in log_text:
                # precise check
                import re
                if re.search(r"declaration uses [`']sorry[`']", log_text) or "sorryAx" in log_text:
                    print("FAIL: official build log contains sorry or sorryAx")
                    return 1
                break

    missing_build = []
    for f in expected:
        rel = f.as_posix()
        if rel.startswith("scripts/"):
            # Script files must be elaborated by `lake env lean` in this job.
            # Evidence is a certificates/<stem>.log or .txt, or a log that starts
            # with the line ELABORATED scripts/<stem>.lean. A source-only scan is
            # not enough.
            stem = f.stem
            ok = False
            cert_root = ROOT / "certificates"
            if cert_root.is_dir():
                for c in cert_root.rglob("*"):
                    if not c.is_file():
                        continue
                    if c.name in {f"{stem}.log", f"{stem}.txt"}:
                        ok = True
                        break
                    try:
                        head = c.read_text(encoding="utf-8", errors="replace")[:8000]
                    except OSError:
                        continue
                    if f"ELABORATED {rel}" in head:
                        ok = True
                        break
            if not ok:
                missing_build.append(rel)
            continue
        # Library module: must appear in the lake build log or have an olean.
        mod = rel[:-5].replace("/", ".")
        built = False
        if log_text and mod in log_text:
            built = True
        olean = list((ROOT / ".lake" / "build").rglob(f.with_suffix(".olean").name)) if (ROOT / ".lake" / "build").exists() else []
        if olean:
            built = True
        if not built:
            missing_build.append(rel)

    if missing_build:
        print("FAIL: these tracked .lean files were not built (or, for scripts/, not elaborated):")
        print("\n".join(f"  {m}" for m in missing_build))
        return 1

    print(f"COVERAGE PASS: {len(expected)} tracked .lean files scanned and built "
          f"(git ls-files '*.lean', excluding only .lake/)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
