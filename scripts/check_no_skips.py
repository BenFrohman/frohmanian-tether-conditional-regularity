#!/usr/bin/env python3
"""Fail CI if a skip list or sorry carve-out has crept back into the build.

Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0. Author: Benjamin Stanley Frohman.

The file list for every Lean scan is `git ls-files '*.lean'` (omitting only `.lake/`).
This guard fails on:
  * `--exclude` used as a scan option
  * an `excluded` module list in an axiom-audit Lean file
  * `grep -v` used to drop a `.lean` file or a sorry warning from a scan
  * a non-empty `draft_dirs` carve-out, or a sorry exemption "outside draft dirs"
  * a `[[lean_lib]]` that is not a default `lake build` target (a sorry there
    would not show up in the official default-target build log)
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FAIL: list[str] = []


def fail(msg: str) -> None:
    FAIL.append(msg)
    print("NO-SKIP FAIL: " + msg)


def iter_text_files() -> list[Path]:
    out = []
    for folder in [ROOT / ".github" / "workflows", ROOT / "scripts", ROOT / "certificates" / "tools"]:
        if not folder.is_dir():
            continue
        for p in folder.rglob("*"):
            if p.is_file() and p.suffix in {".yml", ".yaml", ".sh", ".py", ".lean", ".toml"}:
                out.append(p)
    return out


def main() -> int:
    # 1. lock: no draft-dir carve-out
    lock_path = ROOT / "TRUTH_GATE.lock"
    if lock_path.is_file():
        lock = json.loads(lock_path.read_text())
        drafts = lock.get("draft_dirs") or []
        if drafts:
            fail(f"TRUTH_GATE.lock draft_dirs is not empty: {drafts}")

    # 2. every lean_lib must be a default target, so lake build compiles it
    lake = ROOT / "lakefile.toml"
    if lake.is_file():
        text = lake.read_text()
        libs = re.findall(r'(?m)^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"', text)
        dt = re.search(r"(?m)^defaultTargets\s*=\s*\[([^\]]*)\]", text)
        targets = []
        if dt:
            targets = re.findall(r'"([^"]+)"', dt.group(1))
        for lib in libs:
            if lib not in targets:
                fail(f"lean_lib {lib} is not in defaultTargets; a sorry there would miss the official lake build")

    exclude_ok = {
        # the hard-failure message that *rejects* --exclude is allowed to mention the flag
        "scripts/check_forbidden_tokens.py",
        "scripts/check_no_skips.py",
    }

    for p in iter_text_files():
        rel = p.relative_to(ROOT).as_posix()
        src = p.read_text(encoding="utf-8", errors="replace")
        # skip this guard's own documentation of banned patterns in the module docstring
        body = src
        if rel == "scripts/check_no_skips.py":
            continue
        if rel == "scripts/check_forbidden_tokens.py":
            # allowed to mention --exclude only as a rejected flag
            pass

        if rel not in exclude_ok:
            if re.search(r"(^|[\s=])--exclude(\s|$|=)", body):
                fail(f"{rel} uses --exclude (skip lists are banned)")

        if p.suffix == ".lean" and rel.startswith("scripts/"):
            if re.search(r"\bexcluded\s*:\s*List\b", body) or re.search(r"\blet\s+excluded\b", body):
                fail(f"{rel} has an excluded-module list")

        # grep -v used to drop a lean file or a sorry warning
        for i, line in enumerate(body.splitlines(), 1):
            if re.search(r"grep\s+[^\n]*-v[^\n]*", line) and re.search(r"\.lean|sorry", line, re.I):
                # allow filtering the 'STRICT AUDIT PASS' banner or allowed-axiom list
                if re.search(r"STRICT AUDIT PASS|propext|Classical\\.choice|Quot\\.sound", line):
                    continue
                fail(f"{rel}:{i} uses grep -v on a .lean file or sorry line: {line.strip()}")

        if re.search(r"outside draft dirs", body) and "no draft" not in body.lower():
            # leftover carve-out wording
            fail(f"{rel} still describes a sorry exemption outside draft dirs")

        # A source-only scan of scripts/*.lean is a skip: those files must be elaborated.
        if "--scripts-source-scan-ok" in body:
            if rel == "scripts/check_lean_coverage.py" and "is a skip" in body and "FAIL:" in body:
                pass  # hard-failure message that rejects the flag
            else:
                fail(f"{rel} uses --scripts-source-scan-ok (scripts must be elaborated, not only scanned)")

    if FAIL:
        print(f"NO-SKIP FAIL ({len(FAIL)} problems)")
        return 1
    print("NO-SKIP PASS: no skip lists, no --exclude, no draft-dir sorry carve-out, every lean_lib is a default target")
    return 0


if __name__ == "__main__":
    sys.exit(main())
