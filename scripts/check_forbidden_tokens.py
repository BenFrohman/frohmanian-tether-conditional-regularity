"""Forbidden-token scan for Lean sources, with comments and string literals stripped.

Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0. Author: Benjamin Stanley Frohman.

Fails if any scanned file contains `sorry`, `admit`, `native_decide`, or an `axiom`
declaration in code (text inside `--` and `/- ... -/` comments and inside string
literals is ignored).

Usage:
  python3 scripts/check_forbidden_tokens.py --from-git
  python3 scripts/check_forbidden_tokens.py [--require-imported-by AUDIT.lean] PATH [PATH ...]

The file list is never a skip list. Prefer `--from-git`, which scans every path
from `git ls-files '*.lean'` (the only omitted paths are those under `.lake/`).
There is no `--exclude` option: passing one is a hard failure.

`--require-imported-by AUDIT.lean` (repeatable) additionally fails if some
scanned library file is not in the import closure of the AUDIT files.
A list of scanned files is written to certificates/scanned-lean-files.txt.
"""
import re
import sys
from pathlib import Path

BAD = re.compile(
    r'(?<![A-Za-z0-9_.\'])(sorry|admit|native_decide)(?![A-Za-z0-9_\'])'
    r'|^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable|unsafe)\s+)*axiom\s',
    re.M,
)


def strip(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
            continue
        if src.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth and src.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth == 0 and src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('""')
            i = j + 1
            continue
        if depth == 0:
            out.append(src[i])
        elif src[i] == '\n':
            out.append('\n')
        i += 1
    return ''.join(out)


def files(paths):
    for p in map(Path, paths):
        if p.is_file() and p.suffix == '.lean':
            yield p
        elif p.is_dir():
            for f in sorted(p.rglob('*.lean')):
                if '.lake' not in f.parts:
                    yield f
        else:
            sys.exit(f'path not found: {p}')


IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.\u00ab\u00bb]+)', re.M)


def module_of(path: Path) -> str:
    return '.'.join(path.with_suffix('').parts)


def closure(audit: Path) -> set:
    seen, todo = set(), [audit]
    while todo:
        f = todo.pop()
        if f in seen or not f.exists():
            continue
        seen.add(f)
        for m in IMPORT.findall(strip(f.read_text(encoding='utf-8'))):
            todo.append(Path(*m.split('.')).with_suffix('.lean'))
    return {module_of(f) for f in seen if f != audit}



def git_lean_files():
    import subprocess
    out = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], text=True)
    files_ = []
    for rel in out.split("\0"):
        if not rel:
            continue
        if ".lake/" in rel.split("/") or rel.startswith(".lake/"):
            continue
        files_.append(Path(rel))
    return files_


def main(argv):
    if "--exclude" in argv:
        sys.exit("FAIL: --exclude is not allowed. Scan every tracked .lean file; never skip one.")
    audits, paths, from_git = [], [], False
    it = iter(argv)
    for a in it:
        if a == "--from-git":
            from_git = True
        elif a == "--require-imported-by":
            audits.append(Path(next(it)))
        else:
            paths.append(a)
    if from_git:
        if paths:
            sys.exit("FAIL: --from-git does not take PATH arguments")
        to_scan = git_lean_files()
        source = "git ls-files '*.lean' (excluding only .lake/)"
    else:
        if not paths:
            sys.exit(__doc__)
        to_scan = list(files(paths))
        source = " ".join(paths)
    for audit in audits:
        if not audit.exists():
            sys.exit(f"audit file not found: {audit}")
    reach = set().union(*(closure(a) for a in audits)) if audits else None
    audit = " + ".join(map(str, audits))
    bad, missing, count, scanned = [], [], 0, []
    for f in to_scan:
        if reach is not None and module_of(f) not in reach and not str(f).startswith("scripts/"):
            missing.append(str(f))
        count += 1
        scanned.append(f.as_posix())
        code = strip(f.read_text(encoding="utf-8"))
        for k, line in enumerate(code.splitlines(), 1):
            if BAD.search(line):
                bad.append(f"{f}:{k}: {line.strip()}")
    print(f"scanned {count} Lean files from {source}")
    Path("certificates").mkdir(exist_ok=True)
    Path("certificates/scanned-lean-files.txt").write_text("\n".join(scanned) + "\n")
    if count == 0:
        sys.exit("FAIL: no Lean files scanned")
    if missing:
        print("\n".join(f"NOT IMPORTED by {audit}: {m}" for m in missing))
        sys.exit(f"FAIL: {len(missing)} scanned module(s) are outside the axiom audit")
    if audits:
        print(f"coverage: every scanned library module is imported (transitively) by {audit}")
    if bad:
        print("\n".join(bad))
        sys.exit(f"FAIL: {len(bad)} forbidden token(s) in code")
    print("PASS: no sorry / admit / native_decide / axiom declarations (comments excluded)")


if __name__ == '__main__':
    main(sys.argv[1:])
