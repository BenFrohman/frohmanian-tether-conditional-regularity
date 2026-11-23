#!/usr/bin/env bash
# Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
# 1) Reject forbidden tokens in the Lean sources.
# 2) Re-elaborate the audit file and require that every theorem/lemma depends only
#    on Lean's three standard axioms (propext, Classical.choice, Quot.sound).
# 3) Write certificates/axioms.log, axioms-bridge.log + SUMMARY.txt for CI artifact upload.
set -euo pipefail
cd "$(dirname "$0")/.."

mkdir -p certificates

echo "== forbidden-token scan (every tracked .lean file; no exclusions) =="
python3 scripts/check_forbidden_tokens.py --from-git

audit() {
  # $1 = audit .lean file, $2 = log file (also written as certificates/<stem>.log)
  local file="$1" log="$2" out expected got bad stem
  stem="$(basename "$file" .lean)"
  echo "== #print axioms (all declarations listed in $file) =="
  out="$(lake env lean "$file" 2>&1)" || {
    { echo "ELABORATED $file"; printf '%s\n' "$out"; } | tee "$log" "certificates/${stem}.log"
    echo "FAIL: lake env lean $file"
    exit 1
  }
  { echo "ELABORATED $file"; printf '%s\n' "$out"; } | tee "$log" "certificates/${stem}.log"

  # Fail on sorry warnings / sorryAx / lean errors in the audit output
  if printf '%s\n' "$out" | grep -qiE 'sorryAx|\bsorry\b|error:'; then
    echo "FAIL: errors, sorry, or sorryAx in axiom audit ($file)"; exit 1
  fi

  expected=$(grep -c '^#print axioms' "$file")
  got=$(printf '%s\n' "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)
  if [ "$got" -ne "$expected" ]; then
    echo "FAIL: expected $expected axiom reports, got $got ($file)"; exit 1
  fi

  bad=$(printf '%s' "$out" | tr '\n' ' ' | grep -oE 'depends on axioms: \[[^]]*\]' \
        | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' | sed '/^$/d' \
        | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
  if [ -n "$bad" ]; then
    echo "FAIL: non-standard axioms in $file: $bad"; exit 1
  fi
  AUDITED=$((AUDITED + expected))
}

AUDITED=0
audit scripts/PrintAxioms.lean certificates/axioms.log
audit scripts/PrintAxiomsBridge.lean certificates/axioms-bridge.log
expected=$AUDITED

{
  echo "FrohmanianTetherConditional axiom certificate"
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "toolchain=$(cat lean-toolchain)"
  echo "mathlib_inputRev=v4.30.0-rc1"
  echo "declarations_audited=$expected"
  echo "allowed_axioms=propext,Classical.choice,Quot.sound"
  echo "result=PASS"
  echo "scope=conditional abstract algebra/Grönwall over assumed PDE structure fields; not Clay Statement B"
  echo "bridge_audit=LEGACY placeholder target refuted; ClassicalNS genuine NS encoding with non-vacuity lemmas; lifespan-corrected triple architecture; OPEN target recorded as ClassicalNS.analytic_bridge_unconditional_Statement (a Prop, no proof, not claimed); every tracked .lean file is scanned and axiom-audited, including the open-target module"
} | tee certificates/SUMMARY.txt

echo "OK: all $expected declarations use only propext, Classical.choice, Quot.sound"

echo "== Truth Gate kernel audits =="
for f in TruthGateAudit TruthGateAuditVacuity TruthGateAuditPillars TruthGateAuditUnifiedHs; do
  { echo "ELABORATED scripts/$f.lean"; lake env lean "scripts/$f.lean" 2>&1; } | tee "certificates/$f.txt"
  grep -q 'TRUTH GATE AUDIT PASS' "certificates/$f.txt"
  if grep -qE 'TRUTH GATE FAIL|error:|sorryAx' "certificates/$f.txt"; then
    echo "FAIL: Truth Gate audit $f"; exit 1
  fi
done

echo "== Strict whole-library axiom audit (every declaration, not only listed ones) =="
for f in StrictAxiomAudit StrictAxiomAuditBridge; do
  { echo "ELABORATED scripts/$f.lean"; lake env lean "scripts/$f.lean" 2>&1; } | tee "certificates/$f.txt"
  grep -q '^STRICT AUDIT PASS' "certificates/$f.txt"
  if grep -v '^STRICT AUDIT PASS' "certificates/$f.txt" | grep -qE 'STRICT AUDIT FAIL|sorryAx|ofReduceBool|error:'; then
    echo "FAIL: strict axiom audit $f"; exit 1
  fi
  grep '^STRICT AUDIT SUMMARY' "certificates/$f.txt" || true
done

echo "== coverage: every tracked .lean file must be built and scanned =="
python3 scripts/check_lean_coverage.py --build-log "${BUILD_LOG:-cert-bundle/lake-build.log}"

