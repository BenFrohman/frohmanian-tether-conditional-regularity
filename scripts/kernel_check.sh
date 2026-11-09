#!/usr/bin/env bash
# Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
# 1) Reject forbidden tokens in the Lean sources.
# 2) Re-elaborate the audit file and require that every theorem/lemma depends only
#    on Lean's three standard axioms (propext, Classical.choice, Quot.sound).
# 3) Write certificates/axioms.log + SUMMARY.txt for CI artifact upload.
set -euo pipefail
cd "$(dirname "$0")/.."

mkdir -p certificates

echo "== forbidden-token scan =="
if grep -rnE '\b(sorry|admit|native_decide|implemented_by)\b|^\s*(axiom|unsafe|opaque)\b' \
     --include='*.lean' FrohmanianTetherConditional FrohmanianTetherConditional.lean \
   | grep -v 'Zero-sorry'; then
  echo "FAIL: forbidden token found"; exit 1
fi
echo "OK: no sorry/admit/axiom/native_decide/opaque/unsafe"

echo "== #print axioms (all theorems/lemmas listed in scripts/PrintAxioms.lean) =="
out="$(lake env lean scripts/PrintAxioms.lean 2>&1)" || {
  printf '%s\n' "$out" | tee certificates/axioms.log
  echo "FAIL: lake env lean scripts/PrintAxioms.lean"
  exit 1
}
printf '%s\n' "$out" | tee certificates/axioms.log

# Fail on sorry warnings / sorryAx / lean errors in the audit output
if printf '%s\n' "$out" | grep -qiE 'sorryAx|\bsorry\b|error:'; then
  echo "FAIL: errors, sorry, or sorryAx in axiom audit"; exit 1
fi

expected=$(grep -c '^#print axioms' scripts/PrintAxioms.lean)
got=$(printf '%s\n' "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)
if [ "$got" -ne "$expected" ]; then
  echo "FAIL: expected $expected axiom reports, got $got"; exit 1
fi

bad=$(printf '%s' "$out" | tr '\n' ' ' | grep -oE 'depends on axioms: \[[^]]*\]' \
      | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' | sed '/^$/d' \
      | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then
  echo "FAIL: non-standard axioms: $bad"; exit 1
fi

{
  echo "FrohmanianTetherConditional axiom certificate"
  echo "date_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "toolchain=$(cat lean-toolchain)"
  echo "mathlib_inputRev=v4.30.0-rc1"
  echo "declarations_audited=$expected"
  echo "allowed_axioms=propext,Classical.choice,Quot.sound"
  echo "result=PASS"
  echo "scope=conditional abstract algebra/Grönwall over assumed PDE structure fields; not Clay Statement B"
} | tee certificates/SUMMARY.txt

echo "OK: all $expected declarations use only propext, Classical.choice, Quot.sound"
