# Kernel certificate: FrohmanianTetherConditional.ClassicalEstimatePieces

Copyright (c) 2026 Benjamin Stanley Frohman. Author: Benjamin Stanley Frohman

Generated from the actual `lake build` and `lake env lean scripts/PrintAxioms.lean` runs (logs in this folder, unedited).

| Field | Value |
|---|---|
| Repository | BenFrohman/frohmanian-tether-conditional-regularity |
| Branch | feat/classical-estimate-pieces-20261116 |
| Source commit built | 51c32a3c71311f58d24c87b33a3b23717f9f10e5 |
| lean-toolchain contents | leanprover/lean4:v4.30.0-rc1 |
| sha256(lean-toolchain) | 1098ca8368e0db12138f33b070187e1f6527984ae0451a587b20e3e661f96a76 |
| sha256(lake-manifest.json) | 0024851d12fc7f5986ced05ff51d014f0b8b4df728bb8f9cef2812126a21ebb2 |
| Mathlib rev (manifest) | 0c154d67103f74be3a0f2c509f72ccbf5be9f2a7 |
| Mathlib cache | `lake exe cache get` for that rev: see cache-get.log |
| elan | elan 4.2.4 (227caca13 2026-08-25) |
| lake | Lake version 5.0.0-src+714601b (Lean version 4.30.0-rc1) |
| lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Build result | Build completed successfully (8274 jobs). (lake-build.log) |
| Kernel check | scripts/kernel_check.sh: OK: all 74 declarations use only propext, Classical.choice, Quot.sound |
| sha256(ClassicalEstimatePieces.lean) | e1abe673954175d0dcdb988502f51bc5cd530958094bdfe6be908bbec264734a |
| Date (UTC) | 2026-11-17T03:30:07Z |

## #print axioms (ClassicalEstimatePieces, verbatim from print-axioms.log)
```
'ClassicalEstimatePieces.sym_part_frobenius_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.sym_part_frobenius_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.antisym_mul_curl_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.grad_mul_curl_eq_sym_mul_curl' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.quadform_le_frobenius_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.gronwall_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.cutoff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.cutoff_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.hasFDerivAt_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.norm_fderiv_cutoff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.comoving_cutoff_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.holder_triple_pasted_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.holder_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.interp_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.young_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.serrin_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.amplitude_refutes_rate_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.amplitude_refutes_rate_enstrophy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.amplitude_refutes_rate_enstrophy_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.deriv_le_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.rate_false_of_touch' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassicalEstimatePieces.not_uniform_rate_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Expected warning in lake-build.log: the pre-existing OPEN target `ClassicalNSOpenTarget.lean` (one intentional `sorry`, excluded from all audits). The new module has no warnings.

## Rebuild
```
git clone https://github.com/BenFrohman/frohmanian-tether-conditional-regularity.git && cd frohmanian-tether-conditional-regularity && git checkout 51c32a3c71311f58d24c87b33a3b23717f9f10e5 && lake exe cache get && lake build && lake env lean scripts/PrintAxioms.lean | grep ClassicalEstimatePieces
```

## Notes on the logs
- `lake-build.log` line 1 warns "mathlib: repository ... has local changes". In the Mathlib checkout used (git HEAD = the manifest rev above), the only differences are 6 deleted files under `scripts/bench/build/` (benchmark tooling). No `Mathlib/` source file differs from the manifest rev.
- The `.lake/packages` directory is the box's shared checkout of exactly the manifest revisions (every package's git HEAD equals its `lake-manifest.json` rev). `lake exe cache get` reported "No files to download / Already decompressed 8248 file(s)".
