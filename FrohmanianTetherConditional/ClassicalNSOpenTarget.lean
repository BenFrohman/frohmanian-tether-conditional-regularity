/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.ClassicalNS

/-!
# OPEN target: the analytic bridge with genuine definitions (statement only)

`AnalyticBridgeStatement` (defined and documented in `ClassicalNS.lean`) says: for every
`ν > 0` and every smooth, periodic, divergence-free `u₀`, **every maximal classical
solution** of periodic incompressible Navier–Stokes is global (`T⋆ = ⊤`) and has
`∫₀ᵀ ‖∇u‖_∞ dt < ∞` for every `T`.

With the genuine `NSSolution` of `ClassicalNS.lean` this is, modulo standard
local-existence/uniqueness facts that are not formalized, Clay Millennium Problem (B)
on `T³`. It is **OPEN**. This file records that statement as a `def` of type `Prop`.
It is not a theorem, it has no proof, and it is not claimed.

This file used to contain a `theorem` whose proof was `sorry`. That `sorry` is gone.
The file is part of the certified build and of every scan. A later commit may prove
the statement; until then it remains a statement only.

What *is* proved (audited, in `ClassicalNS.lean`):
`analyticBridge_of_formB : FormBPerSolution → BKMCriterionSmooth → AnalyticBridgeStatement`
(conditional), and the non-vacuity lemmas.
-/

namespace ClassicalNS

/-- OPEN (Clay Millennium Problem (B), periodic case, with genuine definitions).
This is a statement only: it is not a theorem and it is not proved. -/
def analytic_bridge_unconditional_Statement : Prop := AnalyticBridgeStatement

end ClassicalNS
