-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import FrohmanianTetherConditional.ClassicalNS

/-!
# OPEN target: the analytic bridge with genuine definitions

`AnalyticBridgeStatement` (defined and documented in `ClassicalNS.lean`) says: for every
`ν > 0` and every smooth, periodic, divergence-free `u₀`, **every maximal classical
solution** of periodic incompressible Navier–Stokes is global (`T⋆ = ⊤`) and has
`∫₀ᵀ ‖∇u‖_∞ dt < ∞` for every `T`.

With the genuine `NSSolution` of `ClassicalNS.lean` this is, modulo standard
local-existence/uniqueness facts that are not formalized, Clay Millennium Problem (B)
on `T³`. It is **OPEN**. The single `sorry` below marks that; this file is excluded
from the forbidden-token scan and from the axiom audit, and nothing in this repository
claims to prove it.

What *is* proved (audited, in `ClassicalNS.lean`):
`analyticBridge_of_formB : HypothesisB C⋆ → BKMCriterion → AnalyticBridgeStatement`
(conditional), and the non-vacuity lemmas.
-/

namespace ClassicalNS

/-- OPEN (Clay Millennium Problem (B), periodic case, with genuine definitions). -/
theorem analytic_bridge_unconditional : AnalyticBridgeStatement := by
  sorry  -- OPEN: Clay Millennium Problem Statement (B); not claimed.

end ClassicalNS
