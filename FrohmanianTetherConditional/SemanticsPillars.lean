/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.ClassicalNS

/-!
# Truth Gate: semantics lock for the Three Pillars note (see `TRUTH_GATE.md`)

PAPER_PATH: paper/Three_Pillars_NS.tex
PAPER_SHA256: 6d3d04b27fddb11547df6a72a08473eb281618957258ec06f8ac01705fb7d8b4
PAPER_SECTION: Section 1 "The Lean-certified implication", Theorem thm:conditional

Locked paper claim: Theorem `thm:conditional` ("Conditional implication"). The two
hypotheses and the conclusion are independently transcribed from the English of
that theorem.

PAPER_QUOTE_BEGIN
\begin{theorem}[Conditional implication]\label{thm:conditional}
For every bound \(C_\star:\mathbb{R}\to\mathbb{R}\), if Lean's \texttt{HypothesisB} holds for \(C_\star\) and if Lean's \texttt{BKMCriterion} holds, then for every viscosity \(\nu>0\) and every smooth, periodic, divergence-free initial datum, every maximal classical solution (an object of type \texttt{NSSolution}) is global (\(T^\star=\top\)) and has finite \(\int_0^T\|\nabla\mathbf{u}(t)\|_{L^\infty}\,dt\) for every finite \(T>0\).
\end{theorem}
PAPER_QUOTE_END

`formal_claim_conditional` is the statement of `ClassicalNS.analyticBridge_of_formB_forall`.
`paper_claim_conditional` writes the hypotheses and the conclusion out from the
English of `thm:conditional`. The named BKM hypothesis is transcribed in
contrapositive form. It does not name the repository Props `HypothesisB`,
`BKMCriterion` or `AnalyticBridgeStatement`.

Scope: CONDITIONAL. The two hypotheses are assumptions. An independent review of
whether those encodings are faithful, and whether they are vacuous, is in
progress. Kato local existence, Fujita--Kato small-data global regularity, and
the Beale--Kato--Majda criterion itself are not formalized and are not locked.
-/

open ClassicalNS Set MeasureTheory
open scoped ContDiff

namespace TruthGatePillars

-- TRUTH-GATE LOCK BEGIN
def formal_claim_conditional : Prop :=
  ∀ (C_star : ℝ → ℝ), HypothesisB C_star → BKMCriterion → AnalyticBridgeStatement

def paper_claim_conditional : Prop :=
  ∀ (C_star : ℝ → ℝ),
    (∀ (ν : ℝ) (u0 : E3 → E3) (sol : NSSolution ν u0) (T : ℝ),
      0 < T → gradIntegral sol T ≤ ENNReal.ofReal (C_star T)) →
    (∀ (ν : ℝ) (u0 : E3 → E3) (sol : NSSolution ν u0),
      (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (gradLinf (sol.u t))) ≠ ⊤ →
        sol.Tstar = ⊤) →
    ∀ (ν : ℝ), 0 < ν → ∀ (u0 : E3 → E3),
      ContDiff ℝ ∞ u0 → IsPeriodic u0 → (∀ x, divergence u0 x = 0) →
      ∀ sol : NSSolution ν u0,
        sol.Tstar = ⊤ ∧ ∀ T : ℝ, 0 < T → gradIntegral sol T < ⊤

theorem intended_correspondence_conditional :
    formal_claim_conditional ↔ paper_claim_conditional := by
  constructor
  · intro hf C_star hB' hBKM'
    have hB : HypothesisB C_star := fun {ν} {u0} sol T hT =>
      hB' ν u0 sol T hT
    have bkm : BKMCriterion := fun {ν} {u0} sol hne => by
      by_contra hfin
      exact hne (hBKM' ν u0 sol hfin)
    exact hf C_star hB bkm
  · intro hp C_star hB bkm
    refine hp C_star ?_ ?_
    · intro ν u0 sol T hT
      exact hB sol T hT
    · intro ν u0 sol hfin
      by_contra hne
      exact hfin (bkm sol hne)
-- TRUTH-GATE LOCK END

theorem formal_claim_conditional_holds : formal_claim_conditional :=
  ClassicalNS.analyticBridge_of_formB_forall

theorem paper_claim_conditional_holds : paper_claim_conditional :=
  intended_correspondence_conditional.mp formal_claim_conditional_holds

end TruthGatePillars
