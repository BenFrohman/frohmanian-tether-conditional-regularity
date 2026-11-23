/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.ClassicalNS

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/Frohmanian_Tether_Unified.tex
PAPER_SHA256: e8723c81b7d94f595b053e8e260c8037f349960951a6612f18b98b73f46703f4
PAPER_SECTION: Section 2 "The Lean hypotheses and the certified implication", Definitions def:hypB, def:bkm, def:bridge, and Theorem thm:A

Locked paper claim: Theorem `thm:A` ("Conditional implication"), together with
Definitions `def:hypB`, `def:bkm` and `def:bridge`, from which the two hypotheses
and the conclusion are independently transcribed.

PAPER_QUOTE_BEGIN
\begin{definition}[Hypothesis~B, Lean \texttt{HypothesisB}]\label{def:hypB}
For a bound \(C_\star:\R\to\R\), Hypothesis~B says: for every viscosity \(\nu\), every initial datum \(\uvec_0\), every maximal classical solution \(\mathrm{sol}\), and every \(T>0\),
\[
\texttt{gradIntegral}(\mathrm{sol},T)\le \texttt{ENNReal.ofReal}(C_\star(T)).
\]
\end{definition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Named BKM hypothesis, Lean \texttt{BKMCriterion}]\label{def:bkm}
\texttt{BKMCriterion} says: for every maximal classical solution with \(T^\star\neq\top\),
\[
\int_{[0,T^\star)}^\texttt{-}\texttt{ENNReal.ofReal}(\texttt{gradLinf}(\uvec(t)))\,dt=\top.
\]
This is a named hypothesis in the Lean development, written after the Beale--Kato--Majda continuation criterion~\cite{BKM1984}. It is not proved in Lean.
\end{definition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{definition}[Analytic bridge statement, Lean \texttt{AnalyticBridgeStatement}]\label{def:bridge}
The analytic bridge statement says: for every \(\nu>0\) and every smooth, periodic, divergence-free initial datum \(\uvec_0\), every maximal classical solution satisfies \(T^\star=\top\) and \(\texttt{gradIntegral}(\mathrm{sol},T)<\top\) for every \(T>0\).
\end{definition}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[Conditional implication, Lean \texttt{analyticBridge\_of\_formB} / \texttt{analyticBridge\_of\_formB\_forall}]\label{thm:A}
For every bound \(C_\star:\R\to\R\), if Hypothesis~B holds for \(C_\star\) and if \texttt{BKMCriterion} holds, then the analytic bridge statement holds.
\end{theorem}
PAPER_QUOTE_END

`formal_claim` is the statement of `ClassicalNS.analyticBridge_of_formB_forall`.
`paper_claim` writes Hypothesis~B, the named BKM hypothesis (in contrapositive form:
if the lower integral on `[0, T⋆)` is not `⊤`, then `T⋆ = ⊤`), and the analytic
bridge conclusion out in full from the English of `def:hypB`, `def:bkm` and
`def:bridge`. It does not name, unfold, or otherwise refer to the repository Props
`HypothesisB`, `BKMCriterion` or `AnalyticBridgeStatement`, nor to `formal_claim`.

Scope: CONDITIONAL. The two hypotheses are assumptions, not theorems of this
development. An independent review of whether those encodings are faithful, and
whether they are vacuous, is in progress. This lock certifies only the implication.
It is not a proof of Clay Millennium Problem Statement~(B).
-/

open ClassicalNS Set MeasureTheory
open scoped ContDiff

namespace TruthGate

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`analyticBridge_of_formB_forall`). -/
def formal_claim : Prop :=
  ∀ (C_star : ℝ → ℝ), HypothesisB C_star → BKMCriterion → AnalyticBridgeStatement

/-- The paper's Theorem thm:A. Hypothesis~B, the named BKM hypothesis, and the
analytic-bridge conclusion are written out from Definitions def:hypB, def:bkm and
def:bridge. The BKM hypothesis is transcribed in contrapositive form. -/
def paper_claim : Prop :=
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

theorem intended_correspondence : formal_claim ↔ paper_claim := by
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

theorem formal_claim_holds : formal_claim :=
  ClassicalNS.analyticBridge_of_formB_forall

theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
