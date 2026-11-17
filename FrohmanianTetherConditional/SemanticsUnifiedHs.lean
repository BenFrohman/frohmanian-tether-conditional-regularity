/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.ClassicalNS

/-!
# Truth Gate: lock for the companion `formB_Hs_bound` paragraph of the Unified paper

PAPER_PATH: paper/Frohmanian_Tether_Unified.tex
PAPER_SHA256: e8723c81b7d94f595b053e8e260c8037f349960951a6612f18b98b73f46703f4
PAPER_SECTION: Section 2 "The Lean hypotheses and the certified implication", the companion paragraph on formB_Hs_bound

PAPER_QUOTE_BEGIN
A companion Lean theorem, \texttt{formB\_Hs\_bound}, gives a direct \(H^s\)-style bound under the additional named hypothesis \texttt{KatoPonceEnergy} (a cited Kato--Ponce energy inequality on genuine solutions, not proved in Lean): on \([0,T]\),
\[
\texttt{HsR}(s,\uvec(t))\le \texttt{HsR}(s,\uvec_0)\exp\bigl(C_s\max(C_\star(T),0)\bigr).
\]
The content of that bound for a zero dummy norm is trivial (\texttt{kp\_trivial}); its intended content is for a true \(H^s\) norm, which Mathlib does not yet supply on \(\T^3\).
PAPER_QUOTE_END

`formal_claim_hsbound` is the statement of `ClassicalNS.formB_Hs_bound`.
`paper_claim_hsbound` writes the named hypotheses and the bound out from the
English of that paragraph, with membership in `[0,T]` written as `0 ≤ t ∧ t ≤ T`,
and with the named BKM hypothesis in contrapositive form.
-/

open ClassicalNS Set MeasureTheory
open scoped ContDiff intervalIntegral

namespace TruthGateUnifiedHs

-- TRUTH-GATE LOCK BEGIN
def formal_claim_hsbound : Prop :=
  ∀ {HsR : ℝ → (E3 → E3) → ℝ} {s C_s : ℝ}, KatoPonceEnergy HsR s C_s →
    ∀ {C_star : ℝ → ℝ}, HypothesisB C_star → BKMCriterion →
      ∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (T : ℝ),
        0 < T → ∀ t ∈ Icc 0 T, HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max (C_star T) 0)

def paper_claim_hsbound : Prop :=
  ∀ (HsR : ℝ → (E3 → E3) → ℝ) (s C_s : ℝ),
    (∀ f, 0 ≤ HsR s f) → 0 ≤ C_s →
    (∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (T : ℝ),
      0 ≤ T → ENNReal.ofReal T < sol.Tstar →
        ContinuousOn (fun t => HsR s (sol.u t)) (Icc 0 T)) →
    (∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (t : ℝ),
      t ∈ lifespan sol.Tstar →
        HsR s (sol.u t) ≤
          HsR s u0 + ∫ τ in (0 : ℝ)..t, C_s * gradLinf (sol.u τ) * HsR s (sol.u τ)) →
    ∀ (C_star : ℝ → ℝ),
      (∀ (ν : ℝ) (u0 : E3 → E3) (sol : NSSolution ν u0) (T : ℝ),
        0 < T → gradIntegral sol T ≤ ENNReal.ofReal (C_star T)) →
      (∀ (ν : ℝ) (u0 : E3 → E3) (sol : NSSolution ν u0),
        (∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (gradLinf (sol.u t))) ≠ ⊤ →
          sol.Tstar = ⊤) →
      ∀ (ν : ℝ) (u0 : E3 → E3) (sol : NSSolution ν u0) (T : ℝ),
        0 < T → ∀ t : ℝ, 0 ≤ t ∧ t ≤ T →
          HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max (C_star T) 0)

theorem intended_correspondence_hsbound :
    formal_claim_hsbound ↔ paper_claim_hsbound := by
  constructor
  · intro hf HsR s C_s hnn hC hcont hE C_star hB' hBKM' ν u0 sol T hTpos t ht
    have kp : KatoPonceEnergy HsR s C_s :=
      { HsR_nonneg := hnn
        C_s_nonneg := hC
        HsR_cont := hcont
        energy := hE }
    have hB : HypothesisB C_star := by
      intro sol' T' hT'
      exact hB' _ _ sol' T' hT'
    have bkm : BKMCriterion := by
      intro sol' hne
      by_contra hfin
      exact hne (hBKM' _ _ sol' hfin)
    exact hf kp hB bkm sol T hTpos t ⟨ht.1, ht.2⟩
  · intro hp HsR s C_s kp C_star hB bkm ν u0 sol T hTpos t ht
    refine hp HsR s C_s kp.HsR_nonneg kp.C_s_nonneg kp.HsR_cont kp.energy C_star ?_ ?_
        ν u0 sol T hTpos t ⟨ht.1, ht.2⟩
    · intro ν' u0' sol' T' hT'
      exact hB sol' T' hT'
    · intro ν' u0' sol' hfin
      by_contra hne
      exact hfin (bkm sol' hne)
-- TRUTH-GATE LOCK END

theorem formal_claim_hsbound_holds : formal_claim_hsbound :=
  fun {_} {_} {_} => ClassicalNS.formB_Hs_bound

theorem paper_claim_hsbound_holds : paper_claim_hsbound :=
  intended_correspondence_hsbound.mp formal_claim_hsbound_holds

end TruthGateUnifiedHs
