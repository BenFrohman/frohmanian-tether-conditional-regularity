-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import FrohmanianTetherConditional.FrohmanianTripleArchitecture
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lifespan-corrected `NavierStokesUnifiedData`

The original `FrohmanianTripleArchitecture.NavierStokesUnifiedData` (kept unchanged,
it is the file archived with the Tether Zenodo record) asks for continuity of
`strainSup` on **every** `[0, T]`. That already forces Hypothesis B, so its
`clayStatementB` holds for every data object
(`AnalyticBridgeRefutation.clayStatementB_holds`): the structure presupposes global
regularity and `three_way_equivalence` / `hypothesisB_implies_clayStatementB` carry no
information.

Here the data carry a lifespan `T⋆ : ℝ≥0∞`; all regularity requirements hold only on
`[0, T⋆)`; `clayStatementB` is *defined* as `T⋆ = ⊤`; the BKM field is the (cited)
one-directional continuation criterion with integrals taken only over lifespan times.

Non-vacuity, proved below:
* `zeroModel` (global) inhabits the structure and satisfies `clayStatementB`;
* `blowupModel` (`T⋆ = 1`, `‖ω‖_∞ = ‖S‖_∞ = (1 - t)⁻¹`) inhabits it and does **not**;
* hence `clayStatementB_not_automatic`, `hypothesisB_not_automatic` and
  `old_trivialization_fails`: the earlier "every data object satisfies Hypothesis B"
  argument no longer goes through.
These models are abstract scalar data (as in the original structure), not
Navier–Stokes solutions; they show only that the abstract implications are no longer
contentless.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral Filter Topology

namespace FrohmanianTripleArchitectureLifespan

structure NavierStokesUnifiedData where
  Tstar : ENNReal
  vorticitySup : ℝ → ℝ
  strainSup : ℝ → ℝ
  vorticity_nonneg : ∀ t, 0 ≤ t → ENNReal.ofReal t < Tstar → 0 ≤ vorticitySup t
  /-- BKM continuation (cited): bounded vorticity integrals on the lifespan ⇒ global. -/
  bkm_vorticity_criterion :
    (∀ T > 0, ∃ C_ω : ℝ, ∀ t ∈ Icc 0 T, ENNReal.ofReal t < Tstar →
      (∫ τ in (0 : ℝ)..t, vorticitySup τ) ≤ C_ω) → Tstar = ⊤
  /-- Regularity and `M' ≤ S·M` only on compact subintervals of the lifespan. -/
  differential_bounds : ∀ T > 0, ENNReal.ofReal T < Tstar →
    (∀ t ∈ Icc 0 T, DifferentiableAt ℝ vorticitySup t) ∧
    (ContinuousOn vorticitySup (Icc 0 T)) ∧
    (ContinuousOn strainSup (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, deriv vorticitySup t ≤ strainSup t * vorticitySup t)

/-- Clay (B) for this data: the lifespan is infinite. -/
def clayStatementB (sol : NavierStokesUnifiedData) : Prop := sol.Tstar = ⊤

def HypothesisB (sol : NavierStokesUnifiedData) : Prop :=
  ∀ T > 0, ∃ C_star : ℝ, ∀ t ∈ Icc 0 T, ENNReal.ofReal t < sol.Tstar →
    (∫ τ in (0 : ℝ)..t, sol.strainSup τ) ≤ C_star

def BKMVorticityIntegrable (sol : NavierStokesUnifiedData) : Prop :=
  ∀ T > 0, ∃ C_ω : ℝ, ∀ t ∈ Icc 0 T, ENNReal.ofReal t < sol.Tstar →
    (∫ τ in (0 : ℝ)..t, sol.vorticitySup τ) ≤ C_ω

/-- A continuous function on `[0, T]` has bounded primitives there. -/
lemma primitive_bounded {f : ℝ → ℝ} {T : ℝ} (_hT : 0 < T) (hf : ContinuousOn f (Icc 0 T)) :
    ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ τ in (0 : ℝ)..t, f τ) ≤ C := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨max K 0 * T, fun t ht => ?_⟩
  have hInt : IntervalIntegrable f volume 0 t := by
    have hc : ContinuousOn f (uIcc 0 t) := by
      simpa [uIcc_of_le ht.1] using hf.mono (Icc_subset_Icc_right ht.2)
    exact hc.intervalIntegrable
  calc ∫ τ in (0 : ℝ)..t, f τ
      ≤ ∫ _ in (0 : ℝ)..t, max K 0 := by
        apply integral_mono_on ht.1 hInt intervalIntegral.intervalIntegrable_const
        intro τ hτ
        have := hK τ ⟨hτ.1, hτ.2.trans ht.2⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    _ = max K 0 * t := by simp [mul_comm]
    _ ≤ max K 0 * T := mul_le_mul_of_nonneg_left ht.2 (le_max_right _ _)

/-- CONDITIONAL (on the cited BKM field): Hypothesis B ⇒ Clay (B). -/
theorem hypothesisB_implies_clayStatementB (sol : NavierStokesUnifiedData)
    (hB : HypothesisB sol) : clayStatementB sol := by
  apply sol.bkm_vorticity_criterion
  intro T hT
  obtain ⟨C, hC⟩ := hB T hT
  set M := |sol.vorticitySup 0| * Real.exp C
  have hM : 0 ≤ M := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨M * T, fun t ht hlife => ?_⟩
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · subst h0
    simp only [integral_same]
    exact mul_nonneg hM hT.le
  · obtain ⟨hDiff, hVC, hSC, hR⟩ := sol.differential_bounds t htpos hlife
    have h0life : ENNReal.ofReal 0 < sol.Tstar :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.1) hlife
    have hM0 : 0 ≤ sol.vorticitySup 0 := sol.vorticity_nonneg 0 le_rfl h0life
    have hptw : ∀ τ ∈ Icc 0 t, sol.vorticitySup τ ≤ M := by
      intro τ hτ
      have hG := FrohmanianTripleArchitecture.gronwall_differential_bound htpos.le hDiff hSC hR τ hτ
      have hτlife : ENNReal.ofReal τ < sol.Tstar :=
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hτ.2) hlife
      have hCτ := hC τ ⟨hτ.1, hτ.2.trans ht.2⟩ hτlife
      calc sol.vorticitySup τ
          ≤ sol.vorticitySup 0 * Real.exp (∫ r in (0 : ℝ)..τ, sol.strainSup r) := hG
        _ ≤ sol.vorticitySup 0 * Real.exp C :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hCτ) hM0
        _ ≤ M := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    have hInt : IntervalIntegrable sol.vorticitySup volume 0 t := by
      have hc : ContinuousOn sol.vorticitySup (uIcc 0 t) := by
        simpa [uIcc_of_le ht.1] using hVC
      exact hc.intervalIntegrable
    calc ∫ τ in (0 : ℝ)..t, sol.vorticitySup τ
        ≤ ∫ _ in (0 : ℝ)..t, M :=
          integral_mono_on ht.1 hInt intervalIntegral.intervalIntegrable_const hptw
      _ = M * t := by simp [mul_comm]
      _ ≤ M * T := mul_le_mul_of_nonneg_left ht.2 hM

/-- CONDITIONAL (on the cited BKM field): the three statements are equivalent. -/
theorem three_way_equivalence (sol : NavierStokesUnifiedData) :
    (HypothesisB sol ↔ BKMVorticityIntegrable sol) ∧
    (BKMVorticityIntegrable sol ↔ clayStatementB sol) := by
  have life : clayStatementB sol → ∀ T : ℝ, ENNReal.ofReal T < sol.Tstar := by
    intro h T; rw [clayStatementB] at h; rw [h]; exact ENNReal.ofReal_lt_top
  have clay_bkm : clayStatementB sol → BKMVorticityIntegrable sol := by
    intro h T hT
    obtain ⟨C, hC⟩ := primitive_bounded hT (sol.differential_bounds T hT (life h T)).2.1
    exact ⟨C, fun t ht _ => hC t ht⟩
  have clay_hypB : clayStatementB sol → HypothesisB sol := by
    intro h T hT
    obtain ⟨C, hC⟩ := primitive_bounded hT (sol.differential_bounds T hT (life h T)).2.2.1
    exact ⟨C, fun t ht _ => hC t ht⟩
  have bkm_clay : BKMVorticityIntegrable sol → clayStatementB sol :=
    fun h => sol.bkm_vorticity_criterion h
  exact ⟨⟨fun h => clay_bkm (hypothesisB_implies_clayStatementB sol h),
      fun h => clay_hypB (bkm_clay h)⟩, ⟨bkm_clay, clay_bkm⟩⟩

/-! ## Non-vacuity models -/

/-- Global model: all quantities zero, `T⋆ = ⊤`. -/
def zeroModel : NavierStokesUnifiedData where
  Tstar := ⊤
  vorticitySup := fun _ => 0
  strainSup := fun _ => 0
  vorticity_nonneg := fun _ _ _ => le_rfl
  bkm_vorticity_criterion := fun _ => rfl
  differential_bounds := fun _ _ _ =>
    ⟨fun _ _ => differentiableAt_const _, continuousOn_const, continuousOn_const,
      fun _ _ => by simp⟩

theorem clayStatementB_zeroModel : clayStatementB zeroModel := rfl

/-- `∫₀ᵗ (1 - τ)⁻¹ dτ = log (1 / (1 - t))` for `t < 1`. -/
lemma integral_inv_one_sub {t : ℝ} (ht : t < 1) :
    (∫ τ in (0 : ℝ)..t, (1 - τ)⁻¹) = Real.log (1 / (1 - t)) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t)
    (fun x : ℝ => x⁻¹) (1 : ℝ)
  simp only at h
  rw [h, sub_zero, integral_inv_of_pos (by linarith) one_pos]

/-- Blow-up model: `T⋆ = 1`, `‖ω‖_∞ = ‖S‖_∞ = (1 - t)⁻¹` (so `M' = S·M`). -/
def blowupModel : NavierStokesUnifiedData where
  Tstar := 1
  vorticitySup := fun t => (1 - t)⁻¹
  strainSup := fun t => (1 - t)⁻¹
  vorticity_nonneg := fun t _ ht => by
    rw [ENNReal.ofReal_lt_one] at ht
    exact inv_nonneg.2 (by linarith)
  bkm_vorticity_criterion := by
    intro h
    exfalso
    obtain ⟨C, hC⟩ := h 1 one_pos
    set a := Real.exp (-(|C| + 1)) with ha
    have ha0 : 0 < a := Real.exp_pos _
    have ha1 : a < 1 := Real.exp_lt_one_iff.2 (by linarith [abs_nonneg C])
    have hlt : 1 - a < 1 := by linarith
    have hbound := hC (1 - a) ⟨by linarith, by linarith⟩ (ENNReal.ofReal_lt_one.2 hlt)
    rw [integral_inv_one_sub hlt] at hbound
    have h1a : 1 - (1 - a) = a := by ring
    rw [h1a, one_div, Real.log_inv, ha, Real.log_exp] at hbound
    linarith [le_abs_self C]
  differential_bounds := by
    intro T _ hT
    rw [ENNReal.ofReal_lt_one] at hT
    have hne : ∀ t ∈ Icc 0 T, (1 - t) ≠ 0 := fun t ht => by linarith [ht.2]
    have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t : ℝ => (1 - t)⁻¹) (-(-1) / (1 - t) ^ 2) t :=
      fun t ht => ((hasDerivAt_id' t).const_sub 1).inv (hne t ht)
    have hcont : ContinuousOn (fun t : ℝ => (1 - t)⁻¹) (Icc 0 T) :=
      (continuousOn_const.sub continuousOn_id).inv₀ hne
    refine ⟨fun t ht => (hd t ht).differentiableAt, hcont, hcont, fun t ht => ?_⟩
    rw [(hd t ht).deriv]
    apply le_of_eq
    have := hne t ht
    field_simp

theorem blowupModel_not_clay : ¬ clayStatementB blowupModel := ENNReal.one_ne_top

/-- `clayStatementB` is no longer automatic. -/
theorem clayStatementB_not_automatic : ∃ sol : NavierStokesUnifiedData, ¬ clayStatementB sol :=
  ⟨blowupModel, blowupModel_not_clay⟩

theorem hypothesisB_not_automatic : ∃ sol : NavierStokesUnifiedData, ¬ HypothesisB sol :=
  ⟨blowupModel, fun h => blowupModel_not_clay (hypothesisB_implies_clayStatementB _ h)⟩

/-- The earlier trivialization (`∀ sol, HypothesisB sol`) fails for corrected data. -/
theorem old_trivialization_fails : ¬ ∀ sol : NavierStokesUnifiedData, HypothesisB sol :=
  fun h => blowupModel_not_clay (hypothesisB_implies_clayStatementB _ (h blowupModel))

end FrohmanianTripleArchitectureLifespan
