-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import FrohmanianTetherConditional.AnalyticBridgeTarget
import FrohmanianTetherConditional.FrohmanianTripleArchitecture

/-!
# The analytic bridge target, as currently formalized, is false

This file does **not** prove or disprove Clay Millennium Problem (B). It shows that
the Lean *encoding* in `AnalyticBridgeTarget.lean` cannot be proved, because it is
refutable, and it records two vacuity defects in the surrounding abstractions.

Root cause: `NSSolution` does not encode the Navier–Stokes equations. `solves_NS` and
`maximal` are fields of type `Prop` (arbitrary propositions, never required to hold),
and `Tstar` is an arbitrary element of `ENNReal`. So the zero field with lifespan
`Tstar = 1` is a valid `NSSolution`, for every `NormData` and every viscosity.

* `zeroSolution` : that object.
* `analytic_bridge_unconditional_false` : the negation of the exact statement of
  `analytic_bridge_unconditional` (same binders, same conclusion).
* `not_nonempty_BKMCriterion` : `BKMCriterion N` is uninhabited for **every** `N`.
  So `clayB_iff_bkm_integrable`, `formB_implies_clayB`, `hypothesisB_implies_clayB`
  and `formB_Hs_bound` are vacuously true: no `bkm` argument can ever be supplied.
* `FrohmanianTripleArchitecture`-side: `differential_bounds` asks for continuity of
  `strainSup` on every `[0, T]`, which already forces Hypothesis B; so
  `hypothesisB_holds` and `clayStatementB_holds` prove both for *every*
  `NavierStokesUnifiedData`, i.e. that structure presupposes global regularity.

All proofs here use only `propext`, `Classical.choice`, `Quot.sound`.
-/

open Real Set MeasureTheory intervalIntegral Filter Topology

namespace AnalyticBridgeRefutation

/-- The zero velocity field, declared to live on `[0, 1)`. Valid for every `N`, `ν`. -/
def zeroSolution (N : NormData) (ν : ℝ) : NSSolution N ν (fun _ => 0) where
  Tstar := 1
  u := fun _ _ => 0
  init := rfl
  periodic := fun _ _ _ => rfl
  smooth := fun _ _ _ => contDiff_const
  vort_cont := continuousOn_const
  grad_cont := continuousOn_const
  HsR_cont := fun _ => continuousOn_const
  solves_NS := True
  maximal := True

lemma zeroSolution_Tstar_ne_top (N : NormData) (ν : ℝ) :
    (zeroSolution N ν).Tstar ≠ ⊤ := ENNReal.one_ne_top

lemma zeroSolution_gradInt (N : NormData) (ν : ℝ) (T : ℝ) :
    IntervalIntegrable (fun t => N.gradLinf ((zeroSolution N ν).u t)) volume 0 T :=
  show IntervalIntegrable (fun _ => N.gradLinf (fun _ => 0)) volume 0 T from
    intervalIntegral.intervalIntegrable_const

lemma isPeriodic_zero : IsPeriodic (fun _ : R3 => (0 : Vec3)) := fun _ _ => rfl

/-- A concrete `NormData` (all norms zero), so the finiteness hypothesis holds. -/
def zeroNorms : NormData where
  Hs := fun _ _ => 0
  HsR := fun _ _ => 0
  vortLinf := fun _ => 0
  gradLinf := fun _ => 0
  HsR_nonneg := fun _ _ => le_rfl
  gradLinf_nonneg := fun _ => le_rfl

/-- The exact statement of `analytic_bridge_unconditional` is refutable. -/
theorem analytic_bridge_unconditional_false :
    ¬ (∀ (N : NormData) (ν : ℝ) (_hν : 0 < ν) (s : ℝ) (_hs : 5 / 2 < s)
        (u0 : R3 → Vec3) (_hper : IsPeriodic u0) (_hu0 : N.Hs s u0 < ⊤),
        ∀ sol : NSSolution N ν u0,
          sol.Tstar = ⊤ ∧
          ∀ T : ℝ, 0 < T →
            IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T) := by
  intro h
  have hs : (5 : ℝ) / 2 < 3 := by norm_num
  have hfin : zeroNorms.Hs 3 (fun _ => 0) < ⊤ := ENNReal.zero_lt_top
  exact zeroSolution_Tstar_ne_top zeroNorms 1
    (h zeroNorms 1 one_pos 3 hs (fun _ => 0) isPeriodic_zero hfin (zeroSolution zeroNorms 1)).1

/-- Same result stated against the *literal* type of `analytic_bridge_unconditional`
(read off the declaration with `type_of%`), so no restatement drift is possible.
Only the type is used, not the (open-target) proof term. -/
theorem analytic_bridge_target_statement_false :
    ¬ (type_of% @analytic_bridge_unconditional) :=
  fun h => analytic_bridge_unconditional_false h

/-- Stronger: for every `NormData`, every `ν`, `s`, the target fails at `u0 = 0`
as soon as `N.Hs s 0 < ⊤`. -/
theorem analytic_bridge_fails_at_zero (N : NormData) (ν : ℝ) :
    ∃ sol : NSSolution N ν (fun _ => 0), sol.Tstar ≠ ⊤ ∧
      ∀ T : ℝ, IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T :=
  ⟨zeroSolution N ν, zeroSolution_Tstar_ne_top N ν, zeroSolution_gradInt N ν⟩

/-- `BKMCriterion N` is uninhabited for every `N`: the cited continuation input is
inconsistent with the `NSSolution` encoding. -/
theorem not_nonempty_BKMCriterion (N : NormData) : ¬ Nonempty (BKMCriterion N) := by
  rintro ⟨bkm⟩
  exact zeroSolution_Tstar_ne_top N 0
    (bkm.continuation (zeroSolution N 0) (fun T _ => zeroSolution_gradInt N 0 T))

/-- Consequently any statement taking a `BKMCriterion` argument is vacuous; e.g.
it yields `False`. -/
theorem BKMCriterion_elim {N : NormData} (bkm : BKMCriterion N) : False :=
  not_nonempty_BKMCriterion N ⟨bkm⟩

open FrohmanianTripleArchitecture in
/-- In `FrohmanianTripleArchitecture`, `differential_bounds` already forces
Hypothesis B for every data object. -/
theorem hypothesisB_holds (sol : NavierStokesUnifiedData) :
    FrohmanianTripleArchitecture.HypothesisB sol := by
  intro T hT
  have hcont : ContinuousOn sol.strainSup (Icc 0 T) := (sol.differential_bounds T hT).2.2.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0 * T, ?_⟩
  intro t ht
  have hInt : IntervalIntegrable sol.strainSup volume 0 t := by
    have hc : ContinuousOn sol.strainSup (uIcc 0 t) := by
      simpa [uIcc_of_le ht.1] using hcont.mono (Icc_subset_Icc_right ht.2)
    exact hc.intervalIntegrable
  calc ∫ τ in (0 : ℝ)..t, sol.strainSup τ
      ≤ ∫ _ in (0 : ℝ)..t, max C 0 := by
        apply integral_mono_on ht.1 hInt intervalIntegral.intervalIntegrable_const
        intro τ hτ
        have hτT : τ ∈ Icc 0 T := ⟨hτ.1, le_trans hτ.2 ht.2⟩
        exact le_trans (le_abs_self _) (le_trans (hC τ hτT) (le_max_left _ _))
    _ = max C 0 * t := by simp [mul_comm]
    _ ≤ max C 0 * T := mul_le_mul_of_nonneg_left ht.2 (le_max_right _ _)

open FrohmanianTripleArchitecture in
/-- Hence `clayStatementB` holds for every `NavierStokesUnifiedData`: the structure
presupposes global regularity rather than deriving it. -/
theorem clayStatementB_holds (sol : NavierStokesUnifiedData) : sol.clayStatementB :=
  hypothesisB_implies_clayStatementB sol (hypothesisB_holds sol)

end AnalyticBridgeRefutation
