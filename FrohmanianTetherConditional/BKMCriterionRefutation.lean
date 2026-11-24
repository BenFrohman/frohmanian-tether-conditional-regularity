/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.ClassicalNS

/-!
# `BKMCriterion` quantifies over all data and is false

`NSSolution ν u₀` places no smoothness or periodicity requirement on `u₀` beyond
`u 0 = u₀`. With `T⋆ = 0` every lifespan condition is vacuous, and maximality holds
whenever `u₀` is not periodic: any extension to `T' > 0` would make `u₀ = u 0` periodic.
Such a solution has `T⋆ ≠ ⊤` and gradient integral `0`, so `BKMCriterion` fails.

`BKMCriterionSmooth` (in `ClassicalNS.lean`) restricts the statement to smooth, periodic,
divergence-free `u₀`.
-/

open Set MeasureTheory
open scoped ContDiff

namespace ClassicalNS

/-- The linear, non-periodic field `x ↦ x₁ e₁`. -/
noncomputable def rampU0 : E3 → E3 := fun x => (x 0) • e 0

lemma not_isPeriodic_rampU0 : ¬ IsPeriodic rampU0 := by
  intro h
  have h1 := congrArg (fun v : E3 => v 0) (h 0 0)
  simp [rampU0, e] at h1

lemma lifespan_zero : lifespan 0 = ∅ := by
  ext t
  simp [lifespan]

lemma openLifespan_zero : openLifespan 0 = ∅ := by
  ext t
  simp [openLifespan]

/-- A maximal solution object of lifespan `T⋆ = 0` with non-periodic initial datum. -/
noncomputable def rampSolution : NSSolution 1 rampU0 where
  visc_pos := one_pos
  Tstar := 0
  u := fun _ => rampU0
  p := fun _ _ => 0
  isNS :=
    { init := rfl
      periodic_u := by intro t ht; rw [lifespan_zero] at ht; simp at ht
      periodic_p := by intro t ht; rw [lifespan_zero] at ht; simp at ht
      smooth_u := by intro t ht; rw [lifespan_zero] at ht; simp at ht
      smooth_p := by intro t ht; rw [lifespan_zero] at ht; simp at ht
      jointSmooth_u := by rw [openLifespan_zero, Set.empty_prod]; exact contDiffOn_empty
      jointSmooth_p := by rw [openLifespan_zero, Set.empty_prod]; exact contDiffOn_empty
      cont_u := by rw [lifespan_zero, Set.empty_prod]; exact continuousOn_empty _
      cont_grad := by rw [lifespan_zero, Set.empty_prod]; exact continuousOn_empty _
      div_free := by intro t ht; rw [lifespan_zero] at ht; simp at ht
      momentum := by intro t ht; rw [openLifespan_zero] at ht; simp at ht }
  maximal := by
    intro T' v q hT' hv _
    have h0 : (0 : ℝ) ∈ lifespan T' := ⟨le_rfl, by simpa using hT'⟩
    have hper := hv.periodic_u 0 h0
    rw [hv.init] at hper
    exact not_isPeriodic_rampU0 hper

/-- **`BKMCriterion` is false.** -/
theorem not_BKMCriterion : ¬ BKMCriterion := by
  intro bkm
  have h := bkm rampSolution (by simp [rampSolution])
  simp [rampSolution] at h

/-- The unrestricted criterion implies `BKMCriterionSmooth` (defined in `ClassicalNS.lean`). -/
theorem bkmCriterionSmooth_of_bkmCriterion (bkm : BKMCriterion) : BKMCriterionSmooth :=
  fun _ _ _ sol hne => bkm sol hne

end ClassicalNS
