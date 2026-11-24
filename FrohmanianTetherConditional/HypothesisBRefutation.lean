/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import FrohmanianTetherConditional.BKMCriterionRefutation

/-!
# The uniform Hypothesis B is false; Form B per solution

`ClassicalNS.HypothesisB C⋆` asks for one bound `∫₀ᵀ ‖∇u‖_∞ ≤ C⋆(T)` that is uniform over
every viscosity `ν`, every initial datum `u₀` and every maximal classical solution.
No such bound exists. The decaying shear flow

  `u(t, x) = A e^{-4π²νt} sin(2πx₂) e₁`,  `p = 0`

(coordinates `x₁, x₂, x₃` are `x 0, x 1, x 2` in Lean) is an exact global classical solution:
the advection term `(u·∇)u` vanishes, `∂ₜu = νΔu` and `div u = 0`. Its gradient has
`‖∇u(t)‖_∞ ≥ 2π A e^{-4π²νt}`, so `∫₀ᵀ ‖∇u‖_∞ ≥ 2π A e^{-4π²νT} T`, which exceeds any
given number for large `A`. Hence `¬ HypothesisB C⋆` for every `C⋆`
(`not_hypothesisB`), and `analyticBridge_of_formB_forall` holds only vacuously.

The statement with content is Form B **per solution**: for every smooth periodic
divergence-free datum, every maximal solution and every `T > 0`, the integral
`∫₀ᵀ ‖∇u‖_∞` is bounded by some real number (depending on the solution and `T`).
Given the cited `BKMCriterion` it is equivalent to the analytic bridge statement
(Clay (B) for this class): `formBPerSolution_iff_analyticBridge`. Its converse
direction needs no hypothesis (`formBPerSolution_of_analyticBridge`). Whether it holds is
OPEN; nothing here proves it.
-/

open Real Set MeasureTheory intervalIntegral Filter Topology
open scoped ContDiff

namespace ClassicalNS

/-! ## Coordinates and derivatives along `x₂` -/

lemma e_apply (i j : Fin 3) : (e i) j = if j = i then 1 else 0 := by
  simp [e, PiLp.single_apply]

lemma norm_e (i : Fin 3) : ‖e i‖ = 1 := by
  simp [e]

lemma hasFDerivAt_coord (k : Fin 3) (x : E3) :
    HasFDerivAt (fun y : E3 => y k) (EuclideanSpace.proj (𝕜 := ℝ) k) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt

lemma contDiff_coord (k : Fin 3) : ContDiff ℝ ∞ (fun y : E3 => y k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff

/-- `∂ᵢ (f(x₂)) = f'(x₂) · (eᵢ)₂`. -/
lemma pd_comp_coord1 (i : Fin 3) {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s) (x : E3) :
    pd i (fun y => f (y 1)) x = f' (x 1) * (e i) 1 := by
  have h := (hf (x 1)).comp_hasFDerivAt x (hasFDerivAt_coord 1 x)
  have h' : HasFDerivAt (fun y : E3 => f (y 1)) (f' (x 1) • EuclideanSpace.proj (𝕜 := ℝ) 1) x :=
    h
  simp [pd, h'.fderiv]

lemma hasDerivAt_sin2pi (c s : ℝ) :
    HasDerivAt (fun s => c * Real.sin (2 * π * s)) (c * (2 * π) * Real.cos (2 * π * s)) s := by
  have h := (((hasDerivAt_id s).const_mul (2 * π)).sin).const_mul c
  convert h using 1
  simp only [id, mul_one]
  ring

lemma hasDerivAt_cos2pi (c s : ℝ) :
    HasDerivAt (fun s => c * Real.cos (2 * π * s)) (-(c * (2 * π)) * Real.sin (2 * π * s)) s := by
  have h := (((hasDerivAt_id s).const_mul (2 * π)).cos).const_mul c
  convert h using 1
  simp only [id, mul_one]
  ring

/-! ## The decaying shear flow -/

/-- Amplitude `a(t) = A e^{-4π²νt}`. -/
noncomputable def shearAmp (A ν t : ℝ) : ℝ := A * Real.exp (-(4 * π ^ 2 * ν) * t)

/-- `u(t, x) = a(t) sin(2πx₂) e₁`. -/
noncomputable def shearU (A ν : ℝ) (t : ℝ) (x : E3) : E3 :=
  (shearAmp A ν t * Real.sin (2 * π * x 1)) • e 0

/-- Zero pressure. -/
def shearP : ℝ → E3 → ℝ := fun _ _ => 0

lemma shearU_apply (A ν t : ℝ) (x : E3) (j : Fin 3) :
    shearU A ν t x j = shearAmp A ν t * Real.sin (2 * π * x 1) * (e 0) j := by
  simp [shearU]

lemma comp_shearU (A ν t : ℝ) (j : Fin 3) :
    comp (shearU A ν t) j =
      fun y => (shearAmp A ν t * (e 0) j) * Real.sin (2 * π * y 1) := by
  funext y
  simp only [comp, shearU_apply]
  ring

lemma pd_comp_shearU (A ν t : ℝ) (i j : Fin 3) :
    pd i (comp (shearU A ν t) j) =
      fun x => (shearAmp A ν t * (e 0) j) * (2 * π) * (e i) 1 * Real.cos (2 * π * x 1) := by
  funext x
  rw [comp_shearU]
  rw [pd_comp_coord1 i (fun s => hasDerivAt_sin2pi (shearAmp A ν t * (e 0) j) s) x]
  ring

lemma laplacian_shearU (A ν t : ℝ) (j : Fin 3) (x : E3) :
    laplacian (shearU A ν t) j x =
      -(4 * π ^ 2) * (shearAmp A ν t * Real.sin (2 * π * x 1) * (e 0) j) := by
  simp only [laplacian]
  have hi : ∀ i : Fin 3, pd i (pd i (comp (shearU A ν t) j)) x =
      -((shearAmp A ν t * (e 0) j) * (2 * π) * (e i) 1 * (2 * π)) * Real.sin (2 * π * x 1)
        * (e i) 1 := by
    intro i
    rw [pd_comp_shearU]
    exact pd_comp_coord1 i
      (fun s => hasDerivAt_cos2pi ((shearAmp A ν t * (e 0) j) * (2 * π) * (e i) 1) s) x
  simp only [hi, Fin.sum_univ_three, e_apply]
  simp
  ring

lemma advection_shearU (A ν t : ℝ) (j : Fin 3) (x : E3) :
    advection (shearU A ν t) j x = 0 := by
  simp only [advection, pd_comp_shearU, shearU_apply, Fin.sum_univ_three, e_apply]
  simp

lemma divergence_shearU (A ν t : ℝ) (x : E3) : divergence (shearU A ν t) x = 0 := by
  simp only [divergence, pd_comp_shearU, Fin.sum_univ_three, e_apply]
  simp

lemma jointContDiff_shearU (A ν : ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ × E3 => shearU A ν q.1 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × E3 => q.2 1) := (contDiff_coord 1).comp contDiff_snd
  have ha : ContDiff ℝ ∞ (fun q : ℝ × E3 => shearAmp A ν q.1) := by
    unfold shearAmp
    exact contDiff_const.mul ((contDiff_const.mul contDiff_fst).exp)
  exact (ha.mul ((contDiff_const.mul h1).sin)).smul contDiff_const

lemma contDiff_shearU (A ν t : ℝ) : ContDiff ℝ ∞ (shearU A ν t) :=
  (jointContDiff_shearU A ν).comp (contDiff_const.prodMk contDiff_id)

lemma periodic_shearU (A ν t : ℝ) : IsPeriodic (shearU A ν t) := by
  intro x i
  have hx : (x + e i) 1 = x 1 + (e i) 1 := rfl
  simp only [shearU, hx, e_apply]
  fin_cases i <;> simp [mul_add, Real.sin_add_two_pi]

lemma hasDerivAt_shearAmp (A ν t : ℝ) :
    HasDerivAt (fun τ => shearAmp A ν τ) (-(4 * π ^ 2 * ν) * shearAmp A ν t) t := by
  unfold shearAmp
  have h := (((hasDerivAt_id t).const_mul (-(4 * π ^ 2 * ν))).exp).const_mul A
  convert h using 1
  simp only [id, mul_one]
  ring

/-- The decaying shear flow is a global classical solution (`T⋆ = ⊤`). -/
theorem shear_isClassicalNS (A ν : ℝ) :
    IsClassicalNS ν (shearU A ν 0) (shearU A ν) shearP ⊤ where
  init := rfl
  periodic_u := fun t _ => periodic_shearU A ν t
  periodic_p := fun _ _ _ _ => rfl
  smooth_u := fun t _ => contDiff_shearU A ν t
  smooth_p := fun _ _ => contDiff_const
  jointSmooth_u := (jointContDiff_shearU A ν).contDiffOn
  jointSmooth_p := contDiffOn_const
  cont_u := (jointContDiff_shearU A ν).continuous.continuousOn
  cont_grad := by
    have h : ContDiff ℝ ∞ (Function.uncurry fun (q : ℝ × E3) (y : E3) => shearU A ν q.1 y) :=
      (jointContDiff_shearU A ν).comp (contDiff_fst.fst.prodMk contDiff_snd)
    have h0 : ContDiff ℝ 0 (fun q : ℝ × E3 => fderiv ℝ (shearU A ν q.1) q.2) :=
      h.fderiv contDiff_snd (by simp)
    exact h0.continuous.continuousOn
  div_free := fun t _ x => divergence_shearU A ν t x
  momentum := by
    intro t _ x j
    have hp : pd j (shearP t) x = 0 := by simp [shearP]
    rw [laplacian_shearU, advection_shearU, hp]
    have h := (hasDerivAt_shearAmp A ν t).mul_const (Real.sin (2 * π * x 1) * (e 0) j)
    convert h using 1
    · funext τ; rw [shearU_apply]; ring
    · ring

/-- The shear flow as a maximal solution (global, so maximality is automatic). -/
noncomputable def shearSolution (A ν : ℝ) (hν : 0 < ν) : NSSolution ν (shearU A ν 0) where
  visc_pos := hν
  Tstar := ⊤
  u := shearU A ν
  p := shearP
  isNS := shear_isClassicalNS A ν
  maximal := fun _ _ _ h _ _ => (not_top_lt h).elim

/-! ## Lower bound for `‖∇u(t)‖_∞` -/

/-- The point `0 ∈ [0,1]³`. -/
lemma zero_mem_cube : (0 : E3) ∈ cube :=
  ⟨fun _ => 0, fun _ _ => ⟨le_rfl, zero_le_one⟩, by ext i; simp⟩

lemma gradLinf_shearU_ge (A ν t : ℝ) :
    2 * π * |shearAmp A ν t| ≤ gradLinf (shearU A ν t) := by
  set g : ℝ → ℝ := fun s => shearAmp A ν t * Real.sin (2 * π * s)
  have hg := hasDerivAt_sin2pi (shearAmp A ν t) ((0 : E3) 1)
  have hc : HasFDerivAt (fun y : E3 => g (y 1))
      ((shearAmp A ν t * (2 * π) * Real.cos (2 * π * (0 : E3) 1)) •
        EuclideanSpace.proj (𝕜 := ℝ) 1) 0 :=
    hg.comp_hasFDerivAt (0 : E3) (hasFDerivAt_coord 1 0)
  have hF : HasFDerivAt (shearU A ν t)
      (((shearAmp A ν t * (2 * π) * Real.cos (2 * π * (0 : E3) 1)) •
        EuclideanSpace.proj (𝕜 := ℝ) 1).smulRight (e 0)) 0 :=
    hc.smul_const (e 0)
  have hval : ‖fderiv ℝ (shearU A ν t) 0 (e 1)‖ = 2 * π * |shearAmp A ν t| := by
    rw [hF.fderiv]
    simp [e_apply, norm_e, abs_mul, abs_of_pos Real.pi_pos]
    ring
  have hle : ‖fderiv ℝ (shearU A ν t) 0 (e 1)‖ ≤ ‖fderiv ℝ (shearU A ν t) 0‖ := by
    simpa [norm_e] using (fderiv ℝ (shearU A ν t) 0).le_opNorm (e 1)
  have hcont : ContinuousOn (fun x => ‖fderiv ℝ (shearU A ν t) x‖) cube :=
    ((contDiff_shearU A ν t).continuous_fderiv (by simp)).norm.continuousOn
  have hbdd := isCompact_cube.bddAbove_image hcont
  calc 2 * π * |shearAmp A ν t| = ‖fderiv ℝ (shearU A ν t) 0 (e 1)‖ := hval.symm
    _ ≤ ‖fderiv ℝ (shearU A ν t) 0‖ := hle
    _ ≤ gradLinf (shearU A ν t) := le_csSup hbdd (mem_image_of_mem _ zero_mem_cube)

/-- `∫₀ᵀ ‖∇u‖_∞ ≥ 2π A e^{-4π²νT} T` for the shear flow with `A ≥ 0`. -/
theorem gradIntegral_shear_ge (A ν : ℝ) (hν : 0 < ν) (hA : 0 ≤ A) (T : ℝ) (hT : 0 < T) :
    ENNReal.ofReal (2 * π * A * Real.exp (-(4 * π ^ 2 * ν) * T) * T) ≤
      gradIntegral (shearSolution A ν hν) T := by
  have hset : lifeIco (shearSolution A ν hν).Tstar T = Ico 0 T := by
    ext t
    simp [lifeIco, shearSolution]
  set c := 2 * π * A * Real.exp (-(4 * π ^ 2 * ν) * T)
  have hpt : ∀ t ∈ Ico 0 T, ENNReal.ofReal c ≤ ENNReal.ofReal (gradLinf (shearU A ν t)) := by
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    refine le_trans ?_ (gradLinf_shearU_ge A ν t)
    have hexp : Real.exp (-(4 * π ^ 2 * ν) * T) ≤ Real.exp (-(4 * π ^ 2 * ν) * t) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ 4 * π ^ 2 * ν := by positivity
      nlinarith [ht.2]
    have habs : |shearAmp A ν t| = A * Real.exp (-(4 * π ^ 2 * ν) * t) := by
      unfold shearAmp
      exact abs_of_nonneg (mul_nonneg hA (Real.exp_pos _).le)
    rw [habs]
    have h2pi : 0 ≤ 2 * π := by positivity
    calc c = 2 * π * (A * Real.exp (-(4 * π ^ 2 * ν) * T)) := by ring
      _ ≤ 2 * π * (A * Real.exp (-(4 * π ^ 2 * ν) * t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hA) h2pi
  have hc0 : 0 ≤ c := by positivity
  calc ENNReal.ofReal (c * T)
      = ∫⁻ _ in Ico 0 T, ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero, ← ENNReal.ofReal_mul hc0]
    _ ≤ ∫⁻ t in Ico 0 T, ENNReal.ofReal (gradLinf (shearU A ν t)) :=
        setLIntegral_mono' measurableSet_Ico hpt
    _ = gradIntegral (shearSolution A ν hν) T := by
        rw [gradIntegral, hset]; rfl

/-- For every `ν > 0`, `T > 0` and real `M` there is a global classical solution with
`∫₀ᵀ ‖∇u‖_∞ > M`. -/
theorem gradIntegral_unbounded (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (M : ℝ) :
    ∃ (u0 : E3 → E3) (sol : NSSolution ν u0),
      ENNReal.ofReal M < gradIntegral sol T := by
  set k := Real.exp (-(4 * π ^ 2 * ν) * T)
  have hk : 0 < k := Real.exp_pos _
  set D := |M| + 1
  have hD : 0 < D := by positivity
  set A := D / (2 * π * k * T)
  have hden : 0 < 2 * π * k * T := by positivity
  have hA : 0 ≤ A := (div_pos hD hden).le
  refine ⟨shearU A ν 0, shearSolution A ν hν, ?_⟩
  have heq : 2 * π * A * k * T = D := by
    simp only [A]; field_simp
  have hlt : ENNReal.ofReal M < ENNReal.ofReal (2 * π * A * k * T) := by
    rw [heq, ENNReal.ofReal_lt_ofReal_iff hD]
    simp only [D]; linarith [le_abs_self M]
  exact lt_of_lt_of_le hlt (gradIntegral_shear_ge A ν hν hA T hT)

/-- **The uniform Hypothesis B is false for every `C⋆`.** -/
theorem not_hypothesisB : ∀ C_star : ℝ → ℝ, ¬ HypothesisB C_star := by
  intro C_star hB
  obtain ⟨u0, sol, hlt⟩ := gradIntegral_unbounded 1 one_pos 1 one_pos (C_star 1)
  exact absurd (hB sol 1 one_pos) (not_le.2 hlt)

/-! ## Form B per solution -/

/-- **Form B (per solution).** For every smooth, `1`-periodic, divergence-free datum, every
maximal classical solution and every `T > 0`, `∫₀ᵀ ‖∇u‖_∞` is bounded by a real number
(depending on the solution and on `T`). OPEN; given `BKMCriterion` it is equivalent to
`AnalyticBridgeStatement` (`formBPerSolution_iff_analyticBridge`). -/
def FormBPerSolution : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u0 : E3 → E3), ContDiff ℝ ∞ u0 → IsPeriodic u0 →
    (∀ x, divergence u0 x = 0) →
    ∀ (sol : NSSolution ν u0) (T : ℝ), 0 < T → ∃ C : ℝ, gradIntegral sol T ≤ ENNReal.ofReal C

lemma exists_bound_iff_lt_top (x : ENNReal) : (∃ C : ℝ, x ≤ ENNReal.ofReal C) ↔ x < ⊤ :=
  ⟨fun ⟨_, h⟩ => lt_of_le_of_lt h ENNReal.ofReal_lt_top,
    fun h => ⟨x.toReal, (ENNReal.ofReal_toReal h.ne).ge⟩⟩

/-- CONDITIONAL (on the cited `BKMCriterion`): Form B per solution implies the analytic
bridge statement. -/
theorem analyticBridge_of_formBPerSolution (hB : FormBPerSolution) (bkm : BKMCriterion) :
    AnalyticBridgeStatement := by
  intro ν hν u0 hs hp hd sol
  have hG : sol.Tstar = ⊤ :=
    (clayB_iff_gradIntegral_finite bkm sol).2 fun T hT =>
      (exists_bound_iff_lt_top _).1 (hB ν hν u0 hs hp hd sol T hT)
  exact ⟨hG, fun T _ => global_implies_gradIntegral_finite sol hG T⟩

/-- The converse needs no hypothesis. -/
theorem formBPerSolution_of_analyticBridge (h : AnalyticBridgeStatement) : FormBPerSolution :=
  fun ν hν u0 hs hp hd sol T hT =>
    (exists_bound_iff_lt_top _).2 ((h ν hν u0 hs hp hd sol).2 T hT)

/-- Given `BKMCriterion`, Form B per solution is equivalent to the analytic bridge statement. -/
theorem formBPerSolution_iff_analyticBridge (bkm : BKMCriterion) :
    FormBPerSolution ↔ AnalyticBridgeStatement :=
  ⟨fun h => analyticBridge_of_formBPerSolution h bkm, formBPerSolution_of_analyticBridge⟩

/-- The uniform hypothesis implies the per-solution one (it is strictly stronger; in fact
false by `not_hypothesisB`). -/
theorem formBPerSolution_of_hypothesisB {C_star : ℝ → ℝ} (hB : HypothesisB C_star) :
    FormBPerSolution :=
  fun _ _ _ _ _ _ sol T hT => ⟨C_star T, hB sol T hT⟩

/-- Non-vacuity: the per-solution conclusion holds for the shear flows, whose gradient
integrals are unbounded. -/
theorem formBPerSolution_shear (A ν : ℝ) (hν : 0 < ν) (T : ℝ) :
    ∃ C : ℝ, gradIntegral (shearSolution A ν hν) T ≤ ENNReal.ofReal C :=
  (exists_bound_iff_lt_top _).2 (global_implies_gradIntegral_finite _ rfl T)

/-! ## `Hˢ` bound from Form B per solution -/

/-- On a global solution, a bound `∫₀ᵀ ‖∇u‖_∞ ≤ C` and the cited Kato–Ponce energy inequality
give `HsR(u(t)) ≤ HsR(u₀) exp(C_s max(C, 0))` on `[0, T]`. -/
theorem Hs_bound_of_gradIntegral_le {HsR : ℝ → (E3 → E3) → ℝ} {s C_s : ℝ}
    (kp : KatoPonceEnergy HsR s C_s) {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0)
    (hGlobal : sol.Tstar = ⊤) (T : ℝ) (hTpos : 0 < T) (C : ℝ)
    (hC : gradIntegral sol T ≤ ENNReal.ofReal C) :
    ∀ t ∈ Icc 0 T, HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max C 0) := by
  have life : ∀ t : ℝ, ENNReal.ofReal t < sol.Tstar := fun t => by
    rw [hGlobal]; exact ENNReal.ofReal_lt_top
  have hTle : 0 ≤ T := hTpos.le
  have hy_cont := kp.HsR_cont sol T hTle (life T)
  have hg_cont := gradLinf_continuousOn sol hTle (life T)
  have hβ_cont : ContinuousOn (fun t => C_s * gradLinf (sol.u t)) (Icc 0 T) :=
    continuousOn_const.mul hg_cont
  have hβ_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ C_s * gradLinf (sol.u t) := fun t _ =>
    mul_nonneg kp.C_s_nonneg (gradLinf_nonneg _)
  have hineq : ∀ t ∈ Icc 0 T, HsR s (sol.u t) ≤
      HsR s u0 + ∫ τ in (0 : ℝ)..t, (C_s * gradLinf (sol.u τ)) * HsR s (sol.u τ) := by
    intro t ht
    simpa [mul_assoc] using kp.energy sol t ⟨ht.1, life t⟩
  have hG := integral_gronwall_bound hTle hy_cont hβ_cont hβ_nonneg hineq
  intro t ht
  -- `∫₀ᵗ ‖∇u‖_∞ ≤ max C 0`, converted from the Lebesgue bound of the per-solution bound.
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have hint : IntegrableOn (fun τ => gradLinf (sol.u τ)) (Ioo 0 t) :=
    ((hg_cont.mono (Icc_subset_Icc_right ht.2)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hsubset : Ioo 0 t ⊆ lifeIco sol.Tstar T := fun τ hτ =>
    ⟨hτ.1.le, lt_of_lt_of_le hτ.2 ht.2, life τ⟩
  have hreal : (∫ τ in (0 : ℝ)..t, gradLinf (sol.u τ)) ≤ max C 0 := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    have hofReal : ENNReal.ofReal (∫ τ in Ioo 0 t, gradLinf (sol.u τ)) ≤
        ENNReal.ofReal (max C 0) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun τ => gradLinf_nonneg _)]
      calc ∫⁻ τ in Ioo 0 t, ENNReal.ofReal (gradLinf (sol.u τ))
          ≤ gradIntegral sol T := lintegral_mono_set hsubset
        _ ≤ ENNReal.ofReal C := hC
        _ ≤ ENNReal.ofReal (max C 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
    exact (ENNReal.ofReal_le_ofReal_iff hM).1 hofReal
  have hβ_int_le : (∫ τ in (0 : ℝ)..t, C_s * gradLinf (sol.u τ)) ≤ C_s * max C 0 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hreal kp.C_s_nonneg
  exact le_trans (hG t ht)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hβ_int_le) (kp.HsR_nonneg u0))

/-- CONDITIONAL direct `Hˢ` bound (per solution): Kato–Ponce + Form B per solution + BKM give,
for each smooth periodic divergence-free datum, each maximal solution and each `T > 0`, a real
`C` with `HsR(u(t)) ≤ HsR(u₀) exp(C_s max(C, 0))` on `[0, T]`. -/
theorem formBPerSolution_Hs_bound {HsR : ℝ → (E3 → E3) → ℝ} {s C_s : ℝ}
    (kp : KatoPonceEnergy HsR s C_s) (hB : FormBPerSolution) (bkm : BKMCriterion)
    {ν : ℝ} {u0 : E3 → E3} (hs : ContDiff ℝ ∞ u0) (hp : IsPeriodic u0)
    (hd : ∀ x, divergence u0 x = 0) (sol : NSSolution ν u0) (T : ℝ) (hTpos : 0 < T) :
    ∃ C : ℝ, ∀ t ∈ Icc 0 T, HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max C 0) := by
  have hG := (analyticBridge_of_formBPerSolution hB bkm ν sol.visc_pos u0 hs hp hd sol).1
  obtain ⟨C, hC⟩ := hB ν sol.visc_pos u0 hs hp hd sol T hTpos
  exact ⟨C, Hs_bound_of_gradIntegral_le kp sol hG T hTpos C hC⟩

/-- CONDITIONAL (on `BKMCriterionSmooth`): Form B per solution implies the analytic bridge
statement. -/
theorem analyticBridge_of_formBPerSolution_smooth (hB : FormBPerSolution)
    (bkm : BKMCriterionSmooth) : AnalyticBridgeStatement := by
  intro ν hν u0 hs hp hd sol
  have hG : sol.Tstar = ⊤ := by
    by_contra hne
    have hI := bkm hs hp hd sol hne
    have hsub : Ico 0 sol.Tstar.toReal ⊆ lifeIco sol.Tstar (sol.Tstar.toReal + 1) :=
      fun t ht => ⟨ht.1, by linarith [ht.2], (ENNReal.ofReal_lt_iff_lt_toReal ht.1 hne).2 ht.2⟩
    have hle : (⊤ : ENNReal) ≤ gradIntegral sol (sol.Tstar.toReal + 1) := by
      rw [← hI]; exact lintegral_mono_set hsub
    have hfin := (exists_bound_iff_lt_top _).1
      (hB ν hν u0 hs hp hd sol (sol.Tstar.toReal + 1) (by positivity))
    exact absurd hfin (not_lt.2 hle)
  exact ⟨hG, fun T _ => global_implies_gradIntegral_finite sol hG T⟩

/-- Given `BKMCriterionSmooth`, Form B per solution is equivalent to the analytic bridge
statement. -/
theorem formBPerSolution_iff_analyticBridge_smooth (bkm : BKMCriterionSmooth) :
    FormBPerSolution ↔ AnalyticBridgeStatement :=
  ⟨fun h => analyticBridge_of_formBPerSolution_smooth h bkm,
    formBPerSolution_of_analyticBridge⟩

end ClassicalNS
