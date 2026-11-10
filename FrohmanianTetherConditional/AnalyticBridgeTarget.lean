-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import Mathlib

open Real Set MeasureTheory intervalIntegral Filter Topology

/-!
# Analytic bridge target (OPEN)

Statement of Clay Millennium Problem (B) on the periodic 3-torus, stated as a target.

* Exactly one `sorry`: `analytic_bridge_unconditional` (the open problem).
* Form~B / Hypothesis~B is the **full-gradient** integrability
  `∫₀ᵀ ‖∇u‖_{L^∞} dt ≤ C_*(T)`, which with the cited Kato–Ponce energy
  inequality yields the **direct** bound
  `‖u(t)‖_{Hˢ} ≤ ‖u₀‖_{Hˢ} exp(C_s C_*(T))` (proved, no `sorry`).
  A strain-only (`S`) version does **not** give this direct constant (log loss).
* Nothing in this file is claimed to resolve Clay (B). Because `solves_NS` and
  `maximal` are placeholders, a proof of `analytic_bridge_unconditional` would
  **not** yet constitute a proof of Clay (B).
-/

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

def IsPeriodic (f : R3 → Vec3) : Prop :=
  ∀ (x : R3) (i : Fin 3), f (x + EuclideanSpace.single i 1) = f x

structure NormData where
  Hs : ℝ → (R3 → Vec3) → ENNReal
  HsR : ℝ → (R3 → Vec3) → ℝ
  vortLinf : (R3 → Vec3) → ℝ
  gradLinf : (R3 → Vec3) → ℝ
  HsR_nonneg : ∀ s f, 0 ≤ HsR s f
  gradLinf_nonneg : ∀ f, 0 ≤ gradLinf f

def lifespanSet (Tstar : ENNReal) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < Tstar}

structure NSSolution (N : NormData) (ν : ℝ) (u0 : R3 → Vec3) where
  Tstar : ENNReal
  u : ℝ → R3 → Vec3
  init : u 0 = u0
  periodic : ∀ t, IsPeriodic (u t)
  smooth : ∀ t, 0 ≤ t → ENNReal.ofReal t < Tstar → ContDiff ℝ ⊤ (u t)
  vort_cont : ContinuousOn (fun t => N.vortLinf (u t)) (lifespanSet Tstar)
  grad_cont : ContinuousOn (fun t => N.gradLinf (u t)) (lifespanSet Tstar)
  HsR_cont : ∀ s, ContinuousOn (fun t => N.HsR s (u t)) (lifespanSet Tstar)
  solves_NS : Prop
  maximal : Prop

/-- Beale–Kato–Majda / Kato continuation in ‖∇u‖_{L^∞} (cited, not proved here). -/
structure BKMCriterion (N : NormData) where
  continuation :
    ∀ {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0),
      (∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T) →
      sol.Tstar = ⊤

/-- Kato–Ponce 1988 energy inequality in integrated form (cited, not proved here). -/
structure KatoPonceEnergy (N : NormData) (s : ℝ) (C_s : ℝ) where
  C_s_nonneg : 0 ≤ C_s
  energy :
    ∀ {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0) (t : ℝ),
      0 ≤ t → ENNReal.ofReal t < sol.Tstar →
      N.HsR s (sol.u t) ≤
        N.HsR s u0 +
          ∫ τ in (0 : ℝ)..t,
            C_s * N.gradLinf (sol.u τ) * N.HsR s (sol.u τ)

/-- Form B / Hypothesis B: full-gradient integrability with derived `C_star`.
One-directional; no Clay(B) → Form B. -/
structure HypothesisB (N : NormData) where
  C_star : ℝ → ℝ
  formB :
    ∀ {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0) (T : ℝ),
      0 < T →
        IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T ∧
          (∫ τ in (0 : ℝ)..T, N.gradLinf (sol.u τ)) ≤ C_star T

theorem clayB_implies_bkm_integrable
    {N : NormData} {ν : ℝ} {u0 : R3 → Vec3}
    (sol : NSSolution N ν u0) (hGlobal : sol.Tstar = ⊤)
    (T : ℝ) (hTpos : 0 < T) :
    IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T := by
  have hcont : ContinuousOn (fun t => N.gradLinf (sol.u t)) (uIcc 0 T) := by
    refine sol.grad_cont.mono ?_
    intro t ht
    rw [uIcc_of_le (le_of_lt hTpos)] at ht
    refine ⟨ht.1, ?_⟩
    rw [hGlobal]
    exact ENNReal.ofReal_lt_top
  exact hcont.intervalIntegrable

theorem clayB_iff_bkm_integrable
    {N : NormData} (bkm : BKMCriterion N) {ν : ℝ} {u0 : R3 → Vec3}
    (sol : NSSolution N ν u0) :
    sol.Tstar = ⊤ ↔
      ∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T := by
  constructor
  · intro hGlobal T hTpos
    exact clayB_implies_bkm_integrable sol hGlobal T hTpos
  · intro hint
    exact bkm.continuation sol hint

theorem formB_implies_clayB
    {N : NormData} (hB : HypothesisB N) (bkm : BKMCriterion N)
    {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0) :
    sol.Tstar = ⊤ :=
  bkm.continuation sol (fun T hT => (hB.formB sol T hT).1)

theorem hypothesisB_implies_clayB
    {N : NormData} (hB : HypothesisB N) (bkm : BKMCriterion N)
    {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0) :
    sol.Tstar = ⊤ :=
  formB_implies_clayB hB bkm sol

/-- Integrating-factor Grönwall with an explicit derivative `Y'` on the open interval. -/
lemma gronwall_differential_bound {Y Y' α : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hY_cont : ContinuousOn Y (Icc 0 T))
    (hY_deriv : ∀ t ∈ interior (Icc 0 T), HasDerivAt Y (Y' t) t)
    (hα_cont : ContinuousOn α (Icc 0 T))
    (h_ineq : ∀ t ∈ interior (Icc 0 T), Y' t ≤ α t * Y t) :
    ∀ t ∈ Icc 0 T, Y t ≤ Y 0 * Real.exp (∫ τ in (0 : ℝ)..t, α τ) := by
  intro t ht
  set I : ℝ → ℝ := fun s => ∫ τ in (0 : ℝ)..s, α τ
  let φ : ℝ → ℝ := fun s => Y s * Real.exp (-I s)
  have hα_uIcc : ContinuousOn α (uIcc 0 T) := by rwa [uIcc_of_le hT]
  have h_int : IntervalIntegrable α volume 0 T := hα_uIcc.intervalIntegrable
  have hI_cont : ContinuousOn I (Icc 0 T) := by
    have hCu : ContinuousOn I (uIcc 0 T) :=
      continuousOn_primitive_interval' (μ := volume) h_int
        (by simpa [uIcc_of_le hT] using left_mem_Icc.mpr hT)
    rwa [uIcc_of_le hT] at hCu
  have hI_deriv_int : ∀ s ∈ interior (Icc 0 T), HasDerivAt I (α s) s := by
    intro s hs
    have hs' : s ∈ Icc 0 T := interior_subset hs
    have hs_mem : s ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using hs'
    have h_int_s : IntervalIntegrable α volume 0 s :=
      h_int.mono_set (uIcc_subset_uIcc_left hs_mem)
    have hnhds : Icc 0 T ∈ 𝓝 s :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hs) interior_subset
    have hcontAt : ContinuousAt α s := hα_cont.continuousAt hnhds
    have hAe : AEStronglyMeasurable α (volume.restrict (Icc 0 T)) :=
      hα_cont.aestronglyMeasurable measurableSet_Icc
    have hmeas : StronglyMeasurableAtFilter α (𝓝 s) volume := ⟨Icc 0 T, hnhds, hAe⟩
    exact integral_hasDerivAt_right h_int_s hmeas hcontAt
  have hφ_anti : AntitoneOn φ (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · intro s hs
      have hexp : ContinuousWithinAt (fun x => Real.exp (-I x)) (Icc 0 T) s :=
        continuous_exp.continuousWithinAt.comp (hI_cont.continuousWithinAt hs).neg
          (mapsTo_univ _ _)
      exact (hY_cont s hs).mul hexp
    · intro s hs
      have hYd : DifferentiableWithinAt ℝ Y (interior (Icc 0 T)) s :=
        (hY_deriv s hs).differentiableAt.differentiableWithinAt
      have hId : DifferentiableWithinAt ℝ (fun x => Real.exp (-I x))
          (interior (Icc 0 T)) s :=
        ((hI_deriv_int s hs).differentiableAt.neg.exp).differentiableWithinAt
      exact hYd.mul hId
    · intro s hs
      have hYd : HasDerivAt Y (Y' s) s := hY_deriv s hs
      have hId : HasDerivAt (fun x => Real.exp (-I x))
          (Real.exp (-I s) * -α s) s := (hI_deriv_int s hs).neg.exp
      have hprod := hYd.mul hId
      have hderiv : deriv φ s =
          Y' s * Real.exp (-I s) + Y s * (Real.exp (-I s) * -α s) := by
        simpa [φ] using hprod.deriv
      rw [hderiv]
      have hpos : 0 < Real.exp (-I s) := Real.exp_pos _
      have hineq := h_ineq s hs
      calc
        Y' s * Real.exp (-I s) + Y s * (Real.exp (-I s) * -α s)
            = (Y' s - α s * Y s) * Real.exp (-I s) := by ring
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hineq) (le_of_lt hpos)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, hT⟩
  have hle : φ t ≤ φ 0 := hφ_anti h0 ht ht.1
  dsimp [φ] at hle
  have hI0 : I 0 = 0 := integral_same
  rw [hI0, neg_zero, Real.exp_zero, mul_one] at hle
  calc
    Y t = (Y t * Real.exp (-I t)) * Real.exp (I t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ Y 0 * Real.exp (I t) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt (Real.exp_pos _))

/-- Integral-form Grönwall. Requires `0 ≤ β`. -/
lemma integral_gronwall_bound {y β : ℝ → ℝ} {a T : ℝ} (hT : 0 ≤ T)
    (hy_cont : ContinuousOn y (Icc 0 T))
    (hβ_cont : ContinuousOn β (Icc 0 T))
    (hβ_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ β t)
    (hineq : ∀ t ∈ Icc 0 T, y t ≤ a + ∫ τ in (0 : ℝ)..t, β τ * y τ) :
    ∀ t ∈ Icc 0 T, y t ≤ a * Real.exp (∫ τ in (0 : ℝ)..t, β τ) := by
  -- Define φ as a pointwise sum so `HasDerivAt.add` matches definitionally.
  let prim : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, β τ * y τ
  let φ : ℝ → ℝ := (fun _ => a) + prim
  let φ' : ℝ → ℝ := fun t => β t * y t
  have hφ_point : ∀ t, φ t = a + prim t := fun t => by simp [φ, Pi.add_apply]
  have hβy_cont : ContinuousOn (fun τ => β τ * y τ) (Icc 0 T) := hβ_cont.mul hy_cont
  have hβy_uIcc : ContinuousOn (fun τ => β τ * y τ) (uIcc 0 T) := by
    rwa [uIcc_of_le hT]
  have h_int : IntervalIntegrable (fun τ => β τ * y τ) volume 0 T :=
    hβy_uIcc.intervalIntegrable
  have hy_le_φ : ∀ t ∈ Icc 0 T, y t ≤ φ t := fun t ht => by
    rw [hφ_point]; exact hineq t ht
  have hφ_cont : ContinuousOn φ (Icc 0 T) := by
    have hprim : ContinuousOn prim (uIcc 0 T) :=
      continuousOn_primitive_interval' (μ := volume) h_int
        (by simpa [uIcc_of_le hT] using left_mem_Icc.mpr hT)
    have hprim' : ContinuousOn prim (Icc 0 T) := by rwa [uIcc_of_le hT] at hprim
    exact continuousOn_const.add hprim'
  have hφ_deriv : ∀ t ∈ interior (Icc 0 T), HasDerivAt φ (φ' t) t := by
    intro t ht
    have ht' : t ∈ Icc 0 T := interior_subset ht
    have ht_u : t ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using ht'
    have h_int_t : IntervalIntegrable (fun τ => β τ * y τ) volume 0 t :=
      h_int.mono_set (uIcc_subset_uIcc_left ht_u)
    have hnhds : Icc 0 T ∈ 𝓝 t :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior ht) interior_subset
    have hcontAt : ContinuousAt (fun τ => β τ * y τ) t := hβy_cont.continuousAt hnhds
    have hAe : AEStronglyMeasurable (fun τ => β τ * y τ) (volume.restrict (Icc 0 T)) :=
      hβy_cont.aestronglyMeasurable measurableSet_Icc
    have hmeas : StronglyMeasurableAtFilter (fun τ => β τ * y τ) (𝓝 t) volume :=
      ⟨Icc 0 T, hnhds, hAe⟩
    have hderiv : HasDerivAt prim (β t * y t) t :=
      integral_hasDerivAt_right h_int_t hmeas hcontAt
    have hsum := (hasDerivAt_const (F := ℝ) t a).add hderiv
    simpa [φ, φ', Pi.add_apply] using hsum
  have h_ineqφ : ∀ t ∈ interior (Icc 0 T), φ' t ≤ β t * φ t := by
    intro t ht
    have ht' : t ∈ Icc 0 T := interior_subset ht
    dsimp [φ']
    exact mul_le_mul_of_nonneg_left (hy_le_φ t ht') (hβ_nonneg t ht')
  have hφ_bound := gronwall_differential_bound hT hφ_cont hφ_deriv hβ_cont h_ineqφ
  intro t ht
  have hφ0 : φ 0 = a := by simp [φ, prim, Pi.add_apply, integral_same]
  have := hφ_bound t ht
  rw [hφ0] at this
  exact le_trans (hy_le_φ t ht) this

/-- Direct Hˢ bound from Form B + Kato–Ponce (PROVED). -/
theorem formB_Hs_bound
    {N : NormData} {s C_s : ℝ} (kp : KatoPonceEnergy N s C_s)
    (hB : HypothesisB N) (bkm : BKMCriterion N)
    {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0)
    (T : ℝ) (hTpos : 0 < T) :
    ∀ t ∈ Icc 0 T, N.HsR s (sol.u t) ≤ N.HsR s u0 * Real.exp (C_s * hB.C_star T) := by
  have hGlobal : sol.Tstar = ⊤ := formB_implies_clayB hB bkm sol
  have hTle : 0 ≤ T := le_of_lt hTpos
  have hform := hB.formB sol T hTpos
  have hIntGrad := hform.1
  have hCstar := hform.2
  have hlife : Icc 0 T ⊆ lifespanSet sol.Tstar := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rw [hGlobal]
    exact ENNReal.ofReal_lt_top
  have hy_cont : ContinuousOn (fun t => N.HsR s (sol.u t)) (Icc 0 T) :=
    (sol.HsR_cont s).mono hlife
  have hgrad_cont : ContinuousOn (fun t => N.gradLinf (sol.u t)) (Icc 0 T) :=
    sol.grad_cont.mono hlife
  have hβ_cont : ContinuousOn (fun t => C_s * N.gradLinf (sol.u t)) (Icc 0 T) :=
    continuousOn_const.mul hgrad_cont
  have hβ_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ C_s * N.gradLinf (sol.u t) := by
    intro t _ht
    exact mul_nonneg kp.C_s_nonneg (N.gradLinf_nonneg _)
  have hineq :
      ∀ t ∈ Icc 0 T,
        N.HsR s (sol.u t) ≤
          N.HsR s u0 +
            ∫ τ in (0 : ℝ)..t,
              (C_s * N.gradLinf (sol.u τ)) * N.HsR s (sol.u τ) := by
    intro t ht
    have ht_life : ENNReal.ofReal t < sol.Tstar := by
      rw [hGlobal]; exact ENNReal.ofReal_lt_top
    have hE := kp.energy sol t ht.1 ht_life
    simpa [mul_assoc] using hE
  have hG := integral_gronwall_bound hTle hy_cont hβ_cont hβ_nonneg hineq
  intro t ht
  have hpt := hG t ht
  have hβ_int_le :
      (∫ τ in (0 : ℝ)..t, C_s * N.gradLinf (sol.u τ)) ≤ C_s * hB.C_star T := by
    have hpull :
        (∫ τ in (0 : ℝ)..t, C_s * N.gradLinf (sol.u τ)) =
          C_s * ∫ τ in (0 : ℝ)..t, N.gradLinf (sol.u τ) := by
      exact intervalIntegral.integral_const_mul C_s (fun τ => N.gradLinf (sol.u τ))
    rw [hpull]
    have hsub :
        (∫ τ in (0 : ℝ)..t, N.gradLinf (sol.u τ)) ≤
          ∫ τ in (0 : ℝ)..T, N.gradLinf (sol.u τ) := by
      have hf : ∀ᵐ τ ∂volume.restrict (Ioc (0 : ℝ) T),
          (0 : ℝ) ≤ N.gradLinf (sol.u τ) :=
        ae_of_all _ fun τ => N.gradLinf_nonneg (sol.u τ)
      exact integral_mono_interval (μ := volume) (f := fun τ => N.gradLinf (sol.u τ))
        (c := (0 : ℝ)) (d := T) (a := (0 : ℝ)) (b := t)
        le_rfl ht.1 ht.2 hf hIntGrad
    exact mul_le_mul_of_nonneg_left (le_trans hsub hCstar) kp.C_s_nonneg
  have hExp :
      Real.exp (∫ τ in (0 : ℝ)..t, C_s * N.gradLinf (sol.u τ)) ≤
        Real.exp (C_s * hB.C_star T) :=
    Real.exp_le_exp.mpr hβ_int_le
  have ha0 : 0 ≤ N.HsR s u0 := N.HsR_nonneg s u0
  exact le_trans hpt (mul_le_mul_of_nonneg_left hExp ha0)

/-- Clay (B) target (OPEN). Placeholders mean a proof would not yet be Clay (B). -/
theorem analytic_bridge_unconditional
    (N : NormData) (ν : ℝ) (hν : 0 < ν) (s : ℝ) (hs : 5 / 2 < s)
    (u0 : R3 → Vec3) (hper : IsPeriodic u0) (hu0 : N.Hs s u0 < ⊤) :
    ∀ sol : NSSolution N ν u0,
      sol.Tstar = ⊤ ∧
      ∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.gradLinf (sol.u t)) volume 0 T := by
  sorry  -- OPEN: this is Clay Millennium Problem Statement (B)
