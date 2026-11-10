-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import Mathlib

/-!
# Classical periodic incompressible Navier–Stokes on `T³` (genuine encoding)

This file replaces the placeholder `NSSolution` of `AnalyticBridgeTarget.lean`
(kept there as LEGACY) by an object that **requires** the Navier–Stokes equations
and a **maximal** lifespan.

## Torus model
`T³ = ℝ³/ℤ³` is modelled by functions on `E3 = EuclideanSpace ℝ (Fin 3)` that are
`1`-periodic in each coordinate (`IsPeriodic`). Spatial derivatives are Fréchet
derivatives on `ℝ³`; `pd i g x = fderiv ℝ g x (e i)` is `∂ᵢ g (x)`.

## The equations (`IsClassicalNS ν u₀ u p T⋆`)
On the lifespan `[0, T⋆)` (with `T⋆ : ℝ≥0∞`, `T⋆ = ⊤` meaning global):
* `u 0 = u₀`;
* `u t`, `p t` are `C^∞` (`ContDiff ℝ ∞`, i.e. smooth, **not** analytic) and
  periodic; `(t, x) ↦ u`, `(t, x) ↦ p` are jointly `C^∞` on `(0, T⋆) × ℝ³`;
  `u` and `∇ₓu` are jointly continuous on `[0, T⋆) × ℝ³`;
* `div u = 0`;
* for `0 < t < T⋆`, every `x` and every component `j`,
  `∂ₜ uⱼ = ν Δuⱼ − (u·∇)uⱼ − ∂ⱼ p` (as `HasDerivAt` in `t`).

## Maximality (`NSSolution.maximal`)
No classical solution with the same data on a strictly longer interval agrees with
`u` on `[0, T⋆)`. Hence `T⋆` is the genuine maximal time of existence in this class.

## Norms
`gradLinf f = sup_{x ∈ [0,1]³} ‖Df(x)‖` (operator norm), the `L^∞` norm of `∇f` over
one period cell (equal to the sup over `ℝ³` for periodic `f`; that equality is not
needed here). It is a genuine definition, not a free parameter.
The `Hˢ` norm (Mathlib has no Sobolev spaces on `T³`) is **not** defined: it enters
only through the explicitly named cited hypothesis `KatoPonceEnergy`, where it is a
documented parameter `HsR`.

## Cited, not proved
`BKMCriterion` (Beale–Kato–Majda 1984 / Kato) and `KatoPonceEnergy` (Kato–Ponce 1988)
are stated as named hypotheses about these genuine solutions. Their truth for this
class uses standard local existence/uniqueness theory, which is not formalized.
-/

open Real Set MeasureTheory intervalIntegral Filter Topology
open scoped ContDiff

namespace ClassicalNS

/-- Physical space `ℝ³` (the torus is modelled by periodic functions on it). -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Standard basis vector `eᵢ`. -/
noncomputable def e (i : Fin 3) : E3 := EuclideanSpace.single i 1

/-- `1`-periodicity in every coordinate direction: functions on `T³ = ℝ³/ℤ³`. -/
def IsPeriodic {β : Type*} (f : E3 → β) : Prop := ∀ (x : E3) (i : Fin 3), f (x + e i) = f x

/-- Partial derivative `∂ᵢ g (x)`. -/
noncomputable def pd (i : Fin 3) (g : E3 → ℝ) (x : E3) : ℝ := fderiv ℝ g x (e i)

/-- The `j`-th component of a vector field. -/
def comp (f : E3 → E3) (j : Fin 3) : E3 → ℝ := fun x => f x j

/-- `div f = ∑ᵢ ∂ᵢ fᵢ`. -/
noncomputable def divergence (f : E3 → E3) (x : E3) : ℝ := ∑ i, pd i (comp f i) x

/-- `((f·∇) f)ⱼ = ∑ᵢ fᵢ ∂ᵢ fⱼ`. -/
noncomputable def advection (f : E3 → E3) (j : Fin 3) (x : E3) : ℝ :=
  ∑ i, f x i * pd i (comp f j) x

/-- `(Δ f)ⱼ = ∑ᵢ ∂ᵢ∂ᵢ fⱼ`. -/
noncomputable def laplacian (f : E3 → E3) (j : Fin 3) (x : E3) : ℝ :=
  ∑ i, pd i (pd i (comp f j)) x

/-- Lifespan `[0, T⋆)`. -/
def lifespan (Tstar : ENNReal) : Set ℝ := {t | 0 ≤ t ∧ ENNReal.ofReal t < Tstar}

/-- Open lifespan `(0, T⋆)`. -/
def openLifespan (Tstar : ENNReal) : Set ℝ := {t | 0 < t ∧ ENNReal.ofReal t < Tstar}

/-- `(u, p)` is a classical solution of periodic incompressible Navier–Stokes with
viscosity `ν` and initial datum `u₀` on `[0, T⋆)`. -/
structure IsClassicalNS (ν : ℝ) (u0 : E3 → E3) (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ)
    (Tstar : ENNReal) : Prop where
  init : u 0 = u0
  periodic_u : ∀ t ∈ lifespan Tstar, IsPeriodic (u t)
  periodic_p : ∀ t ∈ lifespan Tstar, IsPeriodic (p t)
  smooth_u : ∀ t ∈ lifespan Tstar, ContDiff ℝ ∞ (u t)
  smooth_p : ∀ t ∈ lifespan Tstar, ContDiff ℝ ∞ (p t)
  jointSmooth_u : ContDiffOn ℝ ∞ (fun q : ℝ × E3 => u q.1 q.2) (openLifespan Tstar ×ˢ univ)
  jointSmooth_p : ContDiffOn ℝ ∞ (fun q : ℝ × E3 => p q.1 q.2) (openLifespan Tstar ×ˢ univ)
  cont_u : ContinuousOn (fun q : ℝ × E3 => u q.1 q.2) (lifespan Tstar ×ˢ univ)
  cont_grad : ContinuousOn (fun q : ℝ × E3 => fderiv ℝ (u q.1) q.2) (lifespan Tstar ×ˢ univ)
  div_free : ∀ t ∈ lifespan Tstar, ∀ x, divergence (u t) x = 0
  momentum : ∀ t ∈ openLifespan Tstar, ∀ (x : E3) (j : Fin 3),
    HasDerivAt (fun τ => u τ x j)
      (ν * laplacian (u t) j x - advection (u t) j x - pd j (p t) x) t

/-- A **maximal** classical solution. The viscosity is required to be positive. -/
structure NSSolution (ν : ℝ) (u0 : E3 → E3) where
  visc_pos : 0 < ν
  Tstar : ENNReal
  u : ℝ → E3 → E3
  p : ℝ → E3 → ℝ
  isNS : IsClassicalNS ν u0 u p Tstar
  maximal : ∀ (T' : ENNReal) (v : ℝ → E3 → E3) (q : ℝ → E3 → ℝ),
    Tstar < T' → IsClassicalNS ν u0 v q T' → ¬ (∀ t ∈ lifespan Tstar, v t = u t)

/-! ## Norms -/

/-- The closed unit period cell `[0,1]³`. -/
def cube : Set E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm '' (univ.pi fun _ => Icc (0 : ℝ) 1)

lemma isCompact_cube : IsCompact cube :=
  (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous

lemma cube_nonempty : cube.Nonempty :=
  ⟨_, mem_image_of_mem _ (show (fun _ => (0 : ℝ)) ∈ univ.pi fun _ => Icc (0 : ℝ) 1 from
    fun _ _ => ⟨le_rfl, zero_le_one⟩)⟩

/-- `‖∇f‖_{L^∞(T³)}`: sup of the operator norm of `Df` over the period cell. -/
noncomputable def gradLinf (f : E3 → E3) : ℝ := sSup ((fun x => ‖fderiv ℝ f x‖) '' cube)

lemma gradLinf_nonneg (f : E3 → E3) : 0 ≤ gradLinf f :=
  Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg _)

/-- `[0, T) ∩ [0, T⋆)`. -/
def lifeIco (Tstar : ENNReal) (T : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ t < T ∧ ENNReal.ofReal t < Tstar}

/-- `∫_{[0,T) ∩ [0,T⋆)} ‖∇u(t)‖_∞ dt ∈ [0, ∞]` (no junk values: only lifespan times). -/
noncomputable def gradIntegral {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (T : ℝ) :
    ENNReal :=
  ∫⁻ t in lifeIco sol.Tstar T, ENNReal.ofReal (gradLinf (sol.u t))

/-! ## Non-vacuity: the structure is inhabited, constrains, and rejects the old object -/

@[simp] lemma comp_const (c : E3) (j : Fin 3) : comp (fun _ : E3 => c) j = fun _ => c j := rfl

@[simp] lemma pd_const (i : Fin 3) (a : ℝ) : pd i (fun _ : E3 => a) = fun _ => 0 := by
  funext x; simp [pd]

/-- Constant velocity `c` with zero pressure is a global classical solution. -/
theorem const_isClassicalNS (ν : ℝ) (c : E3) :
    IsClassicalNS ν (fun _ => c) (fun _ _ => c) (fun _ _ => 0) ⊤ where
  init := rfl
  periodic_u := fun _ _ _ _ => rfl
  periodic_p := fun _ _ _ _ => rfl
  smooth_u := fun _ _ => contDiff_const
  smooth_p := fun _ _ => contDiff_const
  jointSmooth_u := contDiffOn_const
  jointSmooth_p := contDiffOn_const
  cont_u := continuousOn_const
  cont_grad := by simp only [fderiv_const_apply]; exact continuousOn_const
  div_free := by intro t _ x; simp [divergence]
  momentum := by
    intro t _ x j
    simpa [laplacian, advection] using hasDerivAt_const t (c j)

/-- The constant-velocity maximal solution (`T⋆ = ⊤`). -/
noncomputable def constSolution (ν : ℝ) (hν : 0 < ν) (c : E3) : NSSolution ν (fun _ => c) where
  visc_pos := hν
  Tstar := ⊤
  u := fun _ _ => c
  p := fun _ _ => 0
  isNS := const_isClassicalNS ν c
  maximal := fun _ _ _ h _ _ => (not_top_lt h).elim

/-- The zero solution: `NSSolution` is inhabited. -/
noncomputable def zeroSolution (ν : ℝ) (hν : 0 < ν) : NSSolution ν (fun _ => 0) :=
  constSolution ν hν 0

theorem zeroSolution_global (ν : ℝ) (hν : 0 < ν) : (zeroSolution ν hν).Tstar = ⊤ := rfl

theorem nonempty_NSSolution_zero (ν : ℝ) (hν : 0 < ν) :
    Nonempty (NSSolution ν (fun _ => 0)) := ⟨zeroSolution ν hν⟩

/-- Any maximal solution with zero data that is identically zero on its lifespan is
global: maximality forbids an artificial finite lifespan. -/
theorem zero_field_is_global {ν : ℝ} (sol : NSSolution ν (fun _ => 0))
    (hu : ∀ t ∈ lifespan sol.Tstar, sol.u t = fun _ => 0) : sol.Tstar = ⊤ := by
  by_contra h
  exact sol.maximal ⊤ (fun _ _ => 0) (fun _ _ => 0) (lt_top_iff_ne_top.2 h)
    (const_isClassicalNS ν 0) (fun t ht => (hu t ht).symm)

/-- The object that refuted the LEGACY target (zero field, lifespan `T⋆ = 1`) is
**not** a valid `NSSolution`. -/
theorem old_counterexample_invalid (ν : ℝ) :
    ¬ ∃ sol : NSSolution ν (fun _ => 0), sol.Tstar = 1 ∧ ∀ t, sol.u t = fun _ => 0 := by
  rintro ⟨sol, hT, hu⟩
  have := zero_field_is_global sol (fun t _ => hu t)
  rw [hT] at this
  exact ENNReal.one_ne_top this

/-- The momentum equation genuinely constrains: `u(t,x) = t e₀`, `p = 0` is not a
solution on any nonempty lifespan (`∂ₜu = e₀` but the right-hand side vanishes). -/
theorem linear_in_time_not_NS (ν : ℝ) (Tstar : ENNReal) (hT : 0 < Tstar) :
    ¬ IsClassicalNS ν (fun _ => 0) (fun t _ => t • e 0) (fun _ _ => 0) Tstar := by
  intro h
  obtain ⟨r, _hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hT
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr1
  have hd := h.momentum r ⟨hrpos, hr2⟩ 0 0
  simp [laplacian, advection, e] at hd
  have h1 : HasDerivAt (fun τ : ℝ => τ) 1 r := hasDerivAt_id' r
  exact one_ne_zero (h1.unique hd)

/-! ## Continuity of `‖∇u(t)‖_∞` along a solution (proved, not assumed) -/

lemma gradLinf_continuousOn {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) {T : ℝ}
    (hT : 0 ≤ T) (hTlt : ENNReal.ofReal T < sol.Tstar) :
    ContinuousOn (fun t => gradLinf (sol.u t)) (Icc 0 T) := by
  have hsub : ∀ s ∈ Icc 0 T, s ∈ lifespan sol.Tstar := fun s hs =>
    ⟨hs.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.2) hTlt⟩
  let G : ℝ × E3 → ℝ := fun q => ‖fderiv ℝ (sol.u q.1) q.2‖
  have hG : ContinuousOn G (lifespan sol.Tstar ×ˢ univ) := sol.isNS.cont_grad.norm
  let prj : ℝ × E3 → ℝ × E3 := fun q => ((projIcc 0 T hT q.1 : ℝ), q.2)
  have hprj : Continuous prj :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
  have hH : Continuous (G ∘ prj) :=
    hG.comp_continuous hprj (fun q => ⟨hsub _ (projIcc 0 T hT q.1).2, trivial⟩)
  have hS : Continuous fun t => sSup ((fun x => (G ∘ prj) (t, x)) '' cube) :=
    isCompact_cube.continuous_sSup (f := fun t x => (G ∘ prj) (t, x)) hH
  refine hS.continuousOn.congr ?_
  intro t ht
  simp only [gradLinf, Function.comp, prj, G, projIcc_of_mem hT ht]

/-! ## Genuine BKM criterion (cited hypothesis) and its consequences -/

/-- **Beale–Kato–Majda / Kato continuation criterion (cited, not proved).**
If a maximal classical solution has finite lifespan then
`∫₀^{T⋆} ‖∇u(t)‖_∞ dt = ∞`. This is a statement about genuine solutions; it is a
known theorem (BKM 1984, with Kato's local theory and uniqueness of classical
solutions), not formalized here. -/
def BKMCriterion : Prop :=
  ∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0), sol.Tstar ≠ ⊤ →
    ∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (gradLinf (sol.u t)) = ⊤

/-- The BKM conclusion holds trivially for global solutions such as `constSolution`;
in particular the `T⋆ = 1` zero object that made the LEGACY `BKMCriterion`
uninhabitable is excluded by `old_counterexample_invalid`. -/
theorem bkm_conclusion_of_global {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0)
    (h : sol.Tstar = ⊤) :
    sol.Tstar ≠ ⊤ →
      ∫⁻ t in Ico 0 sol.Tstar.toReal, ENNReal.ofReal (gradLinf (sol.u t)) = ⊤ :=
  fun hne => absurd h hne

/-- Global solutions have finite `∫₀ᵀ ‖∇u‖_∞` for every `T` (proved). -/
theorem global_implies_gradIntegral_finite {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0)
    (hG : sol.Tstar = ⊤) (T : ℝ) : gradIntegral sol T < ⊤ := by
  rcases le_or_gt T 0 with hT | hT
  · have hempty : lifeIco sol.Tstar T = ∅ := by
      ext t
      simp only [lifeIco, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro h0 hlt
      linarith
    simp [gradIntegral, hempty]
  · have hcont := gradLinf_continuousOn sol hT.le (by rw [hG]; exact ENNReal.ofReal_lt_top)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    have hsub : lifeIco sol.Tstar T ⊆ Icc 0 T := fun t ht => ⟨ht.1, ht.2.1.le⟩
    calc gradIntegral sol T
        ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (gradLinf (sol.u t)) := lintegral_mono_set hsub
      _ ≤ ∫⁻ _ in Icc 0 T, ENNReal.ofReal C :=
          setLIntegral_mono measurable_const (fun t ht =>
            ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _)
              (by simpa [Real.norm_eq_abs] using hC t ht)))
      _ = ENNReal.ofReal C * volume (Icc (0 : ℝ) T) := setLIntegral_const _ _
      _ < ⊤ := by
          rw [Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Under BKM, finite `∫₀ᵀ ‖∇u‖_∞` for all `T` forces `T⋆ = ⊤`. -/
theorem gradIntegral_finite_implies_global (bkm : BKMCriterion) {ν : ℝ} {u0 : E3 → E3}
    (sol : NSSolution ν u0) (h : ∀ T : ℝ, 0 < T → gradIntegral sol T < ⊤) :
    sol.Tstar = ⊤ := by
  by_contra hne
  have hB := bkm sol hne
  have hT0 : 0 ≤ sol.Tstar.toReal := ENNReal.toReal_nonneg
  have hsub : Ico 0 sol.Tstar.toReal ⊆ lifeIco sol.Tstar (sol.Tstar.toReal + 1) :=
    fun t ht => ⟨ht.1, by linarith [ht.2], (ENNReal.ofReal_lt_iff_lt_toReal ht.1 hne).2 ht.2⟩
  have hle : (⊤ : ENNReal) ≤ gradIntegral sol (sol.Tstar.toReal + 1) := by
    rw [← hB]; exact lintegral_mono_set hsub
  exact absurd (h _ (by linarith)) (not_lt.2 hle)

/-- Clay (B) for one solution ⇔ BKM integrability (genuine content; needs BKM only
for `⇐`). -/
theorem clayB_iff_gradIntegral_finite (bkm : BKMCriterion) {ν : ℝ} {u0 : E3 → E3}
    (sol : NSSolution ν u0) :
    sol.Tstar = ⊤ ↔ ∀ T : ℝ, 0 < T → gradIntegral sol T < ⊤ :=
  ⟨fun h T _ => global_implies_gradIntegral_finite sol h T,
    gradIntegral_finite_implies_global bkm sol⟩

/-- **Hypothesis B / Form B** (an assumption of Clay strength; whether it holds is
open): a uniform bound on `∫₀ᵀ ‖∇u‖_∞` over all genuine maximal solutions. -/
def HypothesisB (C_star : ℝ → ℝ) : Prop :=
  ∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (T : ℝ), 0 < T →
    gradIntegral sol T ≤ ENNReal.ofReal (C_star T)

/-- CONDITIONAL: Hypothesis B + BKM ⇒ every maximal solution is global. -/
theorem formB_implies_clayB {C_star : ℝ → ℝ} (hB : HypothesisB C_star) (bkm : BKMCriterion)
    {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) : sol.Tstar = ⊤ :=
  gradIntegral_finite_implies_global bkm sol fun T hT =>
    lt_of_le_of_lt (hB sol T hT) ENNReal.ofReal_lt_top

/-- The analytic bridge statement with the genuine definitions. Modulo standard,
unformalized local existence/uniqueness facts this is Clay Millennium Problem (B)
(periodic case). It is OPEN; see `ClassicalNSOpenTarget.lean`. -/
def AnalyticBridgeStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u0 : E3 → E3), ContDiff ℝ ∞ u0 → IsPeriodic u0 →
    (∀ x, divergence u0 x = 0) →
    ∀ sol : NSSolution ν u0, sol.Tstar = ⊤ ∧ ∀ T : ℝ, 0 < T → gradIntegral sol T < ⊤

/-- CONDITIONAL: Hypothesis B + BKM imply the analytic bridge statement. -/
theorem analyticBridge_of_formB {C_star : ℝ → ℝ} (hB : HypothesisB C_star)
    (bkm : BKMCriterion) : AnalyticBridgeStatement := by
  intro ν _ u0 _ _ _ sol
  have hG := formB_implies_clayB hB bkm sol
  exact ⟨hG, fun T _ => global_implies_gradIntegral_finite sol hG T⟩

/-- The statement is not refuted by the zero solution (its conclusion holds there). -/
theorem analyticBridge_conclusion_zeroSolution (ν : ℝ) (hν : 0 < ν) :
    (zeroSolution ν hν).Tstar = ⊤ ∧
      ∀ T : ℝ, 0 < T → gradIntegral (zeroSolution ν hν) T < ⊤ :=
  ⟨rfl, fun T _ => global_implies_gradIntegral_finite _ rfl T⟩

/-! ## Kato–Ponce energy (cited hypothesis) and the conditional `Hˢ` bound

The two Grönwall lemmas below are verbatim copies of the (sound, non-vacuous) lemmas
in the LEGACY file, re-stated in this namespace. -/

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

/-- **Kato–Ponce (1988) integrated energy inequality (cited, not proved).**
`HsR s f` is an explicitly documented parameter standing for `‖f‖_{Hˢ(T³)}`
(Mathlib has no Sobolev spaces on `T³`). Every field is a property of genuine
solutions that the true `Hˢ` norm satisfies (Kato–Ponce commutator estimate and
`u ∈ C([0,T⋆); Hˢ)`). Note `kp_trivial`: `HsR = 0` is also an instance, so this
structure is consistent, and for that instance the bound below is trivially true;
its content is for the true `Hˢ` norm. -/
structure KatoPonceEnergy (HsR : ℝ → (E3 → E3) → ℝ) (s C_s : ℝ) : Prop where
  HsR_nonneg : ∀ f, 0 ≤ HsR s f
  C_s_nonneg : 0 ≤ C_s
  HsR_cont : ∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (T : ℝ), 0 ≤ T →
    ENNReal.ofReal T < sol.Tstar → ContinuousOn (fun t => HsR s (sol.u t)) (Icc 0 T)
  energy : ∀ {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (t : ℝ), t ∈ lifespan sol.Tstar →
    HsR s (sol.u t) ≤
      HsR s u0 + ∫ τ in (0 : ℝ)..t, C_s * gradLinf (sol.u τ) * HsR s (sol.u τ)

theorem kp_trivial (s : ℝ) : KatoPonceEnergy (fun _ _ => 0) s 0 where
  HsR_nonneg := fun _ => le_rfl
  C_s_nonneg := le_rfl
  HsR_cont := fun _ _ _ _ => continuousOn_const
  energy := fun _ _ _ => by simp

/-- CONDITIONAL direct `Hˢ` bound: Kato–Ponce + Hypothesis B + BKM give
`‖u(t)‖_{Hˢ} ≤ ‖u₀‖_{Hˢ} exp(C_s · max(C⋆(T), 0))` on `[0, T]`. -/
theorem formB_Hs_bound {HsR : ℝ → (E3 → E3) → ℝ} {s C_s : ℝ} (kp : KatoPonceEnergy HsR s C_s)
    {C_star : ℝ → ℝ} (hB : HypothesisB C_star) (bkm : BKMCriterion)
    {ν : ℝ} {u0 : E3 → E3} (sol : NSSolution ν u0) (T : ℝ) (hTpos : 0 < T) :
    ∀ t ∈ Icc 0 T, HsR s (sol.u t) ≤ HsR s u0 * Real.exp (C_s * max (C_star T) 0) := by
  have hGlobal : sol.Tstar = ⊤ := formB_implies_clayB hB bkm sol
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
  -- `∫₀ᵗ ‖∇u‖_∞ ≤ max (C⋆ T) 0`, converted from the Lebesgue bound of Hypothesis B.
  have hM : 0 ≤ max (C_star T) 0 := le_max_right _ _
  have hint : IntegrableOn (fun τ => gradLinf (sol.u τ)) (Ioo 0 t) :=
    ((hg_cont.mono (Icc_subset_Icc_right ht.2)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hsubset : Ioo 0 t ⊆ lifeIco sol.Tstar T := fun τ hτ =>
    ⟨hτ.1.le, lt_of_lt_of_le hτ.2 ht.2, life τ⟩
  have hreal : (∫ τ in (0 : ℝ)..t, gradLinf (sol.u τ)) ≤ max (C_star T) 0 := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    have hofReal : ENNReal.ofReal (∫ τ in Ioo 0 t, gradLinf (sol.u τ)) ≤
        ENNReal.ofReal (max (C_star T) 0) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun τ => gradLinf_nonneg _)]
      calc ∫⁻ τ in Ioo 0 t, ENNReal.ofReal (gradLinf (sol.u τ))
          ≤ gradIntegral sol T := lintegral_mono_set hsubset
        _ ≤ ENNReal.ofReal (C_star T) := hB sol T hTpos
        _ ≤ ENNReal.ofReal (max (C_star T) 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
    exact (ENNReal.ofReal_le_ofReal_iff hM).1 hofReal
  have hβ_int_le : (∫ τ in (0 : ℝ)..t, C_s * gradLinf (sol.u τ)) ≤ C_s * max (C_star T) 0 := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hreal kp.C_s_nonneg
  exact le_trans (hG t ht)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hβ_int_le) (kp.HsR_nonneg u0))

end ClassicalNS
