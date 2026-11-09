-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import Mathlib

open Set MeasureTheory

/-!
# Analytic bridge target (OPEN)

Statement of Clay Millennium Problem (B) on the periodic 3-torus, stated as a target.

* Exactly one `sorry`: `analytic_bridge_unconditional` (the open problem).
* The easy direction `Clay(B) ⇒ BKM-integrability` and the conditional
  equivalence under an assumed BKM hypothesis are **proved** (no `sorry`).
* Nothing in this file is claimed to resolve Clay (B). Because `solves_NS` and
  `maximal` are placeholders, a proof of `analytic_bridge_unconditional` would
  **not** yet constitute a proof of Clay (B).
-/

/-- Points of ℝ³; fields are periodic lifts of fields on 𝕋³ = (ℝ/ℤ)³. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

/-- A field on ℝ³ that is 1-periodic in each coordinate, i.e. a field on 𝕋³. -/
def IsPeriodic (f : R3 → Vec3) : Prop :=
  ∀ (x : R3) (i : Fin 3), f (x + EuclideanSpace.single i 1) = f x

/-- Norms Mathlib does not yet provide on 𝕋³, valued in [0, ∞]. -/
structure NormData where
  Hs : ℝ → (R3 → Vec3) → ENNReal        -- ‖·‖_{Hˢ(𝕋³)}
  vortLinf : (R3 → Vec3) → ℝ            -- ‖∇ × ·‖_{L^∞(𝕋³)}

/-- A smooth solution of 3D Navier–Stokes on 𝕋³ × [0, T*) with data u0. -/
structure NSSolution (N : NormData) (ν : ℝ) (u0 : R3 → Vec3) where
  Tstar : ENNReal                        -- maximal existence time (⊤ = global)
  u : ℝ → R3 → Vec3
  init : u 0 = u0
  periodic : ∀ t, IsPeriodic (u t)
  smooth : ∀ t, 0 ≤ t → ENNReal.ofReal t < Tstar → ContDiff ℝ ⊤ (u t)
  /-- Regularity of a smooth solution; assumed input. -/
  vort_cont : ContinuousOn (fun t => N.vortLinf (u t))
    {t | 0 ≤ t ∧ ENNReal.ofReal t < Tstar}
  solves_NS : Prop      -- PLACEHOLDER: the PDE itself, not yet expressible in Mathlib
  maximal : Prop        -- PLACEHOLDER: Tstar cannot be extended

/-- Beale–Kato–Majda 1984, cited, not proved here.
If vorticity is L¹_t L^∞-integrable on every finite horizon, the solution is global. -/
structure BKMCriterion (N : NormData) where
  continuation :
    ∀ {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0),
      (∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.vortLinf (sol.u t)) volume 0 T) →
      sol.Tstar = ⊤

/-- One-directional Hypothesis B: supplies L¹_t L^∞ vorticity integrability.
No converse (Clay(B) → Hypothesis B) is stated. -/
structure HypothesisB (N : NormData) where
  integrable :
    ∀ {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0) (T : ℝ),
      0 < T → IntervalIntegrable (fun t => N.vortLinf (sol.u t)) volume 0 T

/-- Easy direction (PROVED): global lifespan ⇒ BKM-integrability of vorticity.
Uses the assumed `vort_cont` continuity of a smooth solution on [0, T*). -/
theorem clayB_implies_bkm_integrable
    {N : NormData} {ν : ℝ} {u0 : R3 → Vec3}
    (sol : NSSolution N ν u0) (hGlobal : sol.Tstar = ⊤)
    (T : ℝ) (hTpos : 0 < T) :
    IntervalIntegrable (fun t => N.vortLinf (sol.u t)) volume 0 T := by
  have hcont : ContinuousOn (fun t => N.vortLinf (sol.u t)) (uIcc 0 T) := by
    refine sol.vort_cont.mono ?_
    intro t ht
    -- With T > 0 we have uIcc 0 T = Icc 0 T ⊆ {t | 0 ≤ t ∧ ofReal t < ⊤}.
    rw [uIcc_of_le (le_of_lt hTpos)] at ht
    refine ⟨ht.1, ?_⟩
    rw [hGlobal]
    exact ENNReal.ofReal_lt_top
  exact hcont.intervalIntegrable

/-- Under assumed BKM (cited, not proved): Clay(B) ↔ BKM-integrability. PROVED. -/
theorem clayB_iff_bkm_integrable
    {N : NormData} (bkm : BKMCriterion N) {ν : ℝ} {u0 : R3 → Vec3}
    (sol : NSSolution N ν u0) :
    sol.Tstar = ⊤ ↔
      ∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.vortLinf (sol.u t)) volume 0 T := by
  constructor
  · intro hGlobal T hTpos
    exact clayB_implies_bkm_integrable sol hGlobal T hTpos
  · intro hint
    exact bkm.continuation sol hint

/-- Hypothesis B + assumed BKM ⇒ Clay(B). One-directional. PROVED. -/
theorem hypothesisB_implies_clayB
    {N : NormData} (hB : HypothesisB N) (bkm : BKMCriterion N)
    {ν : ℝ} {u0 : R3 → Vec3} (sol : NSSolution N ν u0) :
    sol.Tstar = ⊤ :=
  bkm.continuation sol (fun T hT => hB.integrable sol T hT)

/-- Clay (B) target: smooth periodic Hˢ data (s > 5/2) never blows up.
Because `solves_NS` and `maximal` are placeholders, a proof of this exact
statement would NOT yet constitute a proof of Clay (B). -/
theorem analytic_bridge_unconditional
    (N : NormData) (ν : ℝ) (hν : 0 < ν) (s : ℝ) (hs : 5 / 2 < s)
    (u0 : R3 → Vec3) (hper : IsPeriodic u0) (hu0 : N.Hs s u0 < ⊤) :
    ∀ sol : NSSolution N ν u0,
      sol.Tstar = ⊤ ∧
      ∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.vortLinf (sol.u t)) volume 0 T := by
  sorry  -- OPEN: this is Clay Millennium Problem Statement (B)
