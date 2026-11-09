-- Copyright 2026 Benjamin Stanley Frohman. Apache-2.0.
import Mathlib

open MeasureTheory

/-!
# Analytic bridge target (OPEN)

Statement of Clay Millennium Problem (B) on the periodic 3-torus, stated as a target.
The single `sorry` below is the open problem. Nothing in this file is claimed proved.
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
  solves_NS : Prop      -- PLACEHOLDER: the PDE itself, not yet expressible in Mathlib
  maximal : Prop        -- PLACEHOLDER: Tstar cannot be extended

/-- Clay (B) target: smooth periodic Hˢ data (s > 5/2) never blows up.
Because `solves_NS` and `maximal` are placeholders, a proof of this exact
statement would NOT yet constitute a proof of Clay (B). -/
theorem analytic_bridge_unconditional
    (N : NormData) (ν : ℝ) (hν : 0 < ν) (s : ℝ) (hs : 5/2 < s)
    (u0 : R3 → Vec3) (hper : IsPeriodic u0) (hu0 : N.Hs s u0 < ⊤) :
    ∀ sol : NSSolution N ν u0,
      sol.Tstar = ⊤ ∧
      ∀ T : ℝ, 0 < T →
        IntervalIntegrable (fun t => N.vortLinf (sol.u t)) volume 0 T := by
  sorry  -- OPEN: this is Clay Millennium Problem Statement (B)
