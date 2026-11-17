/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import Mathlib

/-!
# FrohmanianTetherConditional.ClassicalEstimatePieces

The pieces of the standard vorticity / strain toolkit for 3D Navier–Stokes on `𝕋³` that are
within Mathlib's reach, proved here with no extra hypotheses beyond those stated:

* `sym_part_frobenius_le`: `‖S‖_F ≤ ‖∇u‖_F` pointwise, `S = (∇u + ∇uᵀ)/2` (as sums of squares).
* `antisym_mul_curl_eq_zero`, `grad_mul_curl_eq_sym_mul_curl`: `Ω ω = 0` for
  `Ω = (∇u − ∇uᵀ)/2`, `ω = curl u`, hence `(ω·∇)u = (∇u) ω = S ω`.
* `quadform_le_frobenius_mul_sq`: `⟨Sω, ω⟩ ≤ ‖S‖_F |ω|²`.
* `gronwall_linear`: `y' ≤ a(t) y` on `[0,T]` ⇒ `y T ≤ y 0 · exp ∫₀ᵀ a`.
* `cutoff_nonneg`, `cutoff_le_one`, `norm_fderiv_cutoff_le`: `φ = χ((x − x₀)/R)` satisfies
  `0 ≤ φ ≤ 1` and `‖∇φ‖ ≤ ‖∇χ‖_∞ / R`.
* `comoving_cutoff_bound`: `|(u(x) − u(x₀))·∇φ(x)| ≤ 2 C₁ L` on `B(x₀, 2R)` when
  `‖∇u‖ ≤ L` there and `‖∇φ‖ ≤ C₁/R` (mean-value inequality).
* Exponent arithmetic for the Prodi–Serrin-type `Lᵖ` bootstrap (`holder_triple_pasted_sum`,
  `interp_theta`, `young_pair`, `serrin_scaling`).
* `amplitude_refutes_rate_sup`, `amplitude_refutes_rate_enstrophy`, `rate_false_of_touch`:
  algebra showing the rate `M' ≤ C M² − κ M³` with `C, κ` independent of the amplitude fails
  for the explicit family `u₀ = A·U`.

## Cited classical results (NOT formalized here; never used as axioms)
* Calderón–Zygmund on `𝕋³`: for mean-zero divergence-free `u` with `ω = curl u`,
  `‖∇u‖_{Lᵖ(𝕋³)} ≤ C_p ‖ω‖_{Lᵖ(𝕋³)}`, `1 < p < ∞` (Fourier multipliers `ξ_k ξ_l/|ξ|²` on `ℤ³∖{0}`;
  Marcinkiewicz multiplier theorem / transference: Grafakos, *Classical Fourier Analysis*, §§4.3, 6.2;
  Stein, *Singular Integrals*, 1970; Majda–Bertozzi, *Vorticity and Incompressible Flow*, 2002, §2.4).
* Pointwise `d/dt ‖ω‖_∞ ≤ ‖S‖_∞ ‖ω‖_∞` along smooth solutions (Majda–Bertozzi §3.2;
  Beale–Kato–Majda 1984); the log-Sobolev inequality
  `‖∇u‖_∞ ≤ C(1 + ‖ω‖₂ + ‖ω‖_∞ log(e + ‖u‖_{Hˢ}))`, `s > 5/2`, on `𝕋³`
  (Beale–Kato–Majda 1984; Kozono–Taniuchi 2000); Sobolev `‖f‖₆ ≤ C(‖∇f‖₂ + ‖f‖₂)` on `𝕋³`;
  Moser iteration. These enter only as explicit hypotheses of the statements below.
-/

open Real Finset

noncomputable section

namespace ClassicalEstimatePieces

/-! ## 1. Strain vs. full gradient (pointwise Frobenius) -/

/-- Symmetric part. -/
def symPart (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (A i j + A j i) / 2

/-- Antisymmetric part. -/
def antiPart (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (A i j - A j i) / 2

/-- Squared Frobenius norm. -/
def frob2 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- `‖S‖_F² ≤ ‖A‖_F²`: the strain is pointwise no larger than the velocity gradient. -/
theorem sym_part_frobenius_le (A : Matrix (Fin 3) (Fin 3) ℝ) :
    frob2 (symPart A) ≤ frob2 A := by
  simp only [frob2, symPart, Fin.sum_univ_three]
  nlinarith [sq_nonneg (A 0 1 - A 1 0), sq_nonneg (A 0 2 - A 2 0), sq_nonneg (A 1 2 - A 2 1)]

/-- Square-root form: `‖S‖_F ≤ ‖A‖_F`. -/
theorem sym_part_frobenius_le_sqrt (A : Matrix (Fin 3) (Fin 3) ℝ) :
    √(frob2 (symPart A)) ≤ √(frob2 A) :=
  Real.sqrt_le_sqrt (sym_part_frobenius_le A)

/-! ## 2. `Ω ω = 0` -/

/-- `ω = curl u` from `A i j = ∂_j u_i`. -/
def curlOf (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![A 2 1 - A 1 2, A 0 2 - A 2 0, A 1 0 - A 0 1]

theorem antisym_mul_curl_eq_zero (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ∑ j, antiPart A i j * curlOf A j = 0 := by
  fin_cases i <;> simp [antiPart, curlOf, Fin.sum_univ_three] <;> ring

/-- Vortex stretching sees only the strain: `(ω·∇)u = (∇u) ω = S ω`. -/
theorem grad_mul_curl_eq_sym_mul_curl (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    ∑ j, A i j * curlOf A j = ∑ j, symPart A i j * curlOf A j := by
  have h := antisym_mul_curl_eq_zero A i
  have : ∀ j, A i j = symPart A i j + antiPart A i j := fun j => by
    simp only [symPart, antiPart]; ring
  simp_rw [this, add_mul, Finset.sum_add_distrib, h, add_zero]

/-! ## 3. `⟨Sω, ω⟩ ≤ ‖S‖_F |ω|²` -/

theorem quadform_le_frobenius_mul_sq (S : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) :
    ∑ i, ∑ j, S i j * w i * w j ≤ √(frob2 S) * ∑ i, w i ^ 2 := by
  -- Cauchy–Schwarz over the 9 index pairs.
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => S p.1 p.2) (fun p => w p.1 * w p.2)
  have h1 : ∑ p : Fin 3 × Fin 3, S p.1 p.2 * (w p.1 * w p.2) = ∑ i, ∑ j, S i j * w i * w j := by
    rw [Fintype.sum_prod_type]; simp [mul_assoc]
  have h2 : ∑ p : Fin 3 × Fin 3, S p.1 p.2 ^ 2 = frob2 S := by
    rw [Fintype.sum_prod_type]; rfl
  have h3 : ∑ p : Fin 3 × Fin 3, (w p.1 * w p.2) ^ 2 = (∑ i, w i ^ 2) ^ 2 := by
    rw [Fintype.sum_prod_type]; simp only [Fin.sum_univ_three]; ring
  rw [h1, h2, h3] at hcs
  have hw : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ∑ i, ∑ j, S i j * w i * w j ≤ |∑ i, ∑ j, S i j * w i * w j| := le_abs_self _
    _ ≤ √(frob2 S * (∑ i, w i ^ 2) ^ 2) := Real.abs_le_sqrt hcs
    _ = √(frob2 S) * ∑ i, w i ^ 2 := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hw]

/-! ## 4. Linear Grönwall `y' ≤ a(t) y` -/

/-- **Grönwall (linear, time-dependent rate).** If `y` is differentiable on `[0,T]` with
`y' ≤ a(t) y` on `(0,T)` and `a` is continuous, then `y T ≤ y 0 · exp (∫₀ᵀ a)`.
With `y = ‖ω‖_∞` and `a = ‖S‖_∞` this is BKM's exponential bound, *given* the cited pointwise
inequality `d/dt ‖ω‖_∞ ≤ ‖S‖_∞ ‖ω‖_∞` as the hypothesis `hle`. -/
theorem gronwall_linear {y y' a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (ha : Continuous a)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t)
    (hle : ∀ t ∈ Set.Ioo 0 T, y' t ≤ a t * y t) :
    y T ≤ y 0 * Real.exp (∫ s in (0 : ℝ)..T, a s) := by
  set I : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s with hI
  have hIder : ∀ t, HasDerivAt I (a t) t := fun t => (ha.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℝ := fun t => y t * Real.exp (-I t) with hg
  have hgder : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt g (y' t * Real.exp (-I t) + y t * (Real.exp (-I t) * -a t)) t := by
    intro t ht
    exact (hy t ht).mul ((hIder t).neg.exp)
  have hcont : ContinuousOn g (Set.Icc 0 T) := fun t ht => (hgder t ht).continuousAt.continuousWithinAt
  have hint : interior (Set.Icc (0 : ℝ) T) = Set.Ioo 0 T := interior_Icc
  have hanti : AntitoneOn g (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont
    · rw [hint]; intro t ht
      exact (hgder t (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · rw [hint]; intro t ht
      rw [(hgder t (Set.Ioo_subset_Icc_self ht)).deriv]
      have he := Real.exp_pos (-I t)
      have := hle t ht
      nlinarith
  have h0 : g T ≤ g 0 := hanti ⟨le_refl 0, hT⟩ ⟨hT, le_refl T⟩ hT
  have hI0 : I 0 = 0 := by simp [hI]
  simp only [hg, hI0, neg_zero, Real.exp_zero, mul_one] at h0
  have he := Real.exp_pos (I T)
  calc y T = y T * Real.exp (-I T) * Real.exp (I T) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ y 0 * Real.exp (I T) := mul_le_mul_of_nonneg_right h0 he.le

/-! ## 5. The cutoff `φ(x) = χ((x − x₀)/R)` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rescaled, recentred cutoff. -/
def cutoff (χ : E → ℝ) (x₀ : E) (R : ℝ) : E → ℝ := fun x => χ (R⁻¹ • (x - x₀))

theorem cutoff_nonneg {χ : E → ℝ} (h : ∀ y, 0 ≤ χ y) (x₀ : E) (R : ℝ) (x : E) :
    0 ≤ cutoff χ x₀ R x := h _

theorem cutoff_le_one {χ : E → ℝ} (h : ∀ y, χ y ≤ 1) (x₀ : E) (R : ℝ) (x : E) :
    cutoff χ x₀ R x ≤ 1 := h _

/-- Chain rule: `Dφ(x) = R⁻¹ · Dχ((x − x₀)/R)`. -/
theorem hasFDerivAt_cutoff {χ : E → ℝ} (hχ : Differentiable ℝ χ) (x₀ : E) (R : ℝ) (x : E) :
    HasFDerivAt (cutoff χ x₀ R)
      ((fderiv ℝ χ (R⁻¹ • (x - x₀))).comp (R⁻¹ • ContinuousLinearMap.id ℝ E)) x := by
  have hin : HasFDerivAt (fun x : E => R⁻¹ • (x - x₀)) (R⁻¹ • ContinuousLinearMap.id ℝ E) x := by
    have := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀).const_smul R⁻¹
    simpa using this
  exact (hχ _).hasFDerivAt.comp x hin

/-- Derivative scaling: if `‖Dχ‖ ≤ B` everywhere and `R > 0` then `‖Dφ‖ ≤ B / R`. -/
theorem norm_fderiv_cutoff_le {χ : E → ℝ} (hχ : Differentiable ℝ χ) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ χ y‖ ≤ B) (x₀ : E) {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (cutoff χ x₀ R) x‖ ≤ B / R := by
  rw [(hasFDerivAt_cutoff hχ x₀ R x).fderiv]
  calc _ ≤ ‖fderiv ℝ χ (R⁻¹ • (x - x₀))‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ E‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * R⁻¹ := by
        apply mul_le_mul (hB _) _ (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
        calc ‖R⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ ‖R⁻¹‖ * ‖ContinuousLinearMap.id ℝ E‖ :=
              ContinuousLinearMap.opNorm_smul_le (R⁻¹) (ContinuousLinearMap.id ℝ E)
          _ ≤ ‖R⁻¹‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
          _ = R⁻¹ := by rw [mul_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    _ = B / R := by rw [div_eq_mul_inv]

/-! ## 6. Comoving bound -/

/-- **Comoving cutoff bound.** If `‖Du‖ ≤ L` on the ball `B(x₀, 2R)` (convex, `u` differentiable
there), `‖∇φ(x)‖ ≤ C₁/R` and `x ∈ B(x₀, 2R)`, then `|⟪u(x) − u(x₀), ∇φ(x)⟫| ≤ 2 C₁ L`.
Since `(∂ₜ + u·∇)φ = (u(x) − ẋ₀)·∇φ` and `ẋ₀ = u(x₀)`, this is the pasted bound; outside the ball
`∇φ = 0` when `supp χ ⊆ B(0,2)`. -/
theorem comoving_cutoff_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : F → F} {x₀ x g : F} {R L C₁ : ℝ} (hR : 0 < R)
    (hdiff : ∀ y ∈ Metric.closedBall x₀ (2 * R), DifferentiableAt ℝ u y)
    (hL : ∀ y ∈ Metric.closedBall x₀ (2 * R), ‖fderiv ℝ u y‖ ≤ L)
    (hx : x ∈ Metric.closedBall x₀ (2 * R)) (hg : ‖g‖ ≤ C₁ / R) :
    |@inner ℝ F _ (u x - u x₀) g| ≤ 2 * C₁ * L := by
  have hmv : ‖u x - u x₀‖ ≤ L * ‖x - x₀‖ :=
    (convex_closedBall x₀ (2 * R)).norm_image_sub_le_of_norm_fderiv_le hdiff hL
      (Metric.mem_closedBall_self (by positivity)) hx
  have hxd : ‖x - x₀‖ ≤ 2 * R := by rw [← dist_eq_norm]; exact hx
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x hx)
  calc |@inner ℝ F _ (u x - u x₀) g| ≤ ‖u x - u x₀‖ * ‖g‖ := abs_real_inner_le_norm _ _
    _ ≤ (L * (2 * R)) * (C₁ / R) := by
        apply mul_le_mul (hmv.trans (mul_le_mul_of_nonneg_left hxd hL0)) hg (norm_nonneg _)
        positivity
    _ = 2 * C₁ * L := by field_simp

/-! ## 7. Exponent arithmetic for the `Lᵖ` vorticity bootstrap -/

/-- The pasted triple `(r/p, 2r/(r−2p), 2r/r)`: its reciprocals DO sum to `1` (for `r ≠ 0`),
so it is an admissible Hölder triple when `r > 2p`. (Its defect is a mismatch with the stated
`L^r` condition on `S`, not the arithmetic.) -/
theorem holder_triple_pasted_sum {p r : ℝ} (hr : r ≠ 0) :
    p / r + (r - 2 * p) / (2 * r) + r / (2 * r) = 1 := by
  field_simp; ring

/-- Two-factor Hölder for `∫ |S| f²`, `f = |ω|^{p/2}`: `1/r + 1/r' = 1` with `r' = r/(r−1)`. -/
theorem holder_pair {r : ℝ} (hr : 1 < r) : 1 / r + (r - 1) / r = 1 := by
  have : r ≠ 0 := by linarith
  field_simp; ring

/-- Interpolation `L^{2r'} ⊂ [L², L⁶]`: with `θ = 3/(2r)`,
`1/(2r') = (1−θ)/2 + θ/6` where `r' = r/(r−1)`; `0 < θ ≤ 1` iff `r ≥ 3/2`. -/
theorem interp_theta {r : ℝ} (hr : 3 / 2 ≤ r) :
    (r - 1) / (2 * r) = (1 - 3 / (2 * r)) / 2 + (3 / (2 * r)) / 6 ∧
      0 < 3 / (2 * r) ∧ 3 / (2 * r) ≤ 1 := by
  have hr0 : 0 < r := by linarith
  refine ⟨by field_simp; ring, by positivity, ?_⟩
  rw [div_le_one (by positivity)]; linarith

/-- Young pair absorbing `‖∇f‖₂^{3/r}` into `‖∇f‖₂²`: exponents `2r/3` and `2r/(2r−3)`. -/
theorem young_pair {r : ℝ} (hr : 3 / 2 < r) : 3 / (2 * r) + (2 * r - 3) / (2 * r) = 1 := by
  have : r ≠ 0 := by linarith
  field_simp; ring

/-- Resulting time exponent `s = 2r/(2r−3)` satisfies the Prodi–Serrin scaling `2/s + 3/r = 2`. -/
theorem serrin_scaling {r : ℝ} (hr : 3 / 2 < r) : 2 / (2 * r / (2 * r - 3)) + 3 / r = 2 := by
  have h1 : r ≠ 0 := by linarith
  have h2 : 2 * r - 3 ≠ 0 := by linarith
  field_simp; ring

/-! ## 8. Amplitude refutation of the rate with amplitude-independent constants -/

/-- Sup-norm proxy, `u₀ = A·U`: `M(0) = 6A`, and the touching component has right-derivative
`6A(A − ν)`. For every `ν, C` and `κ > 0` some amplitude beats `C M(0)² − κ M(0)³`. -/
theorem amplitude_refutes_rate_sup (ν C κ : ℝ) (hν : 0 < ν) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ C * (6 * A) ^ 2 - κ * (6 * A) ^ 3 < 6 * A * (A - ν) := by
  refine ⟨1 + ν + |C| / κ, by positivity, ?_⟩
  set A := 1 + ν + |C| / κ with hA
  have hCk : |C| ≤ κ * A := by
    rw [hA]; have : |C| / κ * κ = |C| := div_mul_cancel₀ _ hκ.ne'
    nlinarith [abs_nonneg C, div_nonneg (abs_nonneg C) hκ.le]
  have hApos : 0 < A := by positivity
  have hAν : 1 ≤ A - ν := by rw [hA]; have := div_nonneg (abs_nonneg C) hκ.le; linarith
  have hC : C ≤ |C| := le_abs_self C
  nlinarith [mul_pos hApos hApos, mul_pos (mul_pos hApos hApos) hκ]

/-- Enstrophy proxy, `E(0) = e X`, `E'(0) = −d X` with `X = A² > 0` (for `U`: `e = 80π³`,
`d = 176π³ν`, production `∫ ω·Sω = 0`). Even though `E` decreases, the cubic damping
`−κ E³` (degree 6 in `A`) beats the true decay rate (degree 2) for large `A`. -/
theorem amplitude_refutes_rate_enstrophy (e d C κ : ℝ) (he : 0 < e) (hd : 0 ≤ d) (hκ : 0 < κ) :
    ∃ X : ℝ, 0 < X ∧ C * (e * X) ^ 2 - κ * (e * X) ^ 3 < -(d * X) := by
  refine ⟨(|C| + 1) / (κ * e) + d / e ^ 2 + 1, by positivity, ?_⟩
  set X := (|C| + 1) / (κ * e) + d / e ^ 2 + 1 with hX
  have hXpos : 0 < X := by positivity
  have hke : 0 < κ * e := mul_pos hκ he
  have h1 : |C| + 1 ≤ κ * e * X := by
    have : (|C| + 1) / (κ * e) * (κ * e) = |C| + 1 := div_mul_cancel₀ _ hke.ne'
    have h0 : 0 ≤ d / e ^ 2 := by positivity
    nlinarith
  have h2 : d < e ^ 2 * X := by
    have : d / e ^ 2 * e ^ 2 = d := div_mul_cancel₀ _ (by positivity)
    have h0 : 0 ≤ (|C| + 1) / (κ * e) := by positivity
    nlinarith [sq_nonneg e, pow_pos he 2]
  have hC : C ≤ |C| := le_abs_self C
  -- κ e³X³ − C e²X² − dX ≥ e²X²(κeX − |C|) − dX ≥ e²X² − dX > 0
  have key : e ^ 2 * X ^ 2 * (κ * e * X - |C|) ≥ e ^ 2 * X ^ 2 := by
    have : 1 ≤ κ * e * X - |C| := by linarith
    have hp : 0 ≤ e ^ 2 * X ^ 2 := by positivity
    nlinarith
  have hdX : d * X < e ^ 2 * X ^ 2 := by nlinarith
  have hCX : C * (e * X) ^ 2 ≤ |C| * (e * X) ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  nlinarith

/-- Explicit `U` instance of the enstrophy computation (`∫|curl U|² = 80π³`,
`∫|∇ curl U|² = 88π³` on `(ℝ/2πℤ)³`, so `E'(0) = −2ν·88π³A² = −176π³νA²`; computed exactly by
`taskA/hdi_check.py`, cited here as data). -/
theorem amplitude_refutes_rate_enstrophy_U (ν C κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧
      C * (80 * π ^ 3 * A ^ 2) ^ 2 - κ * (80 * π ^ 3 * A ^ 2) ^ 3 < -(176 * π ^ 3 * ν * A ^ 2) := by
  obtain ⟨X, hX, h⟩ := amplitude_refutes_rate_enstrophy (80 * π ^ 3) (176 * π ^ 3 * ν) C κ
    (by positivity) (by positivity) hκ
  refine ⟨√X, Real.sqrt_pos.mpr hX, ?_⟩
  rw [Real.sq_sqrt hX.le]
  linarith

/-- **Touching lemma.** If `g ≤ M` on `[0, δ)`, `g 0 = M 0`, and both have right derivatives
at `0`, then `g'(0⁺) ≤ M'(0⁺)`. With `g(t) = ω₃(0,t)` and `M = ‖ω‖_∞` this transfers the
vorticity-equation value `6A(A−ν)` (classical smoothness at `t = 0`, cited) to `M`. -/
theorem deriv_le_of_touch {M g : ℝ → ℝ} {m d δ : ℝ} (hδ : 0 < δ)
    (hM : HasDerivWithinAt M m (Set.Ici 0) 0) (hg : HasDerivWithinAt g d (Set.Ici 0) 0)
    (hle : ∀ t ∈ Set.Ico 0 δ, g t ≤ M t) (h0 : g 0 = M 0) : d ≤ m := by
  have hmin : IsLocalMinOn (fun t => M t - g t) (Set.Ici 0) 0 := by
    have : Set.Ico (0 : ℝ) δ ∈ nhdsWithin 0 (Set.Ici 0) := Ico_mem_nhdsGE hδ
    filter_upwards [this] with t ht
    simp only [h0, sub_self]; linarith [hle t ht]
  have hder : HasFDerivWithinAt (fun t => M t - g t)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (m - d))) (Set.Ici 0) 0 :=
    (hM.sub hg).hasFDerivWithinAt
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    intro t ht
    simp only [zero_add] at ht
    rw [segment_eq_Icc (by norm_num)] at ht
    exact ht.1
  have := hmin.hasFDerivWithinAt_nonneg hder hcone
  simp at this
  linarith

/-- **Rate fails at a touch.** If `M` has right derivative `m` at `0` obeying
`m ≤ C M(0)² − κ M(0)³`, while a touching `g` has `g'(0⁺) > C M(0)² − κ M(0)³`, contradiction. -/
theorem rate_false_of_touch {M g : ℝ → ℝ} {m d δ C κ : ℝ} (hδ : 0 < δ)
    (hM : HasDerivWithinAt M m (Set.Ici 0) 0) (hg : HasDerivWithinAt g d (Set.Ici 0) 0)
    (hle : ∀ t ∈ Set.Ico 0 δ, g t ≤ M t) (h0 : g 0 = M 0)
    (hrate : m ≤ C * M 0 ^ 2 - κ * M 0 ^ 3) (hbig : C * M 0 ^ 2 - κ * M 0 ^ 3 < d) : False := by
  have := deriv_le_of_touch hδ hM hg hle h0
  linarith

/-- **ν-only constants are refuted (sup-norm form), conditional only on the cited classical
facts for the datum `A·U`.** Suppose for every amplitude `A > 0` the solution's `M_A = ‖ω‖_∞`
has a right derivative `m A` at `0` with `M_A(0) = 6A`, and a touching component `g_A` with
right-derivative `6A(A−ν)` (the vorticity equation at the origin; classical, cited). Then no
pair `C, κ > 0` independent of `A` makes `M_A' ≤ C M_A² − κ M_A³` hold at `t = 0` for all `A`. -/
theorem not_uniform_rate_sup {ν C κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ)
    (M g : ℝ → ℝ → ℝ) (m : ℝ → ℝ) (δ : ℝ → ℝ) (hδ : ∀ A, 0 < δ A)
    (hM : ∀ A, 0 < A → HasDerivWithinAt (M A) (m A) (Set.Ici 0) 0)
    (hM0 : ∀ A, 0 < A → M A 0 = 6 * A)
    (hg : ∀ A, 0 < A → HasDerivWithinAt (g A) (6 * A * (A - ν)) (Set.Ici 0) 0)
    (hle : ∀ A, 0 < A → ∀ t ∈ Set.Ico 0 (δ A), g A t ≤ M A t)
    (h0 : ∀ A, 0 < A → g A 0 = M A 0) :
    ¬ ∀ A, 0 < A → m A ≤ C * M A 0 ^ 2 - κ * M A 0 ^ 3 := by
  intro hrate
  obtain ⟨A, hA, hbig⟩ := amplitude_refutes_rate_sup ν C κ hν hκ
  exact rate_false_of_touch (hδ A) (hM A hA) (hg A hA) (hle A hA) (h0 A hA) (hrate A hA)
    (by rw [hM0 A hA]; exact hbig)

end ClassicalEstimatePieces
