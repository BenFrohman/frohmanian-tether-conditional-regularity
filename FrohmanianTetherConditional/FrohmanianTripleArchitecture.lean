import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# Complete Zero-sorry Lean 4 Formalization:
# The Frohmanian Triple Architecture & Metriplectic Navier–Stokes Regularity

Corrected for Mathlib v4.30.0-rc1 API (`intervalIntegral`, `uIcc`, `antitoneOn_of_deriv_nonpos`).
Strictly conditional: Clay/BKM analytic content remains assumed structure fields.
-/

noncomputable section
open Real Set MeasureTheory intervalIntegral Filter Topology

namespace FrohmanianTripleArchitecture

section OrthogonalTether

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def projPerp (u Φ : V) : V := Φ - (inner ℝ Φ u / ‖u‖ ^ 2) • u

@[simp]
lemma projPerp_self (u : V) : projPerp u u = 0 := by
  unfold projPerp
  by_cases hu : u = 0
  · simp [hu]
  · have hnorm : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    have hinner : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
    rw [hinner, div_self hnorm, one_smul, sub_self]

lemma inner_projPerp_self (u Φ : V) : inner ℝ (projPerp u Φ) u = 0 := by
  unfold projPerp
  by_cases hu : u = 0
  · simp [hu]
  · have hnorm : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq u]
    simp only [conj_trivial]
    rw [div_mul_cancel₀ _ hnorm, sub_self]

def tetherMetricCorrection (κ W_ω : ℝ) (u dF dG : V) : ℝ :=
  -κ * W_ω * inner ℝ (projPerp u dF) (projPerp u dG)

theorem tether_degenerate_H (κ W_ω : ℝ) (u dF : V) :
    tetherMetricCorrection κ W_ω u dF u = 0 := by
  unfold tetherMetricCorrection
  rw [projPerp_self, inner_zero_right, mul_zero]

theorem tether_symmetric (κ W_ω : ℝ) (u dF dG : V) :
    tetherMetricCorrection κ W_ω u dF dG = tetherMetricCorrection κ W_ω u dG dF := by
  unfold tetherMetricCorrection
  rw [real_inner_comm]

theorem tether_nonpos {κ W_ω : ℝ} (hκ : 0 ≤ κ) (hW : 0 ≤ W_ω) (u dF : V) :
    tetherMetricCorrection κ W_ω u dF dF ≤ 0 := by
  unfold tetherMetricCorrection
  have h_inner : 0 ≤ inner ℝ (projPerp u dF) (projPerp u dF) := real_inner_self_nonneg
  have h_coeff : 0 ≤ κ * W_ω := mul_nonneg hκ hW
  nlinarith

end OrthogonalTether

structure MetriplecticSystem (State V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  ν : ℝ
  hν : 0 < ν
  κ : ℝ
  hκ : 0 ≤ κ
  velField : State → V
  enstrophy : State → ℝ
  curlGradVar : ((State → ℝ) → State → V)
  curlGradVar_H : ∀ H : State → ℝ, ∀ ω, curlGradVar H ω = velField ω
  liePoisson : (State → ℝ) → (State → ℝ) → State → ℝ
  lp_skew : ∀ F G ω, liePoisson F G ω = -liePoisson G F ω
  morrisonDiss : (State → ℝ) → (State → ℝ) → State → ℝ
  diss_symm : ∀ F G ω, morrisonDiss F G ω = morrisonDiss G F ω

def totalMetriplecticBracket {State V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sys : MetriplecticSystem State V) (F G : State → ℝ) (ω : State) : ℝ :=
  sys.morrisonDiss F G ω + tetherMetricCorrection sys.κ (sys.enstrophy ω) (sys.velField ω)
    (sys.curlGradVar F ω) (sys.curlGradVar G ω)

theorem totalMetriplectic_symm {State V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sys : MetriplecticSystem State V) (F G : State → ℝ) (ω : State) :
    totalMetriplecticBracket sys F G ω = totalMetriplecticBracket sys G F ω := by
  unfold totalMetriplecticBracket
  rw [sys.diss_symm, tether_symmetric]

theorem totalMetriplectic_flow_equals_unmodified_NS {State V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sys : MetriplecticSystem State V) (H : State → ℝ) (F : State → ℝ) (ω : State) :
    sys.liePoisson F H ω + totalMetriplecticBracket sys F H ω =
    sys.liePoisson F H ω + sys.morrisonDiss F H ω := by
  unfold totalMetriplecticBracket
  rw [sys.curlGradVar_H H ω]
  have h_deg := tether_degenerate_H sys.κ (sys.enstrophy ω) (sys.velField ω)
    (sys.curlGradVar F ω)
  rw [h_deg, add_zero]

section AlignmentKernel

def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ := crossProduct a b
def dot3 (a b : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, a i * b i
def normSq3 (a : Fin 3 → ℝ) : ℝ := dot3 a a
def norm3 (a : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq3 a)

lemma abs_dot3_le (a b : Fin 3 → ℝ) : |dot3 a b| ≤ norm3 a * norm3 b := by
  unfold norm3 normSq3 dot3
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => mul_self_nonneg (a i))]
  apply Real.abs_le_sqrt
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) a b
  simpa only [sq] using hcs

def alignmentTetherKernel (dist : ℝ) (r_hat ξ_x ξ_y : Fin 3 → ℝ) : ℝ :=
  (3 / (4 * Real.pi * dist ^ 3)) * (dot3 r_hat ξ_x) * (dot3 (cross3 r_hat ξ_y) ξ_x)

lemma triple_product_cycle (r_hat ξ_x ξ_y : Fin 3 → ℝ) :
    dot3 (cross3 r_hat ξ_y) ξ_x = dot3 r_hat (cross3 ξ_y ξ_x) := by
  -- (a × b) · c = a · (b × c); expand components of `crossProduct`.
  simp [dot3, cross3, crossProduct, Fin.sum_univ_three]
  ring

theorem abs_alignmentKernel_le {dist : ℝ} (hdist : 0 < dist) {r_hat ξ_x : Fin 3 → ℝ}
    (hr : norm3 r_hat = 1) (hξx : norm3 ξ_x = 1) (ξ_y : Fin 3 → ℝ) :
    |alignmentTetherKernel dist r_hat ξ_x ξ_y| ≤
      (3 / (4 * Real.pi * dist ^ 3)) * norm3 (cross3 ξ_y ξ_x) := by
  unfold alignmentTetherKernel
  have hcoeff_pos : 0 < 3 / (4 * Real.pi * dist ^ 3) := by positivity
  rw [abs_mul, abs_mul, abs_of_pos hcoeff_pos]
  have h1 : |dot3 r_hat ξ_x| ≤ 1 := by
    calc |dot3 r_hat ξ_x| ≤ norm3 r_hat * norm3 ξ_x := abs_dot3_le r_hat ξ_x
      _ = 1 * 1 := by rw [hr, hξx]
      _ = 1 := mul_one 1
  have h2 : |dot3 (cross3 r_hat ξ_y) ξ_x| ≤ norm3 (cross3 ξ_y ξ_x) := by
    rw [triple_product_cycle]
    calc |dot3 r_hat (cross3 ξ_y ξ_x)| ≤ norm3 r_hat * norm3 (cross3 ξ_y ξ_x) :=
      abs_dot3_le r_hat (cross3 ξ_y ξ_x)
    _ = 1 * norm3 (cross3 ξ_y ξ_x) := by rw [hr]
    _ = norm3 (cross3 ξ_y ξ_x) := one_mul _
  calc (3 / (4 * Real.pi * dist ^ 3)) * |dot3 r_hat ξ_x| * |dot3 (cross3 r_hat ξ_y) ξ_x|
      ≤ (3 / (4 * Real.pi * dist ^ 3)) * 1 * norm3 (cross3 ξ_y ξ_x) := by gcongr
    _ = (3 / (4 * Real.pi * dist ^ 3)) * norm3 (cross3 ξ_y ξ_x) := by ring

theorem constantin_fefferman_desingularization {dist K_θ : ℝ} (hdist : 0 < dist)
    {r_hat ξ_x ξ_y : Fin 3 → ℝ} (hr : norm3 r_hat = 1) (hξx : norm3 ξ_x = 1)
    (h_lipschitz : norm3 (cross3 ξ_y ξ_x) ≤ K_θ * dist) :
    |alignmentTetherKernel dist r_hat ξ_x ξ_y| ≤ (3 / (4 * Real.pi * dist ^ 2)) * K_θ := by
  have h_kernel := abs_alignmentKernel_le hdist hr hξx ξ_y
  calc |alignmentTetherKernel dist r_hat ξ_x ξ_y|
      ≤ (3 / (4 * Real.pi * dist ^ 3)) * norm3 (cross3 ξ_y ξ_x) := h_kernel
    _ ≤ (3 / (4 * Real.pi * dist ^ 3)) * (K_θ * dist) := by gcongr
    _ = (3 / (4 * Real.pi * dist ^ 2)) * K_θ := by field_simp

end AlignmentKernel

lemma gronwall_differential_bound {Y α : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hY_diff : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ Y t)
    (hα_cont : ContinuousOn α (Icc 0 T))
    (h_ineq : ∀ t ∈ Icc 0 T, deriv Y t ≤ α t * Y t) :
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
      exact (hY_diff s hs).continuousAt.continuousWithinAt.mul hexp
    · intro s hs
      have hs' : s ∈ Icc 0 T := interior_subset hs
      have hYd : DifferentiableWithinAt ℝ Y (interior (Icc 0 T)) s :=
        (hY_diff s hs').differentiableWithinAt
      have hId : DifferentiableWithinAt ℝ (fun x => Real.exp (-I x)) (interior (Icc 0 T)) s :=
        ((hI_deriv_int s hs).differentiableAt.neg.exp).differentiableWithinAt
      exact hYd.mul hId
    · intro s hs
      have hs' : s ∈ Icc 0 T := interior_subset hs
      have hYd : HasDerivAt Y (deriv Y s) s := (hY_diff s hs').hasDerivAt
      have hId : HasDerivAt (fun x => Real.exp (-I x))
          (Real.exp (-I s) * -α s) s := (hI_deriv_int s hs).neg.exp
      have hprod := hYd.mul hId
      have hderiv : deriv φ s =
          deriv Y s * Real.exp (-I s) + Y s * (Real.exp (-I s) * -α s) := by
        simpa [φ] using hprod.deriv
      rw [hderiv]
      have hpos : 0 < Real.exp (-I s) := Real.exp_pos _
      have hineq := h_ineq s hs'
      calc
        deriv Y s * Real.exp (-I s) + Y s * (Real.exp (-I s) * -α s)
            = (deriv Y s - α s * Y s) * Real.exp (-I s) := by ring
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

structure NavierStokesUnifiedData where
  vorticitySup : ℝ → ℝ
  enstrophySq : ℝ → ℝ
  strainSup : ℝ → ℝ
  vorticity_nonneg : ∀ t ≥ 0, 0 ≤ vorticitySup t
  clayStatementB : Prop
  bkm_vorticity_criterion : clayStatementB ↔
    ∀ T > 0, ∃ C_ω : ℝ, ∀ t ∈ Icc 0 T, (∫ τ in (0 : ℝ)..t, vorticitySup τ) ≤ C_ω
  smooth_implies_bounded_strain : clayStatementB →
    ∀ T > 0, ∃ C_S : ℝ, ∀ t ∈ Icc 0 T, strainSup t ≤ C_S
  differential_bounds : ∀ T > 0,
    (∀ t ∈ Icc 0 T, DifferentiableAt ℝ vorticitySup t) ∧
    (ContinuousOn vorticitySup (Icc 0 T)) ∧
    (ContinuousOn strainSup (Icc 0 T)) ∧
    (∀ t ∈ Icc 0 T, deriv vorticitySup t ≤ strainSup t * vorticitySup t)

def HypothesisB (sol : NavierStokesUnifiedData) : Prop :=
  ∀ T > 0, ∃ C_star : ℝ, ∀ t ∈ Icc 0 T, (∫ τ in (0 : ℝ)..t, sol.strainSup τ) ≤ C_star

def BKMVorticityIntegrable (sol : NavierStokesUnifiedData) : Prop :=
  ∀ T > 0, ∃ C_ω : ℝ, ∀ t ∈ Icc 0 T, (∫ τ in (0 : ℝ)..t, sol.vorticitySup τ) ≤ C_ω

theorem hypothesisB_implies_clayStatementB (sol : NavierStokesUnifiedData)
    (hHypB : HypothesisB sol) : sol.clayStatementB := by
  rw [sol.bkm_vorticity_criterion]
  intro T hT
  obtain ⟨C_star, hC⟩ := hHypB T hT
  obtain ⟨hDiff, hVortCont, hStrainCont, hRiccati⟩ := sol.differential_bounds T hT
  have hM0 : 0 ≤ sol.vorticitySup 0 := sol.vorticity_nonneg 0 (le_refl 0)
  let M_max := sol.vorticitySup 0 * Real.exp C_star
  use M_max * T
  intro t ht
  have hVortInt : IntervalIntegrable sol.vorticitySup volume 0 t := by
    have hC : ContinuousOn sol.vorticitySup (uIcc 0 t) := by
      simpa [uIcc_of_le ht.1] using hVortCont.mono (Icc_subset_Icc_right ht.2)
    exact hC.intervalIntegrable
  have h_ptwise : ∀ τ ∈ Icc 0 t, sol.vorticitySup τ ≤ M_max := by
    intro τ hτ
    have hτT : τ ∈ Icc 0 T := ⟨hτ.1, le_trans hτ.2 ht.2⟩
    have hGron := gronwall_differential_bound (le_of_lt hT) hDiff hStrainCont hRiccati τ hτT
    have h_int_le : (∫ r in (0 : ℝ)..τ, sol.strainSup r) ≤ C_star := hC τ hτT
    exact le_trans hGron (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_int_le) hM0)
  have hM_max_nonneg : 0 ≤ M_max := mul_nonneg hM0 (le_of_lt (Real.exp_pos _))
  calc ∫ τ in (0 : ℝ)..t, sol.vorticitySup τ
      ≤ ∫ _ in (0 : ℝ)..t, M_max :=
        integral_mono_on ht.1 hVortInt intervalIntegrable_const h_ptwise
    _ = M_max * t := by simp [mul_comm]
    _ ≤ M_max * T := mul_le_mul_of_nonneg_left ht.2 hM_max_nonneg

theorem three_way_equivalence (sol : NavierStokesUnifiedData) :
    (HypothesisB sol ↔ BKMVorticityIntegrable sol) ∧
    (BKMVorticityIntegrable sol ↔ sol.clayStatementB) := by
  have h_bkm_clay : BKMVorticityIntegrable sol ↔ sol.clayStatementB :=
    sol.bkm_vorticity_criterion.symm
  have h_clay_hypB : sol.clayStatementB → HypothesisB sol := by
    intro hClay T hT
    obtain ⟨C_S, hCS⟩ := sol.smooth_implies_bounded_strain hClay T hT
    let C_S' := max C_S 0
    have hCS' : ∀ t ∈ Icc 0 T, sol.strainSup t ≤ C_S' := fun t ht =>
      (hCS t ht).trans (le_max_left _ _)
    have hCS_nonneg : 0 ≤ C_S' := le_max_right _ _
    use C_S' * T
    intro t ht
    have hStrainCont := (sol.differential_bounds T hT).2.2.1
    have hInt_sub : IntervalIntegrable sol.strainSup volume 0 t := by
      have hC : ContinuousOn sol.strainSup (uIcc 0 t) := by
        simpa [uIcc_of_le ht.1] using hStrainCont.mono (Icc_subset_Icc_right ht.2)
      exact hC.intervalIntegrable
    calc ∫ τ in (0 : ℝ)..t, sol.strainSup τ
        ≤ ∫ _ in (0 : ℝ)..t, C_S' := by
          apply integral_mono_on ht.1 hInt_sub intervalIntegrable_const
          intro τ hτ
          exact hCS' τ ⟨hτ.1, le_trans hτ.2 ht.2⟩
      _ = C_S' * t := by simp [mul_comm]
      _ ≤ C_S' * T := mul_le_mul_of_nonneg_left ht.2 hCS_nonneg
  constructor
  · constructor
    · intro hHypB
      exact h_bkm_clay.mpr (hypothesisB_implies_clayStatementB sol hHypB)
    · intro hBKM
      exact h_clay_hypB (h_bkm_clay.mp hBKM)
  · exact h_bkm_clay

end FrohmanianTripleArchitecture
