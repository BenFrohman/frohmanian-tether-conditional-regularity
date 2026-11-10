# Frohmanian Tether: Conditional Continuation and Small-Data Regularity for 3D Navier–Stokes on T³

[![Lean build and kernel check](https://github.com/BenFrohman/frohmanian-tether-conditional-regularity/actions/workflows/lean.yml/badge.svg)](https://github.com/BenFrohman/frohmanian-tether-conditional-regularity/actions/workflows/lean.yml)

Companion repository for two published preprint drafts by Benjamin Stanley
Frohman:

- *Geometric Phase-Space Completion and Conditional Global Regularity for the
  3D Incompressible Navier–Stokes Equations* (Frohmanian Tether draft),
  DOI [10.5281/zenodo.24079623](https://doi.org/10.5281/zenodo.24079623).
- *Three Pillars of 3D Incompressible Navier–Stokes Theory: Kato Local
  Existence, Fujita–Kato Small-Data Globality, and the Beale–Kato–Majda
  Continuation Criterion* (Three Pillars draft),
  DOI [10.5281/zenodo.24080310](https://doi.org/10.5281/zenodo.24080310).

> **Status:** the two Zenodo records above are published. The `paper/`
> directory holds the LaTeX sources and PDFs (MD5s listed in
> `paper/README.md`).

## Scope (read this first)

This is a **strictly conditional, expository** work. It does **not** solve the
Clay Millennium Problem on Navier–Stokes existence and smoothness.

| Component | Scope | Status |
|---|---|---|
| Theorem A: Beale–Kato–Majda continuation | Arbitrary data, u₀ ∈ Hˢ(T³), s > 5/2 | **Conditional, one-directional.** For each finite T, ∫₀ᵀ ‖S(t)‖_{L^∞} dt < ∞ ⇒ T* > T. Conditional on Form B / Hypothesis B. |
| Theorem B: Kato local existence | Arbitrary data, u₀ ∈ Hˢ(T³), s > 5/2 | **Unconditional, local.** Unique solution on [0, T_loc] with T_loc ≥ 1/(C_s ‖u₀‖_{Hˢ}) (Kato–Ponce commutator, mollified/Galerkin construction with Aubin–Lions, L² uniqueness by Grönwall). |
| Theorem C: Fujita–Kato small data | ‖u₀‖_{Ḣ^{1/2}} ≤ εν | **Unconditional, small-data global** (T* = ∞). |
| Metriplectic geometry | Phase-space completion | **Exact / canonical.** Arnold Lie–Poisson bracket (Jacobi identity cited: Arnold 1966; Marsden–Weinstein 1983; Arnold–Khesin 1998) plus the symmetric tether B(F,G) with B(F,H) ≡ 0. |
| Clay Statement (B) | Arbitrary large smooth data | **OPEN.** Nothing here bridges the gap between the energy-class bound L²ₜL²ₓ and the critical strain integrability L¹ₜL^∞ₓ. |

Theorems A, B and C are classical results (Beale–Kato–Majda 1984;
Kozono–Taniuchi 2000; Kato 1972/1984; Fujita–Kato 1964). They are cited, not
claimed as new and not as consequences of the tether.

The tether term B(F,G) is **symmetric** in F and G, so it is a metric-type
(metriplectic) term, **not** a Poisson-bracket correction. In the
velocity-slot form, where the projection Π_u acts on ∇×δF/δω, B(F,H) = 0 for
the kinetic-energy Hamiltonian H, since ∇×δH/δω = u.

## Lean formalization

`FrohmanianTetherConditional/FrohmanianTripleArchitecture.lean` (the same file
as in the Tether Zenodo draft, MD5 `285eb86970485f0d053f7406fca944f0`) is a
machine-checked proof of the metriplectic algebra, tether degeneracy and
symmetry, the ℝ³ alignment-kernel (Constantin–Fefferman-type) pointwise bound,
and Grönwall logic **over abstract PDE input types**.

- Toolchain: Lean `v4.30.0-rc1`, Mathlib `v4.30.0-rc1` (pinned in
  `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`).
- Zero `sorry`, `admit`, `axiom` or `native_decide`.
- Every checked theorem depends only on Lean's three standard axioms:
  `propext`, `Classical.choice`, `Quot.sound`.

Checked declarations: `projPerp_self`, `inner_projPerp_self`,
`tether_degenerate_H`, `tether_symmetric`, `tether_nonpos`,
`totalMetriplectic_symm`, `totalMetriplectic_flow_equals_unmodified_NS`,
`abs_dot3_le`, `triple_product_cycle`, `abs_alignmentKernel_le`,
`constantin_fefferman_desingularization`, `gronwall_differential_bound`,
`hypothesisB_implies_clayStatementB`, `three_way_equivalence`.

**What the Lean file does not prove.** The Navier–Stokes analytic content is
supplied as assumed structure fields, not derived:

- `MetriplecticSystem`: skew-symmetry of the Lie–Poisson bracket (`lp_skew`),
  symmetry of the dissipative bracket (`diss_symm`), and ∇×δH/δω = u
  (`curlGradVar_H`). The Jacobi identity is not formalized.
- `NavierStokesUnifiedData`: `clayStatementB` is an abstract `Prop`; the BKM
  criterion, bounded strain for smooth solutions, and the growth inequality
  M′ ≤ S·M are hypotheses.

So `hypothesisB_implies_clayStatementB` and `three_way_equivalence` are
logical consequences of those assumptions. They are not a proof of Clay
Statement (B) for 3D Navier–Stokes on T³.


## Genuine Navier–Stokes encoding and the OPEN target (Nov 2026)

`FrohmanianTetherConditional/ClassicalNS.lean` (namespace `ClassicalNS`) defines a
solution object that **requires** the equations:

- **Genuinely encoded:** periodic (`T³ = ℝ³/ℤ³` as 1-periodic functions on ℝ³)
  velocity `u` and pressure `p`; `u(0) = u₀`; `C^∞` in space at every lifespan time and
  jointly `C^∞` on `(0, T⋆) × ℝ³`; `u` and `∇u` jointly continuous on `[0, T⋆) × ℝ³`;
  `div u = 0`; and `∂ₜuⱼ = νΔuⱼ − (u·∇)uⱼ − ∂ⱼp` pointwise on `(0, T⋆)`, with `ν > 0`.
  **Maximality:** no classical solution on a strictly longer interval agrees with `u`
  on `[0, T⋆)`. `‖∇u‖_∞` is a real definition (sup of `‖Du‖` over the period cell).
- **Cited hypotheses (named, not proved):** `BKMCriterion` (finite `T⋆` ⇒
  `∫₀^{T⋆}‖∇u‖_∞ = ∞`; Beale–Kato–Majda 1984 / Kato) and `KatoPonceEnergy`, where
  the `Hˢ` norm is an explicitly documented parameter `HsR` (Mathlib has no Sobolev
  spaces on `T³`). `HypothesisB` is a Clay-strength assumption whose truth is open.
- **Non-vacuity, proved:** `zeroSolution` / `constSolution` are genuine global
  solutions (`nonempty_NSSolution_zero`); `old_counterexample_invalid` (the zero field
  with `T⋆ = 1` is not an `NSSolution`); `zero_field_is_global`;
  `linear_in_time_not_NS` (the momentum equation really constrains).
- **Proved with genuine content:** `global_implies_gradIntegral_finite`,
  `gradLinf_continuousOn`; **conditional** on the cited hypotheses:
  `clayB_iff_gradIntegral_finite`, `formB_implies_clayB`, `analyticBridge_of_formB`,
  `formB_Hs_bound`.
- **OPEN:** `ClassicalNSOpenTarget.lean` states `ClassicalNS.analytic_bridge_unconditional
  : AnalyticBridgeStatement` (every maximal classical solution is global, with finite
  `∫₀ᵀ‖∇u‖_∞`). Modulo standard local existence/uniqueness facts (not formalized) this
  is Clay Millennium Problem (B). It has exactly one intentional `sorry`, is excluded
  from the forbidden-token scan and from every axiom audit, and is **not claimed**.

`FrohmanianTetherConditional/FrohmanianTripleArchitectureLifespan.lean` gives the
lifespan-corrected `NavierStokesUnifiedData` (regularity only on `[0, T⋆)`,
`clayStatementB := T⋆ = ⊤`), re-proves `hypothesisB_implies_clayStatementB` and
`three_way_equivalence` (conditional on the cited BKM field) and proves they are no
longer contentless: `blowupModel` (`T⋆ = 1`) satisfies the structure but not Clay (B)
(`clayStatementB_not_automatic`, `hypothesisB_not_automatic`,
`old_trivialization_fails`).

### LEGACY findings (kept, not deleted)

`FrohmanianTetherConditional/AnalyticBridgeRefutation.lean` proves, about the LEGACY
files:

- `analytic_bridge_target_statement_false`: the LEGACY target statement
  (`analytic_bridge_unconditional_statement` in `AnalyticBridgeTarget.lean`, formerly a
  theorem with a placeholder proof) is **false**, because the LEGACY `NSSolution` does
  not encode Navier–Stokes (zero field with `Tstar = 1`).
- `not_nonempty_BKMCriterion`: the LEGACY `BKMCriterion N` is uninhabited, so the
  LEGACY `clayB_iff_bkm_integrable`, `formB_implies_clayB`,
  `hypothesisB_implies_clayB`, `formB_Hs_bound` are **vacuous**.
- `hypothesisB_holds` / `clayStatementB_holds`: the original
  `FrohmanianTripleArchitecture.NavierStokesUnifiedData` presupposes `clayStatementB`,
  so the original `hypothesisB_implies_clayStatementB` and `three_way_equivalence`
  carry **no information**. That file is left byte-identical (it is the file archived
  with the Tether Zenodo record); use the `…Lifespan` versions instead.

None of this proves anything about Navier–Stokes regularity. A write-up of how these
defects were found is in `papers/vacuity-audit/`.

## Build and check

```bash
# needs elan (https://github.com/leanprover/elan)
lake exe cache get        # download prebuilt Mathlib
lake build                # builds all three libraries (one expected OPEN-target warning)
./scripts/kernel_check.sh # forbidden-token scan + #print axioms audit
```

CI (`.github/workflows/lean.yml`) runs `lake build` and the kernel/axiom check
on every push and pull request.

## Contents

| Path | Description |
|------|-------------|
| `FrohmanianTetherConditional/FrohmanianTripleArchitecture.lean` | Lean 4 formalization (conditional, abstract PDE inputs) |
| `FrohmanianTetherConditional/AnalyticBridgeTarget.lean` | LEGACY placeholder encoding (refuted / vacuous; kept for the record) |
| `FrohmanianTetherConditional/AnalyticBridgeRefutation.lean` | Kernel-checked refutation and vacuity witnesses for the LEGACY files |
| `FrohmanianTetherConditional/ClassicalNS.lean` | Genuine classical periodic NS solutions, maximal lifespan, BKM/Kato–Ponce as named cited hypotheses, non-vacuity lemmas |
| `FrohmanianTetherConditional/ClassicalNSOpenTarget.lean` | The single OPEN Clay (B) target (one intentional `sorry`; excluded from scan and audits) |
| `FrohmanianTetherConditional/FrohmanianTripleArchitectureLifespan.lean` | Lifespan-corrected `NavierStokesUnifiedData` with non-vacuity models |
| `papers/vacuity-audit/` | Side note (LaTeX + PDF + draft Zenodo metadata) on these findings |
| `FrohmanianTetherConditional.lean` | Library root |
| `scripts/PrintAxioms.lean`, `scripts/PrintAxiomsBridge.lean`, `scripts/kernel_check.sh` | Axiom audits used by CI |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lake project and pins |
| `paper/Frohmanian_Tether_Unified.tex`, `.pdf` | Frohmanian Tether draft manuscript (10.5281/zenodo.24079623) |
| `paper/references.bib` | BibTeX references for the Unified paper |
| `paper/Three_Pillars_NS.tex`, `.pdf` | Three Pillars draft manuscript (10.5281/zenodo.24080310) |
| `paper/README.md` | Manuscript file list with MD5 checksums |
| `LICENSE` | Apache License 2.0 (code) |
| `LICENSE-paper` | CC BY 4.0 (paper) |
| `NOTICE` | Copyright and attribution notice |
| `CITATION.cff`, `.zenodo.json` | Citation and Zenodo metadata |

## References

- V. I. Arnold, *Sur la géométrie différentielle des groupes de Lie de
  dimension infinie et ses applications à l'hydrodynamique des fluides
  parfaits*, Ann. Inst. Fourier 16 (1966), 319–361.
- J. E. Marsden, A. Weinstein, *Coadjoint orbits, vortices, and Clebsch
  variables for incompressible fluids*, Physica D 7 (1983), 305–323.
- V. I. Arnold, B. A. Khesin, *Topological Methods in Hydrodynamics*,
  Springer, 1998.
- J. T. Beale, T. Kato, A. Majda, *Remarks on the breakdown of smooth solutions
  for the 3-D Euler equations*, Comm. Math. Phys. 94 (1984), 61–66.
- H. Kozono, Y. Taniuchi, *Limiting case of the Sobolev inequality in BMO, with
  application to the Euler equations*, Comm. Math. Phys. 214 (2000), 191–200.
- T. Kato, *Nonstationary flows of viscous and ideal fluids in ℝ³*, J. Funct.
  Anal. 9 (1972), 296–305.
- T. Kato, *Strong Lᵖ-solutions of the Navier–Stokes equation in ℝᵐ, with
  applications to weak solutions*, Math. Z. 187 (1984), 471–480.
- H. Fujita, T. Kato, *On the Navier–Stokes initial value problem I*, Arch.
  Rational Mech. Anal. 16 (1964), 269–315.

## License

- Code: Apache License 2.0 (`LICENSE`).
- Paper (`paper/`): Creative Commons Attribution 4.0 International
  (`LICENSE-paper`).

Copyright 2026 Benjamin Stanley Frohman.

## Citation

See `CITATION.cff`. Author: Frohman, Benjamin Stanley
(ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)),
Independent Researcher.
