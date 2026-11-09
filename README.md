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


## Open target

`FrohmanianTetherConditional/AnalyticBridgeTarget.lean` states Clay Millennium
Problem Statement (B) on T³ as an **open formalization target**. It contains
exactly one intentional `sorry`, marking the open problem. Nothing in that
file is claimed proved.

- It is **not** imported by the library root `FrohmanianTetherConditional.lean`,
  so `lake build` and the zero-`sorry` kernel/axiom CI check stay green.
- `scripts/kernel_check.sh` explicitly excludes this file from the forbidden-
  token scan for that reason.
- `solves_NS` and `maximal` are labelled PLACEHOLDER: Mathlib cannot yet state
  the PDE on the torus, so a proof of this exact statement would **not** yet
  constitute a proof of Clay (B).

## Build and check

```bash
# needs elan (https://github.com/leanprover/elan)
lake exe cache get        # download prebuilt Mathlib
lake build                # builds FrohmanianTetherConditional
./scripts/kernel_check.sh # forbidden-token scan + #print axioms audit
```

CI (`.github/workflows/lean.yml`) runs `lake build` and the kernel/axiom check
on every push and pull request.

## Contents

| Path | Description |
|------|-------------|
| `FrohmanianTetherConditional/FrohmanianTripleArchitecture.lean` | Lean 4 formalization (conditional, abstract PDE inputs) |
| `FrohmanianTetherConditional/AnalyticBridgeTarget.lean` | OPEN Clay (B) target (one intentional `sorry`; not imported; excluded from kernel check) |
| `FrohmanianTetherConditional.lean` | Library root |
| `scripts/PrintAxioms.lean`, `scripts/kernel_check.sh` | Axiom audit used by CI |
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
