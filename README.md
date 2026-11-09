# Frohmanian Tether: Conditional Continuation and Small-Data Regularity for 3D Navier–Stokes on T³

Companion repository for the preprint *Conditional Continuation and Small-Data
Regularity for 3D Navier–Stokes on T³, with the Frohmanian Symplectic Tether as
a Metric (Non-Poisson) Correction* by Benjamin Stanley Frohman.

> **Status:** draft. The manuscript is in preparation. The `paper/` directory
> is a placeholder until the LaTeX source and PDF are synced from the Zenodo
> draft. No DOI has been issued yet.

## Scope (read this first)

This is a **conditional, expository** work. It does **not** solve the Clay
Millennium Problem on Navier–Stokes existence and smoothness.

### Classical results (cited, not new)

- **Theorem A: continuation criterion.** Beale–Kato–Majda, with the
  Kozono–Taniuchi refinement: a smooth solution on T³ continues past T* if
  ∫₀^{T*} ‖ω(t)‖_{B⁰_{∞,∞}} dt < ∞.
- **Theorem B: Kato local existence.** For u₀ ∈ Hˢ(T³), s > 5/2, a unique
  solution exists on [0, T_loc] with T_loc ≥ 1/(C_s ‖u₀‖_{Hˢ}).
- **Theorem C: Fujita–Kato small-data global existence.** Mean-zero data with
  ‖u₀‖_{Ḣ^{1/2}} ≤ ε₀ ν give a global smooth solution.

These are known theorems. They are presented with citations, not as
contributions of this work and not as consequences of the tether.

### The Frohmanian Symplectic Tether

- The tether term B(F,G) is **symmetric** in F and G. It is therefore a
  **metric-type (metriplectic) term, not a Poisson-bracket correction**, and
  this repository makes **no Jacobi identity claim**.
- In the **velocity-slot form**, where the projection Π_u is applied to
  ∇×δF/δω, one has **B(F,H) = 0** for the kinetic-energy Hamiltonian H, since
  ∇×δH/δω = u.

### What remains open

- **Large-data global regularity for 3D Navier–Stokes is OPEN.** Nothing here
  proves it, and the repository makes no Clay/Millennium proof claim.

## Contents

| Path | Description |
|------|-------------|
| `paper/` | LaTeX source and PDF (placeholder until synced from the Zenodo draft) |
| `LICENSE` | Apache License 2.0 (code) |
| `LICENSE-paper` | CC BY 4.0 (paper) |
| `NOTICE` | Copyright and attribution notice |
| `CITATION.cff` | Citation metadata |
| `.zenodo.json` | Zenodo metadata |

There is no Lean formalization in this repository.

## References

- J. T. Beale, T. Kato, A. Majda, *Remarks on the breakdown of smooth solutions
  for the 3-D Euler equations*, Comm. Math. Phys. 94 (1984), 61–66.
- H. Kozono, Y. Taniuchi, *Limiting case of the Sobolev inequality in BMO, with
  application to the Euler equations*, Comm. Math. Phys. 214 (2000), 191–200.
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
(ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)).
