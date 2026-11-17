# paper/

LaTeX sources and compiled PDFs for the Unified Tether, Three Pillars, and
vacuity-audit notes. The papers are licensed under CC BY 4.0 (see
`../LICENSE-paper`). Lean code in this repository is licensed under
Apache-2.0 (see `../LICENSE` and `../NOTICE`).

| File | Record |
|------|--------|
| `Frohmanian_Tether_Unified.tex` / `.pdf` | Unified Tether, concept DOI [10.5281/zenodo.24079622](https://doi.org/10.5281/zenodo.24079622) |
| `references.bib` | BibTeX for the Unified paper |
| `Three_Pillars_NS.tex` / `.pdf` | Three Pillars, concept DOI [10.5281/zenodo.24080309](https://doi.org/10.5281/zenodo.24080309) |
| `vacuity-audit/` | Vacuity audit, concept DOI [10.5281/zenodo.24102968](https://doi.org/10.5281/zenodo.24102968) |

The papers remain strictly conditional and make no claim to resolve the Clay
Millennium Problem.

Each paper records the certifying Git commit, the GitHub Actions run, the
`lake-manifest.json` SHA-256, the Lean toolchain, the Mathlib revision, and
the rebuild command `lake exe cache get && lake build && ./scripts/kernel_check.sh`.
The macros in `provenance-stamp.tex` hold the stable identifiers; the official
deposited PDF fills in the certifying commit and Actions run.

Build the Unified paper with `pdflatex`, `bibtex`, then `pdflatex` twice, from
this directory. Build Three Pillars with `pdflatex`. Build the vacuity note
from `vacuity-audit/` with `pdflatex`.
