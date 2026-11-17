# Changelog

Reader-facing record of releases and corrections. Changes to frozen claims are also logged,
with their reasons, in `docs/drift-log.tsv`.

## 1.0.1 (2026-11-17)

The paper is on arXiv: [arXiv:2611.19929](https://arxiv.org/abs/2611.19929), with the
Supplemental Material as its ancillary file. Nothing changes in the code, the Lean
formalization, the checks, the run records or the claims.

- `CITATION.cff` and the README cite the paper and the repository's Zenodo DOI for all
  versions, 10.5281/zenodo.24244236 (v1.0.0 is 10.5281/zenodo.24244237); the README has a
  BibTeX entry for each.
- README: a figure of the moment hierarchy (the paper's Fig. 6 redrawn, with a version for
  dark themes; source in `docs/figures/hierarchy.tex`).
- `docs/method.md`: the commits named in the run records belong to the development history
  before the release, which is not public; a table says, for each record, how the code it ran
  compares with the released code.

## 1.0.0 (2026-11-15)

First public version, to accompany the preprint.

- The code, the Lean 4 formalization, the golden-value checks and the run records that
  accompany the paper; the paper and its Supplemental Material (notes S1–S12) are on arXiv.
- The 27 principal claims were frozen on 2026-11-13. Three were changed on 2026-11-14 with the author's
  approval: `sec:discussion#open-beta` (the bound on $c_2$ gives $|\beta|$ at most of order
  $1/N$, not a rate), `sec:benchmark#nonclaim-doublonform` (the citations: an extended,
  mass-imbalanced model and a periodically driven one; machine-checked for the two-electron
  problem) and `sec:SW#beta-trend` (the relative spread defined, and the pair named for the
  $n=6$ value).
