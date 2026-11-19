# Changelog

Reader-facing record of releases and corrections. Changes to frozen claims are also logged,
with their reasons, in `docs/drift-log.tsv`.

## 1.1.0 (2026-11-19)

Accompanies arXiv:2611.19929v2. The fourth moment at U = ∞ is now complete and machine-checked:
the intercept A(N, n), left open in v1, is derived in closed form on every finite simple graph,
μ₄ = A + α P_same is proved in Lean, and the fourth moment is derived in closed form for arbitrary
Peierls phases.

- **The intercept.**
  - `app:mu4walks#hcb-lemma`: the canonical fourth moment of hard-core bosons,
    (2m + 4W + 8C₄) p₁₁ + (24D + 16C₄) p₂₂.
  - `eq:AfromHCB`: A = μ₄^HCB − T₂ − (3/2)T₃.
  - `eq:Aclosed`: A(N, n) = (2m + 4W + 8C₄) p₁₁ + (24D − 16C₄) p₂₂ − 12C₄ p₃₁.
  - The Proposition (`sec:mu4exchange#proposition`) gives μ₄ in closed form for every n ≤ N; v1
    stated n ≥ 2.
  - Its grand-canonical limit reproduces the f.c.c. XY series of Rogiers and Dekeyser (1973)
    (`sec:mu4exchange#xy-limit`).
- **Lean:** 51 theorems, up from 46.
  - New: `TorusGraphCounts`, `HardCoreBosonFourthMoment`, `FourthMomentHubbardTorus`,
    `FourthMomentTableL4`, and `FourthMomentHubbard`: μ₄ = A + α P_same for H∞ built from fermion
    operators, on any finite simple graph, N ≥ 4, any n ≤ N, no Peierls phases, two spin species.
  - Proofs in `lean/HubbardMoments/FourthMoment/`.
  - Linux run record `evidence/2026-11-18-lean-linux`: all ten steps pass.
  - `checks/make_challenge.py` regenerates `lean/Challenge.lean`.
- **Peierls phases** (`eq:mu4flux`): μ₄(Θ) = (2m + 4W) p₁₁ + 24D p₂₂ + B(N, n, P_same) Σ_C cos Θ_C,
  summed over the 4-cycles.
  - Its flux-independent baseline, left open in v1, is the same for every spin composition.
  - On L × L tori with L = 3 or L ≥ 5, the exchange slope is α(N, n) cos Φ at every n.
  - At L = 4, the cos 4Φ and cos 8Φ terms and the twist dependence come from the holonomies of the
    winding 4-cycles.
  - Derived and checked (`checks/hinf_flux.py`), not machine-checked.
- **§8, doublons:**
  - the second-order terms with several doublons are stated precisely;
  - loops beyond second order, with charge-e Wilson phases at order λ^ℓ/U^(ℓ−1), are distinguished
    from the doublon's gauge charge, which is 2e at every order.
- **Claims:**
  - review round 4 (2026-11-18: mathematics, Lean statement fidelity, literature, prose truth) found
    no mathematical error;
  - 11 new principal claims frozen, 38 in all;
  - one drift entry, for `sec:discussion#nonclaims`;
  - `checks/make_statement.py` regenerates `STATEMENT.md`.
- **Code and checks:**
  - new files: `mu4_closed_form.py`, `fig_mu4_kurtosis.py` (the new Fig. 6), `checks/hinf_flux.py`,
    `checks/slow_mu4_intercept.py`;
  - `checks/run_checks.py` now has 215 checks;
  - the clean reruns `evidence/2026-11-18-mu4-intercept` and `evidence/2026-11-18-n3-bound-states`
    replace records that had run from uncommitted trees.
- **Paper (arXiv v2):**
  - a new figure, Fig. 6, so every later figure's number increases by one: the moment hierarchy,
    Fig. 6 in v1, is Fig. 7;
  - the proofs, in App. C;
  - 19 new references;
  - the abstract, shortened to about 300 words;
  - 41 pages;
  - the running text no longer names the authors of Ref. [3].

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
