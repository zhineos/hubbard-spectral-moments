# Golden-value checks

```sh
python checks/run_checks.py     # from the repository root; about 2 minutes; exit status 0 if all pass
```

Each check compares a number printed in the paper with an independent computation, and
where a proven closed form exists (`lean/`), with that formula too. All values are exact
rationals: at `λ = 1` every matrix element is `0` or `±1`, so traces are integers.

| paper label | what is checked | computed by | closed form |
|---|---|---|---|
| `sec:fewbody` | sector dimensions 10920/3360/120 (L = 4) and 6900/600 (L = 5) | enumeration | `sectorDimensionsQuoted` |
| `tab:mu2verify` | `μ₂(∞)` for (L, n) = (3,2), (4,3), (4,4), (5,4), (6,4) | `uinf_traces_sparse.py` | `secondMomentTorus` |
| `tab:mu4exact` | `μ₂(∞)`, `μ₄(∞)` at L = 4 for all seven compositions; the two n = 4 slopes in `P_same` agree | `uinf_traces_sparse.py` | `secondMomentTorus` (`μ₂` only) |
| `tab:fpcexact` | `U = 0` `μ₂`, `μ₄` for k = 2, 3, 4 at L = 4 | enumeration of the band | `finitePopulationVariance`, `finitePopulationFourthMoment` |
| `sec:fermistats` | one species: `μ₄(U = 0) = μ₄(U = ∞)` | both of the above | — |
| `sec:mu4exchange` | `α(N, 2) = −64/(N − 1)` at L = 5, 6, 7 and `−32/5` at L = 4 | `uinf_traces_sparse.py` | — (tier N) |
| `sec:SW` | `Tr(T₀V) = 0` at L = 4, 5, 6; nonzero at L = 3, where the `1/U` coefficient from full exact diagonalization matches `−2Tr(T₀V)/D₀` | `sw_correction.py`, dense ED | `schriefferWolffCrossTerm`, `torusTriangleFree` |
| `sec:mu2theorem` | `μ₂` on an open chain, a star and an irregular graph, seven compositions | explicit `H∞` (`checks/hinf_local.py`) | `secondMomentTheorem` |
| `sec:mu4exchange` | `α(N, 2)` by channel: `−8` per pair at L = 5–7; at L = 4, 48 diagonal-type pairs and edge channel `−12` | `checks/hinf_local.py` | — |
| `app:mu4fpc` | the `μ₄` formula against brute force on a random centred population | enumeration | `finitePopulationFourthMoment` |
| `app:numerics` | the sorted-tuple sign rule against an independent Jordan–Wigner implementation (4000 moves); `H∞` symmetric | — | `sortedTupleSignRule` |
| `app:mu4walks` | `α(27, 2) = −96/13` with both channels at `−1296`; the local values 208/200 and 180/186/182 at L = 5, 6; `α(N,2)` on 5×5×5, 4×4×4, 3×4, 4×5 (the side-of-4 formula); kagome `α = 0` at N = 27, 48 | `checks/hinf_local.py` | — |
| `tab:swamp` | `Var(V)` and the U⁻² coefficient `c2` at L = 4 (exact rationals); `c2` against full ED at L = 4 (1,1), (2,1) and L = 5 (1,1); `c2(1,1) = −96/(N−1) − 64/(N−1)²` at L = 5–8; `c2 > 0` near half filling (L = 4, n = 14); `c2 < 0` at L = 4, n = 6 | `sw_correction.py`, dense ED | — (tier N) |
| `sec:SW#beta-trend` | composition dependence of `c2/(N↑N↓)`, relative spread \|x − y\|/mean: 0.14, 0.06, 0.03 % at L = 4, 5, 6 (n = 4), 0.34 % at L = 4 (n = 5), 0.79 % at L = 4 (n = 6) | `sw_correction.py` | — (tier E) |
| `eq:alphaN` | the closed form `α(N,n) = −8C₄(N−n)(8N−11n−2)/[N(N−1)(N−2)(N−3)]` against exact slopes: square tori L = 3–7, the 4×4 torus (C₄ = 24), K₆, Petersen, the 3×3 triangular torus, a random graph; the transposition part alone misses by 1.8 % and 3.9 % at L = 5 | `uinf_traces_sparse.py`, `checks/hinf_local.py` | — (tier A + N) |
| `sec:fewbody#shape` | the N_d = 0 band of (1,1) at L = 5: `μ₂ = 23/3`, `μ₄ = 461/3`, excess kurtosis `−204/529` | `uinf_traces_sparse.py` | — (tier N) |
| `sec:discussion#bond-linearity` | with complex bond-dependent amplitudes on a random 8-site graph (n = 4), `μ₄` is affine in `P_same` and its slope differs from the uniform one | independent Jordan–Wigner construction | — (tier A) |
| `sec:futurework` | `α(N,2,Φ)` at every quantized flux (L = 3, 5, 6; every third at L = 7) and its orbital piece; the twist: U-band π-periodicity deviations and their scaling (L = 4, 5, 6), agreement with the doubled-twist doublon model; the L = 3 third-order band-centre shift | `mu4_flux_validation.py`, dense ED | — |

Slow runs, each writing a dated record under `evidence/`:

| script | claims | record |
|---|---|---|
| `checks/slow_n6_linearity.py` | `tab:n6test` (exact rationals, exact line) | `evidence/2026-11-12-n6-linearity` (dirty tree), `evidence/2026-11-13-n6-linearity` |
| `checks/slow_finite_U.py` | `sec:benchmark#closure`, `sec:fewbody#centres`, `sec:n4test#threebands`, the doublon-flux residual ratios (U = 10, 20, 40, 80 from 2026-11-13) | `evidence/2026-11-12-finite-U` (dirty tree), `evidence/2026-11-13-finite-U` |
| `checks/slow_bound_states.py` | `sec:n3test#unbound` (momentum-resolved bound-state search, exact and first order) | `evidence/2026-11-12-n3-bound-states` |
| `checks/slow_alpha_c2.py` | `eq:alphaN#numeric` (L = 6, n = 4, 5), `sec:SW#beta-trend` and `sec:SW#c2-sign` (c2 for n = 5 at L = 5, 6) | `evidence/2026-11-13-alpha-c2` (L = 5), `evidence/2026-11-14-alpha-c2` |

Fig. 3 (`fig_sectors.py`, full spectra) has its own record, `evidence/2026-11-14-fig-sectors`.

Not yet covered: the density-of-states figures (tier E, visual statements).

