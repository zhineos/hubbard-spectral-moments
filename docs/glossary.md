# Glossary

Names in the code and the formalization, and the paper symbols they stand for.

## Symbols

| paper | Python | Lean | meaning |
|---|---|---|---|
| $\lambda$ | `lam`, `LAM` | `t` | nearest-neighbour hopping amplitude (energy unit) |
| $U$ | `U` | `U` | on-site repulsion |
| $L$, $N=L^2$ | `L`, `N` | `L`, `Fintype.card` | torus side, number of sites |
| $N_\uparrow, N_\downarrow$, $n$ | `nup`, `ndn` (`Nup`, `Ndown`), `n` | `a`, `b` | numbers of up and down electrons, their sum |
| $N_d$, $\hat N_d$ | `Nd`, `indicator`, `n_d_expectation` | `k` in `sector` | number of doubly occupied sites |
| $D_0$ | `D0`, `D` | card of `sector` | dimension of the $N_d=0$ sector of one composition |
| $H_t$ | `H` (with `U = 0`), `build_H_*` | `hubbardHopping` | hopping term |
| $H_\infty=P_0H_tP_0=T_0$ | `build_Uinf_H_sparse`, `apply_H`, `T0` | `projectedHubbard`, `IsProjectedHopping` | projected hopping operator at $U\to\infty$ |
| $T_1$, $V=T_1^\dagger T_1$, $T_0^Q$, $H^{(3)}$ | `T1`, `V`, `T0Q`, `tr_T0H3` (`sw_correction.py`) | `virtualOp` ($V$) | Schrieffer–Wolff operators |
| $\mu_2$, $\mu_4$ | `mu2`, `mu4`, `tr2`/`tr4`, `uinf_moments`, `h2_diag`/`h4_diag` | `secondMoment`, `fourthMoment` | spectral moments (trace / dimension) |
| $c_2$ | `c2`, `sw_c2` | — | $U^{-2}$ coefficient of $\mu_{2,c}(U)$ |
| $P_{\rm same}$, $P_3$ | `p_same`, `ps` | written out in `Spec.lean` | same-spin pair and triple counts |
| $\alpha(N,n)$ | `alpha_formula`, `alpha` (`mu4_closed_form.py`), slopes | `exchangeSlope` | exchange coefficient |
| $C_4$ | `four_cycles`, `four_cycle_list` | `fourCycleCount` | number of 4-cycles of the graph |
| $m$, $W$, $D$ | `invariants` (`mu4_closed_form.py`) | `G.edgeFinset.card`, `wedgeCount`, `disjointEdgePairs` | edges, pairs of edges sharing a vertex, pairs of disjoint edges |
| $p_{ab}$ | `p` (`mu4_closed_form.py`) | `occProb` | canonical probability of $a$ given occupied and $b$ given empty sites |
| $\mu_4^{\rm HCB}$ | `mu4_hcb`, `hcb_mu4_exact` | `hardCoreHopping`, `fourthMoment` | fourth moment of $n$ hard-core bosons (the $n$-token graph) |
| $A(N,n)$ | `intercept`, `mu4_fermion` | `fourthMomentIntercept` | spin-independent part of $\mu_4(\infty)$ |
| $\Theta_C$, $B(N,n,P_{\rm same})$ | `wilson_cos_sum` (`checks/hinf_flux.py`), `flux_coefficient`, `mu4_fermion_flux` | — | Wilson phase of a 4-cycle, and the coefficient of $\sum_C\cos\Theta_C$ in $\mu_4$ under Peierls phases (not formalized) |
| $\varepsilon_d$, $t_d$ | `center`/`eps_d`, `lam_eff`/`t_d` (`pair_theory`) | `doublonSecondOrder` (the second-order terms) | doublon energy and hopping |
| $\Phi_\square$, $A_{ij}$ | `alpha` (flux quantum number), `link_phase`, `plaquette_flux` | phases of `pairHopping`, `hubbardHopping` | plaquette flux, Peierls phase |
| $\theta$ | `theta`, `twisted_adjacency` | — | boundary twist |
| $\sigma_1^2$, $P_2$, $P_4$, $p_m$ | `fpc_formulas`, `sample_moments` | `sampleMoment`, `inclusionProb`, `torusBand` | finite-population quantities |

The Lean names are definitions in `lean/HubbardMoments/Defs.lean`; the claims built from them
are in `Spec.lean`.

## Results and their formal names

The paper's Appendix F lists every machine-checked statement with its Lean theorems, and
[`lean/README.md`](../lean/README.md) ("What is proved") maps each to the paper section and
says what it does not cover. The register column `lean` gives the same names per claim.

## Register labels

Rows of `correspondence.tsv` are labelled by the paper's LaTeX label (`sec:mu4exchange`,
`eq:alphaN`, `tab:swamp`, ...), with `#name` for the individual claims of a section
(`sec:SW#c2-sign`). `checks/run_checks.py` prints the same labels next to each check, and the
Supplemental notes S1–S12 are the files `analytic_studies/01_*.tex` to `12_*.tex` (S12 is generated
from the Lean sources by `analytic_studies/make_s12.py` and built with LuaLaTeX).

| file | note |
|---|---|
| `01_configuration_space_and_dos.tex` | S1 |
| `02_doublon_effective_hamiltonian.tex` | S2 |
| `03_mu2_exact_theorem.tex` | S3 |
| `04_finite_population_corrections.tex` | S4 |
| `05_mu4_exchange_topology.tex` | S5 |
| `06_lattice_specificity_and_finite_size.tex` | S6 |
| `07_schrieffer_wolff.tex` | S7 |
| `08_fermion_sign_rule.tex` | S8 |
| `09_gauge_flux_extension_sketch.tex` | S9 |
| `10_flux_resolved_mu4_decomposition.tex` | S10 |
| `11_gauge_covariant_doublon_hamiltonian.tex` | S11 |
| `12_lean_formalization.tex` | S12 |
