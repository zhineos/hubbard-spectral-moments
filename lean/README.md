# Lean formalization

Machine-checked proofs of the exact combinatorial results of the paper, in Lean 4 with
Mathlib. The conventions are those of
[`docs/framework.md`](../docs/framework.md), section 4.

## Build and check

Requires [elan](https://github.com/leanprover/elan) (`brew install elan-init` on macOS),
which installs the Lean version pinned in `lean-toolchain` (v4.35.0). Mathlib is pinned
to release v4.35.0 (commit `56a0058`) in `lakefile.toml` and `lake-manifest.json`.

```sh
cd lean
lake exe cache get              # once: prebuilt Mathlib (about 7 GB), never rebuilt locally
lake build                      # must finish with no errors and no warnings
lake env lean AxiomAudit.lean   # axioms used by each headline theorem
```

The audit must print, for every theorem, exactly
`[propext, Classical.choice, Quot.sound]`: the standard axioms of Mathlib, with no
`sorryAx` and no trusted-compiler axiom.

### Comparator and the final run

`Challenge.lean` restates the 46 theorems of `HubbardMoments/Main.lean` with `sorry`, under
the same names; it imports only `HubbardMoments.Spec` (hence `Defs` and Mathlib), so that
import closure is the trusted statement. `comparator.json` names the challenge, the
solution `HubbardMoments.Main`, the 46 theorems and the permitted axioms. Then

```sh
lake comparator --paranoid      # each proof proves exactly the challenge statement
lake check                      # the whole default build replays through the kernel
```

`lake comparator --paranoid` runs Lean's kernel and the five external checkers bundled with
the toolchain (`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) on an
export of the 46 theorems and everything they depend on (about 20 000 declarations, under two
minutes). `lake check` exports the whole build, which imports all of Mathlib: about 6 GB,
written to `$TMPDIR`, and 36 minutes with Lean's kernel on a 16-core machine with 16 GB of
memory. Where `/tmp` is held in memory, point `TMPDIR` at a disk. Both build and export
inside a `bwrap` sandbox, which exists only on Linux. Exit code 0 means
accepted, 1 rejected, 2 could not start. `Challenge` and `NegativeControls` are separate
libraries outside the default target, so `lake build` and `lake check` never see their
`sorry`s and axioms.

The full run (clean build, audit, comparator, check, negative controls, numerical checks)
is `python checks/lean_linux_run.py --record` from the repository root, which writes
`evidence/<date>-lean-linux/`.

## Files

| file | contents |
|---|---|
| `HubbardMoments/Defs.lean` | every object the claims refer to: sectors, the torus, hops, configurations, projected hopping operators, the second moment |
| `HubbardMoments/Spec.lean` | the claims, as propositions; with `Defs`, all a reader needs to know what is proved |
| `HubbardMoments/Main.lean` | one headline theorem proving each proposition of `Spec` |
| `HubbardMoments/Combinatorics/Subsets.lean` | counting subsets with a prescribed trace |
| `HubbardMoments/Sectors.lean` | sector dimensions |
| `HubbardMoments/Torus.lean` | the torus is 4-regular for `L ≥ 3`, and has a triangle exactly when `L = 3` |
| `HubbardMoments/SecondMoment.lean` | the average hop count |
| `HubbardMoments/ProjectedHopping.lean` | the exact second-moment theorem for projected hopping operators |
| `HubbardMoments/Doublon.lean` | the doubled Peierls phase of the doublon |
| `HubbardMoments/SchriefferWolff.lean` | the Schrieffer–Wolff cross term, and the `3 × 3` example where it is nonzero |
| `HubbardMoments/FinitePopulation.lean` | moments of sampling without replacement; sums of independent variables |
| `HubbardMoments/TorusBand.lean` | the tight-binding band of the torus, the `U = 0` moments, the finite-population table |
| `HubbardMoments/ClosedWalks.lean` | permutations induced by closed walks of hard-core particles |
| `HubbardMoments/Fermions.lean` | fermion creation and annihilation operators; anticommutation relations; the sign rule |
| `HubbardMoments/Hubbard.lean` | the hopping term `H_t` and `H∞ = P₀H_tP₀` built from them |
| `HubbardMoments/Weighted.lean` | the second-moment theorem for arbitrary Hermitian amplitudes `t_ij` |
| `AxiomAudit.lean` | `#print axioms` for the headline theorems |
| `Challenge.lean` | the 46 statements with `sorry`: the reference for `lake comparator` |
| `comparator.json` | challenge, solution, theorem names and permitted axioms |
| `NegativeControls/` | four bad proofs and their configurations, which must be rejected |

## What is proved

| claim (paper) | Lean | does not cover |
|---|---|---|
| sector dimensions `C(N,a)·C(a,k)·C(N−a,b−k)` (§4, Fig. 3) | `sectorDimensions` | energies of the sectors |
| 10920 / 3360 / 120 (4 × 4, two up and two down); 6900 / 600 (5 × 5, two up and one down) | `sectorDimensionsQuoted` | — |
| average hop count `2|E|·n(N−n)/(N(N−1))` on any finite simple graph (§5.2) | `hopAverage` | — (the counting step; `μ₂` itself is `secondMomentTheorem` below) |
| `z`-regular form `n z (N−n)/(N−1)` | `hopAverageRegular` | — |
| torus form `4n(L²−n)/(L²−1)`, `L ≥ 3` | `hopAverageTorus` | `L ≤ 2` |
| `64/5` at `L = 4` and `14` at `L = 5`, `n = 4` (the sparse-trace `μ₂` values at `λ = 1`) | `hopAverageTorusValues` | — |
| `Tr H∞ = 0` (§5.2) | `projectedHoppingDiagonalZero` | — |
| `(H∞²)_cc = λ² M(c)` (§5.2) | `projectedHoppingSquareDiagonal` | — |
| **exact second-moment theorem** `μ₂ = λ²·2|E|·n(N−n)/(N(N−1))`, any finite simple graph, any spin composition (§5.2) | `secondMomentTheorem` | the construction of `H∞` from fermion operators (see below) |
| `z`-regular form `μ₂ = λ² n z (N−n)/(N−1)` | `secondMomentRegular` | as above |
| torus form `μ₂ = λ²·4n(L²−n)/(L²−1)`, `L ≥ 3` | `secondMomentTorus` | as above |
| the hypotheses can be met (hop matrix with all signs `+`) | `projectedHoppingExists` | — |
| two electrons of opposite spin with Peierls phases: the model is Hermitian | `pairHoppingHermitian` | — (a check of the definition) |
| no single hop connects two doublons (§8) | `doublonFirstOrderZero` | — |
| **doubled Peierls phase**: the doublon hops with `t_d e^{2iA}`, `t_d = 2t²/U`, on any finite simple graph (§8) | `doubledPeierlsPhase` | the second-order formula itself; several doublons |
| at second order the doublon hops only to nearest neighbours | `doublonHoppingRange` | — |
| its on-site shift `2zt²/U` does not depend on the phases; `8t²/U` on the torus | `doublonOnSiteShift`, `doublonOnSiteShiftTorus` | higher orders in `t/U` |
| the `L × L` torus has a triangle exactly when `L = 3` | `torusTriangleFree` | — |
| **Schrieffer–Wolff cross term** `Tr(T₀V) = 0` on every triangle-free graph (§7.2, App. D) | `schriefferWolffCrossTerm` | the expansion `H_eff = T₀ − V/U + O(1/U²)` itself (see below) |
| hence `μ₂(T₀ − V/U) = μ₂(T₀) + Var(V)/U²`: no `1/U` term; on the torus for `L ≥ 4` | `schriefferWolffSecondMoment`, `schriefferWolffSecondMomentTorus` | the size of `Var(V)` |
| the triangle-free hypothesis cannot be dropped: a Hermitian hopping operator on the `3 × 3` torus with a nonzero cross term | `crossTermNeedsTriangleFree` | the paper's `L = 3` value over a full sector (numerical) |
| sampling `k` of `N` values without replacement from a centred population: mean `0` | `sampleMean` | — |
| **finite-population correction** `Var = kσ₁²(N − k)/(N − 1)` (§5.3) | `finitePopulationVariance` | — |
| **finite-population fourth moment** `μ₄ = P₄(p₁ − 7p₂ + 12p₃ − 6p₄) + 3P₂²(p₂ − 2p₃ + p₄)`, every `k ≤ N` (App. B) | `finitePopulationFourthMoment` | — |
| independent sums: `E[(X+Y)²] = E[X²] + E[Y²]`; `μ₄(X+Y) = μ₄(X) + μ₄(Y) + 6 Var X Var Y` (App. B) | `independentSumSecondMoment`, `independentSumFourthMoment` | — |
| the torus band `−2t(cos q₁ + cos q₂)`: `∑ε = 0`, `∑ε² = 4t²L²`, so `σ₁² = zt²` | `torusBandMoments` | that it is the spectrum of the torus hopping matrix (plane waves) |
| `U = 0`, one spin species: `μ₂ = t²·4n(L² − n)/(L² − 1)` (§5.3) | `freeFermionSecondMomentTorus` | that free-fermion energies are sums of distinct band energies (Slater determinants) |
| for one species the `U = 0` and `U = ∞` values of `μ₂` coincide | `freeAndProjectedSecondMomentsAgree` | as above |
| the finite-population table at `L = 4`: `112/15, 2176/15; 52/5, 9976/35; 64/5, 197632/455` | `finitePopulationTable` | as above |
| a closed walk of `h` hard-core hops, on any graph, moves no particle or fewer than `h` | `closedWalkFewMoved` | — |
| **four-hop closed walks** induce only the identity, a transposition or a 3-cycle: no 4-cycle, no double transposition (§6, App. C) | `fourHopPermutations` | fermion signs and spin conditions; the form `μ₄ = A + α P_same` |
| both occur on every torus, `L ≥ 3`: ring exchange, and the plaquette 3-cycle | `fourHopExchangesOccur` | — |
| `P₃ = C(N↑,3) + C(N↓,3) = C(n,3) − (n−2)/2·(C(n,2) − P_same)`, affine in `P_same` (§6) | `threeCycleCountAffine` | — |
| fermion operators on any finite set of orbitals, any ordering: `(c_o)† = c†_o`, `{c,c} = {c†,c†} = 0`, `{c_o, c†_o'} = δ` | `canonicalAnticommutation` | — |
| one hop: `c†_{o'}c_o\|S⟩ = (−1)^{m+p}\|S∖{o}∪{o'}⟩`, the sorted-tuple rule (App. E) | `sortedTupleSignRule` | — |
| the hopping term `H_t = −t Σ e^{iA} c†_{y s} c_{x s}` is Hermitian and connects only states one hop apart | `hubbardHoppingHermitian`, `hubbardHoppingIsHoppingOperator` | — |
| **`H∞ = P₀H_tP₀` built from fermion operators has the properties of `IsProjectedHopping`**, any signs, any phases | `projectedHubbardIsProjectedHopping` | — |
| hence the exact second-moment theorem for `H∞` itself; square-lattice form | `secondMomentHubbard`, `secondMomentHubbardTorus` | — |
| hence no `1/U` term for `H_t` itself on triangle-free graphs | `schriefferWolffHubbard` | the expansion `H_eff = T₀ − V/U + O(1/U²)` |
| **weighted form** `μ₂ = n(N−n)/(N(N−1)) Σ_{i≠j} \|t_ij\|²` for `H∞` with any Hermitian amplitudes `t_ji = t_ij*` (abstract, §5.2) | `secondMomentWeightedTheorem`, `secondMomentHubbardWeighted` | — |

The second-moment theorems hold for every operator with the three properties of
`IsProjectedHopping` (Hermitian; nonzero matrix elements only for one hop to an empty
neighbouring site; modulus `λ`). `H∞ = P₀H_tP₀`, built in Lean from fermion operators that
satisfy the canonical anticommutation relations, has these properties for any Peierls
phases and any ordering of the orbitals (`projectedHubbardIsProjectedHopping`). The
theorem is therefore proved for the Hubbard model's own `H∞` (`secondMomentHubbard`).

The cross-term theorems hold for every operator with the property of `IsHoppingOperator`
(matrix elements only between Fock states one hop apart), and the hopping term built from
fermion operators has it (`hubbardHoppingIsHoppingOperator`). The second-order formula of
degenerate perturbation theory (Schrieffer–Wolff) is not proved here. The doublon theorems
compute its terms, and the cross-term theorems concern the operators `T₀ = P₀HP₀` and
`V = T₁†T₁` that it produces.

## Negative controls

Automated, in `NegativeControls/`: each module offers a bad proof of the headline theorem
`secondMomentTheorem`, and `lake comparator --config=NegativeControls/<name>.json` must
reject it (exit code 1) with the error shown:

| control | what it does | expected error |
|---|---|---|
| `weakened` | proves `SecondMomentTheorem ∨ True` | statement do not match |
| `added-axiom` | proves the exact statement from a new axiom | illegal axiom `secondMomentCheat` |
| `changed-definition` | redefines `Spec.SecondMomentTheorem` as `True` | const does not match |
| `sorry` | leaves the proof as `sorry` | illegal axiom `sorryAx` |

Run by hand on 12 November 2026:

* a wrong sector dimension (10921 instead of 10920) is rejected by the build;
* a statement proved with `sorry` shows `sorryAx` in its axiom list. This was checked for a
  sector dimension and for `SchriefferWolffCrossTerm`;
* the single-phase formula `2t²/U · e^{iA}` for the doublon is false. On two sites with
  `A = π/2`, `doubledPeierlsPhase` gives `−2` and the single-phase formula gives `2i`; Lean
  derives the contradiction.

* without the signs `(−1)^m`, the annihilation operators of two orbitals do not
  anticommute: `{c₀, c₁}` has the entry `2` from `{0, 1}` to `∅`;
* the fourth-moment formula with the multiplicity `−7p₂` replaced by `−6p₂` is false: on
  the `L = 4` band with `k = 4` it contradicts `finitePopulationFourthMoment` (it differs by
  `P₄ p₂ = 32`).

`crossTermNeedsTriangleFree` is a negative control kept in the project. Without the
triangle-free hypothesis, the conclusion of `schriefferWolffCrossTerm` can fail.
