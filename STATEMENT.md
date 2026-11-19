# Statement

The precise claims of *Spectral Moments of the Projected Hubbard Configuration Graph*: the
38 principal claims, frozen in two steps (27 on 2026-11-13 and 11 on 2026-11-18), and
changed since only through
[`docs/drift-log.tsv`](docs/drift-log.tsv), with the conventions they use, the non-claims, and
the evidence tier of each. Every other numbered result of the paper, with its evidence, is a
row of [`docs/correspondence.tsv`](docs/correspondence.tsv).
[`docs/method.md`](docs/method.md) explains how the evidence was produced and what each check
does and does not establish.

This file is generated from the register; the claims below are its frozen rows, verbatim.

## Conventions

- **Model.** The Hubbard model on a finite simple graph $G$ with $N$ sites (the $L\times L$
  torus, $N=L^2$, unless stated):
  $H=H_t+U\hat N_d$, $H_t=-\lambda\sum_{\langle ij\rangle,\sigma}(c^\dagger_{i\sigma}c_{j\sigma}+\mathrm{h.c.})$,
  $\hat N_d=\sum_i n_{i\uparrow}n_{i\downarrow}$ the number of doubly occupied sites. Energies
  are in units of the hopping $\lambda$ (written $t$ in the Lean formalization).
- **Sectors.** A composition is a fixed $(N_\uparrow,N_\downarrow)$, $n=N_\uparrow+N_\downarrow$.
  $P_0$ projects onto states with no doubly occupied site (the $N_d=0$ sector, dimension $D_0$);
  $H_\infty=P_0H_tP_0$ (also $T_0$).
- **Moments.** $\mu_\ell=\mathrm{Tr}(H^\ell)/D$ over the sector; $\mu_{2,c}$ is the central
  second moment. $P_{\rm same}=\binom{N_\uparrow}{2}+\binom{N_\downarrow}{2}$ is the same-spin
  pair count, $P_3=\binom{N_\uparrow}{3}+\binom{N_\downarrow}{3}$, and
  $\mu_4(\infty)=A(N,n)+\alpha(N,n)P_{\rm same}$ defines the exchange coefficient $\alpha$.
  $C_4$ is the number of 4-cycles of the graph (cycle subgraphs of length four, chords allowed);
  $m$ is the number of edges, $W=\sum_v\binom{d_v}{2}$ the number of pairs of edges sharing a
  vertex, $D=\binom m2-W$ the number of pairs of disjoint edges, and
  $p_{ab}=(n)_a(N-n)_b/(N)_{a+b}$.
- **Doublon.** $\varepsilon_d=U+8\lambda^2/U$ and $t_d=2\lambda^2/U$ on the square lattice; the
  doublon band is $\varepsilon_d+2t_d(\cos K_x+\cos K_y)$.
- **Finite U.** $V=T_1^\dagger T_1$ with $T_1=Q_1H_tP_0$; $c_2$ is the $U^{-2}$ coefficient of
  $\mu_{2,c}(U)$.
- **Flux.** Peierls phases $t_{ij}\to t_{ij}e^{iA_{ij}}$, plaquette flux
  $\Phi_\square=\sum_\square A_{ij}$; $\Theta_C=\sum_{(ij)\in C}A_{ij}$ is the Wilson phase of a
  4-cycle $C$.

## Evidence tiers

| tier | meaning |
|---|---|
| L | machine-checked in Lean 4 with Mathlib (`lean/`) |
| A | analytic proof, written out in the Supplemental Material and reviewed |
| N | exact numerical result (exact rationals or a stated tolerance), recomputed by `checks/` |
| E | numerical evidence for a trend; not a proof |
| C | taken from the literature, with the exact citation |

The relation column says how the statement relates to its evidence: DIRECT (the evidence
proves or computes the statement itself), COMPOSITION (it follows from several pieces of
evidence), CITED, or NONE (a non-claim).

## §2 The two-particle benchmark

**`sec:benchmark#doublonH`** (formula; tier A, DIRECT)

At fixed total momentum and every U, the two-electron relative-coordinate equation is exactly the Koster-Slater bound state at a repulsive defect; to leading order in $\lambda/U$ the pair is a composite boson hopping on the same LxL lattice with $E_{\rm pair}(K)\approx\varepsilon_d+2t_d(\cos K_x+\cos K_y)$, $\varepsilon_d=U+8\lambda^2/U$, $t_d=2\lambda^2/U$.

## §5 The second moment at U → ∞

**`sec:mu2theorem#theorem`** (theorem; tier L, DIRECT; Lean: `secondMomentTheorem`, `secondMomentHubbard`, `hopAverage`, `hopAverageRegular`, `hopAverageTorus`, `hopAverageTorusValues`, `projectedHoppingDiagonalZero`, `projectedHoppingSquareDiagonal`, `projectedHoppingExists`)

For every finite simple graph G=(V,E) with |V|=N>=2, hopping amplitude lambda, and 0<=n<=N, the U->infinity projected hopping operator $H_\infty=P_0H_tP_0$ in any spin-composition sector with N_up+N_down=n satisfies $\mu_2=\lambda^2\cdot2|E|\cdot n(N-n)/[N(N-1)]$, independent of spin composition.

**`sec:mu2theorem#weighted`** (theorem; tier L, DIRECT; Lean: `secondMomentWeightedTheorem`, `secondMomentHubbardWeighted`)

For every spin-independent Hermitian weighted hopping matrix $H_t=-\sum_{i\ne j,\sigma}t_{ij}c^\dagger_{i\sigma}c_{j\sigma}$ ($t_{ji}=t_{ij}^*$, no on-site terms) on N>=2 sites and every n<=N, $\mu_2(U\to\infty)=\frac{n(N-n)}{N(N-1)}\sum_{i\ne j}|t_{ij}|^2$, independent of spin composition: the squared Frobenius norm of the off-diagonal part of the one-body hopping matrix T=(t_ij) times the combinatorial blocking probability.

**`sec:mu2theorem#fermionic`** (theorem; tier L, DIRECT; Lean: `secondMomentHubbard`, `secondMomentHubbardTorus`, `canonicalAnticommutation`, `hubbardHoppingHermitian`, `projectedHubbardIsProjectedHopping`, `secondMomentHubbardWeighted`)

The second-moment theorem and its weighted form hold for $H_\infty=P_0H_tP_0$ built from fermion operators satisfying the canonical anticommutation relations, for any spin-independent Hermitian hopping amplitudes (in particular any Peierls phases) and any ordering of the orbitals (which fixes the fermionic signs).

**`sec:fermistats#fpcvariance`** (formula; tier L, DIRECT; Lean: `finitePopulationVariance`, `sampleMean`)

For every N>=2 and k<=N, the sum of k values drawn without replacement from a population of N values with mean 0 and variance $\sigma_1^2$ (population variance, 1/N convention) has variance $k\sigma_1^2(N-k)/(N-1)$ (the classical finite-population-correction identity).

**`app:mu4fpc#formula`** (formula; tier L, DIRECT; Lean: `finitePopulationFourthMoment`)

For every k<=N, the fourth moment of the sum of k values sampled without replacement from a zero-mean population $\{\varepsilon_1,\dots,\varepsilon_N\}$ ($\sum_i\varepsilon_i=0$) is $\mu_4=P_4(p_1-7p_2+12p_3-6p_4)+3P_2^2(p_2-2p_3+p_4)$, with $P_m=\sum_i\varepsilon_i^m$, $p_m=k(k-1)\cdots(k-m+1)/[N(N-1)\cdots(N-m+1)]$ and $p_m=0$ for m>k.

## §6 Exchange in the fourth moment

**`sec:mu4exchange#channels`** (proposition; tier A, DIRECT)

On the LxL torus with L=3 or L>=5, ring exchange proceeds through exactly two geometrically distinct channels of equal weight, diagonal (next-nearest-neighbour pairs sharing two common neighbours, 2+2 hops) and edge (nearest-neighbour pairs, 3+1 hops around an adjacent plaquette); at n=2 each eligible pair contributes $-8\lambda^4$, derived by a complete fermion-sign count of every contributing path; 2N pairs in each channel.

**`sec:mu4exchange#fourhop`** (theorem; tier L, DIRECT; Lean: `closedWalkFewMoved`, `fourHopPermutations`, `fourHopExchangesOccur`)

On any graph without self-loops, a closed walk of four hard-core hops induces on the particles only the identity, a transposition or a 3-cycle (a 4-cycle or double transposition would need a 1+1+1+1 hop schedule with no legal first move); more generally a closed walk of h hops moves no particle or fewer than h; a transposition and a 3-cycle both occur in four hops on every LxL torus with L>=3.

**`sec:mu4exchange#P3affine`** (formula; tier L, DIRECT; Lean: `threeCycleCountAffine`)

For every n, $P_3=\binom{N_\uparrow}{3}+\binom{N_\downarrow}{3}$ is an exact affine function of $P_{\rm same}$ at fixed $n=N_\uparrow+N_\downarrow$: $P_3=\binom{n}{3}-\frac{n-2}{2}\big[\binom{n}{2}-P_{\rm same}\big]$.

**`sec:mu4exchange#linearity`** (theorem; tier A, COMPOSITION; Lean: `fourHopPermutations`, `threeCycleCountAffine`)

On any finite graph, for every particle number n with two spin species, $\mu_4(U\to\infty)$ is exactly affine in the same-spin pair count at fixed (N,n), $\mu_4=A(N,n)+\alpha(N,n)P_{\rm same}$ (units of $\lambda^4$), with $\alpha=-T_2/\binom n2+(n-2)T_3/(2\binom n3)$ in terms of the average numbers of transposition and 3-cycle walks: proved from first principles (four-hop permutation bound, spin-averaging over labellings, and the $P_3$ identity), not an empirical observation.

**`eq:alphaN`** (formula; tier A, DIRECT)

On any finite simple graph with N>=4 sites, uniform hopping and C4 four-cycles (cycle subgraphs of length four, chords allowed), for n>=2, $\alpha(N,n)=-8C_4(N-n)(8N-11n-2)/[N(N-1)(N-2)(N-3)]$ for every n: $32C_4$ transposition walks (a pair exchanged around a 4-cycle, the other two corners empty) and $8C_4$ 3-cycle walks (the empty corner circulating once), weighted by exact hypergeometric probabilities; it reduces to $-64C_4/[N(N-1)]$ at n=2, and on the LxL torus $C_4=N$ for L=3 or L>=5, $C_4=24$ at L=4.

**`app:mu4walks#hypercubic`** (theorem; tier A, DIRECT)

For the d-dimensional periodic hypercubic lattice (z=2d) with every side 3 or >=5, the 4-cycles are the plaquettes, $C_4=Nd(d-1)/2$, so $\alpha_d(N,2)=-32d(d-1)/(N-1)=-16(d-1)z/(N-1)$; it reproduces $\alpha(27,2)=-96/13$ at d=3 and -48/31 on 5x5x5; each side of length 4 adds axis-ring 4-cycles, giving $-16[2d(d-1)+m]/(N-1)$ with m such sides (4x4x4: -80/21; 3x4: -80/11; 4x5: -80/19).

**`app:mu4walks#hcb-lemma`** (lemma; tier L, DIRECT; Lean: `hardCoreBosonFourthMoment`)

On any finite simple graph with N>=4 vertices, m edges, $W=\sum_v\binom{d_v}{2}$, $D=\binom m2-W$ pairs of disjoint edges and C4 four-cycles, the fourth moment of n hard-core bosons with uniform hopping (the adjacency matrix of the n-token graph, the fixed-n block of the spin-1/2 XX model) is $\mu_4^{\rm HCB}=(2m+4W+8C_4)p_{11}+(24D+16C_4)p_{22}$, $p_{ab}=(n)_a(N-n)_b/(N)_{a+b}$; equivalently $\Tr(\zeta^{\hat n}H^4)=(2m+4W+8C_4)\zeta(1+\zeta)^{N-2}+(24D+16C_4)\zeta^2(1+\zeta)^{N-4}$.

**`eq:Aclosed`** (formula; tier L, DIRECT; Lean: `fourthMomentHubbard`, `fourthMomentHubbardTorus`, `torusGraphCounts`)

On any finite simple graph with N>=4 sites and uniform hopping, for every n, $A(N,n)=(2m+4W+8C_4)p_{11}+(24D-16C_4)p_{22}-12C_4p_{31}$ (units of $\lambda^4$), from eq:AfromHCB, the hard-core-boson lemma and $T_2=32C_4p_{22}$, $T_3=8C_4p_{31}$ (eq:alphaapprox); no step assumes the graph triangle-free; on the LxL torus with L=3 or L>=5, $A=36Np_{11}+(48N^2-184N)p_{22}-12Np_{31}$; at L=4 ($C_4=24$), A=2272/15, 10534/35, 5984/13 for n=2,3,4 (the intercepts of the lines through tab:mu4exact).

**`sec:mu4exchange#proposition`** (proposition; tier L, DIRECT; Lean: `fourthMomentHubbard`, `torusGraphCounts`)

On any finite simple graph with N>=4 sites, m edges, W pairs of edges sharing a vertex, D pairs of disjoint edges, C4 four-cycles and uniform hopping lambda without Peierls phases (for those, eq:mu4flux), for projected spin-1/2 fermions in any sector (N_up, N_down) with n=N_up+N_down<=N and $P_{\rm same}=\binom{N_\uparrow}{2}+\binom{N_\downarrow}{2}$ (for n<=1, P_same=0 and mu4=A), in units of $\lambda^4$: $\mu_4(\infty)=A(N,n)+\alpha(N,n)P_{\rm same}$ with $A(N,n)=(2m+4W+8C_4)p_{11}+(24D-16C_4)p_{22}-12C_4p_{31}$, $\alpha(N,n)=-8C_4(N-n)(8N-11n-2)/[N(N-1)(N-2)(N-3)]$ and $p_{ab}=(n)_a(N-n)_b/(N)_{a+b}$; on the square-lattice torus with L=3 or L>=5, $C_4=N$ and $\alpha(N,2)=-64/(N-1)$.

## §7 Finite U

**`sec:SW#centralmoment`** (formula; tier A, DIRECT)

With $\langle X\rangle=\mathrm{Tr}X/D_0$, the mean energy is $\bar E(U)=-\langle V\rangle/U+O(1/U^2)$ and the central second moment is $\mu_{2,c}(U)=\mu_2(\infty)-\frac2U\langle T_0V\rangle+\frac{c_2}{U^2}+O(1/U^3)$ with $c_2=\mathrm{Var}(V)+2\langle T_0H^{(3)}\rangle$.

**`sec:SW#crossterm`** (theorem; tier L, COMPOSITION; Lean: `schriefferWolffCrossTerm`, `schriefferWolffSecondMoment`, `schriefferWolffSecondMomentTorus`, `schriefferWolffHubbard`, `hubbardHoppingIsHoppingOperator`, `torusTriangleFree`, `crossTermNeedsTriangleFree`)

On any triangle-free graph $\mathrm{Tr}(T_0V)=0$ (in the proof each term vanishes, needing a triangle); the LxL torus (L>=3) is triangle-free exactly when L is not 3, so for L>=4 the second-order correction operator V is exactly Hilbert-Schmidt orthogonal to the projected kinetic operator and $\mu_{2,c}$ has no 1/U term (a proven cancellation, not a fit).

**`sec:SW#c2-sign`** (numerical result; tier N, DIRECT)

In every low-filling sector computed (n<=5 at L=4,5,6) the third-order overlap is larger than Var(V) and of opposite sign, so c2<0 and the N_d=0 band narrows at large finite U; near half filling the sign reverses (at half filling T0=0 and c2=Var(V)>0; at L=4, c2(13,1)=6848/1575 and c2(12,2)=23424/2275 are positive). For n=2, c2(1,1)=-96/(N-1)-64/(N-1)^2 exactly at L=5..8 (computed, not derived).

**`sec:SW#beta-trend`** (numerical result; tier E, DIRECT)

At low filling, c2/(N_up N_down) is close to composition-independent at fixed (L,n), with relative spread (|difference|/mean) shrinking as L grows: 0.14%, 0.06%, 0.03% between (3,1) and (2,2) at L=4,5,6 (n=4), and 0.34%, 0.13% between (4,1) and (3,2) at L=4,5 (n=5); the near-independence degrades with filling (0.79% between (5,1) and (3,3) at L=4, n=6) and c2 changes sign near half filling: numerical evidence that at low filling the U^-2 coefficient is governed by the opposite-spin pair count, c2 ~ beta(L,n) N_up N_down with beta<0.

## §8 Gauge response

**`sec:futurework#alphaflux`** (formula; tier A, DIRECT)

For n=2 on the LxL torus with L=3 or L>=5 and uniform plaquette flux $\Phi_\square=2\pi p/L^2$, the exchange coefficient is exactly $\alpha(N,2,\Phi)=-\frac{64}{N-1}\cos\Phi_\square$; it fails at L=4.

**`eq:doublonSW`** (formula; tier A, COMPOSITION; Lean: `doubledPeierlsPhase`, `doublonHoppingRange`, `doublonOnSiteShift`, `doublonOnSiteShiftTorus`, `doublonFirstOrderZero`, `pairHoppingHermitian`)

For every finite graph, in the two-electron (single-doublon) sector, Peierls substitution followed by second-order Schrieffer-Wolff projection gives the doublon Hamiltonian $H_d^{(2)}(A)=\varepsilon_d^{(2)}\sum_in_i^d+t_d\sum_{\langle ij\rangle}(e^{2iA_{ji}}d_j^\dagger d_i+{\rm h.c.})$, $A_{ji}=-A_{ij}$, $t_d=2\lambda^2/U$: the hopping carries twice the bare link phase, there is no longer-range doublon hopping at this order, and the on-site shift ($8\lambda^2/U$; $2z\lambda^2/U$ at coordination z) is exactly flux-blind. The second-order terms are machine-checked; the Schrieffer-Wolff formula itself is tier A.

**`sec:futurework#twist-periodicity`** (proposition; tier A, DIRECT)

Under a global boundary twist theta, the one-doublon dispersion is $E_d(K;\theta)=\varepsilon_d+2t_d[\cos(K_x+2\theta/L)+\cos K_y]$ and ${\rm Spec}\,H_d(\theta+\pi)={\rm Spec}\,H_d(\theta)$ exactly for the second-order effective single-doublon Hamiltonian; the full two-electron spectrum is not pi-periodic.

**`sec:futurework#twist-uband`** (numerical result; tier N, DIRECT)

The exact two-electron U-band under a boundary twist is pi-periodic up to deviations ~ (2 lambda)^L/U^(L-1) (L=6: about 1e-4 lambda at U=20 lambda, 3e-6 lambda at U=40 lambda; ratios between U=20 and 40 near 2^(L-1) at L=4,5,6) and matches the doubled-twist doublon dispersion to O(lambda^4/U^3) (8e-3 and 1e-3 lambda at L=6).

**`sec:futurework#doublonflux-numeric`** (numerical result; tier E, DIRECT)

Against the exact flux-threaded finite-U two-electron Hubbard problem on the 6x6 torus, over all 36 quantized uniform fluxes, with no fitted parameters, the doubled-phase doublon prediction for the U-band outperforms an undoubled control in RMS residual by a factor of 12.5 at U=20 lambda and 48 at U=40 lambda (residual ratio 0.080 and 0.021; 0.280 at U=10 lambda and 0.0052 at U=80 lambda).

**`eq:mu4flux`** (proposition; tier A, DIRECT)

On any finite simple graph with N>=4 sites, m edges, W pairs of edges sharing a vertex, D pairs of disjoint edges, uniform hopping modulus lambda and arbitrary spin-independent Peierls phases $A_{ij}=-A_{ji}$, for any number n<=N of projected spin-1/2 fermions, in units of $\lambda^4$: $\mu_4(\Theta)=(2m+4W)p_{11}+24Dp_{22}+B(N,n,P_{\rm same})\sum_C\cos\Theta_C$, the sum over every 4-cycle C (chords allowed), $\Theta_C$ its Wilson phase, $B=8p_{11}-16p_{22}-12p_{31}-8(N-n)(8N-11n-2)P_{\rm same}/[N(N-1)(N-2)(N-3)]$ (eq:Bflux); at zero phases it is sec:mu4exchange#proposition. Proof: every phase-dependent cross term of $\sum|(H^2)_{c''c}|^2$ closes one 4-cycle, with sign from the closed-walk lemma and per-cycle weight $8p_{13}-32s_2p_{22}+8s_3p_{31}$ = B.

**`sec:futurework#alphaflux-n`** (formula; tier A, COMPOSITION)

On the LxL torus with L=3 or L>=5 every 4-cycle is a plaquette, so under a uniform flux $\sum_C\cos\Theta_C=N\cos\Phi_\square$ and the exchange slope is $\alpha(N,n)\cos\Phi_\square$ at every n (eq:alphaflux at n=2).

**`sec:futurework#L4-winding`** (formula; tier A, DIRECT)

At L=4 the four rows and four columns are 4-cycles winding around the torus; their Wilson phases are boundary holonomies. With the link phases of the numerics (Landau gauge: a +x hop at height y carries $-y\Phi_\square$, the +y wrap-around hop in column x carries $4x\Phi_\square$) and twists $\theta_x,\theta_y$, rows carry $\theta_x-4y\Phi_\square$ and columns $\theta_y+4x\Phi_\square$; without twists, at $\Phi_\square=2\pi p/16$, $\sum_C\cos\Theta_C=16\cos\Phi_\square+2+4\cos4\Phi_\square+2\cos8\Phi_\square$. The L=4 cos 4Phi, cos 8Phi terms and twist dependence come from the winding loops' holonomies, which differ row to row by the strip flux $4\Phi_\square$ and depend on the twists; no contractible loop produces them.

## §9 What is not claimed

**`sec:benchmark#nonclaim-doublonform`** (non-claim; tier C, CITED)

The functional form of the perturbative doublon Hamiltonian is not claimed as new (comparable effective doublon Hamiltonians exist for an extended, mass-imbalanced Hubbard model and for a periodically driven one), nor is its doubled Peierls phase; the stated contributions are its explicit derivation on any graph (second-order terms machine-checked for the two-electron problem) and the zero-fitted-parameter connection to the exact two-electron U-band.

**`sec:discussion#nonclaim-alpha`** (non-claim; tier A, NONE)

Eq. alphaN is stated for finite simple graphs; no claim is made for graphs with self-loops or multiple edges, nor for coefficients of higher moments.

**`sec:discussion#open-beta`** (non-claim; tier E, NONE)

The paper does not derive beta(L,n), the prefactor of N_up N_down in the U^-2 coefficient c2 of $\mu_2$, nor the sign of c2; c2 itself is an exact trace for every composition, but its sign and the law c2 ~ beta(L,n) N_up N_down at low filling are numerical (at fixed n, |beta| is at most of order 1/N by the bound in annex 07 §6), epistemically distinct from the exact $\mu_2(\infty)$ theorem and the exact vanishing of the 1/U term.

**`sec:discussion#nonclaims`** (non-claim; tier A, NONE)

Dedicated non-claims paragraph: beta(L,n), the sign of c2 and the many-cluster sector shift are not derived; the graph expansion behind the hard-core-boson moment (eq:muHCB) is not new; the fourth moment under Peierls phases (eq:mu4flux) is derived but not machine-checked; the exchange coefficient (uniform hopping) depends only on C4 and is not a law in z, alpha_d(N,2) needs every side 3 or >=5; the doublon Hamiltonian derived for one doublon and its pi-periodicity exact only for that model; no many-pair stiffness, ODLRO, condensation, collective transport or superconductivity; projection, moment method and doublon form not claimed as new; machine-checked scope in App. F.

**`sec:futurework#nonclaim-sc`** (non-claim; tier A, NONE)

The paper establishes repulsive binding, a microscopic charge-2e gauge coupling and single-pair h/(2e) periodicity at leading order in 1/U only; it makes no claim about collective (non-additive) charge-2e transport, many-pair phase stiffness, off-diagonal long-range order, condensation or superconductivity, and the single-pair doublon flux response is a standard consequence of the effective Hamiltonian, not evidence of collective or superconducting behaviour.

**`app:mu4walks#nonclaim-graphgeneral`** (non-claim; tier A, NONE)

The exchange coefficient depends on the graph only through its number of 4-cycles: the square-lattice value -64/(N-1), written -16z/(N-1), is not a law in the coordination number (kagome, d=2 and z=4, has C4=0 and alpha=0; d=3 gives -96/13, not -48/13 or -72/13); the hypercubic form alpha_d(N,2) holds only on tori whose sides are all 3 or >=5.

**`sec:mu4exchange#nonclaim-xy`** (non-claim; tier C, CITED)

Not claimed as new: the graph expansion behind the hard-core-boson moment, the fourth-order term of the spin-1/2 XY (quantum lattice gas) high-temperature series (Betts, Elliott and Lee 1970; Lee 1971) in its field-dependent, grand-canonical form (Rogiers and Dekeyser 1973; Dekeyser and Rogiers 1975); the token graphs and the XX block (Fabila-Monroy et al. 2012; Matsubara and Matsuda 1956; Audenaert et al. 2007) and the classification of their induced 4-cycles (Fabila-Monroy and Trujillo-Negrete 2022); the grand-canonical high-temperature series of the U=infinity Hubbard and J=0 t-J models on specific lattices (Plischke 1974; Kubo and Tada 1983, 1984; Putikka, Luchini and Ogata 1992); the Thouless-Nagaoka hole loop (the 3-cycle term). What is added is the exact canonical (fixed N_up, N_down) form on an arbitrary finite graph and its combination into A(N,n).

**`sec:futurework#nonclaim-gain`** (non-claim; tier C, CITED)

Not claimed as new: at n=1, eq:mu4flux is $\Tr A_\Theta^4/N$ with $\Tr A_\Theta^4=2m+4W+8\sum_C\cos\Theta_C$ for the magnetic adjacency matrix, the length-4 case of the closed-walk sum of gain graphs (Cavaleri and Donno 2022, Eq. (4.3)), on the square lattice the Hofstadter moment $28+8\cos\Phi_\square$ per site (Bellissard et al. 1997; Ouvry, Wagner and Wu 2016).

**`sec:futurework#nonclaim-flux-lean`** (non-claim; tier A, NONE)

The fourth moment under Peierls phases (eq:mu4flux), including its flux-independent baseline $(2m+4W)p_{11}+24Dp_{22}$, is derived and checked numerically but not machine-checked: the fourth-moment Lean statements (App. F) are for zero phases.

**`sec:futurework#multidoublon`** (non-claim; tier A, NONE)

With several doublons further second-order terms appear, not derived here: in a doublon-only sector with no unpaired electrons and no interaction beyond on-site U, a nearest-neighbour doublon-doublon interaction; with unpaired electrons the doublon already moves at first order (exchanging places with a singly occupied neighbour) and the second-order terms include spin exchange and correlated three-site hoppings; extended interactions add further terms.

**`sec:futurework#loops-beyond-second`** (non-claim; tier A, NONE)

Beyond second order the single-doublon Hamiltonian acquires flux-dependent terms: a virtual electron running around a loop of length l contributes that loop's ordinary charge-e Wilson phase at order $\lambda^l/U^{l-1}$ ($\lambda^3/U^2$ around a triangle); on the LxL torus the twist is first felt at length L, when the pair dissociates and its two electrons together wind once around the torus, the $(2\lambda)^L/U^{L-1}$ deviation. These change the effective Hamiltonian beyond doubled-link hopping, not the doublon's gauge charge, which is 2e at every order.
