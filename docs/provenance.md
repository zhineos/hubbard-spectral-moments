# Provenance

What the paper takes from earlier work, and what is new. The paper's introduction and its
"What is not claimed" paragraph say the same in context; tier-C rows of
[`correspondence.tsv`](correspondence.tsv) carry the exact citations.

## Taken from earlier work

| idea or result | source | how it is used |
|---|---|---|
| the two-electron Hubbard problem on the square lattice; the repulsively bound pair (U-band) behaving as a charge-$2e$ composite, with a doubled Bloch-oscillation frequency in simulations | D. Souza and F. Claro, PRB 82, 205437 (2010) | the benchmark of §2; the paper extends it to three and four electrons |
| the exact one-dimensional bound pair, and a semiclassical doubled Bloch frequency at leading order in $\lambda/U$ | F. Claro and P. Robles, Eur. J. Phys. 43, 015403 (2022) | corroborates the sign of the doublon hopping (§2) |
| repulsively bound pairs observed in an optical lattice | Winkler et al. (2006); Daley et al. | context |
| the bound state at a repulsive defect | Koster and Slater (1954) | the relative-coordinate problem of the pair (§2, S2) |
| closed walks inducing permutations of a spin background, restored when each cycle has one spin | Brinkman and Rice (1970); ten Haaf et al. (1995); Meshkov and Berkov (1992) | the starting point of the closed-walk classification of §6 |
| spectral moments and the no-double-occupancy projection | Harris and Lange (1967); Esterling (2023) | the method; neither the projection nor the moment method is claimed as new |
| the strong-coupling (Schrieffer–Wolff) expansion and the decomposition of its second-order operator into superexchange and correlated hopping | Chao, Spałek and Oleś (1977); MacDonald, Girvin and Yoshioka (1988) | §7 and S7 |
| effective doublon Hamiltonians | Zhang et al. (2024), an extended mass-imbalanced model; Valmispild et al. (2020), a periodically driven model | the functional form of the doublon Hamiltonian and its doubled Peierls phase are not claimed as new |
| mapping few-particle problems to single-particle hopping on a higher-dimensional lattice; many-body problems as hopping on a configuration or Fock-space graph | Vallejo, Navarro and Espinosa (2003); Huipe et al. (2024); Altshuler et al. (1997); Roy and Logan (2025) | the language of §3 and §5 |
| the hypercubic-lattice density of states as a Bessel integral; lattice Green's functions | Economou (2006); Morita (1971) | Appendix A |
| moments of a sum sampled without replacement (finite-population correction) | classical sampling statistics | §5.3 and Appendix B; the formulas are derived and machine-checked here, not claimed as new |

## New in this work

- The **exact second-moment theorem** for the projected hopping operator on any finite simple
  graph, for any spin composition and any spin-independent Hermitian amplitudes, with
  $H_\infty$ built from fermion operators (machine-checked).
- The **exact linearity of $\mu_4(U\to\infty)$ in the same-spin pair count** on any finite
  graph: no four-particle permutation in four hops (machine-checked), the spin-averaging lemma,
  and the affine identity for $P_3$ (machine-checked).
- The **exchange coefficient** $\alpha(N,n)=-8C_4(N-n)(8N-11n-2)/[N(N-1)(N-2)(N-3)]$ on any
  finite simple graph with uniform hopping, fixed by the number of 4-cycles; its square-lattice,
  hypercubic, $L=4$ and kagome cases.
- The **vanishing $1/U$ term** of the band variance on every triangle-free graph (the cross
  term is machine-checked), and the $U^{-2}$ coefficient as an exact trace; its sign and its
  near-proportionality to $N_\uparrow N_\downarrow$ at low filling are numerical.
- The **flux-resolved fourth moment** for $n=2$ on $L\times L$ tori with $L=3$ or $L\geq5$:
  $\alpha(N,2,\Phi)=-64\cos\Phi_\square/(N-1)$, with exchange changing the interference parity,
  not the charge.
- The **explicit derivation of the doubled doublon phase** by gauge-covariant
  Schrieffer–Wolff projection on any finite graph, with its second-order terms machine-checked
  for the two-electron problem, and its zero-parameter comparison with the exact flux-threaded
  U-band.
- The **Lean 4 formalization** of the exact combinatorial statements, checked by six
  independent kernels.

## Tools

Python 3.13 with numpy, scipy and matplotlib (`requirements.txt`); Lean 4 v4.35.0 with
Mathlib v4.35.0. The work follows [`framework.md`](framework.md): the author approves every
claim and every change to a frozen claim. Generative AI tools were used: Claude (Anthropic)
as editor (text, code and Lean proofs, under the author's direction) and as the reviewers
described in [`method.md`](method.md); GPT models (OpenAI) as further reviewers of the
statements; Qwen models (Alibaba Cloud) to test and review the scientific code; DeepSeek
models in writing the numerical solvers; and the open-source coding agent opencode in the
development of the code. The author checked the results and is responsible for them.
