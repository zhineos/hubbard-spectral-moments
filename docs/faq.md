# Questions about the result and its limits

**Is this a claim about superconductivity?**
No. The paper concerns one or a few pairs. It makes no claim about many-pair phase stiffness,
off-diagonal long-range order, condensation, collective transport or superconductivity; the
single-pair flux response is a standard consequence of the effective doublon Hamiltonian.

**Is the charge-$2e$ character of the doublon new?**
No. Repulsive binding and the pair's charge $2e$ are known (Souza and Claro 2010; Claro and
Robles 2022). What is new is the explicit gauge-covariant derivation of the doubled Peierls
phase on any graph, with its second-order terms machine-checked, and its parameter-free test
against the exact problem.

**Why moments, and not the spectrum itself?**
Moments are exact traces: they can be evaluated in exact arithmetic, proved for every size and
graph, and machine-checked. They do not determine the density of states completely; the paper
uses them to resolve which structures (connectivity, closed loops, exchange) enter at which
order.

**Does the linearity of $\mu_4$ in $P_{\rm same}$ need the square lattice?**
No. It holds on any finite graph, for every particle number, and with bond-dependent
spin-independent amplitudes. The closed form of the slope $\alpha(N,n)$ assumes uniform
hopping and depends on the graph only through its number of 4-cycles.

**Why is the $4\times4$ torus special?**
Its rows and columns are 4-cycles that wind around the torus, in addition to the plaquettes,
so $C_4=24$ instead of $16$; $\alpha(16,2)=-32/5$ follows from the same formula. Under flux,
those winding loops also add other harmonics.

**Is the $\pi$-periodicity under a twist a property of the exact two-electron spectrum?**
No. It is exact for the second-order effective doublon Hamiltonian. The exact U-band follows it
up to corrections of order $(2\lambda)^L/U^{L-1}$ (computed), and the full two-electron
spectrum is not $\pi$-periodic.

**Is the sign of the $U^{-2}$ coefficient proved?**
No. The coefficient is an exact trace for every composition, but its sign (negative at low
filling, positive near half filling) and its near-proportionality to $N_\uparrow N_\downarrow$
are numerical findings, labelled as such.

**What exactly is machine-checked?**
The statements listed in the paper's Appendix F and in [`../lean/README.md`](../lean/README.md),
including what each does not cover. Since v1.1.0 this includes the whole fourth moment at
$U=\infty$ without Peierls phases: the hard-core-boson moment and $\mu_4=A+\alpha P_{\rm same}$
for $H_\infty$ built from fermion operators on any finite simple graph. Not formalized: the
Schrieffer–Wolff expansion itself, the fourth moment under Peierls phases (derived in the paper
and checked numerically), and the identification of free-fermion energies with sums of band
energies. No numerical result
depends on the formalization.

**How reliable are the reviews?**
Each claim was reviewed by readers who had not written it, on frozen snapshots, and every
finding was answered. The reviewers were AI models, independent of the writer but not of each
other's training, so they can share blind spots; the author's reading and the journal's
referees remain necessary. See [`method.md`](method.md).

**How do I reproduce the numbers?**
`python checks/run_checks.py` recomputes every checked number in about two minutes; the slow
runs and the Lean checks are described in [`method.md`](method.md) and `checks/README.md`.
