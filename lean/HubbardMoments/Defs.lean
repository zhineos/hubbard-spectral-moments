-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib

/-!
# Definitions

Every object that the claims in `HubbardMoments.Spec` refer to is defined here, using
Mathlib only. Together with `Spec`, this file is all a reader needs to check *what* is
claimed. The proofs live in the other files.

* `sector V a b k`: basis states of `a` up and `b` down electrons on the sites `V` with
  exactly `k` doubly occupied sites.
* `torus L`: the `L × L` square-lattice torus.
* `arcs G`: the directed edges of a graph `G`.
* `hops G S`: the hops out of a configuration `S`, from an occupied site to an empty
  neighbouring site.
* `Config V σ`, `occ`, `basis V n`, `move`: configurations without double occupancy, their
  occupied sites, the `N_d = 0` basis of a spin composition `n`, and one hop.
* `IsProjectedHopping G t H`: the properties of the projected hopping operator `H∞`.
* `secondMoment B H`: the second spectral moment of `H` on the basis `B`.
* `pairHopping G t A`, `doublonSecondOrder`: two electrons of opposite spin with Peierls
  phases `A`, and the second-order effective Hamiltonian of a doublon.
* `FockState V σ`, `siteOcc`, `IsHop`, `IsHoppingOperator G H`, `virtualOp Q H`: Fock basis
  states (double occupancy allowed), site occupations, one hop, hopping operators, and the
  operator `V = T₁† T₁` of the Schrieffer–Wolff expansion.
* `wedgeCount G`, `disjointEdgePairs G`, `fourCycleCount G`: the graph counts `W`, `D`, `C₄`
  of the fourth moment; `occProb N n a b`: the occupation probabilities `p_ab`;
  `hardCoreHopping G`: hard-core bosons (the token-graph adjacency matrix);
  `fourthMoment B H`: the fourth moment `Tr(H_B⁴)/|B|`; `fourthMomentIntercept G n`,
  `exchangeSlope G n`: the closed forms `A(N, n)` and `α(N, n)`.
-/

@[expose] public section

namespace HubbardMoments

open Finset SimpleGraph

section Sector

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- The basis states with `a` up electrons, `b` down electrons and exactly `k` doubly
occupied sites, as pairs (up-occupied sites, down-occupied sites). A pair `(u, d)` of
subsets of the sites labels exactly one Fock basis state, so these pairs count the
states. -/
def sector (a b k : ℕ) : Finset (Finset V × Finset V) :=
  (powersetCard a univ ×ˢ powersetCard b univ).filter (fun p => (p.1 ∩ p.2).card = k)

end Sector

/-- The `L × L` square-lattice torus (periodic boundary conditions): the box product of
two `L`-cycles. Each site is adjacent to its nearest neighbours along both axes. -/
abbrev torus (L : ℕ) : SimpleGraph (Fin L × Fin L) := cycleGraph L □ cycleGraph L

instance (L : ℕ) : DecidableRel (torus L).Adj := fun _ _ =>
  decidable_of_iff' _ boxProd_adj

section Hops

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The directed edges of `G`: ordered pairs of adjacent vertices. -/
def arcs : Finset (V × V) := univ.filter (fun p => G.Adj p.1 p.2)

/-- The hops out of a configuration `S` (the set of occupied sites): directed edges from
an occupied site to an empty one. Their number is the `M(S)` of the paper, and the
diagonal element of `H∞²` at `S` is `λ² M(S)`. -/
def hops [DecidableEq V] (S : Finset V) : Finset (V × V) :=
  (arcs G).filter (fun p => p.1 ∈ S ∧ p.2 ∉ S)

end Hops

section Configurations

/-- A configuration with no doubly occupied site: each site is empty (`none`) or holds one
particle with spin label `s : σ`. Take `σ = Unit` for spinless fermions and a two-element
type for spin ½. -/
abbrev Config (V σ : Type*) := V → Option σ

variable {V σ : Type*} [Fintype V] [DecidableEq V]

/-- The occupied sites of a configuration. -/
def occ (c : Config V σ) : Finset V := univ.filter (fun v => c v ≠ none)

variable (V) in
/-- The no-double-occupancy basis (the `N_d = 0` sector) with `n s` particles of spin `s`
for every spin label `s`. -/
def basis [Fintype σ] [DecidableEq σ] (n : σ → ℕ) : Finset (Config V σ) :=
  univ.filter (fun c => ∀ s, (univ.filter (fun v => c v = some s)).card = n s)

/-- The configuration obtained from `c` by moving the particle at site `i` to site `j`,
keeping its spin. -/
def move (c : Config V σ) (i j : V) : Config V σ :=
  Function.update (Function.update c i none) j (c i)

/-- **Projected hopping operators.** `H`, a matrix on the configurations, is a projected
hopping operator on the graph `G` with hopping modulus `t` if

* it is Hermitian;
* its matrix element from `c` to `move c i j` has modulus `t` whenever `i` and `j` are
  adjacent, `i` is occupied and `j` is empty (one particle hops to an empty neighbour);
* its matrix element from `c` to `b` vanishes when `b` is not obtained from `c` by such a hop.

The operator `H∞ = P₀ H_t P₀` of the Hubbard model at `U → ∞`, written in the
configuration basis, has these properties when every bond has `|t_ij| = λ = t`, whatever
the fermionic signs and the Peierls phases: a hop onto an occupied site either violates
the Pauli principle or creates a doubly occupied site, which `P₀` removes. The theorems
about this structure therefore apply to `H∞`; `projectedHubbard_isProjectedHopping` proves
it for `H∞` built from fermion operators (`projectedHubbard`), with any ordering of the
orbitals. -/
structure IsProjectedHopping (G : SimpleGraph V) (t : ℝ)
    (H : Matrix (Config V σ) (Config V σ) ℂ) : Prop where
  isHermitian : H.IsHermitian
  norm_apply_move : ∀ c i j, G.Adj i j → c i ≠ none → c j = none → ‖H (move c i j) c‖ = t
  apply_eq_zero : ∀ c b, (∀ i j, G.Adj i j → c i ≠ none → c j = none → b ≠ move c i j) →
    H b c = 0

/-- **Projected hopping operators with bond-dependent amplitudes.** `w i j` is the modulus
`|t_ji|` of the amplitude for a particle to hop from site `i` to site `j` (`0` if there is
no bond). `H` is Hermitian; its matrix element from `c` to `move c i j` has modulus `w i j`
whenever `i ≠ j`, `i` is occupied and `j` is empty; and it vanishes between configurations
not related by one hop. `IsProjectedHopping G t` is the case `w i j = t` on the bonds of `G`
and `0` elsewhere. -/
structure IsWeightedProjectedHopping (w : V → V → ℝ) (H : Matrix (Config V σ) (Config V σ) ℂ) :
    Prop where
  isHermitian : H.IsHermitian
  norm_apply_move : ∀ c i j, i ≠ j → c i ≠ none → c j = none → ‖H (move c i j) c‖ = w i j
  apply_eq_zero : ∀ c b, (∀ i j, i ≠ j → c i ≠ none → c j = none → b ≠ move c i j) →
    H b c = 0

/-- The second spectral moment of `H` on a finite basis `B`:
`μ₂ = Tr(H_B²)/|B| - (Tr H_B/|B|)²`, where `H_B` is the block of `H` on `B`. For Hermitian
`H_B` this is the variance of its eigenvalue distribution. -/
noncomputable def secondMoment {ι : Type*} (B : Finset ι) (H : Matrix ι ι ℂ) : ℂ :=
  (∑ c ∈ B, ∑ b ∈ B, H c b * H b c) / B.card - ((∑ c ∈ B, H c c) / B.card) ^ 2

end Configurations

section PairHopping

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Two electrons of opposite spin, with Peierls phases.** The basis state `(i, j)` is
`c†_{i↑} c†_{j↓} |0⟩`; `(R, R)` is the doublon `D_R` on site `R`. The hopping operator
`H_t(A) = -t ∑_{x ~ y, s} e^{i A(y, x)} c†_{y s} c_{x s}` moves one electron from a site `x`
to an adjacent site `y` with amplitude `-t e^{i A(y, x)}`: `A y x` is the phase of the hop
`x → y`. With one electron of each spin no fermionic sign arises, so these are all the
matrix elements. -/
noncomputable def pairHopping (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) : Matrix (V × V) (V × V) ℂ := fun p q =>
  (if p.2 = q.2 ∧ G.Adj q.1 p.1 then -t * Complex.exp (A p.1 q.1 * Complex.I) else 0) +
    (if p.1 = q.1 ∧ G.Adj q.2 p.2 then -t * Complex.exp (A p.2 q.2 * Complex.I) else 0)

/-- **The second-order doublon Hamiltonian.** The `O(t²/U)` term of the effective
Hamiltonian on the doublon states, from second-order degenerate perturbation theory
(Schrieffer–Wolff): `⟨D_{R'}| H_eff^{(2)} |D_R⟩ = (1/U) ∑_m ⟨D_{R'}|H|m⟩ ⟨m|H|D_R⟩`, summed
over the two-electron states `m = (i, j)`, `i ≠ j`, without double occupancy. These have
interaction energy `0` and the doublons `U`, so the energy denominator is exactly `U`. -/
noncomputable def doublonSecondOrder (H : Matrix (V × V) (V × V) ℂ) (U : ℝ) (R' R : V) : ℂ :=
  (∑ m ∈ univ.filter (fun m : V × V => m.1 ≠ m.2), H (R', R') m * H m (R, R)) / U

end PairHopping

section Fock

/-- A Fock basis state of fermions with spin labels `σ` on the sites `V`, given by its set of
occupied orbitals `(site, spin)`. Unlike `Config`, it allows doubly occupied sites. -/
abbrev FockState (V σ : Type*) := Finset (V × σ)

variable {V σ : Type*} [DecidableEq V] [DecidableEq σ]

/-- The number of particles on site `v`. The no-double-occupancy states (`P₀`) are those with
`siteOcc c v ≤ 1` at every site. -/
def siteOcc (c : FockState V σ) (v : V) : ℕ := (c.filter (fun p => p.1 = v)).card

/-- `b` is obtained from `a` by one hop: a particle of spin `s` moves from a site `i` to an
adjacent site `j` holding no particle of spin `s` (Pauli principle). -/
def IsHop (G : SimpleGraph V) (a b : FockState V σ) : Prop :=
  ∃ i j s, G.Adj i j ∧ (i, s) ∈ a ∧ (j, s) ∉ a ∧ b = insert (j, s) (a.erase (i, s))

/-- **Hopping operators** on Fock states: the matrix element from `a` to `b` vanishes unless
`b` is obtained from `a` by one hop. The Hubbard hopping term
`H_t = -∑_{i ~ j, s} t_{ij} c†_{j s} c_{i s}` is one, for any amplitudes `t_{ij}`, Peierls
phases and fermionic signs: `c†_{j s} c_{i s}` maps a Fock basis state to `±` the state with
that one particle moved, or to zero (`hubbardHopping_isHoppingOperator` for the hopping term
built from fermion operators). -/
structure IsHoppingOperator (G : SimpleGraph V) (H : Matrix (FockState V σ) (FockState V σ) ℂ) :
    Prop where
  apply_eq_zero : ∀ a b, ¬ IsHop G a b → H b a = 0

/-- **The operator `V = T₁† T₁`** of the Schrieffer–Wolff expansion
`H_eff = T₀ - V/U + O(1/U²)`, where `T₀ = P₀ H P₀`, `T₁ = Q H P₀`, and `Q` is the set of
intermediate states (for the paper, the states with exactly one doubly occupied site):
`V_{ba} = ∑_{m ∈ Q} conj(H_{mb}) H_{ma}`. -/
noncomputable def virtualOp (Q : Finset (FockState V σ))
    (H : Matrix (FockState V σ) (FockState V σ) ℂ) :
    Matrix (FockState V σ) (FockState V σ) ℂ :=
  fun b a => ∑ m ∈ Q, star (H m b) * H m a

end Fock

section FermionOperators

variable {O : Type*} [DecidableEq O]

/-- The number of occupied orbitals of `S` that come before `o` in the order `ord`. -/
def countBelow (ord : O ↪ ℕ) (S : Finset O) (o : O) : ℕ := (S.filter fun x => ord x < ord o).card

/-- **Fermion annihilation operator** `c_o` on the Fock space of the orbitals `O`. The basis
state of an occupied set `S` is `|S⟩ = c†_{o₁} ⋯ c†_{o_k} |0⟩`, with `o₁, …, o_k` the orbitals
of `S` in the order `ord`. Then `c_o |S⟩ = (-1)^m |S \ {o}⟩` if `o ∈ S`, `m` the number of
orbitals of `S` before `o`, and `c_o |S⟩ = 0` otherwise. -/
def annihilate (ord : O ↪ ℕ) (o : O) : Matrix (Finset O) (Finset O) ℂ := fun S' S =>
  if o ∈ S ∧ S' = S.erase o then (-1) ^ countBelow ord S o else 0

/-- **Fermion creation operator** `c†_o`: `c†_o |S⟩ = (-1)^m |S ∪ {o}⟩` if `o ∉ S`, `m` the
number of orbitals of `S` before `o`, and `0` otherwise. It is the adjoint of `annihilate`,
and the two satisfy the canonical anticommutation relations (`HubbardMoments.Fermions`). -/
def create (ord : O ↪ ℕ) (o : O) : Matrix (Finset O) (Finset O) ℂ := fun S' S =>
  if o ∉ S ∧ S' = insert o S then (-1) ^ countBelow ord S o else 0

end FermionOperators

section HubbardOperators

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]

/-- **The Hubbard hopping term with Peierls phases**, built from fermion operators on the
orbitals `(site, spin)` ordered by `ord`:
`H_t = -t ∑_{x ~ y} ∑_s e^{i A(y, x)} c†_{y s} c_{x s}`, the sum over ordered pairs of
adjacent sites (`arcs G`). It is Hermitian when `A` is antisymmetric. -/
noncomputable def hubbardHopping (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (ord : V × σ ↪ ℕ) : Matrix (FockState V σ) (FockState V σ) ℂ :=
  ∑ p ∈ arcs G, ∑ s, (-(t : ℂ) * Complex.exp (A p.2 p.1 * Complex.I)) •
    (create ord (p.2, s) * annihilate ord (p.1, s))

/-- The Fock state of a configuration without double occupancy: its occupied orbitals. -/
def configState (c : Config V σ) : FockState V σ := univ.filter fun o => c o.1 = some o.2

/-- **The projected hopping operator `H∞ = P₀ H_t P₀`** of the `U → ∞` Hubbard model, in the
configuration basis. The configurations are exactly the Fock states without double
occupancy (`configState` is injective with that image), so the block of `H_t` on them is
`c, b ↦ (H_t)_{configState c, configState b}`. -/
noncomputable def projectedHubbard (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (A : V → V → ℝ) (ord : V × σ ↪ ℕ) : Matrix (Config V σ) (Config V σ) ℂ := fun c b =>
  hubbardHopping G t A ord (configState c) (configState b)

/-- **The hopping term with arbitrary amplitudes**, `H_t = -∑_{i ≠ j} ∑_s t_{ij} c†_{i s} c_{j s}`
(a particle hops from `j` to `i` with amplitude `-t_{ij}`). It is Hermitian when
`t_{ji} = conj(t_{ij})`. The sum runs over the ordered pairs of distinct sites, the arcs of
the complete graph. -/
noncomputable def hubbardHoppingWeighted (tt : V → V → ℂ) (ord : V × σ ↪ ℕ) :
    Matrix (FockState V σ) (FockState V σ) ℂ :=
  ∑ p ∈ arcs (⊤ : SimpleGraph V), ∑ s, (-tt p.2 p.1) • (create ord (p.2, s) * annihilate ord (p.1, s))

/-- `H∞ = P₀ H_t P₀` for arbitrary amplitudes, in the configuration basis. -/
noncomputable def projectedHubbardWeighted (tt : V → V → ℂ) (ord : V × σ ↪ ℕ) :
    Matrix (Config V σ) (Config V σ) ℂ := fun c b =>
  hubbardHoppingWeighted tt ord (configState c) (configState b)

end HubbardOperators

section FinitePopulation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Moments of sampling without replacement.** The `ℓ`-th moment of the sum of `k` values
drawn without replacement from the population `ε`: the average of `(∑_{i ∈ K} ε_i)^ℓ` over
the `k`-subsets `K` of `V`. For `k` non-interacting fermions of one spin species with
single-particle energies `ε`, the many-body energies are exactly these sums (one Slater
determinant per `K`), so this is the `μ_ℓ` of the paper at `U = 0`. -/
noncomputable def sampleMoment (ε : V → ℝ) (k ℓ : ℕ) : ℝ :=
  (∑ K ∈ powersetCard k univ, (∑ i ∈ K, ε i) ^ ℓ) / (Fintype.card V).choose k

/-- `p_m = k(k-1)⋯(k-m+1) / (N(N-1)⋯(N-m+1))`: the probability that `m` given distinct labels
are all among `k` labels drawn without replacement from `N`. It is `0` for `m > k`. -/
noncomputable def inclusionProb (N k m : ℕ) : ℝ := (k.descFactorial m : ℝ) / N.descFactorial m

end FinitePopulation

/-- **One hop of labelled hard-core particles.** `pos p` is the site of particle `p`. One
particle `p` moves to a site `w` adjacent to its own that no particle occupies. A closed walk
of `h` hops is a sequence `walk 0, …, walk h` of positions, consecutive ones related by
`IsParticleHop`, whose final sites are a permutation `σ` of the initial ones:
`walk h p = walk 0 (σ p)`. -/
def IsParticleHop {P V : Type*} [DecidableEq P] (G : SimpleGraph V) (pos pos' : P → V) : Prop :=
  ∃ p w, G.Adj (pos p) w ∧ w ∉ Set.range pos ∧ pos' = Function.update pos p w

/-- **The tight-binding band of the `L × L` torus**: the single-particle energies
`ε(q) = -2t (cos q₁ + cos q₂)` at the `L²` momenta `q = 2π (m₁, m₂)/L`. -/
noncomputable def torusBand (L : ℕ) (t : ℝ) : Fin L × Fin L → ℝ := fun m =>
  -2 * t * (Real.cos (2 * Real.pi * (m.1 : ℕ) / L) + Real.cos (2 * Real.pi * (m.2 : ℕ) / L))

section GraphCounts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `W`: the number of unordered pairs of distinct edges sharing a vertex, `∑_v C(d_v, 2)`
(in a simple graph two distinct edges share at most one vertex). -/
def wedgeCount : ℕ := ∑ v, (G.degree v).choose 2

/-- `D`: the number of unordered pairs of vertex-disjoint edges. Each such pair `{e, f}` is
counted twice among the ordered pairs `(e, f)`. (In a simple graph `D = C(m, 2) - W`, the
paper's definition: `disjointEdgePairs_eq` in `HubbardMoments/FourthMoment/GraphCounts.lean`.) -/
def disjointEdgePairs : ℕ :=
  ((G.edgeFinset ×ˢ G.edgeFinset).filter fun ef => ∀ v ∈ ef.1, v ∉ ef.2).card / 2

/-- `C₄`: the number of 4-cycles of `G` (as subgraphs). A 4-cycle with vertices `a, b, c, d`
in cyclic order is counted by the 8 sequences `(a, b, c, d)` given by its starting vertex
and its direction: the sequences of four vertices with `a ~ b ~ c ~ d ~ a`, `a ≠ c` and
`b ≠ d` (adjacent vertices are distinct, so all four are). -/
def fourCycleCount : ℕ :=
  (univ.filter fun x : V × V × V × V =>
    G.Adj x.1 x.2.1 ∧ G.Adj x.2.1 x.2.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧ G.Adj x.2.2.2 x.1 ∧
      x.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2).card / 8

end GraphCounts

/-- `p_ab = (n)_a (N - n)_b / (N)_{a+b}` (falling factorials): when `n` of `N` sites are
occupied, uniformly at random, the probability that `a` given sites are all occupied and `b`
other given sites are all empty. -/
noncomputable def occProb (N n a b : ℕ) : ℝ :=
  (n.descFactorial a * (N - n).descFactorial b : ℝ) / N.descFactorial (a + b)

section HardCoreBosons

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Hard-core bosons** hopping on `G` with unit amplitude, on the configurations `S` (the
sets of occupied sites): the matrix element from `S` to `S'` is `1` if `S'` is obtained from
`S` by moving one particle from an occupied site to an adjacent empty one, and `0` otherwise.
On the `n`-subsets it is the adjacency matrix of the `n`-token graph of `G` (the spin-½ XX
model at fixed magnetization). -/
noncomputable def hardCoreHopping : Matrix (Finset V) (Finset V) ℂ := fun S' S =>
  if ∃ p ∈ hops G S, S' = insert p.2 (S.erase p.1) then 1 else 0

end HardCoreBosons

/-- The fourth moment `Tr(H_B⁴)/|B|` of `H` on a finite basis `B`, where `H_B` is the block
of `H` on `B`. When `Tr H_B = 0`, as for every projected hopping operator
(`ProjectedHoppingDiagonalZero`), it is the fourth central moment of the eigenvalue
distribution of `H_B`: the `μ₄` of the paper. -/
noncomputable def fourthMoment {ι : Type*} (B : Finset ι) (H : Matrix ι ι ℂ) : ℂ :=
  (∑ c ∈ B, ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ b₃ ∈ B, H c b₁ * H b₁ b₂ * H b₂ b₃ * H b₃ c) / B.card

section ClosedForms

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The intercept `A(N, n) = (2m + 4W + 8C₄) p₁₁ + (24D - 16C₄) p₂₂ - 12 C₄ p₃₁`
(eq:Aclosed), `N` the number of sites, in units of `t⁴`. -/
noncomputable def fourthMomentIntercept (n : ℕ) : ℝ :=
  ((2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G : ℕ) : ℝ) *
      occProb (Fintype.card V) n 1 1 +
    (24 * (disjointEdgePairs G : ℝ) - 16 * fourCycleCount G) * occProb (Fintype.card V) n 2 2 -
      12 * (fourCycleCount G : ℝ) * occProb (Fintype.card V) n 3 1

/-- The exchange coefficient `α(N, n) = -8 C₄ (N - n)(8N - 11n - 2)/(N(N - 1)(N - 2)(N - 3))`
(eq:alphaN), in units of `t⁴`. -/
noncomputable def exchangeSlope (n : ℕ) : ℝ :=
  -(8 * (fourCycleCount G : ℝ) * ((Fintype.card V : ℝ) - n) *
      (8 * (Fintype.card V : ℝ) - 11 * n - 2)) /
    ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 2) *
      ((Fintype.card V : ℝ) - 3))

end ClosedForms

end HubbardMoments
