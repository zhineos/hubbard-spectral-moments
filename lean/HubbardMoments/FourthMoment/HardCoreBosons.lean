-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.GraphCounts
public import HubbardMoments.SecondMoment

/-!
# The hard-core-boson fourth moment

Stage 3 of the fourth-moment plan: `fourthMoment_hardCoreHopping` proves
`Spec.HardCoreBosonFourthMoment` (eq:muHCB, `app:mu4walks#hcb-lemma`). On any finite simple
graph with `N ≥ 4` vertices, `m` edges, `W` pairs of edges sharing a vertex, `D` pairs of
vertex-disjoint edges and `C₄` four-cycles, `n ≤ N` hard-core bosons with unit hopping have
`μ₄^HCB = (2m + 4W + 8C₄) p₁₁ + (24D + 16C₄) p₂₂`.

## Method (the paper's App. C)

* `hardCoreHopping` counts hops (`hardCoreHopping_eq`, `hopCount`), is symmetric
  (`hopCount_symm`) and preserves the particle number, so
  `Tr(H_B⁴) = ∑_{S, T} (H²)_{TS}²` (`block_sum_eq`), where `(H²)_{TS}` (`pathCount`) counts the
  two-hop paths from `S` to `T`.
* `∑_T (H²)_{TS}² = ∑_π (H²)_{end π, S}` over the two-hop paths `π` out of `S`
  (`sum_pathCount_sq`). The paths split by type (`sum_paths_decomp`): a hop and its reverse
  (end `S`), a one-particle move `x → z` through a common neighbour `y`, empty (direct) or
  occupied (relay) (`oneMoves`), and a two-particle move (`twoMoves`).
* At these ends, `(H²)_{SS} = M(S)` (`pathCount_self`), `(H²)_{S - x + z, S} = (A_G²)_{xz}`
  whatever the occupation of the common neighbours (`pathCount_oneMove`), and at the end of a
  two-particle move `u₁ → w₁, u₂ → w₂` it is `2 + 2[u₁ ~ w₂ ∧ u₂ ~ w₁]` (`pathCount_twoMove`).
* Summed over the `n`-subsets, each membership pattern of `a` occupied and `b` empty given
  sites occurs `C(N, n) p_ab` times (`card_pattern`, `patternCount_one_one_eq`,
  `patternCount_two_two_eq`; `patternCount_pascal` is `p₁₂ + p₂₁ = p₁₁`). The graph sums are
  `2m` arcs, `2W` arc pairs sharing a tail or a head and `2W` paths `x ~ y ~ z`, `8D` arc pairs
  with four distinct ends (`card_disjointArcs`), and `8C₄` four-cycle sequences
  (`sum_commonCount_wedgeSeq`, `card_disjointArcs_cross`).

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset SimpleGraph

/-! ### Counting `n`-subsets by a membership pattern -/

/-- The number of `n`-subsets of an `N`-set that contain `a` given elements and avoid `b`
other given elements: `C(N - a - b, n - a)` if `a ≤ n`, and `0` otherwise. It is
`C(N, n) · p_ab` (`patternCount_one_one_eq`, `patternCount_two_two_eq`). -/
def patternCount (N n a b : ℕ) : ℕ := if a ≤ n then (N - (a + b)).choose (n - a) else 0

section Pattern

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `n`-subsets containing `X` and avoiding `Y` (disjoint) number
`patternCount N n |X| |Y|`. -/
theorem card_pattern (X Y : Finset V) (hXY : Disjoint X Y) (n : ℕ) :
    ((powersetCard n (univ : Finset V)).filter fun S => X ⊆ S ∧ Disjoint Y S).card =
      patternCount (Fintype.card V) n X.card Y.card := by
  unfold patternCount
  split_ifs with hX
  · have h := card_trace_eq (X ∪ Y) X subset_union_left n hX
    rw [card_union_of_disjoint hXY] at h
    rw [← h]
    congr 1
    refine filter_congr fun S _ => ?_
    constructor
    · rintro ⟨hXS, hYS⟩
      ext v
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hv | hv, hvS⟩
        · exact hv
        · exact absurd hvS (disjoint_left.1 hYS hv)
      · intro hv; exact ⟨Or.inl hv, hXS hv⟩
    · intro h
      refine ⟨fun v hv => ?_, disjoint_left.2 fun v hvY hvS => ?_⟩
      · have : v ∈ (X ∪ Y) ∩ S := by rw [h]; exact hv
        exact (mem_inter.1 this).2
      · have : v ∈ (X ∪ Y) ∩ S := mem_inter.2 ⟨mem_union_right _ hvY, hvS⟩
        rw [h] at this
        exact disjoint_left.1 hXY this hvY
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro S hS hXS
    rw [mem_powersetCard] at hS
    exact hX (hS.2 ▸ card_le_card hXS.1)

end Pattern

/-- `C(N - 2, n - 1) · N(N - 1) = n(N - n) · C(N, n)`, in pattern form. -/
theorem patternCount_one_one_mul (N n : ℕ) :
    patternCount N n 1 1 * (N * (N - 1)) = n * (N - n) * N.choose n := by
  unfold patternCount
  split_ifs with h
  · simpa using choose_sub_two_mul N n h
  · obtain rfl : n = 0 := by omega
    simp

/-- `C(N - 4, n - 2) · N(N - 1)(N - 2)(N - 3) = n(n - 1)(N - n)(N - n - 1) · C(N, n)`, in
pattern form. -/
theorem patternCount_two_two_mul (N n : ℕ) :
    patternCount N n 2 2 * (N * (N - 1) * ((N - 2) * (N - 3))) =
      n * (n - 1) * ((N - n) * (N - n - 1)) * N.choose n := by
  unfold patternCount
  split_ifs with h
  · have h1 := choose_sub_two_mul N n (by omega)
    have h2 := choose_sub_two_mul (N - 2) (n - 1) (by omega)
    rw [show N - 2 - 2 = N - (2 + 2) by omega, show n - 1 - 1 = n - 2 by omega,
      show N - 2 - 1 = N - 3 by omega, show N - 2 - (n - 1) = N - n - 1 by omega] at h2
    calc (N - (2 + 2)).choose (n - 2) * (N * (N - 1) * ((N - 2) * (N - 3)))
        = (N - (2 + 2)).choose (n - 2) * ((N - 2) * (N - 3)) * (N * (N - 1)) := by ring
      _ = (n - 1) * (N - n - 1) * ((N - 2).choose (n - 1) * (N * (N - 1))) := by
          rw [h2]; ring
      _ = n * (n - 1) * ((N - n) * (N - n - 1)) * N.choose n := by rw [h1]; ring
  · obtain h' : n = 0 ∨ n = 1 := by omega
    rcases h' with rfl | rfl <;> simp

theorem patternCount_one_one_eq (N n : ℕ) (hN : 2 ≤ N) :
    (patternCount N n 1 1 : ℝ) = N.choose n * occProb N n 1 1 := by
  have e2 : N.descFactorial (1 + 1) = N * (N - 1) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, mul_comm]
  have hd : ((N * (N - 1) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < N * (N - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this.ne'
  rw [occProb, e2, mul_div_assoc', eq_div_iff hd, Nat.descFactorial_one, Nat.descFactorial_one]
  have h := patternCount_one_one_mul N n
  have : ((patternCount N n 1 1 * (N * (N - 1)) : ℕ) : ℝ) = ((n * (N - n) * N.choose n : ℕ) : ℝ) :=
    by rw [h]
  push_cast at this ⊢
  linarith

theorem patternCount_two_two_eq (N n : ℕ) (hN : 4 ≤ N) :
    (patternCount N n 2 2 : ℝ) = N.choose n * occProb N n 2 2 := by
  have e2 : ∀ M : ℕ, M.descFactorial 2 = M * (M - 1) := by
    intro M; rw [Nat.descFactorial_succ, Nat.descFactorial_one, mul_comm]
  have e4 : N.descFactorial (2 + 2) = N * (N - 1) * ((N - 2) * (N - 3)) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]; ring
  have hd : ((N * (N - 1) * ((N - 2) * (N - 3)) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < N * (N - 1) * ((N - 2) * (N - 3)) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (Nat.mul_pos (by omega) (by omega))
    exact_mod_cast this.ne'
  rw [occProb, e4, mul_div_assoc', eq_div_iff hd, e2, e2]
  have h := patternCount_two_two_mul N n
  have : ((patternCount N n 2 2 * (N * (N - 1) * ((N - 2) * (N - 3))) : ℕ) : ℝ) =
      ((n * (n - 1) * ((N - n) * (N - n - 1)) * N.choose n : ℕ) : ℝ) := by rw [h]
  rw [show N - n - 1 = N - n - 1 from rfl] at this
  push_cast [Nat.cast_mul] at this ⊢
  nlinarith [this]

/-- Pascal's rule in pattern form: `C(N - 3, n - 1) + C(N - 3, n - 2) = C(N - 2, n - 1)`. -/
theorem patternCount_pascal (N n : ℕ) (hN : 3 ≤ N) :
    patternCount N n 1 2 + patternCount N n 2 1 = patternCount N n 1 1 := by
  unfold patternCount
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [show 1 ≤ k + 2 by omega, show 2 ≤ k + 2 by omega, ↓reduceIte,
      show M + 3 - (1 + 2) = M by omega,
      show M + 3 - (1 + 1) = M + 1 by omega, show k + 2 - 1 = k + 1 by omega,
      show k + 2 - 2 = k by omega, Nat.choose_succ_succ]
    ring

/-! ### One hop, and the hard-core-boson matrix as a count -/

section Hops

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The configuration after the hop `p`: the particle at `p.1` moves to `p.2`. -/
def hopTo (S : Finset V) (p : V × V) : Finset V := insert p.2 (S.erase p.1)

omit [Fintype V] in
theorem mem_hopTo {S : Finset V} {p : V × V} {v : V} :
    v ∈ hopTo S p ↔ v = p.2 ∨ (v ≠ p.1 ∧ v ∈ S) := by
  simp [hopTo, mem_insert, mem_erase]

theorem mem_hops {S : Finset V} {p : V × V} :
    p ∈ hops G S ↔ G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S := by
  simp [hops, arcs, mem_filter]

theorem hops_subset_arcs (S : Finset V) : hops G S ⊆ arcs G := filter_subset _ _

theorem card_hopTo {S : Finset V} {p : V × V} (hp : p ∈ hops G S) :
    (hopTo S p).card = S.card := by
  rw [mem_hops] at hp
  have h1 : p.2 ∉ S.erase p.1 := fun h => hp.2.2 (mem_of_mem_erase h)
  rw [hopTo, card_insert_of_notMem h1, card_erase_of_mem hp.2.1]
  have : 0 < S.card := card_pos.2 ⟨_, hp.2.1⟩
  omega

/-- Hopping back undoes a hop. -/
theorem hopTo_hopTo_swap {S : Finset V} {p : V × V} (hp : p ∈ hops G S) :
    hopTo (hopTo S p) (p.2, p.1) = S := by
  rw [mem_hops] at hp
  obtain ⟨hadj, h1, h2⟩ := hp
  have hne : p.1 ≠ p.2 := hadj.ne
  ext v
  simp only [mem_hopTo]
  constructor
  · rintro (rfl | ⟨hv, rfl | ⟨_, hvS⟩⟩)
    · exact h1
    · exact absurd rfl hv
    · exact hvS
  · intro hvS
    by_cases hv : v = p.1
    · exact Or.inl hv
    · exact Or.inr ⟨fun h => h2 (h ▸ hvS), Or.inr ⟨hv, hvS⟩⟩

/-- The hop back is a hop. -/
theorem swap_mem_hops {S : Finset V} {p : V × V} (hp : p ∈ hops G S) :
    (p.2, p.1) ∈ hops G (hopTo S p) := by
  rw [mem_hops] at hp ⊢
  obtain ⟨hadj, h1, h2⟩ := hp
  refine ⟨hadj.symm, ?_, ?_⟩
  · exact mem_hopTo.2 (Or.inl rfl)
  · rw [mem_hopTo]
    rintro (h | ⟨h, _⟩)
    · exact hadj.ne h
    · exact h rfl

omit [Fintype V] in
/-- Two hops out of `S` with the same result are equal. -/
theorem hopTo_inj {S : Finset V} {x x' z z' : V} (hx : x ∈ S) (hx' : x' ∈ S) (hz : z ∉ S)
    (hz' : z' ∉ S) : hopTo S (x, z) = hopTo S (x', z') ↔ x = x' ∧ z = z' := by
  constructor
  · intro h
    have hzx : z ≠ x := fun h' => hz (h' ▸ hx)
    have hzx' : z' ≠ x' := fun h' => hz' (h' ▸ hx')
    have hz1 : z ∈ hopTo S (x', z') := h ▸ mem_hopTo.2 (Or.inl rfl)
    rw [mem_hopTo] at hz1
    have hzz : z = z' := by
      rcases hz1 with h1 | ⟨_, h1⟩
      · exact h1
      · exact absurd h1 hz
    refine ⟨?_, hzz⟩
    by_contra hxx
    have : x ∈ hopTo S (x', z') := mem_hopTo.2 (Or.inr ⟨hxx, hx⟩)
    rw [← h, mem_hopTo] at this
    rcases this with h1 | ⟨h1, _⟩
    · exact hzx h1.symm
    · exact h1 rfl
  · rintro ⟨rfl, rfl⟩; rfl

theorem hopTo_injOn {S : Finset V} {p q : V × V} (hp : p ∈ hops G S) (hq : q ∈ hops G S)
    (h : hopTo S p = hopTo S q) : p = q := by
  rw [mem_hops] at hp hq
  have := (hopTo_inj (S := S) (x := p.1) (z := p.2) hp.2.1 hq.2.1 hp.2.2 hq.2.2).1 h
  exact Prod.ext this.1 this.2

/-- The number of hops from `S` to `T`: `1` if `T` is one hop from `S`, `0` otherwise. -/
def hopCount (T S : Finset V) : ℕ := ((hops G S).filter fun p => T = hopTo S p).card

theorem hopCount_eq (T S : Finset V) :
    hopCount G T S = if ∃ p ∈ hops G S, T = hopTo S p then 1 else 0 := by
  have hle : hopCount G T S ≤ 1 := by
    rw [hopCount, card_le_one]
    intro p hp q hq
    rw [mem_filter] at hp hq
    exact hopTo_injOn G hp.1 hq.1 (hp.2.symm.trans hq.2)
  split_ifs with h
  · obtain ⟨p, hp, hT⟩ := h
    have : 0 < hopCount G T S := card_pos.2 ⟨p, mem_filter.2 ⟨hp, hT⟩⟩
    omega
  · rw [hopCount, card_eq_zero, filter_eq_empty_iff]
    exact fun p hp hT => h ⟨p, hp, hT⟩

theorem hardCoreHopping_eq (T S : Finset V) :
    hardCoreHopping G T S = (hopCount G T S : ℂ) := by
  rw [hopCount_eq]
  show (if ∃ p ∈ hops G S, T = hopTo S p then (1 : ℂ) else 0) = _
  split_ifs <;> simp

theorem hopCount_symm (T S : Finset V) : hopCount G T S = hopCount G S T := by
  have key : ∀ T S : Finset V, (∃ p ∈ hops G S, T = hopTo S p) →
      ∃ q ∈ hops G T, S = hopTo T q := by
    rintro T S ⟨p, hp, rfl⟩
    exact ⟨(p.2, p.1), swap_mem_hops G hp, (hopTo_hopTo_swap G hp).symm⟩
  rw [hopCount_eq, hopCount_eq]
  by_cases h : ∃ p ∈ hops G S, T = hopTo S p
  · rw [ite_eq_left h, ite_eq_left (key T S h)]
  · have h' : ¬ ∃ q ∈ hops G T, S = hopTo T q := fun h' => h (key S T h')
    rw [ite_eq_right h, ite_eq_right h']

end Hops

/-! ### Two-hop paths -/

section Paths

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two-hop paths out of `S`: a hop `π.1` out of `S`, then a hop `π.2` out of the result. -/
def paths (S : Finset V) : Finset ((V × V) × (V × V)) :=
  (arcs G ×ˢ arcs G).filter fun π => π.1 ∈ hops G S ∧ π.2 ∈ hops G (hopTo S π.1)

/-- The end of a two-hop path out of `S`. -/
def pathEnd (S : Finset V) (π : (V × V) × (V × V)) : Finset V := hopTo (hopTo S π.1) π.2

theorem mem_paths {S : Finset V} {π : (V × V) × (V × V)} :
    π ∈ paths G S ↔ π.1 ∈ hops G S ∧ π.2 ∈ hops G (hopTo S π.1) := by
  rw [paths, mem_filter, mem_product]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨hops_subset_arcs G _ h.1, hops_subset_arcs G _ h.2⟩, h⟩

theorem card_pathEnd {S : Finset V} {π : (V × V) × (V × V)} (hπ : π ∈ paths G S) :
    (pathEnd S π).card = S.card := by
  rw [mem_paths] at hπ
  rw [pathEnd, card_hopTo G hπ.2, card_hopTo G hπ.1]

/-- A sum over the paths is a double sum over the hops. -/
theorem sum_paths {M : Type*} [AddCommMonoid M] (S : Finset V) (f : (V × V) × (V × V) → M) :
    ∑ π ∈ paths G S, f π = ∑ p ∈ hops G S, ∑ q ∈ hops G (hopTo S p), f (p, q) := by
  rw [paths, sum_filter, sum_product]
  have hA : ∀ (X : Finset V) (g : V × V → M),
      ∑ q ∈ hops G X, g q = ∑ q ∈ arcs G, if q ∈ hops G X then g q else 0 := by
    intro X g
    rw [← sum_filter]
    congr 1
    ext q; simp only [mem_filter]
    exact ⟨fun h => ⟨hops_subset_arcs G X h, h⟩, fun h => h.2⟩
  rw [hA]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : p ∈ hops G S
  · rw [ite_eq_left hp, hA]
    refine sum_congr rfl fun q _ => ?_
    simp only [hp, true_and]
  · rw [ite_eq_right hp]
    exact sum_eq_zero fun q _ => by simp [hp]

/-- The number of two-hop paths from `S` to `T`. -/
def pathCount (T S : Finset V) : ℕ := ((paths G S).filter fun π => T = pathEnd S π).card

theorem pathCount_eq_sum (T S : Finset V) :
    pathCount G T S = ∑ π ∈ paths G S, if T = pathEnd S π then 1 else 0 := by
  rw [pathCount, card_filter]

/-- `∑_R h(T, R) h(R, S)`, over the `n`-subsets `R`, counts the two-hop paths from `S` to `T`. -/
theorem sum_hopCount_mul {n : ℕ} (T S : Finset V) (hS : S.card = n) :
    ∑ R ∈ powersetCard n (univ : Finset V), hopCount G T R * hopCount G R S =
      pathCount G T S := by
  have h1 : ∀ R, hopCount G R S = ∑ p ∈ hops G S, if R = hopTo S p then 1 else 0 := by
    intro R; rw [hopCount, card_filter]
  simp_rw [h1, mul_sum, mul_ite, mul_one, mul_zero]
  rw [sum_comm]
  have h2 : ∀ p ∈ hops G S, (∑ R ∈ powersetCard n (univ : Finset V),
      if R = hopTo S p then hopCount G T R else 0) = hopCount G T (hopTo S p) := by
    intro p hp
    rw [sum_ite_eq']
    rw [ite_eq_left (mem_powersetCard.2 ⟨subset_univ _, (card_hopTo G hp).trans hS⟩)]
  rw [sum_congr rfl h2, pathCount_eq_sum, sum_paths]
  refine sum_congr rfl fun p _ => ?_
  rw [hopCount, card_filter]
  rfl

end Paths

/-! ### The fourth moment as a sum of squared path counts -/

section Block

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Tr(H_B⁴) = ∑_{S, T} (H²)_{TS}²`, with `H` symmetric and `(H²)_{TS}` the number of two-hop
paths from `S` to `T`. -/
theorem block_sum_eq (n : ℕ) :
    ∑ c ∈ powersetCard n (univ : Finset V), ∑ b₁ ∈ powersetCard n (univ : Finset V),
        ∑ b₂ ∈ powersetCard n (univ : Finset V), ∑ b₃ ∈ powersetCard n (univ : Finset V),
          hopCount G c b₁ * hopCount G b₁ b₂ * hopCount G b₂ b₃ * hopCount G b₃ c =
      ∑ S ∈ powersetCard n (univ : Finset V), ∑ T ∈ powersetCard n (univ : Finset V),
        pathCount G T S ^ 2 := by
  set B := powersetCard n (univ : Finset V)
  have hB : ∀ S ∈ B, S.card = n := fun S hS => (mem_powersetCard.1 hS).2
  calc _ = ∑ c ∈ B, ∑ b₂ ∈ B, (∑ b₁ ∈ B, hopCount G c b₁ * hopCount G b₁ b₂) *
            (∑ b₃ ∈ B, hopCount G b₂ b₃ * hopCount G b₃ c) := by
        refine sum_congr rfl fun c _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun b₂ _ => ?_
        rw [sum_mul_sum]
        refine sum_congr rfl fun b₁ _ => sum_congr rfl fun b₃ _ => ?_
        ring
    _ = ∑ c ∈ B, ∑ b₂ ∈ B, pathCount G c b₂ ^ 2 := by
        refine sum_congr rfl fun c _ => sum_congr rfl fun b₂ hb₂ => ?_
        rw [sum_hopCount_mul G c b₂ (hB b₂ hb₂)]
        have : ∑ b₃ ∈ B, hopCount G b₂ b₃ * hopCount G b₃ c = pathCount G c b₂ := by
          rw [← sum_hopCount_mul G c b₂ (hB b₂ hb₂)]
          refine sum_congr rfl fun b₃ _ => ?_
          rw [hopCount_symm G b₂ b₃, hopCount_symm G b₃ c, mul_comm]
        rw [this, sq]
    _ = _ := sum_comm

/-- `∑_T (H²)_{TS}² = ∑_π (H²)_{end π, S}`, over the two-hop paths `π` out of `S`. -/
theorem sum_pathCount_sq {n : ℕ} (S : Finset V) (hS : S.card = n) :
    ∑ T ∈ powersetCard n (univ : Finset V), pathCount G T S ^ 2 =
      ∑ π ∈ paths G S, pathCount G (pathEnd S π) S := by
  have h : ∀ T, pathCount G T S ^ 2 =
      ∑ π ∈ paths G S, if T = pathEnd S π then pathCount G T S else 0 := by
    intro T
    rw [sq]
    nth_rewrite 1 [pathCount_eq_sum]
    rw [sum_mul]
    refine sum_congr rfl fun π _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl fun T _ => h T, sum_comm]
  refine sum_congr rfl fun π hπ => ?_
  rw [sum_ite_eq', ite_eq_left (mem_powersetCard.2 ⟨subset_univ _, (card_pathEnd G hπ).trans hS⟩)]

end Block

/-! ### The two-hop paths by type -/

section Types

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- A particle moves `x → y → z` through an empty site `y`. -/
theorem hopTo_hopTo_empty {S : Finset V} {x y z : V} (hx : x ∈ S) (hy : y ∉ S) (hz : z ∉ S)
    (hyz : y ≠ z) : hopTo (hopTo S (x, y)) (y, z) = hopTo S (x, z) := by
  ext v
  simp only [mem_hopTo]
  by_cases h1 : v = x <;> by_cases h2 : v = y <;> by_cases h3 : v = z <;> simp_all

omit [Fintype V] in
/-- The particle at `y` moves to `z`, then the particle at `x` moves to `y`: the net move is
`x → z`. -/
theorem hopTo_hopTo_occupied {S : Finset V} {x y z : V} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∉ S)
    (hxy : x ≠ y) : hopTo (hopTo S (y, z)) (x, y) = hopTo S (x, z) := by
  ext v
  simp only [mem_hopTo]
  by_cases h1 : v = x <;> by_cases h2 : v = y <;> by_cases h3 : v = z <;> simp_all

theorem mem_paths_iff {S : Finset V} {u₁ w₁ u₂ w₂ : V} :
    ((u₁, w₁), (u₂, w₂)) ∈ paths G S ↔ G.Adj u₁ w₁ ∧ u₁ ∈ S ∧ w₁ ∉ S ∧ G.Adj u₂ w₂ ∧
      (u₂ = w₁ ∨ (u₂ ≠ u₁ ∧ u₂ ∈ S)) ∧ w₂ ≠ w₁ ∧ (w₂ = u₁ ∨ w₂ ∉ S) := by
  rw [mem_paths, mem_hops, mem_hops, mem_hopTo, mem_hopTo]
  simp only [not_or, not_and]
  tauto

/-- The one-particle moves out of `S`: triples `x ~ y ~ z` with `x` occupied and `z` empty. The
particle at `x` reaches `z` through `y`: directly if `y` is empty, by a relay if it is
occupied. -/
def oneMoves (S : Finset V) : Finset (V × V × V) :=
  univ.filter fun t => t.1 ∈ S ∧ t.2.2 ∉ S ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2

/-- The two-hop paths that move two different particles. -/
def twoMoves (S : Finset V) : Finset ((V × V) × (V × V)) :=
  (paths G S).filter fun π => π.2.1 ≠ π.1.2 ∧ π.2.2 ≠ π.1.1

theorem mem_oneMoves {S : Finset V} {t : V × V × V} :
    t ∈ oneMoves G S ↔ t.1 ∈ S ∧ t.2.2 ∉ S ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 := by
  simp [oneMoves]

theorem mem_twoMoves_iff {S : Finset V} {u₁ w₁ u₂ w₂ : V} :
    ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G S ↔ G.Adj u₁ w₁ ∧ G.Adj u₂ w₂ ∧ u₁ ∈ S ∧ u₂ ∈ S ∧
      w₁ ∉ S ∧ w₂ ∉ S ∧ u₁ ≠ u₂ ∧ w₁ ≠ w₂ := by
  rw [twoMoves, mem_filter, mem_paths_iff]
  simp only
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9⟩
    have hu₂ : u₂ ≠ u₁ ∧ u₂ ∈ S := h5.resolve_left h8
    have hw₂ : w₂ ∉ S := h7.resolve_left h9
    exact ⟨h1, h4, h2, hu₂.2, h3, hw₂, hu₂.1.symm, h6.symm⟩
  · rintro ⟨h1, h4, h2, hu₂, h3, hw₂, hu, hw⟩
    have h8 : u₂ ≠ w₁ := fun h => h3 (h ▸ hu₂)
    have h9 : w₂ ≠ u₁ := fun h => hw₂ (h ▸ h2)
    exact ⟨⟨h1, h2, h3, h4, Or.inr ⟨Ne.symm hu, hu₂⟩, Ne.symm hw, Or.inr hw₂⟩, h8, h9⟩

/-- **The paths by type.** A sum over the two-hop paths out of `S` of a function of their end
splits into: the `|hops S|` paths that hop back (end `S`), the one-particle moves (end
`S - x + z`), and the two-particle moves. -/
theorem sum_paths_decomp {M : Type*} [AddCommMonoid M] (S : Finset V) (g : Finset V → M) :
    ∑ π ∈ paths G S, g (pathEnd S π) =
      (hops G S).card • g S + ∑ t ∈ oneMoves G S, g (hopTo S (t.1, t.2.2)) +
        ∑ π ∈ twoMoves G S, g (pathEnd S π) := by
  set P := paths G S
  rw [← sum_filter_add_sum_filter_not P (fun π => π.2.1 = π.1.2),
    ← sum_filter_add_sum_filter_not (P.filter fun π => π.2.1 = π.1.2) (fun π => π.2.2 = π.1.1),
    ← sum_filter_add_sum_filter_not (P.filter fun π => ¬ π.2.1 = π.1.2) (fun π => π.2.2 = π.1.1),
    ← sum_filter_add_sum_filter_not (oneMoves G S) (fun t => t.2.1 ∉ S)]
  -- hop back
  have hA : ∑ π ∈ (P.filter fun π => π.2.1 = π.1.2).filter (fun π => π.2.2 = π.1.1),
      g (pathEnd S π) = (hops G S).card • g S := by
    rw [sum_congr rfl fun π hπ => ?_, sum_const]
    · congr 1
      refine card_nbij' (fun π => π.1) (fun p => (p, (p.2, p.1))) ?_ ?_ ?_ ?_
      · intro π hπ
        rw [mem_coe, mem_filter, mem_filter] at hπ
        exact mem_coe.2 ((mem_paths G).1 hπ.1.1).1
      · intro p hp
        rw [mem_coe] at hp
        rw [mem_coe, mem_filter, mem_filter]
        exact ⟨⟨(mem_paths G).2 ⟨hp, swap_mem_hops G hp⟩, rfl⟩, rfl⟩
      · intro π hπ
        rw [mem_coe, mem_filter, mem_filter] at hπ
        obtain ⟨⟨_, h1⟩, h2⟩ := hπ
        rcases π with ⟨⟨a, b⟩, ⟨c, d⟩⟩
        simp only at h1 h2 ⊢
        rw [h1, h2]
      · intro p _; rfl
    · simp only [mem_filter, P] at hπ
      obtain ⟨⟨hπ, h1⟩, h2⟩ := hπ
      have hp := ((mem_paths G).1 hπ).1
      rcases π with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only at h1 h2 hp ⊢
      have hs := hopTo_hopTo_swap G hp
      simp only at hs
      rw [pathEnd, h1, h2]
      simp only
      rw [hs]
  -- through an empty site
  have hB : ∑ π ∈ (P.filter fun π => π.2.1 = π.1.2).filter (fun π => ¬ π.2.2 = π.1.1),
      g (pathEnd S π) = ∑ t ∈ (oneMoves G S).filter (fun t => t.2.1 ∉ S),
        g (hopTo S (t.1, t.2.2)) := by
    refine sum_nbij' (fun π => (π.1.1, π.1.2, π.2.2)) (fun t => ((t.1, t.2.1), (t.2.1, t.2.2)))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ
      simp only [mem_filter, P, mem_paths_iff] at hπ
      obtain ⟨⟨⟨h1, h2, h3, h4, _, _, h7⟩, rfl⟩, h9⟩ := hπ
      simp only [mem_filter, mem_oneMoves]
      exact ⟨⟨h2, h7.resolve_left h9, h1, h4⟩, h3⟩
    · rintro ⟨x, y, z⟩ ht
      simp only [mem_filter, mem_oneMoves] at ht
      obtain ⟨⟨hx, hz, hxy, hyz⟩, hy⟩ := ht
      simp only [mem_filter, P, mem_paths_iff]
      refine ⟨⟨⟨hxy, hx, hy, hyz, by simp, hyz.ne.symm, Or.inr hz⟩, by simp⟩, ?_⟩
      exact fun h => hz (h ▸ hx)
    · rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ
      simp only [mem_filter, P] at hπ
      obtain ⟨⟨_, h⟩, _⟩ := hπ
      simp only at h ⊢
      rw [h]
    · rintro ⟨x, y, z⟩ _; rfl
    · rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ
      simp only [mem_filter, P, mem_paths_iff] at hπ
      obtain ⟨⟨⟨h1, h2, h3, h4, _, h6, h7⟩, rfl⟩, h9⟩ := hπ
      simp only [pathEnd]
      rw [hopTo_hopTo_empty h2 h3 (h7.resolve_left h9) h6.symm]
  -- by a relay through an occupied site
  have hC : ∑ π ∈ (P.filter fun π => ¬ π.2.1 = π.1.2).filter (fun π => π.2.2 = π.1.1),
      g (pathEnd S π) = ∑ t ∈ (oneMoves G S).filter (fun t => ¬ t.2.1 ∉ S),
        g (hopTo S (t.1, t.2.2)) := by
    refine sum_nbij' (fun π => (π.2.1, π.1.1, π.1.2)) (fun t => ((t.2.1, t.2.2), (t.1, t.2.1)))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ
      simp only [mem_filter, P, mem_paths_iff] at hπ
      obtain ⟨⟨⟨h1, h2, h3, h4, h5, _, _⟩, h8⟩, rfl⟩ := hπ
      simp only [mem_filter, mem_oneMoves, not_not]
      exact ⟨⟨(h5.resolve_left h8).2, h3, h4, h1⟩, h2⟩
    · rintro ⟨x, y, z⟩ ht
      simp only [mem_filter, mem_oneMoves, not_not] at ht
      obtain ⟨⟨hx, hz, hxy, hyz⟩, hy⟩ := ht
      simp only [mem_filter, P, mem_paths_iff]
      refine ⟨⟨⟨hyz, hy, hz, hxy, Or.inr ⟨hxy.ne, hx⟩, hyz.ne, by simp⟩, ?_⟩, by simp⟩
      exact fun h => hz (h ▸ hx)
    · rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ
      simp only [mem_filter, P] at hπ
      obtain ⟨_, h⟩ := hπ
      simp only at h ⊢
      rw [h]
    · rintro ⟨x, y, z⟩ _; rfl
    · rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ
      simp only [mem_filter, P, mem_paths_iff] at hπ
      obtain ⟨⟨⟨h1, h2, h3, h4, h5, _, _⟩, h8⟩, rfl⟩ := hπ
      simp only [pathEnd]
      rw [hopTo_hopTo_occupied (h5.resolve_left h8).2 h2 h3 h4.ne]
  have hD : (P.filter fun π => ¬ π.2.1 = π.1.2).filter (fun π => ¬ π.2.2 = π.1.1) =
      twoMoves G S := by
    rw [twoMoves, filter_filter]
  rw [hA, hB, hC, hD]
  abel

end Types

/-! ### The path counts at the ends of the paths -/

section Values

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of common neighbours of `x` and `z`, `(A_G²)_{xz}` for `x ≠ z`. -/
def commonCount (x z : V) : ℕ := (univ.filter fun y => G.Adj x y ∧ G.Adj y z).card

theorem pathCount_decomp (T S : Finset V) :
    pathCount G T S = (hops G S).card * (if T = S then 1 else 0) +
      ((oneMoves G S).filter fun t => T = hopTo S (t.1, t.2.2)).card +
      ((twoMoves G S).filter fun π => T = pathEnd S π).card := by
  rw [pathCount_eq_sum, sum_paths_decomp G S (fun X => if T = X then 1 else 0), smul_eq_mul,
    card_filter, card_filter]

theorem mem_pathEnd_two {S : Finset V} {u₁ w₁ u₂ w₂ : V}
    (h : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G S) {v : V} :
    v ∈ pathEnd S ((u₁, w₁), (u₂, w₂)) ↔ v = w₁ ∨ v = w₂ ∨ (v ∈ S ∧ v ≠ u₁ ∧ v ≠ u₂) := by
  rw [mem_twoMoves_iff] at h
  obtain ⟨h1, h2, hu1, hu2, hw1, hw2, hu, hw⟩ := h
  simp only [pathEnd, mem_hopTo]
  by_cases a : v = u₁ <;> by_cases b : v = u₂ <;> by_cases c : v = w₁ <;> by_cases d : v = w₂ <;>
    simp_all

/-- A one-particle move and a two-particle move never end at the same configuration. -/
theorem hopTo_ne_pathEnd {S : Finset V} {x z u₁ w₁ u₂ w₂ : V}
    (hπ : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G S) :
    hopTo S (x, z) ≠ pathEnd S ((u₁, w₁), (u₂, w₂)) := by
  intro h
  obtain ⟨_, _, hu1, hu2, hw1, hw2, hu, _⟩ := (mem_twoMoves_iff G).1 hπ
  have key : ∀ u, u ∈ S → u ≠ x → (u = u₁ ∨ u = u₂) → False := by
    intro u hu' hux hu12
    have h1 : u ∈ hopTo S (x, z) := mem_hopTo.2 (Or.inr ⟨hux, hu'⟩)
    rw [h, mem_pathEnd_two G hπ] at h1
    rcases h1 with h1 | h1 | h1
    · exact hw1 (h1 ▸ hu')
    · exact hw2 (h1 ▸ hu')
    · rcases hu12 with h2 | h2
      · exact h1.2.1 h2
      · exact h1.2.2 h2
  by_cases h1 : u₁ = x
  · exact key u₂ hu2 (fun h2 => hu (h1.trans h2.symm)) (Or.inr rfl)
  · exact key u₁ hu1 h1 (Or.inl rfl)

/-- `(H²)_{SS} = |hops S|`. -/
theorem pathCount_self (S : Finset V) : pathCount G S S = (hops G S).card := by
  rw [pathCount_decomp]
  have h1 : ((oneMoves G S).filter fun t => S = hopTo S (t.1, t.2.2)) = ∅ := by
    rw [filter_eq_empty_iff]
    rintro ⟨x, y, z⟩ ht h
    rw [mem_oneMoves] at ht
    have : z ∈ hopTo S (x, z) := mem_hopTo.2 (Or.inl rfl)
    rw [← h] at this
    exact ht.2.1 this
  have h2 : ((twoMoves G S).filter fun π => S = pathEnd S π) = ∅ := by
    rw [filter_eq_empty_iff]
    rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ h
    have hw : w₁ ∈ pathEnd S ((u₁, w₁), (u₂, w₂)) := (mem_pathEnd_two G hπ).2 (Or.inl rfl)
    rw [← h] at hw
    exact ((mem_twoMoves_iff G).1 hπ).2.2.2.2.1 hw
  rw [h1, h2]
  simp

/-- `(H²)_{S - x + z, S}` is the number of common neighbours of `x` and `z`. -/
theorem pathCount_oneMove {S : Finset V} {t : V × V × V} (ht : t ∈ oneMoves G S) :
    pathCount G (hopTo S (t.1, t.2.2)) S = commonCount G t.1 t.2.2 := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_oneMoves] at ht
  obtain ⟨hx, hz, hxy, hyz⟩ := ht
  simp only
  rw [pathCount_decomp]
  have h0 : hopTo S (x, z) ≠ S := fun h => hz (h ▸ mem_hopTo.2 (Or.inl rfl))
  have h2 : ((twoMoves G S).filter fun π => hopTo S (x, z) = pathEnd S π) = ∅ := by
    rw [filter_eq_empty_iff]
    rintro ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩ hπ h
    exact hopTo_ne_pathEnd G hπ h
  have h1 : ((oneMoves G S).filter fun t' => hopTo S (x, z) = hopTo S (t'.1, t'.2.2)).card =
      commonCount G x z := by
    unfold commonCount
    refine card_nbij' (fun t' => t'.2.1) (fun y' => (x, y', z)) ?_ ?_ ?_ ?_
    · rintro ⟨x', y', z'⟩ h
      rw [mem_coe, mem_filter, mem_oneMoves] at h
      obtain ⟨⟨hx', hz', hxy', hyz'⟩, he⟩ := h
      obtain ⟨rfl, rfl⟩ := (hopTo_inj hx hx' hz hz').1 he
      simp [hxy', hyz']
    · intro y' hy'
      rw [mem_coe, mem_filter] at hy'
      rw [mem_coe, mem_filter, mem_oneMoves]
      exact ⟨⟨hx, hz, hy'.2.1, hy'.2.2⟩, rfl⟩
    · rintro ⟨x', y', z'⟩ h
      rw [mem_coe, mem_filter, mem_oneMoves] at h
      obtain ⟨⟨hx', hz', _, _⟩, he⟩ := h
      obtain ⟨rfl, rfl⟩ := (hopTo_inj hx hx' hz hz').1 he
      rfl
    · intro y' _; rfl
  rw [h1, h2, ite_eq_right h0]
  simp

/-- A two-particle move `(u₁ → w₁, u₂ → w₂)` reaches its end by exactly the paths that move
`{u₁, u₂}` onto `{w₁, w₂}`: these four, when they are paths. -/
theorem pathEnd_eq_iff {S : Finset V} {u₁ w₁ u₂ w₂ a₁ b₁ a₂ b₂ : V}
    (hπ : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G S) (hπ' : ((a₁, b₁), (a₂, b₂)) ∈ twoMoves G S) :
    pathEnd S ((u₁, w₁), (u₂, w₂)) = pathEnd S ((a₁, b₁), (a₂, b₂)) ↔
      ((a₁, b₁), (a₂, b₂)) ∈ ({((u₁, w₁), (u₂, w₂)), ((u₂, w₂), (u₁, w₁)),
        ((u₁, w₂), (u₂, w₁)), ((u₂, w₁), (u₁, w₂))} : Finset ((V × V) × (V × V))) := by
  obtain ⟨_, _, hu1, hu2, hw1, hw2, hu, hw⟩ := (mem_twoMoves_iff G).1 hπ
  obtain ⟨_, _, ha1, ha2, hb1, hb2, ha, hb⟩ := (mem_twoMoves_iff G).1 hπ'
  constructor
  · intro h
    have hm : ∀ v, (v = w₁ ∨ v = w₂ ∨ (v ∈ S ∧ v ≠ u₁ ∧ v ≠ u₂)) ↔
        (v = b₁ ∨ v = b₂ ∨ (v ∈ S ∧ v ≠ a₁ ∧ v ≠ a₂)) := by
      intro v
      rw [← mem_pathEnd_two G hπ, ← mem_pathEnd_two G hπ', h]
    have hA : ∀ a, a ∈ S → (a = a₁ ∨ a = a₂) → a = u₁ ∨ a = u₂ := by
      intro a haS ha12
      by_contra hne
      push Not at hne
      have := (hm a).1 (Or.inr (Or.inr ⟨haS, hne.1, hne.2⟩))
      rcases this with h1 | h1 | h1
      · exact hb1 (h1 ▸ haS)
      · exact hb2 (h1 ▸ haS)
      · rcases ha12 with h2 | h2
        · exact h1.2.1 h2
        · exact h1.2.2 h2
    have hB : ∀ b, (b = b₁ ∨ b = b₂) → b ∉ S → b = w₁ ∨ b = w₂ := by
      intro b hb12 hbS
      have := (hm b).2 (by rcases hb12 with h1 | h1 <;> simp [h1])
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h1.1 hbS
    have e1 := hA a₁ ha1 (Or.inl rfl)
    have e2 := hA a₂ ha2 (Or.inr rfl)
    have f1 := hB b₁ (Or.inl rfl) hb1
    have f2 := hB b₂ (Or.inr rfl) hb2
    simp only [mem_insert, mem_singleton, Prod.mk.injEq]
    rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> rcases f1 with rfl | rfl <;>
      rcases f2 with rfl | rfl <;> simp_all
  · intro h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
    ext v
    rw [mem_pathEnd_two G hπ, mem_pathEnd_two G hπ']
    rcases h with ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ |
      ⟨⟨rfl, rfl⟩, rfl, rfl⟩ <;> tauto

/-- `(H²)_{end, S} = 2 + 2 [u₁ ~ w₂ ∧ u₂ ~ w₁]` at the end of a two-particle move. -/
theorem pathCount_twoMove {S : Finset V} {u₁ w₁ u₂ w₂ : V}
    (hπ : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G S) :
    pathCount G (pathEnd S ((u₁, w₁), (u₂, w₂))) S =
      2 + 2 * (if G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ then 1 else 0) := by
  obtain ⟨h1, h2, hu1, hu2, hw1, hw2, hu, hw⟩ := (mem_twoMoves_iff G).1 hπ
  rw [pathCount_decomp]
  have h0 : pathEnd S ((u₁, w₁), (u₂, w₂)) ≠ S := by
    intro h
    have : w₁ ∈ pathEnd S ((u₁, w₁), (u₂, w₂)) := (mem_pathEnd_two G hπ).2 (Or.inl rfl)
    rw [h] at this
    exact hw1 this
  have hone : ((oneMoves G S).filter fun t =>
      pathEnd S ((u₁, w₁), (u₂, w₂)) = hopTo S (t.1, t.2.2)) = ∅ := by
    rw [filter_eq_empty_iff]
    rintro ⟨x, y, z⟩ ht h
    exact hopTo_ne_pathEnd G hπ h.symm
  set c₁ : (V × V) × (V × V) := ((u₁, w₁), (u₂, w₂))
  set c₂ : (V × V) × (V × V) := ((u₂, w₂), (u₁, w₁))
  set c₃ : (V × V) × (V × V) := ((u₁, w₂), (u₂, w₁))
  set c₄ : (V × V) × (V × V) := ((u₂, w₁), (u₁, w₂))
  have htwo : ((twoMoves G S).filter fun π => pathEnd S c₁ = pathEnd S π) =
      ({c₁, c₂, c₃, c₄} : Finset _).filter (· ∈ twoMoves G S) := by
    ext ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩
    rw [mem_filter, mem_filter]
    constructor
    · rintro ⟨hπ', h⟩
      exact ⟨(pathEnd_eq_iff G hπ hπ').1 h, hπ'⟩
    · rintro ⟨h, hπ'⟩
      exact ⟨hπ', (pathEnd_eq_iff G hπ hπ').2 h⟩
  have m₂ : c₂ ∈ twoMoves G S := (mem_twoMoves_iff G).2 ⟨h2, h1, hu2, hu1, hw2, hw1, hu.symm, hw.symm⟩
  have m₃ : c₃ ∈ twoMoves G S ↔ G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ := by
    rw [mem_twoMoves_iff]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · exact fun h => ⟨h.1, h.2, hu1, hu2, hw2, hw1, hu, hw.symm⟩
  have m₄ : c₄ ∈ twoMoves G S ↔ G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ := by
    rw [mem_twoMoves_iff]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, hu2, hu1, hw1, hw2, hu.symm, hw⟩
  have d12 : c₁ ≠ c₂ := by simp [c₁, c₂, hu]
  have d13 : c₁ ≠ c₃ := by simp [c₁, c₃, hw]
  have d14 : c₁ ≠ c₄ := by simp [c₁, c₄, hu]
  have d23 : c₂ ≠ c₃ := by simp [c₂, c₃, hu.symm]
  have d24 : c₂ ≠ c₄ := by simp [c₂, c₄, hw.symm]
  have d34 : c₃ ≠ c₄ := by simp [c₃, c₄, hu]
  rw [ite_eq_right h0, hone, htwo, card_filter, sum_insert (by simp [d12, d13, d14]),
    sum_insert (by simp [d23, d24]), sum_insert (by simp [d34]), sum_singleton,
    ite_eq_left hπ, ite_eq_left m₂]
  by_cases hc : G.Adj u₁ w₂ ∧ G.Adj u₂ w₁
  · rw [ite_eq_left (m₃.2 hc), ite_eq_left (m₄.2 hc), ite_eq_left hc]
    simp
  · rw [ite_eq_right (fun h => hc (m₃.1 h)), ite_eq_right (fun h => hc (m₄.1 h)),
      ite_eq_right hc]
    simp

/-- **The squared path counts out of one configuration.** -/
theorem sum_pathCount_sq_eq {n : ℕ} (S : Finset V) (hS : S.card = n) :
    ∑ T ∈ powersetCard n (univ : Finset V), pathCount G T S ^ 2 =
      (hops G S).card * (hops G S).card + ∑ t ∈ oneMoves G S, commonCount G t.1 t.2.2 +
        ∑ π ∈ twoMoves G S,
          (2 + 2 * (if G.Adj π.1.1 π.2.2 ∧ G.Adj π.2.1 π.1.2 then 1 else 0)) := by
  rw [sum_pathCount_sq G S hS, sum_paths_decomp G S (fun X => pathCount G X S),
    pathCount_self, smul_eq_mul]
  congr 1
  · congr 1
    exact sum_congr rfl fun t ht => pathCount_oneMove G ht
  · refine sum_congr rfl fun π hπ => ?_
    rcases π with ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩
    exact pathCount_twoMove G hπ

end Values

/-! ### Averaging over the configurations -/

section Averages

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem card_filter_pattern (n : ℕ) (P : Finset V → Prop) [DecidablePred P] (X Y : Finset V)
    (hXY : Disjoint X Y) (hP : ∀ S, P S ↔ X ⊆ S ∧ Disjoint Y S) :
    ((powersetCard n (univ : Finset V)).filter P).card =
      patternCount (Fintype.card V) n X.card Y.card := by
  rw [← card_pattern X Y hXY n]
  congr 1
  exact filter_congr fun S _ => hP S

omit [Fintype V] [DecidableEq V] in
theorem sum_ite_const_eq {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (c : ℕ) :
    ∑ x ∈ s, (if P x then c else 0) = (s.filter P).card * c := by
  rw [← sum_filter, sum_const, smul_eq_mul]

omit [DecidableRel G.Adj] in
/-- For two arcs `p, q`: the number of `n`-subsets in which both are hops, by how the arcs
meet. -/
theorem card_both_hops (n : ℕ) {p q : V × V} (hp : G.Adj p.1 p.2) (hq : G.Adj q.1 q.2) :
    ((powersetCard n (univ : Finset V)).filter fun S =>
        (p.1 ∈ S ∧ p.2 ∉ S) ∧ (q.1 ∈ S ∧ q.2 ∉ S)).card =
      (if p = q then patternCount (Fintype.card V) n 1 1 else 0) +
      (if p.1 = q.1 ∧ p.2 ≠ q.2 then patternCount (Fintype.card V) n 1 2 else 0) +
      (if p.1 ≠ q.1 ∧ p.2 = q.2 then patternCount (Fintype.card V) n 2 1 else 0) +
      (if p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 then
        patternCount (Fintype.card V) n 2 2 else 0) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := q
  simp only at hp hq ⊢
  have hab : a ≠ b := hp.ne
  have hab' : a' ≠ b' := hq.ne
  by_cases h1 : a = a' <;> by_cases h2 : b = b'
  · subst h1 h2
    rw [ite_eq_left rfl, ite_eq_right (fun h => h.2 rfl), ite_eq_right (fun h => h.1 rfl),
      ite_eq_right (fun h => h.1 rfl), add_zero, add_zero, add_zero,
      card_filter_pattern n _ {a} {b} (disjoint_singleton.2 hab) (fun S => by
        simp only [singleton_subset_iff, disjoint_singleton_left]; tauto),
      card_singleton, card_singleton]
  · subst h1
    have hne : (a, b) ≠ (a, b') := fun h => h2 (Prod.mk.inj h).2
    rw [ite_eq_right hne, ite_eq_left ⟨rfl, h2⟩, ite_eq_right (fun h => h.1 rfl),
      ite_eq_right (fun h => h.1 rfl), zero_add, add_zero, add_zero,
      card_filter_pattern n _ {a} {b, b'} (by simp [hab, hab']) (fun S => by
        simp only [singleton_subset_iff, disjoint_insert_left, disjoint_singleton_left]; tauto),
      card_singleton, card_pair h2]
  · subst h2
    have hne : (a, b) ≠ (a', b) := fun h => h1 (Prod.mk.inj h).1
    rw [ite_eq_right hne, ite_eq_right (fun h => h1 h.1), ite_eq_left ⟨h1, rfl⟩,
      ite_eq_right (fun h => h.2.2.2 rfl), zero_add, zero_add, add_zero,
      card_filter_pattern n _ {a, a'} {b} (by
        rw [Finset.disjoint_left]; intro v hv hv'
        simp only [mem_insert, mem_singleton] at hv hv'
        rcases hv with rfl | rfl <;> simp_all) (fun S => by
        simp only [insert_subset_iff, singleton_subset_iff, disjoint_singleton_left]; tauto),
      card_singleton, card_pair h1]
  · have hne : (a, b) ≠ (a', b') := fun h => h1 (Prod.mk.inj h).1
    rw [ite_eq_right hne, ite_eq_right (fun h => h1 h.1), ite_eq_right (fun h => h2 h.2),
      zero_add, zero_add, zero_add]
    by_cases h3 : a ≠ b' ∧ b ≠ a'
    · have h3' : a' ≠ b := Ne.symm h3.2
      have h3'' : a ≠ b' := h3.1
      rw [ite_eq_left ⟨h1, h3.1, h3.2, h2⟩,
        card_filter_pattern n _ {a, a'} {b, b'} (by
          rw [Finset.disjoint_left]; intro v hv hv'
          simp only [mem_insert, mem_singleton] at hv hv'
          rcases hv with rfl | rfl <;> simp_all)
          (fun S => by
            simp only [insert_subset_iff, singleton_subset_iff, disjoint_insert_left,
              disjoint_singleton_left]; tauto),
        card_pair h1, card_pair h2]
    · rw [ite_eq_right (fun h => h3 ⟨h.2.1, h.2.2.1⟩), card_eq_zero, filter_eq_empty_iff]
      rintro S - ⟨⟨haS, hbS⟩, ⟨ha'S, hb'S⟩⟩
      exact h3 ⟨fun h => hb'S (h ▸ haS), fun h => hbS (h ▸ ha'S)⟩

/-- Ordered pairs of arcs with the same tail and different heads. -/
def sameTail : Finset ((V × V) × (V × V)) :=
  (arcs G ×ˢ arcs G).filter fun pq => pq.1.1 = pq.2.1 ∧ pq.1.2 ≠ pq.2.2

/-- Ordered pairs of arcs with different tails and the same head. -/
def sameHead : Finset ((V × V) × (V × V)) :=
  (arcs G ×ˢ arcs G).filter fun pq => pq.1.1 ≠ pq.2.1 ∧ pq.1.2 = pq.2.2

/-- Ordered pairs of arcs with four distinct ends. -/
def disjointArcs : Finset ((V × V) × (V × V)) :=
  (arcs G ×ˢ arcs G).filter fun pq =>
    pq.1.1 ≠ pq.2.1 ∧ pq.1.1 ≠ pq.2.2 ∧ pq.1.2 ≠ pq.2.1 ∧ pq.1.2 ≠ pq.2.2

theorem card_hops_mul_self (S : Finset V) :
    (hops G S).card * (hops G S).card =
      ∑ pq ∈ arcs G ×ˢ arcs G,
        if (pq.1.1 ∈ S ∧ pq.1.2 ∉ S) ∧ (pq.2.1 ∈ S ∧ pq.2.2 ∉ S) then 1 else 0 := by
  rw [hops, card_filter, sum_mul_sum, sum_product]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  split_ifs <;> simp_all

/-- `∑_S M(S)²`, by how the two hops meet. -/
theorem sum_card_hops_sq (n : ℕ) :
    ∑ S ∈ powersetCard n (univ : Finset V), (hops G S).card * (hops G S).card =
      (arcs G).card * patternCount (Fintype.card V) n 1 1 +
        (sameTail G).card * patternCount (Fintype.card V) n 1 2 +
        (sameHead G).card * patternCount (Fintype.card V) n 2 1 +
        (disjointArcs G).card * patternCount (Fintype.card V) n 2 2 := by
  simp_rw [card_hops_mul_self G]
  rw [sum_comm]
  have h : ∀ pq ∈ arcs G ×ˢ arcs G, (∑ S ∈ powersetCard n (univ : Finset V),
      if (pq.1.1 ∈ S ∧ pq.1.2 ∉ S) ∧ (pq.2.1 ∈ S ∧ pq.2.2 ∉ S) then 1 else 0) =
      (if pq.1 = pq.2 then patternCount (Fintype.card V) n 1 1 else 0) +
      (if pq.1.1 = pq.2.1 ∧ pq.1.2 ≠ pq.2.2 then patternCount (Fintype.card V) n 1 2 else 0) +
      (if pq.1.1 ≠ pq.2.1 ∧ pq.1.2 = pq.2.2 then patternCount (Fintype.card V) n 2 1 else 0) +
      (if pq.1.1 ≠ pq.2.1 ∧ pq.1.1 ≠ pq.2.2 ∧ pq.1.2 ≠ pq.2.1 ∧ pq.1.2 ≠ pq.2.2 then
        patternCount (Fintype.card V) n 2 2 else 0) := by
    intro pq hpq
    rw [← card_filter]
    rw [mem_product, arcs, mem_filter, mem_filter] at hpq
    exact card_both_hops G n hpq.1.2 hpq.2.2
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, sum_add_distrib,
    sum_ite_const_eq, sum_ite_const_eq, sum_ite_const_eq, sum_ite_const_eq]
  have hdiag : ((arcs G ×ˢ arcs G).filter fun pq => pq.1 = pq.2).card = (arcs G).card := by
    have : ((arcs G ×ˢ arcs G).filter fun pq => pq.1 = pq.2) = (arcs G).diag := by
      ext pq
      rw [mem_filter, mem_diag, mem_product]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, h.2 ▸ h.1⟩, h.2⟩
    rw [this, diag_card]
  rw [hdiag]
  rfl

/-- Paths of two edges `x ~ y ~ z` with `x ≠ z`. -/
def wedgeSeq : Finset (V × V × V) :=
  univ.filter fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ t.1 ≠ t.2.2

theorem sum_oneMoves_sum (n : ℕ) :
    ∑ S ∈ powersetCard n (univ : Finset V), ∑ t ∈ oneMoves G S, commonCount G t.1 t.2.2 =
      patternCount (Fintype.card V) n 1 1 * ∑ t ∈ wedgeSeq G, commonCount G t.1 t.2.2 := by
  simp only [oneMoves, sum_filter]
  rw [sum_comm, wedgeSeq, sum_filter, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  by_cases ha : G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2
  · by_cases hxz : t.1 = t.2.2
    · rw [ite_eq_right (fun h => h.2.2 hxz), mul_zero]
      exact sum_eq_zero fun S _ => ite_eq_right fun h => h.2.1 (hxz ▸ h.1)
    · rw [ite_eq_left ⟨ha.1, ha.2, hxz⟩]
      have : ∀ S : Finset V, (if t.1 ∈ S ∧ t.2.2 ∉ S ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 then
          commonCount G t.1 t.2.2 else 0) =
          (if t.1 ∈ S ∧ t.2.2 ∉ S then commonCount G t.1 t.2.2 else 0) := by
        intro S
        by_cases h : t.1 ∈ S ∧ t.2.2 ∉ S <;> simp [h, ha.1, ha.2]
      rw [sum_congr rfl fun S _ => this S, sum_ite_const_eq,
        card_filter_pattern n _ {t.1} {t.2.2} (disjoint_singleton.2 hxz)
          (fun S => by simp [singleton_subset_iff, disjoint_singleton_left]),
        card_singleton, card_singleton, mul_comm]
  · rw [ite_eq_right (fun h => ha ⟨h.1, h.2.1⟩), mul_zero]
    exact sum_eq_zero fun S _ => ite_eq_right fun h => ha ⟨h.2.2.1, h.2.2.2⟩

theorem twoMoves_eq (S : Finset V) :
    twoMoves G S = (arcs G ×ˢ arcs G).filter fun π =>
      (π.1.1 ∈ S ∧ π.1.2 ∉ S) ∧ (π.2.1 ∈ S ∧ π.2.2 ∉ S) ∧ π.1.1 ≠ π.2.1 ∧ π.1.2 ≠ π.2.2 := by
  ext ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩
  rw [mem_twoMoves_iff, mem_filter, mem_product, arcs, mem_filter, mem_filter]
  simp only [mem_univ, true_and]
  tauto

theorem sum_twoMoves_sum (n : ℕ) (w : (V × V) × (V × V) → ℕ) :
    ∑ S ∈ powersetCard n (univ : Finset V), ∑ π ∈ twoMoves G S, w π =
      patternCount (Fintype.card V) n 2 2 * ∑ π ∈ disjointArcs G, w π := by
  simp only [twoMoves_eq, sum_filter]
  rw [sum_comm, disjointArcs, sum_filter, mul_sum]
  refine sum_congr rfl fun π hπ => ?_
  rw [mem_product, arcs, mem_filter, mem_filter] at hπ
  have hp := hπ.1.2
  have hq := hπ.2.2
  rw [mul_ite, mul_zero]
  by_cases hd : π.1.1 ≠ π.2.1 ∧ π.1.2 ≠ π.2.2
  · have : ∀ S : Finset V, (if (π.1.1 ∈ S ∧ π.1.2 ∉ S) ∧ (π.2.1 ∈ S ∧ π.2.2 ∉ S) ∧
        π.1.1 ≠ π.2.1 ∧ π.1.2 ≠ π.2.2 then w π else 0) =
        (if (π.1.1 ∈ S ∧ π.1.2 ∉ S) ∧ (π.2.1 ∈ S ∧ π.2.2 ∉ S) then w π else 0) := by
      intro S
      by_cases h : (π.1.1 ∈ S ∧ π.1.2 ∉ S) ∧ (π.2.1 ∈ S ∧ π.2.2 ∉ S) <;> simp [h, hd.1, hd.2]
    rw [sum_congr rfl fun S _ => this S, sum_ite_const_eq, card_both_hops G n hp hq,
      ite_eq_right (fun h => hd.1 (congrArg Prod.fst h)), ite_eq_right (fun h => hd.1 h.1),
      ite_eq_right (fun h => hd.2 h.2), zero_add, zero_add, zero_add]
    by_cases h4 : π.1.1 ≠ π.2.1 ∧ π.1.1 ≠ π.2.2 ∧ π.1.2 ≠ π.2.1 ∧ π.1.2 ≠ π.2.2
    · rw [ite_eq_left h4, ite_eq_left h4, mul_comm]
    · rw [ite_eq_right h4, ite_eq_right h4, zero_mul]
  · rw [ite_eq_right (fun h => hd ⟨h.1, h.2.2.2⟩)]
    exact sum_eq_zero fun S _ => ite_eq_right fun h => hd h.2.2

end Averages

/-! ### The graph counts -/

section Counts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered pairs of distinct neighbours `(a, c)` of a vertex `b`, as triples `(a, b, c)`. -/
def centredPairs : Finset (V × V × V) :=
  univ.filter fun t => G.Adj t.2.1 t.1 ∧ G.Adj t.2.1 t.2.2 ∧ t.1 ≠ t.2.2

/-- There are `∑_v d_v (d_v - 1) = 2W` of them. -/
theorem card_centredPairs : (centredPairs G).card = 2 * wedgeCount G := by
  rw [card_eq_sum_card_fiberwise (f := fun t => t.2.1) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _)), wedgeCount, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  have hfib : ((centredPairs G).filter fun t => t.2.1 = v).card =
      (G.neighborFinset v).offDiag.card := by
    refine card_nbij' (fun t => (t.1, t.2.2)) (fun ab => (ab.1, v, ab.2)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b, c⟩ h
      rw [mem_coe, mem_filter, centredPairs, mem_filter] at h
      obtain ⟨⟨-, h1, h2, h3⟩, rfl⟩ := h
      rw [mem_coe, mem_offDiag, mem_neighborFinset, mem_neighborFinset]
      exact ⟨h1, h2, h3⟩
    · rintro ⟨a, c⟩ h
      rw [mem_coe, mem_offDiag, mem_neighborFinset, mem_neighborFinset] at h
      rw [mem_coe, mem_filter, centredPairs, mem_filter]
      exact ⟨⟨mem_univ _, h.1, h.2.1, h.2.2⟩, rfl⟩
    · rintro ⟨a, b, c⟩ h
      rw [mem_coe, mem_filter] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    · rintro ⟨a, c⟩ _; rfl
  rw [hfib, offDiag_card, card_neighborFinset_eq_degree, Nat.choose_two_right,
    Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd, Nat.mul_sub_one]

theorem card_sameTail : (sameTail G).card = 2 * wedgeCount G := by
  rw [← card_centredPairs G]
  refine card_nbij' (fun pq => (pq.1.2, pq.1.1, pq.2.2))
    (fun t => ((t.2.1, t.1), (t.2.1, t.2.2))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ h
    rw [mem_coe, sameTail, mem_filter, mem_product, arcs, mem_filter, mem_filter] at h
    obtain ⟨⟨⟨-, hab⟩, ⟨-, hab'⟩⟩, h1, hbb⟩ := h
    simp only at h1 hab hab' hbb
    subst h1
    rw [mem_coe, centredPairs, mem_filter]
    exact ⟨mem_univ _, hab, hab', hbb⟩
  · rintro ⟨b, a, b'⟩ h
    rw [mem_coe, centredPairs, mem_filter] at h
    obtain ⟨-, hab, hab', hbb⟩ := h
    rw [mem_coe, sameTail, mem_filter, mem_product, arcs, mem_filter, mem_filter]
    exact ⟨⟨⟨mem_univ _, hab⟩, ⟨mem_univ _, hab'⟩⟩, rfl, hbb⟩
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ h
    rw [mem_coe, sameTail, mem_filter] at h
    obtain ⟨-, h1, -⟩ := h
    simp only at h1
    subst h1
    rfl
  · rintro ⟨b, a, b'⟩ _; rfl

theorem card_sameHead : (sameHead G).card = 2 * wedgeCount G := by
  rw [← card_centredPairs G]
  refine card_nbij' (fun pq => (pq.1.1, pq.1.2, pq.2.1))
    (fun t => ((t.1, t.2.1), (t.2.2, t.2.1))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ h
    rw [mem_coe, sameHead, mem_filter, mem_product, arcs, mem_filter, mem_filter] at h
    obtain ⟨⟨⟨-, hab⟩, ⟨-, hab'⟩⟩, haa, h1⟩ := h
    simp only at h1 hab hab' haa
    subst h1
    rw [mem_coe, centredPairs, mem_filter]
    exact ⟨mem_univ _, hab.symm, hab'.symm, haa⟩
  · rintro ⟨a, b, a'⟩ h
    rw [mem_coe, centredPairs, mem_filter] at h
    obtain ⟨-, hab, hab', haa⟩ := h
    rw [mem_coe, sameHead, mem_filter, mem_product, arcs, mem_filter, mem_filter]
    exact ⟨⟨⟨mem_univ _, hab.symm⟩, ⟨mem_univ _, hab'.symm⟩⟩, haa, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ h
    rw [mem_coe, sameHead, mem_filter] at h
    obtain ⟨-, -, h1⟩ := h
    simp only at h1
    subst h1
    rfl
  · rintro ⟨a, b, a'⟩ _; rfl

theorem card_wedgeSeq : (wedgeSeq G).card = 2 * wedgeCount G := by
  rw [← card_centredPairs G, wedgeSeq, centredPairs]
  congr 1
  exact filter_congr fun t _ => by rw [G.adj_comm t.1 t.2.1]

/-- An edge is the underlying edge of exactly two arcs. -/
theorem card_arcs_edge {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    ((arcs G).filter fun p => s(p.1, p.2) = e).card = 2 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    have : (arcs G).filter (fun p => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
      ext ⟨a, b⟩
      simp only [arcs, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq,
        Sym2.eq_iff]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨hxy.symm, Or.inr ⟨rfl, rfl⟩⟩
    rw [this, card_pair]
    simp [hxy.ne]

/-- **`8D` arc pairs with four distinct ends**: each ordered pair of disjoint edges, of which
there are `2D`, carries `2 × 2` orientations. -/
theorem card_disjointArcs : (disjointArcs G).card = 4 * (disjointPairs G).card := by
  have hmaps : Set.MapsTo (fun pq : (V × V) × (V × V) => (s(pq.1.1, pq.1.2), s(pq.2.1, pq.2.2)))
      ↑(disjointArcs G) ↑(disjointPairs G) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    rw [mem_coe, disjointArcs, mem_filter, mem_product, arcs, mem_filter, mem_filter] at h
    obtain ⟨⟨⟨-, hab⟩, ⟨-, hcd⟩⟩, hac, had, hbc, hbd⟩ := h
    rw [mem_coe, disjointPairs, mem_filter, mem_product, mem_edgeFinset, mem_edgeFinset]
    refine ⟨⟨hab, hcd⟩, fun v hv => ?_⟩
    simp only [Sym2.mem_iff] at hv ⊢
    rcases hv with rfl | rfl <;> tauto
  rw [card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun ef hef => ?_
  rw [disjointPairs, mem_filter, mem_product] at hef
  obtain ⟨⟨he, hf⟩, hdisj⟩ := hef
  have hfib : (disjointArcs G).filter
      (fun pq => (s(pq.1.1, pq.1.2), s(pq.2.1, pq.2.2)) = ef) =
      ((arcs G).filter fun p => s(p.1, p.2) = ef.1) ×ˢ
        ((arcs G).filter fun p => s(p.1, p.2) = ef.2) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rw [mem_filter, disjointArcs, mem_filter, mem_product, mem_product, mem_filter, mem_filter]
    constructor
    · rintro ⟨⟨⟨ha, hc⟩, -⟩, h⟩
      rw [← h]
      exact ⟨⟨ha, rfl⟩, ⟨hc, rfl⟩⟩
    · rintro ⟨⟨ha, h1⟩, ⟨hc, h2⟩⟩
      refine ⟨⟨⟨ha, hc⟩, ?_⟩, Prod.ext h1 h2⟩
      have hA := hdisj a (h1 ▸ Sym2.mem_mk_left a b)
      have hB := hdisj b (h1 ▸ Sym2.mem_mk_right a b)
      rw [← h2, Sym2.mem_iff] at hA hB
      simp only
      tauto
  rw [hfib, card_product, card_arcs_edge G he, card_arcs_edge G hf]

theorem commonCount_eq {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) :
    commonCount G x z = 1 + (univ.filter fun y' => y' ≠ y ∧ G.Adj x y' ∧ G.Adj y' z).card := by
  rw [commonCount, ← card_filter_add_card_filter_not (s := univ.filter _) (fun y' => y' = y)]
  congr 1
  · rw [filter_filter, card_eq_one]
    refine ⟨y, ?_⟩
    ext y'
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨⟨hxy, hyz⟩, rfl⟩
  · rw [filter_filter]
    congr 1
    exact filter_congr fun y' _ => by tauto

/-- `∑_{x ~ y ~ z, x ≠ z} (A_G²)_{xz} = 2W + 8C₄`: the common neighbour `y` itself, and the
4-cycles through `x, y, z`. -/
theorem sum_commonCount_wedgeSeq :
    ∑ t ∈ wedgeSeq G, commonCount G t.1 t.2.2 = 2 * wedgeCount G + (fourCycleSeq G).card := by
  have h1 : ∀ t ∈ wedgeSeq G, commonCount G t.1 t.2.2 =
      1 + (univ.filter fun y' => y' ≠ t.2.1 ∧ G.Adj t.1 y' ∧ G.Adj y' t.2.2).card := by
    intro t ht
    rw [wedgeSeq, mem_filter] at ht
    exact commonCount_eq G ht.2.1 ht.2.2.1
  rw [sum_congr rfl h1, sum_add_distrib, sum_const, smul_eq_mul, mul_one, card_wedgeSeq]
  congr 1
  have h2 : ∑ t ∈ wedgeSeq G,
      (univ.filter fun y' => y' ≠ t.2.1 ∧ G.Adj t.1 y' ∧ G.Adj y' t.2.2).card =
      ((wedgeSeq G ×ˢ univ).filter fun r : (V × V × V) × V =>
        r.2 ≠ r.1.2.1 ∧ G.Adj r.1.1 r.2 ∧ G.Adj r.2 r.1.2.2).card := by
    rw [card_filter, sum_product]
    refine sum_congr rfl fun t _ => ?_
    rw [card_filter]
  rw [h2]
  refine card_nbij' (fun r => (r.1.1, r.1.2.1, r.1.2.2, r.2))
    (fun q => ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨⟨x, y, z⟩, y'⟩ h
    rw [mem_coe, mem_filter, mem_product, wedgeSeq, mem_filter] at h
    obtain ⟨⟨⟨-, hxy, hyz, hxz⟩, -⟩, hy, hxy', hy'z⟩ := h
    rw [mem_coe, fourCycleSeq, mem_filter]
    exact ⟨mem_univ _, hxy, hyz, hy'z.symm, hxy'.symm, hxz, Ne.symm hy⟩
  · rintro ⟨a, b, c, d⟩ h
    rw [mem_coe, fourCycleSeq, mem_filter] at h
    obtain ⟨-, hab, hbc, hcd, hda, hac, hbd⟩ := h
    rw [mem_coe, mem_filter, mem_product, wedgeSeq, mem_filter]
    exact ⟨⟨⟨mem_univ _, hab, hbc, hac⟩, mem_univ _⟩, Ne.symm hbd, hda.symm, hcd.symm⟩
  · rintro ⟨⟨x, y, z⟩, y'⟩ _; rfl
  · rintro ⟨a, b, c, d⟩ _; rfl

/-- The disjoint arc pairs `(u₁ → w₁, u₂ → w₂)` with `u₁ ~ w₂` and `u₂ ~ w₁` are the 4-cycle
sequences `(u₁, w₁, u₂, w₂)`. -/
theorem card_disjointArcs_cross :
    ((disjointArcs G).filter fun π => G.Adj π.1.1 π.2.2 ∧ G.Adj π.2.1 π.1.2).card =
      (fourCycleSeq G).card := by
  refine card_nbij' (fun π => (π.1.1, π.1.2, π.2.1, π.2.2))
    (fun q => ((q.1, q.2.1), (q.2.2.1, q.2.2.2))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    rw [mem_coe, mem_filter, disjointArcs, mem_filter, mem_product, arcs, mem_filter,
      mem_filter] at h
    obtain ⟨⟨⟨⟨-, hab⟩, ⟨-, hcd⟩⟩, hac, -, -, hbd⟩, had, hcb⟩ := h
    rw [mem_coe, fourCycleSeq, mem_filter]
    exact ⟨mem_univ _, hab, hcb.symm, hcd, had.symm, hac, hbd⟩
  · rintro ⟨a, b, c, d⟩ h
    rw [mem_coe, fourCycleSeq, mem_filter] at h
    obtain ⟨-, hab, hbc, hcd, hda, hac, hbd⟩ := h
    rw [mem_coe, mem_filter, disjointArcs, mem_filter, mem_product, arcs, mem_filter,
      mem_filter]
    exact ⟨⟨⟨⟨mem_univ _, hab⟩, ⟨mem_univ _, hcd⟩⟩, hac, hda.ne.symm, hbc.ne, hbd⟩,
      hda.symm, hbc.symm⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _; rfl
  · rintro ⟨a, b, c, d⟩ _; rfl

theorem sum_disjointArcs_weight :
    ∑ π ∈ disjointArcs G, (2 + 2 * (if G.Adj π.1.1 π.2.2 ∧ G.Adj π.2.1 π.1.2 then 1 else 0)) =
      2 * (disjointArcs G).card + 2 * (fourCycleSeq G).card := by
  rw [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, ← card_filter,
    card_disjointArcs_cross]
  ring

end Counts

/-! ### The theorem -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The count behind the boson moment**:
`∑_{S, T} (H²)_{TS}² = (2m + 4W + 8C₄) C(N - 2, n - 1) + (24D + 16C₄) C(N - 4, n - 2)`
(in pattern form, valid for every `n`). -/
theorem sum_sq_pathCount (n : ℕ) (hN : 3 ≤ Fintype.card V) :
    ∑ S ∈ powersetCard n (univ : Finset V), ∑ T ∈ powersetCard n (univ : Finset V),
        pathCount G T S ^ 2 =
      (2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G) *
          patternCount (Fintype.card V) n 1 1 +
        (24 * disjointEdgePairs G + 16 * fourCycleCount G) *
          patternCount (Fintype.card V) n 2 2 := by
  rw [sum_congr rfl fun S hS => sum_pathCount_sq_eq G S (mem_powersetCard.1 hS).2,
    sum_add_distrib, sum_add_distrib, sum_card_hops_sq, sum_oneMoves_sum, sum_twoMoves_sum,
    sum_commonCount_wedgeSeq, sum_disjointArcs_weight, card_arcs, card_sameTail, card_sameHead,
    card_disjointArcs]
  have hP := patternCount_pascal (Fintype.card V) n hN
  have hD : (disjointPairs G).card = 2 * disjointEdgePairs G :=
    (Nat.two_mul_div_two_of_even (even_card_disjointPairs G)).symm
  rw [hD, ← eight_mul_fourCycleCount G]
  zify at hP ⊢
  linear_combination (2 * (wedgeCount G : ℤ)) * hP

/-- **The hard-core-boson fourth moment** (`Spec.HardCoreBosonFourthMoment`). -/
theorem fourthMoment_hardCoreHopping :
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ),
    4 ≤ Fintype.card V → n ≤ Fintype.card V →
      fourthMoment (powersetCard n (univ : Finset V)) (hardCoreHopping G) =
        ((((2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G : ℕ) : ℝ) *
              occProb (Fintype.card V) n 1 1 +
            ((24 * disjointEdgePairs G + 16 * fourCycleCount G : ℕ) : ℝ) *
              occProb (Fintype.card V) n 2 2 : ℝ) : ℂ) := by
  intro V _ _ G _ n hN hn
  set N := Fintype.card V
  have hB : (powersetCard n (univ : Finset V)).card = N.choose n := by
    rw [card_powersetCard, card_univ]
  have hC : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  have hsum : (∑ c ∈ powersetCard n (univ : Finset V), ∑ b₁ ∈ powersetCard n (univ : Finset V),
      ∑ b₂ ∈ powersetCard n (univ : Finset V), ∑ b₃ ∈ powersetCard n (univ : Finset V),
        hardCoreHopping G c b₁ * hardCoreHopping G b₁ b₂ * hardCoreHopping G b₂ b₃ *
          hardCoreHopping G b₃ c) =
      (((2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G) *
          patternCount N n 1 1 +
        (24 * disjointEdgePairs G + 16 * fourCycleCount G) * patternCount N n 2 2 : ℕ) : ℂ) := by
    rw [← sum_sq_pathCount G n (by omega), ← block_sum_eq]
    simp only [hardCoreHopping_eq]
    push_cast
    rfl
  have h11 := patternCount_one_one_eq N n (by omega)
  have h22 := patternCount_two_two_eq N n hN
  have key : (((2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G) *
          patternCount N n 1 1 +
        (24 * disjointEdgePairs G + 16 * fourCycleCount G) * patternCount N n 2 2 : ℕ) : ℝ) =
      ((((2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G : ℕ) : ℝ) *
          occProb N n 1 1 +
        ((24 * disjointEdgePairs G + 16 * fourCycleCount G : ℕ) : ℝ) * occProb N n 2 2) *
          (N.choose n : ℝ)) := by
    push_cast
    rw [h11, h22]
    ring
  rw [fourthMoment, hsum, hB, div_eq_iff (by exact_mod_cast hC), ← Complex.ofReal_natCast, key]
  push_cast
  ring

end Main

end HubbardMoments
