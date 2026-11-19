-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.Defs
public import HubbardMoments.Torus

/-!
# Graph counts for the fourth moment

Facts about the graph counts of `HubbardMoments.Defs` (`wedgeCount`,
`disjointEdgePairs`, `fourCycleCount`), stage 2 of the fourth-moment plan.

## Main results

* `eight_dvd_card_fourCycleSeq`, `eight_mul_fourCycleCount`: the number of sequences
  `(a, b, c, d)` with `a ~ b ~ c ~ d ~ a`, `a ≠ c`, `b ≠ d` is divisible by 8, so
  `8 · C₄` equals it (the division in `fourCycleCount` is exact).
* `card_disjointPairs_add`: the ordered pairs of vertex-disjoint edges, the edges and twice
  the wedges add up to `m²`; hence `even_card_disjointPairs`,
  `wedgeCount_le_choose_two`, `disjointEdgePairs_add_wedgeCount` (`D + W = C(m, 2)`) and
  `disjointEdgePairs_eq` (`D = C(m, 2) - W`, the paper's definition of `D`).
* `torus_graph_counts`: `Spec.TorusGraphCounts`. On the `L × L` torus, `m = 2L²` and
  `W = 6L²` for `L ≥ 3`, `C₄ = L²` for `L = 3` and `L ≥ 5`, and `C₄ = 24` for `L = 4`.

## Method

The 4-cycle sequences are halved three times by fixed-point-free involutions (reverse the
direction, exchange the diagonal `a ↔ c`, shift by one), against an arbitrary order of the
vertices. On the torus, a sequence is a starting site and three steps, each one of the four
unit steps; the closing condition `a - d` is a unit step reduces, through integer lifts of
the steps, to a divisibility condition on integers of absolute value at most 4, decided by
evaluation over the `4³` step triples.
-/

@[expose] public section

namespace HubbardMoments

open Finset SimpleGraph

/-! ### Halving a finite set by an involution -/

/-- If `f` maps `s` to itself, is an involution on `s`, and exchanges `p` with `¬ p`, then `s`
has twice as many elements as it has elements satisfying `p`. -/
theorem card_eq_two_mul_card_filter_of_involution {α : Type*} (s : Finset α) (f : α → α)
    (p : α → Prop) [DecidablePred p] (hf : ∀ x ∈ s, f x ∈ s) (hff : ∀ x ∈ s, f (f x) = x)
    (hp : ∀ x ∈ s, (p (f x) ↔ ¬ p x)) : s.card = 2 * (s.filter p).card := by
  have h : (s.filter fun x => ¬ p x).card = (s.filter p).card := by
    apply Finset.card_nbij' f f
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hf x hx.1, (hp x hx.1).2 hx.2⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hf x hx.1, fun h => ((hp x hx.1).1 h) hx.2⟩
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      exact hff x hx.1
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      exact hff x hx.1
  have := Finset.card_filter_add_card_filter_not (s := s) p
  omega

/-! ### The 4-cycle sequences -/

section FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sequences `(a, b, c, d)` with `a ~ b ~ c ~ d ~ a`, `a ≠ c` and `b ≠ d`: the finset
whose cardinality, divided by 8, is `fourCycleCount G`. -/
def fourCycleSeq : Finset (V × V × V × V) :=
  univ.filter fun x : V × V × V × V =>
    G.Adj x.1 x.2.1 ∧ G.Adj x.2.1 x.2.2.1 ∧ G.Adj x.2.2.1 x.2.2.2 ∧ G.Adj x.2.2.2 x.1 ∧
      x.1 ≠ x.2.2.1 ∧ x.2.1 ≠ x.2.2.2

theorem fourCycleCount_eq_card_div : fourCycleCount G = (fourCycleSeq G).card / 8 := rfl

/-- **The 4-cycle sequences come in eights.** Against an order `e` of the vertices: reversing
the direction `(a, b, c, d) ↦ (a, d, c, b)` exchanges `b < d` and `d < b`; exchanging the
diagonal `(a, b, c, d) ↦ (c, b, a, d)` exchanges `a < c` and `c < a` and keeps `b < d`;
shifting `(a, b, c, d) ↦ (b, a, d, c)` exchanges `a < b` and `b < a` and keeps the two
previous conditions (it swaps them). Each halves the count. -/
theorem eight_dvd_card_fourCycleSeq : 8 ∣ (fourCycleSeq G).card := by
  set e := Fintype.equivFin V
  have he : ∀ {u v : V}, u ≠ v → e u ≠ e v := fun h h' => h (e.injective h')
  set S := fourCycleSeq G
  -- first halving: reverse the direction, against `b < d`
  have h1 : S.card = 2 * (S.filter fun x => e x.2.1 < e x.2.2.2).card := by
    apply card_eq_two_mul_card_filter_of_involution S (fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1))
    · rintro ⟨a, b, c, d⟩ hx
      simp only [S, fourCycleSeq, mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨hx.2.2.2.1.symm, hx.2.2.1.symm, hx.2.1.symm, hx.1.symm, hx.2.2.2.2.1,
        hx.2.2.2.2.2.symm⟩
    · rintro ⟨a, b, c, d⟩ _; rfl
    · rintro ⟨a, b, c, d⟩ hx
      simp only [S, fourCycleSeq, mem_filter, mem_univ, true_and] at hx
      have := he hx.2.2.2.2.2
      simp only [not_lt]
      exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm this)⟩
  set S1 := S.filter fun x => e x.2.1 < e x.2.2.2
  -- second halving: exchange the diagonal `a ↔ c`, against `a < c`
  have h2 : S1.card = 2 * (S1.filter fun x => e x.1 < e x.2.2.1).card := by
    apply card_eq_two_mul_card_filter_of_involution S1 (fun x => (x.2.2.1, x.2.1, x.1, x.2.2.2))
    · rintro ⟨a, b, c, d⟩ hx
      simp only [S1, S, fourCycleSeq, mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨⟨hx.1.2.1.symm, hx.1.1.symm, hx.1.2.2.2.1.symm, hx.1.2.2.1.symm,
        hx.1.2.2.2.2.1.symm, hx.1.2.2.2.2.2⟩, hx.2⟩
    · rintro ⟨a, b, c, d⟩ _; rfl
    · rintro ⟨a, b, c, d⟩ hx
      simp only [S1, S, fourCycleSeq, mem_filter, mem_univ, true_and] at hx
      have := he hx.1.2.2.2.2.1
      simp only [not_lt]
      exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm this)⟩
  set S2 := S1.filter fun x => e x.1 < e x.2.2.1
  -- third halving: shift by one step and reverse, `(a, b, c, d) ↦ (b, a, d, c)`, against `a < b`
  have h3 : S2.card = 2 * (S2.filter fun x => e x.1 < e x.2.1).card := by
    apply card_eq_two_mul_card_filter_of_involution S2 (fun x => (x.2.1, x.1, x.2.2.2, x.2.2.1))
    · rintro ⟨a, b, c, d⟩ hx
      simp only [S2, S1, S, fourCycleSeq, mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨⟨⟨hx.1.1.1.symm, hx.1.1.2.2.2.1.symm, hx.1.1.2.2.1.symm, hx.1.1.2.1.symm,
        hx.1.1.2.2.2.2.2, hx.1.1.2.2.2.2.1⟩, hx.2⟩, hx.1.2⟩
    · rintro ⟨a, b, c, d⟩ _; rfl
    · rintro ⟨a, b, c, d⟩ hx
      simp only [S2, S1, S, fourCycleSeq, mem_filter, mem_univ, true_and] at hx
      have := he hx.1.1.1.ne
      simp only [not_lt]
      exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm this)⟩
  exact ⟨_, by rw [h1, h2, h3]; ring⟩

/-- `8 · C₄` is the number of 4-cycle sequences: the division in `fourCycleCount` is exact. -/
theorem eight_mul_fourCycleCount : 8 * fourCycleCount G = (fourCycleSeq G).card :=
  Nat.mul_div_cancel' (eight_dvd_card_fourCycleSeq G)

end FourCycles

/-! ### Wedges and disjoint pairs of edges -/

section Wedges

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The ordered pairs of vertex-disjoint edges: the finset whose cardinality, divided by 2,
is `disjointEdgePairs G`. -/
def disjointPairs : Finset (Sym2 V × Sym2 V) :=
  (G.edgeFinset ×ˢ G.edgeFinset).filter fun ef => ∀ v ∈ ef.1, v ∉ ef.2

theorem disjointEdgePairs_eq_card_div : disjointEdgePairs G = (disjointPairs G).card / 2 := rfl

/-- The vertices common to two unordered pairs. -/
private def common (ef : Sym2 V × Sym2 V) : Finset V := univ.filter fun v => v ∈ ef.1 ∧ v ∈ ef.2

/-- An edge has exactly two vertices. -/
private theorem card_common_self {e : Sym2 V} (he : e ∈ G.edgeFinset) : (common (e, e)).card = 2 := by
  induction e using Sym2.ind with
  | _ x y =>
    have hxy : x ≠ y := G.ne_of_adj (by simpa using he)
    have : common (s(x, y), s(x, y)) = {x, y} := by
      ext v; simp [common]
    rw [this, card_pair hxy]

/-- Two distinct edges have at most one common vertex. -/
private theorem card_common_le_one {e f : Sym2 V} (hne : e ≠ f) : (common (e, f)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu w hw
  by_contra huw
  simp only [common, mem_filter, mem_univ, true_and] at hu hw
  exact hne (((Sym2.mem_and_mem_iff huw).1 ⟨hu.1, hw.1⟩).trans
    ((Sym2.mem_and_mem_iff huw).1 ⟨hu.2, hw.2⟩).symm)

/-- Summing the common vertices over the ordered pairs of edges counts, at each vertex, the
ordered pairs of edges at that vertex. -/
private theorem sum_card_common :
    ∑ ef ∈ G.edgeFinset ×ˢ G.edgeFinset, (common ef).card = ∑ v, G.degree v * G.degree v := by
  simp only [common, card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← card_filter, ← card_incidenceFinset_eq_degree, ← card_product]
  congr 1
  ext ⟨e, f⟩
  simp [incidenceFinset_eq_filter, and_and_and_comm]

/-- **Pairs of edges by how they meet.** Of the `m²` ordered pairs of edges, the vertex-disjoint
ones, the `m` pairs of an edge with itself, and the `2W` pairs of distinct edges sharing a
vertex exhaust them. -/
theorem card_disjointPairs_add :
    (disjointPairs G).card + G.edgeFinset.card + 2 * wedgeCount G =
      G.edgeFinset.card * G.edgeFinset.card := by
  set E := G.edgeFinset
  set P := E ×ˢ E
  -- the meeting pairs: equal edges, or distinct edges with a common vertex
  set Diag := P.filter fun ef => ef.1 = ef.2
  set Off := P.filter fun ef => ef.1 ≠ ef.2 ∧ ¬ ∀ v ∈ ef.1, v ∉ ef.2
  have hdiag : Diag.card = E.card := by
    refine (Finset.card_nbij' (fun ef => ef.1) (fun e => (e, e)) ?_ ?_ ?_ ?_).symm.symm
    · intro ef hef; simp only [Diag, P, coe_filter, mem_product, Set.mem_ofPred_eq] at hef
      exact hef.1.1
    · intro e he; simp [Diag, P, Finset.mem_coe.1 he]
    · intro ef hef; simp only [Diag, P, coe_filter, Set.mem_ofPred_eq] at hef
      ext <;> simp [hef.2]
    · intro e _; rfl
  -- the common-vertex count is 2 on the diagonal, 1 on `Off`, 0 on the disjoint pairs
  have hsum : ∑ ef ∈ P, (common ef).card = 2 * Diag.card + Off.card := by
    have hval : ∀ ef ∈ P, (common ef).card =
        (if ef.1 = ef.2 then 2 else 0) + (if ef.1 ≠ ef.2 ∧ ¬ ∀ v ∈ ef.1, v ∉ ef.2 then 1 else 0) := by
      rintro ⟨e, f⟩ hef
      simp only [P, mem_product] at hef
      by_cases hef' : e = f
      · subst hef'; simp [card_common_self G hef.1]
      · have hle := card_common_le_one (V := V) hef'
        by_cases hmeet : ∀ v ∈ e, v ∉ f
        · have : common (e, f) = ∅ :=
            Finset.filter_eq_empty_iff.2 fun v _ h => hmeet v h.1 h.2
          rw [this, card_empty, ite_eq_right_of_eq_false _ _ (eq_false hef'),
            ite_eq_right_of_eq_false _ _ (eq_false fun h => h.2 hmeet)]
        · push Not at hmeet
          obtain ⟨v, hve, hvf⟩ := hmeet
          have hpos : 0 < (common (e, f)).card :=
            card_pos.2 ⟨v, by simp [common, hve, hvf]⟩
          have : ¬ ∀ v ∈ e, v ∉ f := fun h => h v hve hvf
          rw [ite_eq_right_of_eq_false _ _ (eq_false hef'), ite_eq_left_of_eq_true _ _ (eq_true ⟨hef', this⟩)]
          omega
    rw [Finset.sum_congr rfl hval, sum_add_distrib, ← sum_filter, ← sum_filter, sum_const,
      sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  have hdeg : ∑ v, G.degree v * G.degree v = 2 * E.card + 2 * wedgeCount G := by
    have : ∀ v, G.degree v * G.degree v = G.degree v + 2 * (G.degree v).choose 2 := by
      intro v
      rw [Nat.choose_two_right]
      have h2 : 2 ∣ G.degree v * (G.degree v - 1) := (Nat.even_mul_pred_self _).two_dvd
      rw [Nat.mul_div_cancel' h2]
      rcases Nat.eq_zero_or_pos (G.degree v) with h | h
      · simp [h]
      · obtain ⟨k, hk⟩ : ∃ k, G.degree v = k + 1 := ⟨G.degree v - 1, by omega⟩
        rw [hk]; simp; ring
    rw [Finset.sum_congr rfl fun v _ => this v, sum_add_distrib, ← mul_sum,
      sum_degrees_eq_twice_card_edges, wedgeCount]
  -- the pairs split into disjoint, diagonal and `Off`
  have hsplit : P.card = (disjointPairs G).card + Diag.card + Off.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := P) (fun ef => ∀ v ∈ ef.1, v ∉ ef.2)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := P.filter fun ef => ¬ ∀ v ∈ ef.1, v ∉ ef.2) (fun ef => ef.1 = ef.2)
    have hD : P.filter (fun ef => ∀ v ∈ ef.1, v ∉ ef.2) = disjointPairs G := rfl
    have hDiag : (P.filter fun ef => ¬ ∀ v ∈ ef.1, v ∉ ef.2).filter (fun ef => ef.1 = ef.2) =
        Diag := by
      ext ⟨e, f⟩
      simp only [Diag, P, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨h, _⟩, he⟩; exact ⟨h, he⟩
      · rintro ⟨h, rfl⟩
        refine ⟨⟨h, fun hd => ?_⟩, rfl⟩
        induction e using Sym2.ind with
        | _ x y => exact hd x (Sym2.mem_mk_left x y) (Sym2.mem_mk_left x y)
    have hOff : (P.filter fun ef => ¬ ∀ v ∈ ef.1, v ∉ ef.2).filter (fun ef => ¬ ef.1 = ef.2) =
        Off := by
      ext ⟨e, f⟩
      simp only [Off, P, mem_filter, mem_product, ne_eq]
      tauto
    rw [hD] at h1; rw [hDiag, hOff] at h2
    omega
  have hP : P.card = E.card * E.card := card_product _ _
  have hc : ∑ ef ∈ P, (common ef).card = ∑ v, G.degree v * G.degree v := sum_card_common G
  omega

/-- The number of ordered pairs of vertex-disjoint edges is even. -/
theorem even_card_disjointPairs : Even (disjointPairs G).card := by
  have h := card_disjointPairs_add G
  have hm : Even (G.edgeFinset.card * G.edgeFinset.card + G.edgeFinset.card) := by
    rw [← Nat.mul_succ]; exact Nat.even_mul_succ_self _
  rw [Nat.even_iff] at hm ⊢
  omega

/-- `W ≤ C(m, 2)`. -/
theorem wedgeCount_le_choose_two : wedgeCount G ≤ G.edgeFinset.card.choose 2 := by
  have h := card_disjointPairs_add G
  rw [Nat.choose_two_right]
  have h2 : 2 ∣ G.edgeFinset.card * (G.edgeFinset.card - 1) :=
    (Nat.even_mul_pred_self _).two_dvd
  obtain ⟨k, hk⟩ := h2
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
  rcases Nat.eq_zero_or_pos G.edgeFinset.card with h0 | hpos
  · rw [h0] at h hk; omega
  · have : G.edgeFinset.card * G.edgeFinset.card = G.edgeFinset.card * (G.edgeFinset.card - 1) +
        G.edgeFinset.card := by
      obtain ⟨j, hj⟩ : ∃ j, G.edgeFinset.card = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hj]; simp; ring
    omega

/-- **`D + W = C(m, 2)`**: a pair of distinct edges either shares a vertex or is disjoint. -/
theorem disjointEdgePairs_add_wedgeCount :
    disjointEdgePairs G + wedgeCount G = G.edgeFinset.card.choose 2 := by
  have h := card_disjointPairs_add G
  rw [disjointEdgePairs_eq_card_div, Nat.choose_two_right]
  have h2 : 2 ∣ G.edgeFinset.card * (G.edgeFinset.card - 1) :=
    (Nat.even_mul_pred_self _).two_dvd
  obtain ⟨k, hk⟩ := h2
  obtain ⟨j, hj⟩ := (even_card_disjointPairs G).two_dvd
  rw [hk, hj, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
  rcases Nat.eq_zero_or_pos G.edgeFinset.card with h0 | hpos
  · rw [h0] at h hk; omega
  · have : G.edgeFinset.card * G.edgeFinset.card = G.edgeFinset.card * (G.edgeFinset.card - 1) +
        G.edgeFinset.card := by
      obtain ⟨i, hi⟩ : ∃ i, G.edgeFinset.card = i + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hi]; simp; ring
    omega

/-- **`D = C(m, 2) - W`**, the paper's definition of `D`. -/
theorem disjointEdgePairs_eq :
    disjointEdgePairs G = G.edgeFinset.card.choose 2 - wedgeCount G := by
  have := disjointEdgePairs_add_wedgeCount G
  omega

end Wedges

/-! ### The torus -/

section Torus

/-- On a graph with every degree `z`, `2m = N z` and `W = N · C(z, 2)`. (Stated with the
degrees computed from `DecidableRel G.Adj`; the torus also has the box-product instance.) -/
private theorem counts_of_degree_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {z : ℕ} (hz : ∀ v, G.degree v = z) :
    2 * G.edgeFinset.card = Fintype.card V * z ∧ wedgeCount G = Fintype.card V * z.choose 2 := by
  constructor
  · rw [← G.sum_degrees_eq_twice_card_edges]; simp [hz]
  · simp [wedgeCount, hz]

/-- The two counts on the torus, from its degree 4 (`torus_isRegularOfDegree`, stated with the
box-product instance for the neighbour sets; the degrees agree through `Nat.card`). -/
private theorem torus_counts (L : ℕ) (hL : 3 ≤ L) :
    2 * (torus L).edgeFinset.card = L * L * 4 ∧ wedgeCount (torus L) = L * L * 6 := by
  have h := counts_of_degree_eq (torus L) (z := 4) fun v => by
    have h2 := torus_isRegularOfDegree L hL v
    rw [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at h2 ⊢
    exact h2
  rw [Fintype.card_prod, Fintype.card_fin, show (4 : ℕ).choose 2 = 6 by decide] at h
  exact h

/-- **Edges of the torus**: `m = 2L²` for `L ≥ 3` (degree 4 at each of the `L²` sites). -/
theorem torus_card_edgeFinset (L : ℕ) (hL : 3 ≤ L) : (torus L).edgeFinset.card = 2 * (L * L) := by
  have h := (torus_counts L hL).1
  omega

/-- **Wedges of the torus**: `W = 6L²` for `L ≥ 3` (`C(4, 2) = 6` at each site). -/
theorem torus_wedgeCount (L : ℕ) (hL : 3 ≤ L) : wedgeCount (torus L) = 6 * (L * L) := by
  rw [(torus_counts L hL).2]; ring

open Fin.CommRing

/-- The four unit steps of the square lattice, as integer vectors. -/
def stepZ : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- An integer vector reduced modulo `L` in both coordinates: a site of the `L × L` torus. -/
def castZ (L : ℕ) [NeZero L] (z : ℤ × ℤ) : Fin L × Fin L := ((z.1 : Fin L), (z.2 : Fin L))

theorem fin_intCast_eq_zero_iff {L : ℕ} [NeZero L] (z : ℤ) : (z : Fin L) = 0 ↔ (L : ℤ) ∣ z := by
  rcases Int.natAbs_eq z with h | h <;> rw [h]
  · rw [Int.cast_natCast, Fin.natCast_eq_zero, Int.natCast_dvd_natCast]
  · rw [Int.cast_neg, neg_eq_zero, Int.cast_natCast, Fin.natCast_eq_zero, dvd_neg,
      Int.natCast_dvd_natCast]

theorem castZ_add {L : ℕ} [NeZero L] (z w : ℤ × ℤ) :
    castZ L (z + w) = castZ L z + castZ L w := by
  simp [castZ, Int.cast_add]

theorem castZ_sub {L : ℕ} [NeZero L] (z w : ℤ × ℤ) :
    castZ L (z - w) = castZ L z - castZ L w := by
  simp [castZ, Int.cast_sub]

theorem castZ_eq_zero_iff {L : ℕ} [NeZero L] (z : ℤ × ℤ) :
    castZ L z = 0 ↔ (L : ℤ) ∣ z.1 ∧ (L : ℤ) ∣ z.2 := by
  simp only [castZ, Prod.mk_eq_zero, fin_intCast_eq_zero_iff]

/-- An integer of absolute value below `L` divisible by `L` is `0`. -/
theorem eq_zero_of_dvd_of_natAbs_lt {L : ℕ} {z : ℤ} (h : (L : ℤ) ∣ z) (hz : z.natAbs < L) :
    z = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using hz)

/-- **Adjacency on the torus is a unit step.** For `L ≥ 3`, `x ~ y` exactly when `y - x` is one
of the four unit steps. -/
theorem torus_adj_iff_step {n : ℕ} {x y : Fin (n + 3) × Fin (n + 3)} :
    (torus (n + 3)).Adj x y ↔ ∃ i, y - x = castZ (n + 3) (stepZ i) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [torus, boxProd_adj, cycleGraph_adj]
  constructor
  · rintro (⟨h | h, h2⟩ | ⟨h | h, h1⟩)
    · refine ⟨1, Prod.ext ?_ ?_⟩
      · simp [stepZ, castZ]; linear_combination -h
      · simp [stepZ, castZ, h2]
    · refine ⟨0, Prod.ext ?_ ?_⟩
      · simp [stepZ, castZ]; linear_combination h
      · simp [stepZ, castZ, h2]
    · refine ⟨3, Prod.ext ?_ ?_⟩
      · simp [stepZ, castZ, h1]
      · simp [stepZ, castZ]; linear_combination -h
    · refine ⟨2, Prod.ext ?_ ?_⟩
      · simp [stepZ, castZ, h1]
      · simp [stepZ, castZ]; linear_combination h
  · rintro ⟨i, hi⟩
    rw [Prod.ext_iff] at hi
    obtain ⟨h1, h2⟩ := hi
    fin_cases i <;> simp [stepZ, castZ] at h1 h2
    · exact Or.inl ⟨Or.inr h1, (sub_eq_zero.1 h2).symm⟩
    · exact Or.inl ⟨Or.inl (by linear_combination -h1), (sub_eq_zero.1 h2).symm⟩
    · exact Or.inr ⟨Or.inr h2, (sub_eq_zero.1 h1).symm⟩
    · exact Or.inr ⟨Or.inl (by linear_combination -h2), (sub_eq_zero.1 h1).symm⟩

theorem castZ_stepZ_injective (n : ℕ) : Function.Injective fun i => castZ (n + 3) (stepZ i) := by
  intro i j h
  have h' : castZ (n + 3) (stepZ i - stepZ j) = 0 := by
    rw [castZ_sub]; exact sub_eq_zero.2 h
  rw [castZ_eq_zero_iff] at h'
  have hb : ∀ i j : Fin 4, (stepZ i - stepZ j).1.natAbs ≤ 2 ∧ (stepZ i - stepZ j).2.natAbs ≤ 2 := by
    decide
  have e1 := eq_zero_of_dvd_of_natAbs_lt h'.1 (by have := (hb i j).1; omega)
  have e2 := eq_zero_of_dvd_of_natAbs_lt h'.2 (by have := (hb i j).2; omega)
  have hij : ∀ i j : Fin 4, (stepZ i - stepZ j).1 = 0 → (stepZ i - stepZ j).2 = 0 → i = j := by
    decide
  exact hij i j e1 e2

/-- The step triples `(i, j, k)` that start a 4-cycle sequence of the `(n + 3) × (n + 3)` torus:
some fourth step closes the walk, and the two diagonals are nonzero. -/
def stepTriples (n : ℕ) : Finset (Fin 4 × Fin 4 × Fin 4) :=
  univ.filter fun t =>
    (∃ l, castZ (n + 3) (stepZ t.1) + castZ (n + 3) (stepZ t.2.1) +
        castZ (n + 3) (stepZ t.2.2) + castZ (n + 3) (stepZ l) = 0) ∧
      castZ (n + 3) (stepZ t.1) + castZ (n + 3) (stepZ t.2.1) ≠ 0 ∧
      castZ (n + 3) (stepZ t.2.1) + castZ (n + 3) (stepZ t.2.2) ≠ 0

/-- A starting site and three steps give the sequence of the four sites visited. -/
def stepWalk (n : ℕ) (p : (Fin (n + 3) × Fin (n + 3)) × (Fin 4 × Fin 4 × Fin 4)) :
    (Fin (n + 3) × Fin (n + 3)) × (Fin (n + 3) × Fin (n + 3)) × (Fin (n + 3) × Fin (n + 3)) ×
      (Fin (n + 3) × Fin (n + 3)) :=
  (p.1, p.1 + castZ (n + 3) (stepZ p.2.1),
    p.1 + castZ (n + 3) (stepZ p.2.1) + castZ (n + 3) (stepZ p.2.2.1),
    p.1 + castZ (n + 3) (stepZ p.2.1) + castZ (n + 3) (stepZ p.2.2.1) +
      castZ (n + 3) (stepZ p.2.2.2))

theorem stepWalk_injective (n : ℕ) : Function.Injective (stepWalk n) := by
  rintro ⟨a, i, j, k⟩ ⟨a', i', j', k'⟩ h
  simp only [stepWalk, Prod.mk.injEq] at h
  obtain ⟨rfl, h1, h2, h3⟩ := h
  have hi : i = i' := castZ_stepZ_injective n (add_left_cancel h1)
  subst hi
  have hj : j = j' := castZ_stepZ_injective n (add_left_cancel h2)
  subst hj
  have hk : k = k' := castZ_stepZ_injective n (add_left_cancel h3)
  subst hk
  rfl

theorem fourCycleSeq_torus (n : ℕ) :
    fourCycleSeq (torus (n + 3)) = (univ ×ˢ stepTriples n).image (stepWalk n) := by
  ext ⟨a, b, c, d⟩
  simp only [fourCycleSeq, mem_filter, mem_univ, true_and, mem_image, mem_product,
    stepTriples, torus_adj_iff_step]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩, ⟨l, hl⟩, hac, hbd⟩
    refine ⟨(a, i, j, k), ⟨⟨l, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [← hi, ← hj, ← hk, ← hl]; abel
    · rw [← hi, ← hj]; intro h; apply hac
      have : c - a = 0 := by rw [← h]; abel
      exact (sub_eq_zero.1 this).symm
    · rw [← hj, ← hk]; intro h; apply hbd
      have : d - b = 0 := by rw [← h]; abel
      exact (sub_eq_zero.1 this).symm
    · simp only [stepWalk, Prod.mk.injEq, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← hi]; abel
      · rw [← hi, ← hj]; abel
      · rw [← hi, ← hj, ← hk]; abel
  · rintro ⟨⟨a', i, j, k⟩, ⟨⟨l, hl⟩, hij, hjk⟩, h⟩
    dsimp only at hl hij hjk
    simp only [stepWalk, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨⟨i, by abel⟩, ⟨j, by abel⟩, ⟨k, by abel⟩, ⟨l, ?_⟩, ?_, ?_⟩
    · rw [eq_neg_of_add_eq_zero_right hl]; abel
    · intro h; apply hij
      calc castZ (n + 3) (stepZ i) + castZ (n + 3) (stepZ j)
          = (a' + castZ (n + 3) (stepZ i) + castZ (n + 3) (stepZ j)) - a' := by abel
        _ = 0 := by rw [← h, sub_self]
    · intro h; apply hjk
      calc castZ (n + 3) (stepZ j) + castZ (n + 3) (stepZ k)
          = (a' + castZ (n + 3) (stepZ i) + castZ (n + 3) (stepZ j) + castZ (n + 3) (stepZ k)) -
              (a' + castZ (n + 3) (stepZ i)) := by abel
        _ = 0 := by rw [← h, sub_self]

/-- The step triples, with the closing and diagonal conditions written as divisibility by
`L` of integer vectors. -/
def stepTriplesZ (L : ℕ) : Finset (Fin 4 × Fin 4 × Fin 4) :=
  univ.filter fun t =>
    (∃ l, (L : ℤ) ∣ (stepZ t.1 + stepZ t.2.1 + stepZ t.2.2 + stepZ l).1 ∧
        (L : ℤ) ∣ (stepZ t.1 + stepZ t.2.1 + stepZ t.2.2 + stepZ l).2) ∧
      ¬ ((L : ℤ) ∣ (stepZ t.1 + stepZ t.2.1).1 ∧ (L : ℤ) ∣ (stepZ t.1 + stepZ t.2.1).2) ∧
      ¬ ((L : ℤ) ∣ (stepZ t.2.1 + stepZ t.2.2).1 ∧ (L : ℤ) ∣ (stepZ t.2.1 + stepZ t.2.2).2)

theorem stepTriples_eq (n : ℕ) : stepTriples n = stepTriplesZ (n + 3) := by
  unfold stepTriples stepTriplesZ
  refine Finset.filter_congr fun t _ => ?_
  simp only [← castZ_add, castZ_eq_zero_iff, ne_eq]

/-- The same triples when the integer vectors must vanish (no winding around the torus). -/
def stepTriples₀ : Finset (Fin 4 × Fin 4 × Fin 4) :=
  univ.filter fun t =>
    (∃ l, stepZ t.1 + stepZ t.2.1 + stepZ t.2.2 + stepZ l = 0) ∧
      stepZ t.1 + stepZ t.2.1 ≠ 0 ∧ stepZ t.2.1 + stepZ t.2.2 ≠ 0

/-- For `L ≥ 5` a sum of at most four unit steps is divisible by `L` only if it is `0`. -/
theorem stepTriplesZ_eq_of_five_le {L : ℕ} (hL : 5 ≤ L) : stepTriplesZ L = stepTriples₀ := by
  have small : ∀ z : ℤ × ℤ, z.1.natAbs ≤ 4 → z.2.natAbs ≤ 4 →
      ((L : ℤ) ∣ z.1 ∧ (L : ℤ) ∣ z.2 ↔ z = 0) := by
    intro z h1 h2
    constructor
    · rintro ⟨d1, d2⟩
      exact Prod.ext (eq_zero_of_dvd_of_natAbs_lt d1 (by omega))
        (eq_zero_of_dvd_of_natAbs_lt d2 (by omega))
    · rintro rfl; exact ⟨dvd_zero _, dvd_zero _⟩
  have b4 : ∀ i j k l : Fin 4, (stepZ i + stepZ j + stepZ k + stepZ l).1.natAbs ≤ 4 ∧
      (stepZ i + stepZ j + stepZ k + stepZ l).2.natAbs ≤ 4 := by decide
  have b2 : ∀ i j : Fin 4, (stepZ i + stepZ j).1.natAbs ≤ 4 ∧ (stepZ i + stepZ j).2.natAbs ≤ 4 := by
    decide
  unfold stepTriplesZ stepTriples₀
  refine Finset.filter_congr fun t _ => ?_
  rw [small _ (b2 _ _).1 (b2 _ _).2, small _ (b2 _ _).1 (b2 _ _).2]
  simp only [fun l => small _ (b4 t.1 t.2.1 t.2.2 l).1 (b4 t.1 t.2.1 t.2.2 l).2]

theorem card_stepTriples₀ : stepTriples₀.card = 8 := by decide

theorem card_stepTriplesZ_three : (stepTriplesZ 3).card = 8 := by decide

theorem card_stepTriplesZ_four : (stepTriplesZ 4).card = 12 := by decide

theorem card_fourCycleSeq_torus (n : ℕ) :
    (fourCycleSeq (torus (n + 3))).card = (n + 3) * (n + 3) * (stepTriples n).card := by
  rw [fourCycleSeq_torus, card_image_of_injective _ (stepWalk_injective n), card_product,
    card_univ, Fintype.card_prod, Fintype.card_fin]

/-- **Four-cycles of the torus**: `C₄ = L²` (the plaquettes) for `L = 3` and `L ≥ 5`. -/
theorem torus_fourCycleCount (L : ℕ) (hL : L = 3 ∨ 5 ≤ L) : fourCycleCount (torus L) = L * L := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
  rw [fourCycleCount_eq_card_div, card_fourCycleSeq_torus, stepTriples_eq]
  have h8 : (stepTriplesZ (n + 3)).card = 8 := by
    rcases hL with h | h
    · obtain rfl : n = 0 := by omega
      exact card_stepTriplesZ_three
    · rw [stepTriplesZ_eq_of_five_le h, card_stepTriples₀]
  rw [h8, Nat.mul_div_cancel _ (by norm_num)]

/-- **Four-cycles of the `4 × 4` torus**: `C₄ = 24`, the 16 plaquettes and the 8 rows and
columns, which close after four steps. -/
theorem torus_four_fourCycleCount : fourCycleCount (torus 4) = 24 := by
  rw [fourCycleCount_eq_card_div,
    show fourCycleSeq (torus 4) = fourCycleSeq (torus (1 + 3)) from rfl,
    card_fourCycleSeq_torus, stepTriples_eq, show (1 + 3 : ℕ) = 4 from rfl,
    card_stepTriplesZ_four]

/-- **`Spec.TorusGraphCounts`.** -/
theorem torus_graph_counts :
  (∀ L : ℕ, 3 ≤ L →
    (torus L).edgeFinset.card = 2 * (L * L) ∧ wedgeCount (torus L) = 6 * (L * L)) ∧
  (∀ L : ℕ, (L = 3 ∨ 5 ≤ L) → fourCycleCount (torus L) = L * L) ∧
  fourCycleCount (torus 4) = 24 :=
  ⟨fun L hL => ⟨torus_card_edgeFinset L hL, torus_wedgeCount L hL⟩, torus_fourCycleCount,
    torus_four_fourCycleCount⟩

end Torus

end HubbardMoments
