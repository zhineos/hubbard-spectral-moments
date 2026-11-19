-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.FermionValues

/-!
# Fermions minus hard-core bosons, as a sum over 4-cycle sequences

Stage 5 of the fourth-moment plan, third part. For a configuration `c` with occupied sites
`S`, the fermionic `∑_{c''} (H²)_{c'' c}²` differs from the hard-core-boson
`∑_T (H²)_{TS}²` only through the 4-cycles: it is the boson value plus
`∑_q w(c, q)` over the 4-cycle sequences `q = (a, b, c', d)` (`sum_Qf_sq_eq_boson_add`), with
the local weight `w = wE + wO + wD`:

* `wE`: `a`, `d` occupied, `b`, `c'` empty: `-(1 + [same spin at a, d])` (a particle moving
  `a → c'` through `b`, against the relay through `d`);
* `wO`: `a`, `b` occupied, `c'` empty: the relay through `b` against the other paths `a → c'`;
* `wD`: `a`, `c'` occupied, `b`, `d` empty: `-2(1 + [same spin at a, c'])` (two particles
  moving crosswise).

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset

section Delta

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
  {G : SimpleGraph V} [DecidableRel G.Adj] {ord : V × σ ↪ ℕ}

/-- The weight of a 4-cycle sequence `(a, b, c', d)` with `a`, `d` occupied and `b`, `c'` empty. -/
def wE (c : Config V σ) (q : V × V × V × V) : ℂ :=
  if c q.1 ≠ none ∧ c q.2.1 = none ∧ c q.2.2.1 = none ∧ c q.2.2.2 ≠ none then
    -(1 + if c q.2.2.2 = c q.1 then 1 else 0) else 0

/-- The weight of a 4-cycle sequence `(a, b, c', d)` with `a`, `b` occupied and `c'` empty. -/
def wO (c : Config V σ) (q : V × V × V × V) : ℂ :=
  if c q.1 ≠ none ∧ c q.2.1 ≠ none ∧ c q.2.2.1 = none then
    (if c q.2.1 = c q.1 then
      (if c q.2.2.2 = c q.1 then 1 else 0) - (if c q.2.2.2 = none then 1 else 0) - 1 else -1)
  else 0

/-- The weight of a 4-cycle sequence `(a, b, c', d)` with `a`, `c'` occupied and `b`, `d`
empty. -/
def wD (c : Config V σ) (q : V × V × V × V) : ℂ :=
  if c q.1 ≠ none ∧ c q.2.1 = none ∧ c q.2.2.1 ≠ none ∧ c q.2.2.2 = none then
    -2 * (1 + if c q.1 = c q.2.2.1 then 1 else 0) else 0

omit [DecidableEq V] [Fintype σ] [DecidableEq σ] in
theorem eCount_eq_sum (c : Config V σ) (x z : V) :
    (eCount G c x z : ℂ) = ∑ w, if G.Adj x w ∧ G.Adj w z ∧ c w = none then 1 else 0 := by
  rw [eCount, card_filter]; push_cast; rfl

omit [DecidableEq V] [Fintype σ] in
theorem oCount_eq_sum (c : Config V σ) (x z : V) :
    (oCount G c x z : ℂ) = ∑ w, if G.Adj x w ∧ G.Adj w z ∧ c w = c x then 1 else 0 := by
  rw [oCount, card_filter]; push_cast; rfl

omit [DecidableEq V] in
theorem commonCount_eq_sum (x z : V) :
    (commonCount G x z : ℂ) = ∑ w, if G.Adj x w ∧ G.Adj w z then 1 else 0 := by
  rw [commonCount, card_filter]; push_cast; rfl

omit [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] in
theorem sum_four_eq {f : V × V × V × V → ℂ} [Fintype V] :
    ∑ q, f q = ∑ x, ∑ y, ∑ z, ∑ w, f (x, y, z, w) := by
  simp only [Fintype.sum_prod_type]

omit [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ] in
theorem sum_three_eq {f : V × V × V → ℂ} [Fintype V] :
    ∑ t, f t = ∑ x, ∑ y, ∑ z, f (x, y, z) := by
  simp only [Fintype.sum_prod_type]

omit [Fintype σ] [DecidableEq σ] in
theorem fourCycleSeq_sum (f : V × V × V × V → ℂ) :
    ∑ q ∈ fourCycleSeq G, f q = ∑ x, ∑ y, ∑ z, ∑ w,
      if G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w then f (x, y, z, w)
        else 0 := by
  rw [fourCycleSeq, sum_filter, sum_four_eq]

/-! ### The empty-site part -/

omit [Fintype σ] in
theorem sum_E_eq (c : Config V σ) :
    ∑ t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c),
        ((eCount G c t.1 t.2.2 : ℂ) - oCount G c t.1 t.2.2 - commonCount G t.1 t.2.2) =
      ∑ q ∈ fourCycleSeq G, wE c q := by
  rw [fourCycleSeq_sum, oneMoves, filter_filter, sum_filter, sum_three_eq]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  simp only [mem_occ, not_not]
  rw [eCount_eq_sum, oCount_eq_sum, commonCount_eq_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  by_cases h1 : (c x ≠ none ∧ c z = none ∧ G.Adj x y ∧ G.Adj y z) ∧ c y = none
  · rw [ite_eq_left h1]
    obtain ⟨⟨hx, hz, hxy, hyz⟩, hy⟩ := h1
    have hxz : x ≠ z := fun e => hx (e ▸ hz)
    refine sum_congr rfl fun w _ => ?_
    by_cases hB : G.Adj x w ∧ G.Adj w z
    · have hcyc : (G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w) ↔ y ≠ w :=
        ⟨fun h => h.2.2.2.2.2, fun h => ⟨hxy, hyz, hB.2.symm, hB.1.symm, hxz, h⟩⟩
      rw [ite_eq_left hB]
      by_cases hw : c w = none
      · have e1 : G.Adj x w ∧ G.Adj w z ∧ c w = none := ⟨hB.1, hB.2, hw⟩
        have e2 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = c x) := fun h => hx (h.2.2.symm.trans hw)
        rw [ite_eq_left e1, ite_eq_right e2]
        by_cases hc : G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w
        · have e3 : ¬(c x ≠ none ∧ c y = none ∧ c z = none ∧ c w ≠ none) :=
            fun h => h.2.2.2 hw
          rw [ite_eq_left hc]
          unfold wE
          dsimp only
          rw [ite_eq_right e3]; ring
        · rw [ite_eq_right hc]; ring
      · have hyw : y ≠ w := fun e => hw (e ▸ hy)
        have e1 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = none) := fun h => hw h.2.2
        have e3 : c x ≠ none ∧ c y = none ∧ c z = none ∧ c w ≠ none := ⟨hx, hy, hz, hw⟩
        rw [ite_eq_right e1, ite_eq_left (hcyc.2 hyw)]
        unfold wE
        dsimp only
        rw [ite_eq_left e3]
        by_cases hs : c w = c x
        · have e2 : G.Adj x w ∧ G.Adj w z ∧ c w = c x := ⟨hB.1, hB.2, hs⟩
          rw [ite_eq_left e2, ite_eq_left hs]; ring
        · have e2 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = c x) := fun h => hs h.2.2
          rw [ite_eq_right e2, ite_eq_right hs]; ring
    · have e1 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = none) := fun h => hB ⟨h.1, h.2.1⟩
      have e2 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = c x) := fun h => hB ⟨h.1, h.2.1⟩
      have hc : ¬(G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w) :=
        fun h => hB ⟨h.2.2.2.1.symm, h.2.2.1.symm⟩
      rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right hB, ite_eq_right hc]
      ring
  · rw [ite_eq_right h1, sum_eq_zero]
    intro w _
    by_cases hc : G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w
    · have e3 : ¬(c x ≠ none ∧ c y = none ∧ c z = none ∧ c w ≠ none) :=
        fun h => h1 ⟨⟨h.1, h.2.2.1, hc.1, hc.2.1⟩, h.2.1⟩
      rw [ite_eq_left hc]
      unfold wE
      dsimp only
      rw [ite_eq_right e3]
    · rw [ite_eq_right hc]

/-! ### The relay part -/

omit [Fintype σ] in
theorem sum_O_eq (c : Config V σ) :
    ∑ t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c),
        ((if c t.2.1 = c t.1 then -((eCount G c t.1 t.2.2 : ℂ) - oCount G c t.1 t.2.2)
          else 1) - commonCount G t.1 t.2.2) =
      ∑ q ∈ fourCycleSeq G, wO c q := by
  rw [fourCycleSeq_sum, oneMoves, filter_filter, sum_filter, sum_three_eq]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  simp only [mem_occ, not_not]
  by_cases h1 : (c x ≠ none ∧ c z = none ∧ G.Adj x y ∧ G.Adj y z) ∧ c y ≠ none
  · rw [ite_eq_left h1]
    obtain ⟨⟨hx, hz, hxy, hyz⟩, hy⟩ := h1
    have hxz : x ≠ z := fun e => hx (e ▸ hz)
    have hO : c x ≠ none ∧ c y ≠ none ∧ c z = none := ⟨hx, hy, hz⟩
    -- the weight of the other paths `x → z`, against the relay through `y`
    set φ : V → ℂ := fun w => if c y = c x then
      (if c w = c x then 1 else 0) - (if c w = none then 1 else 0) - 1 else -1 with hφ
    have hR : ∀ w, (if G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w then
        wO c (x, y, z, w) else 0) =
        (if G.Adj x w ∧ G.Adj w z then φ w else 0) - (if w = y then φ w else 0) := by
      intro w
      by_cases hwy : w = y
      · subst hwy
        have hc : ¬(G.Adj x w ∧ G.Adj w z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ w ≠ w) :=
          fun h => h.2.2.2.2.2 rfl
        have hB : G.Adj x w ∧ G.Adj w z := ⟨hxy, hyz⟩
        rw [ite_eq_right hc, ite_eq_left hB, ite_eq_left rfl]
        ring
      · rw [ite_eq_right hwy, sub_zero]
        by_cases hB : G.Adj x w ∧ G.Adj w z
        · have hc : G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w :=
            ⟨hxy, hyz, hB.2.symm, hB.1.symm, hxz, Ne.symm hwy⟩
          rw [ite_eq_left hc, ite_eq_left hB]
          unfold wO
          dsimp only
          rw [ite_eq_left hO]
        · have hc : ¬(G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w) :=
            fun h => hB ⟨h.2.2.2.1.symm, h.2.2.1.symm⟩
          rw [ite_eq_right hc, ite_eq_right hB]
    rw [sum_congr rfl fun w _ => hR w, sum_sub_distrib, sum_ite_eq', ite_eq_left (mem_univ _)]
    rw [eCount_eq_sum, oCount_eq_sum, commonCount_eq_sum]
    by_cases hs : c y = c x
    · have hφy : φ y = 0 := by
        rw [hφ]
        dsimp only
        rw [ite_eq_left hs, ite_eq_left hs, ite_eq_right hy]; ring
      rw [hφy, ite_eq_left hs, sub_zero, ← sum_sub_distrib, ← sum_neg_distrib,
        ← sum_sub_distrib]
      refine sum_congr rfl fun w _ => ?_
      rw [hφ]
      dsimp only
      rw [ite_eq_left hs]
      by_cases hB : G.Adj x w ∧ G.Adj w z
      · rw [ite_eq_left hB, ite_eq_left hB]
        by_cases hw : c w = none
        · have hwx : c w ≠ c x := fun h => hx (h.symm.trans hw)
          have e1 : G.Adj x w ∧ G.Adj w z ∧ c w = none := ⟨hB.1, hB.2, hw⟩
          have e2 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = c x) := fun h => hwx h.2.2
          rw [ite_eq_left e1, ite_eq_right e2, ite_eq_right hwx, ite_eq_left hw]
          ring
        · have e1 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = none) := fun h => hw h.2.2
          rw [ite_eq_right e1, ite_eq_right hw]
          by_cases hs' : c w = c x
          · have e2 : G.Adj x w ∧ G.Adj w z ∧ c w = c x := ⟨hB.1, hB.2, hs'⟩
            rw [ite_eq_left e2, ite_eq_left hs']; ring
          · have e2 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = c x) := fun h => hs' h.2.2
            rw [ite_eq_right e2, ite_eq_right hs']; ring
      · have e1 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = none) := fun h => hB ⟨h.1, h.2.1⟩
        have e2 : ¬(G.Adj x w ∧ G.Adj w z ∧ c w = c x) := fun h => hB ⟨h.1, h.2.1⟩
        rw [ite_eq_right hB, ite_eq_right e1, ite_eq_right e2, ite_eq_right hB]
        ring
    · have hφy : φ y = -1 := by
        rw [hφ]
        dsimp only
        rw [ite_eq_right hs]
      have hsum : ∑ w, (if G.Adj x w ∧ G.Adj w z then φ w else 0) =
          -∑ w, (if G.Adj x w ∧ G.Adj w z then (1 : ℂ) else 0) := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun w _ => ?_
        rw [hφ]
        dsimp only
        rw [ite_eq_right hs]
        split_ifs <;> ring
      rw [hφy, hsum, ite_eq_right hs]
      ring
  · rw [ite_eq_right h1, sum_eq_zero]
    intro w _
    by_cases hc : G.Adj x y ∧ G.Adj y z ∧ G.Adj z w ∧ G.Adj w x ∧ x ≠ z ∧ y ≠ w
    · have e3 : ¬(c x ≠ none ∧ c y ≠ none ∧ c z = none) :=
        fun h => h1 ⟨⟨h.1, h.2.2, hc.1, hc.2.1⟩, h.2.1⟩
      rw [ite_eq_left hc]
      unfold wO
      dsimp only
      rw [ite_eq_right e3]
    · rw [ite_eq_right hc]

/-! ### The two-particle part -/

omit [Fintype σ] in
theorem sum_D_eq (c : Config V σ) :
    ∑ π ∈ twoMoves G (occ c),
        (-2 * (if G.Adj π.1.1 π.2.2 ∧ G.Adj π.2.1 π.1.2 then (1 : ℂ) else 0) -
          2 * (if G.Adj π.1.1 π.2.2 ∧ G.Adj π.2.1 π.1.2 ∧ c π.1.1 = c π.2.1 then 1 else 0)) =
      ∑ q ∈ fourCycleSeq G, wD c q := by
  rw [fourCycleSeq_sum, ← univ_inter (twoMoves G (occ c)), ← sum_ite_mem]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun u₁ _ => sum_congr rfl fun w₁ _ => sum_congr rfl fun u₂ _ =>
    sum_congr rfl fun w₂ _ => ?_
  by_cases hm : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G (occ c)
  · rw [ite_eq_left hm]
    have h1 := (mem_twoMoves_iff G).1 hm
    rw [mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not] at h1
    obtain ⟨a1, a2, hu1, hu2, hw1, hw2, hu, hw⟩ := h1
    have hD : c u₁ ≠ none ∧ c w₁ = none ∧ c u₂ ≠ none ∧ c w₂ = none := ⟨hu1, hw1, hu2, hw2⟩
    by_cases hA : G.Adj u₁ w₂ ∧ G.Adj u₂ w₁
    · have hc : G.Adj u₁ w₁ ∧ G.Adj w₁ u₂ ∧ G.Adj u₂ w₂ ∧ G.Adj w₂ u₁ ∧ u₁ ≠ u₂ ∧ w₁ ≠ w₂ :=
        ⟨a1, hA.2.symm, a2, hA.1.symm, hu, hw⟩
      rw [ite_eq_left hA, ite_eq_left hc]
      unfold wD
      dsimp only
      rw [ite_eq_left hD]
      by_cases hs : c u₁ = c u₂
      · have e : G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ ∧ c u₁ = c u₂ := ⟨hA.1, hA.2, hs⟩
        rw [ite_eq_left e, ite_eq_left hs]; ring
      · have e : ¬(G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ ∧ c u₁ = c u₂) := fun h => hs h.2.2
        rw [ite_eq_right e, ite_eq_right hs]; ring
    · have e : ¬(G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ ∧ c u₁ = c u₂) := fun h => hA ⟨h.1, h.2.1⟩
      have hc : ¬(G.Adj u₁ w₁ ∧ G.Adj w₁ u₂ ∧ G.Adj u₂ w₂ ∧ G.Adj w₂ u₁ ∧ u₁ ≠ u₂ ∧ w₁ ≠ w₂) :=
        fun h => hA ⟨h.2.2.2.1.symm, h.2.1.symm⟩
      rw [ite_eq_right hA, ite_eq_right e, ite_eq_right hc]
      ring
  · rw [ite_eq_right hm]
    by_cases hc : G.Adj u₁ w₁ ∧ G.Adj w₁ u₂ ∧ G.Adj u₂ w₂ ∧ G.Adj w₂ u₁ ∧ u₁ ≠ u₂ ∧ w₁ ≠ w₂
    · have e3 : ¬(c u₁ ≠ none ∧ c w₁ = none ∧ c u₂ ≠ none ∧ c w₂ = none) := by
        intro h
        refine hm ((mem_twoMoves_iff G).2 ?_)
        rw [mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not]
        exact ⟨hc.1, hc.2.2.1, h.1, h.2.2.1, h.2.1, h.2.2.2, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
      rw [ite_eq_left hc]
      unfold wD
      dsimp only
      rw [ite_eq_right e3]
    · rw [ite_eq_right hc]

/-! ### The difference -/

/-- **Fermions = hard-core bosons + the 4-cycle weights**, for one configuration. -/
theorem sum_Qf_sq_eq_boson_add {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n) :
    ∑ c'' ∈ basis V n, Qf G ord c'' c ^ 2 =
      ((∑ T ∈ powersetCard (occ c).card (univ : Finset V), pathCount G T (occ c) ^ 2 : ℕ) : ℂ) +
        ∑ q ∈ fourCycleSeq G, (wE c q + wO c q + wD c q) := by
  have hsplit : ∑ q ∈ fourCycleSeq G, (wE c q + wO c q + wD c q) =
      ∑ q ∈ fourCycleSeq G, wE c q + ∑ q ∈ fourCycleSeq G, wO c q +
        ∑ q ∈ fourCycleSeq G, wD c q := by
    rw [sum_add_distrib, sum_add_distrib]
  rw [sum_Qf_sq_eq hc, sum_pathCount_sq_eq G (occ c) rfl, hsplit, ← sum_E_eq, ← sum_O_eq,
    ← sum_D_eq, ← sum_filter_add_sum_filter_not (oneMoves G (occ c)) (fun t => t.2.1 ∉ occ c)]
  push_cast
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  ring

end Delta

end HubbardMoments
