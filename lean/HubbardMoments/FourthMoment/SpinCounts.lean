-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.FermionDelta

/-!
# Counting spin-½ configurations by a local pattern

Stage 6 of the fourth-moment plan, first part. A configuration of spin-½ particles
(`σ = Bool`) is a pair of disjoint sets, the up sites and the down sites (`mkC`,
`sum_basis_bool`). Counting the configurations of the basis with `n↑` up and `n↓` down
particles by what they hold on given sites:

* given sites all up, others empty: `C(N - x - y, n↑ - x) · C(N - y - n↑, n↓)`, in pattern
  form (`count_true`); all down, likewise (`count_false`); the basis itself
  (`card_basis_bool`);
* given sites occupied (any spin), others empty: `|B| p_xy` (`count_occ`);
* `patternCount N n a b · (N)_{a+b} = C(N, n) (n)_a (N - n)_b`
  (`patternCount_mul_descFactorial`), so every count is `|B|` times a ratio of falling
  factorials.

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset

/-! ### Falling factorials -/

theorem patternCount_mul_descFactorial (N n a b : ℕ) :
    patternCount N n a b * N.descFactorial (a + b) =
      N.choose n * n.descFactorial a * (N - n).descFactorial b := by
  unfold patternCount
  split_ifs with ha
  · by_cases hb : n + b ≤ N
    · have hk : n - a ≤ N - (a + b) := by omega
      have h1 := Nat.choose_mul_factorial_mul_factorial hk
      have h2 := Nat.factorial_mul_descFactorial (show a + b ≤ N by omega)
      have h3 := Nat.choose_mul_factorial_mul_factorial (show n ≤ N by omega)
      have h4 := Nat.factorial_mul_descFactorial ha
      have h5 := Nat.factorial_mul_descFactorial (show b ≤ N - n by omega)
      have e : N - (a + b) - (n - a) = N - n - b := by omega
      rw [e] at h1
      apply Nat.eq_of_mul_eq_mul_right
        (Nat.mul_pos (Nat.factorial_pos (n - a)) (Nat.factorial_pos (N - n - b)))
      calc (N - (a + b)).choose (n - a) * N.descFactorial (a + b) *
            ((n - a).factorial * (N - n - b).factorial)
          = (N - (a + b)).choose (n - a) * (n - a).factorial * (N - n - b).factorial *
              N.descFactorial (a + b) := by ring
        _ = (N - (a + b)).factorial * N.descFactorial (a + b) := by rw [h1]
        _ = N.factorial := h2
        _ = N.choose n * n.factorial * (N - n).factorial := h3.symm
        _ = N.choose n * ((n - a).factorial * n.descFactorial a) *
              ((N - n - b).factorial * (N - n).descFactorial b) := by rw [h4, h5]
        _ = N.choose n * n.descFactorial a * (N - n).descFactorial b *
              ((n - a).factorial * (N - n - b).factorial) := by ring
    · by_cases hnN : n ≤ N
      · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : N - n < b), mul_zero]
        by_cases hab : a + b ≤ N
        · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
        · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega), mul_zero]
      · rw [Nat.choose_eq_zero_of_lt (by omega : N < n), zero_mul, zero_mul]
        by_cases hab : a + b ≤ N
        · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
        · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega), mul_zero]
  · have h0 : n.descFactorial a = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    rw [h0]
    simp

theorem cast_descFactorial (m k : ℕ) :
    (m.descFactorial k : ℂ) = ∏ i ∈ range k, ((m : ℂ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul, ih, prod_range_succ]
    by_cases hk : k ≤ m
    · rw [Nat.cast_sub hk]; ring
    · have h0 : ∏ i ∈ range k, ((m : ℂ) - i) = 0 :=
        prod_eq_zero (mem_range.2 (by omega : m < k)) (by simp)
      rw [h0]; ring

/-! ### Configurations as pairs of sets -/

section Pairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The configuration with up spins on `U` and down spins on `D \ U`. -/
def mkC (U D : Finset V) : Config V Bool := fun v =>
  if v ∈ U then some true else if v ∈ D then some false else none

/-- The up sites of a configuration. -/
def upSet (c : Config V Bool) : Finset V := univ.filter fun v => c v = some true

/-- The down sites of a configuration. -/
def downSet (c : Config V Bool) : Finset V := univ.filter fun v => c v = some false

theorem mkC_up_down (c : Config V Bool) : mkC (upSet c) (downSet c) = c := by
  funext v
  simp only [mkC, upSet, downSet, mem_filter, mem_univ, true_and]
  cases hc : c v with
  | none => simp
  | some b => cases b <;> simp

omit [DecidableEq V] in
theorem upSet_mkC [DecidableEq V] {U D : Finset V} : upSet (mkC U D) = U := by
  ext v
  rw [upSet, mem_filter, mkC]
  by_cases hU : v ∈ U
  · simp [hU]
  · by_cases hD : v ∈ D <;> simp [hU, hD]

theorem downSet_mkC {U D : Finset V} (h : Disjoint U D) : downSet (mkC U D) = D := by
  ext v
  rw [downSet, mem_filter, mkC]
  by_cases hU : v ∈ U
  · have hD : v ∉ D := disjoint_left.1 h hU
    simp [hU, hD]
  · by_cases hD : v ∈ D <;> simp [hU, hD]

theorem mem_basis_bool {n : Bool → ℕ} {c : Config V Bool} :
    c ∈ basis V n ↔ (upSet c).card = n true ∧ (downSet c).card = n false := by
  simp only [basis, mem_filter, mem_univ, true_and, Bool.forall_bool, upSet, downSet]
  tauto

omit [DecidableEq V] in
theorem disjoint_up_down (c : Config V Bool) : Disjoint (upSet c) (downSet c) := by
  rw [disjoint_left]
  intro v h1 h2
  simp only [upSet, downSet, mem_filter, mem_univ, true_and] at h1 h2
  rw [h1] at h2
  simp at h2

/-- **The basis as pairs of disjoint sets.** -/
theorem sum_basis_bool {M : Type*} [AddCommMonoid M] (n : Bool → ℕ) (f : Config V Bool → M) :
    ∑ c ∈ basis V n, f c =
      ∑ U ∈ powersetCard (n true) (univ : Finset V),
        ∑ D ∈ powersetCard (n false) (univ : Finset V),
          if Disjoint U D then f (mkC U D) else 0 := by
  rw [← sum_product' (f := fun U D => if Disjoint U D then f (mkC U D) else 0), ← sum_filter]
  refine sum_nbij' (fun c => (upSet c, downSet c)) (fun p => mkC p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_basis_bool] at hc
    rw [mem_filter, mem_product, mem_powersetCard, mem_powersetCard]
    exact ⟨⟨⟨subset_univ _, hc.1⟩, ⟨subset_univ _, hc.2⟩⟩, disjoint_up_down c⟩
  · rintro ⟨U, D⟩ hp
    rw [mem_filter, mem_product, mem_powersetCard, mem_powersetCard] at hp
    rw [mem_basis_bool, upSet_mkC, downSet_mkC hp.2]
    exact ⟨hp.1.1.2, hp.1.2.2⟩
  · intro c _
    exact mkC_up_down c
  · rintro ⟨U, D⟩ hp
    rw [mem_filter] at hp
    simp only
    rw [upSet_mkC, downSet_mkC hp.2]
  · intro c _
    simp only
    rw [mkC_up_down]

variable (n : Bool → ℕ)

/-- **Given sites all up, other given sites empty.** -/
theorem count_true (X Y : Finset V) (hXY : Disjoint X Y) :
    ((basis V n).filter fun c => (∀ v ∈ X, c v = some true) ∧ ∀ v ∈ Y, c v = none).card =
      patternCount (Fintype.card V) (n true) X.card Y.card *
        patternCount (Fintype.card V) (n false) 0 (Y.card + n true) := by
  rw [card_filter, sum_basis_bool]
  have inner : ∀ U ∈ powersetCard (n true) (univ : Finset V),
      (∑ D ∈ powersetCard (n false) (univ : Finset V), if Disjoint U D then
        (if (∀ v ∈ X, mkC U D v = some true) ∧ ∀ v ∈ Y, mkC U D v = none then 1 else 0) else 0) =
      if X ⊆ U ∧ Disjoint Y U then
        patternCount (Fintype.card V) (n false) 0 (Y.card + n true) else 0 := by
    intro U hU
    have hUc : U.card = n true := (mem_powersetCard.1 hU).2
    split_ifs with hXU
    · have hk := card_pattern ∅ (Y ∪ U) (disjoint_empty_left _) (n false)
      rw [card_empty, card_union_of_disjoint hXU.2, hUc] at hk
      rw [← hk, card_filter]
      refine sum_congr rfl fun D _ => ?_
      by_cases hUD : Disjoint U D
      · rw [ite_eq_left hUD]
        have key : ((∀ v ∈ X, mkC U D v = some true) ∧ ∀ v ∈ Y, mkC U D v = none) ↔
            (∅ ⊆ D ∧ Disjoint (Y ∪ U) D) := by
          simp only [mkC, empty_subset, true_and, disjoint_union_left, hUD, and_true]
          constructor
          · rintro ⟨-, hY⟩
            rw [disjoint_left]
            intro v hv hvD
            have := hY v hv
            rw [ite_eq_right (disjoint_left.1 hXU.2 hv), ite_eq_left hvD] at this
            simp at this
          · intro hYD
            refine ⟨fun v hv => ite_eq_left (hXU.1 hv), fun v hv => ?_⟩
            rw [ite_eq_right (disjoint_left.1 hXU.2 hv), ite_eq_right (disjoint_left.1 hYD hv)]
        simp only [key]
      · rw [ite_eq_right hUD]
        have : ¬ (∅ ⊆ D ∧ Disjoint (Y ∪ U) D) := fun h =>
          hUD (disjoint_of_subset_left subset_union_right h.2)
        rw [ite_eq_right this]
    · refine sum_eq_zero fun D _ => ?_
      by_cases hUD : Disjoint U D
      · rw [ite_eq_left hUD, ite_eq_right]
        rintro ⟨hX, hY⟩
        refine hXU ⟨fun v hv => ?_, disjoint_left.2 fun v hv hvU => ?_⟩
        · have := hX v hv
          by_contra hvU
          by_cases hvD : v ∈ D <;> simp [mkC, hvU, hvD] at this
        · have := hY v hv
          rw [mkC, ite_eq_left hvU] at this
          simp at this
      · rw [ite_eq_right hUD]
  rw [sum_congr rfl inner, ← sum_filter, sum_const, smul_eq_mul,
    card_pattern X Y hXY (n true)]

/-- **Given sites all down, other given sites empty.** -/
theorem count_false (X Y : Finset V) (hXY : Disjoint X Y) :
    ((basis V n).filter fun c => (∀ v ∈ X, c v = some false) ∧ ∀ v ∈ Y, c v = none).card =
      patternCount (Fintype.card V) (n false) X.card Y.card *
        patternCount (Fintype.card V) (n true) 0 (Y.card + n false) := by
  rw [card_filter, sum_basis_bool, sum_comm]
  have inner : ∀ D ∈ powersetCard (n false) (univ : Finset V),
      (∑ U ∈ powersetCard (n true) (univ : Finset V), if Disjoint U D then
        (if (∀ v ∈ X, mkC U D v = some false) ∧ ∀ v ∈ Y, mkC U D v = none then 1 else 0)
          else 0) =
      if X ⊆ D ∧ Disjoint Y D then
        patternCount (Fintype.card V) (n true) 0 (Y.card + n false) else 0 := by
    intro D hD
    have hDc : D.card = n false := (mem_powersetCard.1 hD).2
    split_ifs with hXD
    · have hk := card_pattern ∅ (Y ∪ D) (disjoint_empty_left _) (n true)
      rw [card_empty, card_union_of_disjoint hXD.2, hDc] at hk
      rw [← hk, card_filter]
      refine sum_congr rfl fun U _ => ?_
      by_cases hUD : Disjoint U D
      · rw [ite_eq_left hUD]
        have key : ((∀ v ∈ X, mkC U D v = some false) ∧ ∀ v ∈ Y, mkC U D v = none) ↔
            (∅ ⊆ U ∧ Disjoint (Y ∪ D) U) := by
          simp only [mkC, empty_subset, true_and, disjoint_union_left, hUD.symm, and_true]
          constructor
          · rintro ⟨-, hY⟩
            rw [disjoint_left]
            intro v hv hvU
            have := hY v hv
            rw [ite_eq_left hvU] at this
            simp at this
          · intro hYU
            refine ⟨fun v hv => ?_, fun v hv => ?_⟩
            · rw [ite_eq_right (disjoint_right.1 hUD (hXD.1 hv)), ite_eq_left (hXD.1 hv)]
            · rw [ite_eq_right (disjoint_left.1 hYU hv), ite_eq_right (disjoint_left.1 hXD.2 hv)]
        simp only [key]
      · rw [ite_eq_right hUD]
        have : ¬ (∅ ⊆ U ∧ Disjoint (Y ∪ D) U) := fun h =>
          hUD (disjoint_of_subset_left subset_union_right h.2).symm
        rw [ite_eq_right this]
    · refine sum_eq_zero fun U _ => ?_
      by_cases hUD : Disjoint U D
      · rw [ite_eq_left hUD, ite_eq_right]
        rintro ⟨hX, hY⟩
        refine hXD ⟨fun v hv => ?_, disjoint_left.2 fun v hv hvD => ?_⟩
        · have := hX v hv
          by_contra hvD
          by_cases hvU : v ∈ U <;> simp [mkC, hvU, hvD] at this
        · have := hY v hv
          rw [mkC, ite_eq_right (disjoint_right.1 hUD hvD), ite_eq_left hvD] at this
          simp at this
      · rw [ite_eq_right hUD]
  rw [sum_congr rfl inner, ← sum_filter, sum_const, smul_eq_mul,
    card_pattern X Y hXY (n false)]

theorem card_basis_bool :
    (basis V n).card = (Fintype.card V).choose (n true) *
      patternCount (Fintype.card V) (n false) 0 (n true) := by
  have h := count_true n (∅ : Finset V) ∅ (disjoint_empty_left _)
  have hf : ((basis V n).filter fun c => (∀ v ∈ (∅ : Finset V), c v = some true) ∧
      ∀ v ∈ (∅ : Finset V), c v = none) = basis V n := by
    ext c; simp
  rw [hf, card_empty, zero_add] at h
  rw [h]
  simp [patternCount]

/-- **Given sites occupied, other given sites empty**:
`#{c ∈ B} · C(N, n) = |B| · C(N, n) p_xy` (in pattern form). -/
theorem count_occ {σ : Type*} [Fintype σ] [DecidableEq σ] (m : σ → ℕ) (X Y : Finset V)
    (hXY : Disjoint X Y) :
    (((basis V m).filter fun c => (∀ v ∈ X, c v ≠ none) ∧ ∀ v ∈ Y, c v = none).card : ℂ) *
        (Fintype.card V).choose (∑ s, m s) =
      (basis V m).card * patternCount (Fintype.card V) (∑ s, m s) X.card Y.card := by
  have h := sum_basis_comp_occ m (fun S => if X ⊆ S ∧ Disjoint Y S then (1 : ℂ) else 0)
  rw [← card_pattern X Y hXY, card_filter, card_filter] at *
  push_cast at h ⊢
  convert h using 2
  · refine sum_congr rfl fun c _ => ?_
    have : ((∀ v ∈ X, c v ≠ none) ∧ ∀ v ∈ Y, c v = none) ↔ (X ⊆ occ c ∧ Disjoint Y (occ c)) := by
      constructor
      · rintro ⟨hX, hY⟩
        exact ⟨fun v hv => (mem_occ).2 (hX v hv),
          disjoint_left.2 fun v hv hvc => (mem_occ).1 hvc (hY v hv)⟩
      · rintro ⟨hX, hY⟩
        exact ⟨fun v hv => (mem_occ).1 (hX hv),
          fun v hv => by_contra fun h => disjoint_left.1 hY hv ((mem_occ).2 h)⟩
    simp only [this]

end Pairs

end HubbardMoments
