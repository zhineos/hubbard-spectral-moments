-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.SpinCounts

/-!
# The exact fourth moment of `H∞`

Stage 6 of the fourth-moment plan: `fourthMoment_projectedHubbard` proves
`Spec.FourthMomentHubbard`. For spin-½ fermions (`σ = Bool`) on any finite simple graph
with `N ≥ 4` sites, uniform hopping `t`, no Peierls phases and any ordering of the orbitals,
`μ₄(∞) = t⁴ (A(N, n) + α(N, n) P_same)`.

## Method

* `H∞ = t · hinf` (`projectedHubbard_eq_smul`), so `μ₄ = t⁴ μ₄(hinf)` (`fourthMoment_smul`).
* `|B| μ₄ = ∑_{c, c''} (H²)_{c'' c}² = ∑_c [boson value at occ c] + ∑_c ∑_q w(c, q)`
  (`block_sum_hinf`, `sum_Qf_sq_eq_boson_add`), the second sum over the 4-cycle sequences `q`.
* The boson part averages to `μ₄^HCB` (`sum_basis_comp_occ`, `sum_sq_pathCount`).
* For every 4-cycle sequence, `∑_c w(c, q)` is the same combination of pattern counts
  (`w_local`, `sum_w`): occupation patterns (`count_occ`) and same-spin patterns
  (`count_true`, `count_false`), so `∑_q ∑_c w = 8 C₄ Φ`.
* The closed forms are then an identity of rational functions of `N`, `n↑`, `n↓`
  (`fourthMoment_hinf`), which uses that for two species the same-spin triples are fixed by
  the same-spin pairs.

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset

/-- `μ₄` scales as the fourth power. -/
theorem fourthMoment_smul {ι : Type*} (B : Finset ι) (H : Matrix ι ι ℂ) (r : ℂ) :
    fourthMoment B (r • H) = r ^ 4 * fourthMoment B H := by
  simp only [fourthMoment, Matrix.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', mul_sum]
  congr 1
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun b₁ _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun b₂ _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun b₃ _ => ?_
  ring

section Local

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `1` if the sites of `X` are occupied and those of `Y` empty. -/
def occInd (c : Config V Bool) (X Y : Finset V) : ℂ :=
  if (∀ v ∈ X, c v ≠ none) ∧ ∀ v ∈ Y, c v = none then 1 else 0

/-- `1` if the sites of `X` hold spin `s` and those of `Y` are empty. -/
def spinInd (s : Bool) (c : Config V Bool) (X Y : Finset V) : ℂ :=
  if (∀ v ∈ X, c v = some s) ∧ ∀ v ∈ Y, c v = none then 1 else 0

/-- **The local weight as pattern indicators.** -/
theorem w_local (c : Config V Bool) (a b c' d : V) :
    wE c (a, b, c', d) + wO c (a, b, c', d) + wD c (a, b, c', d) =
      -occInd c {a, d} {b, c'} - (spinInd true c {a, d} {b, c'} + spinInd false c {a, d} {b, c'})
        - occInd c {a, b} {c'} +
          (spinInd true c {a, b, d} {c'} + spinInd false c {a, b, d} {c'})
        - (spinInd true c {a, b} {c', d} + spinInd false c {a, b} {c', d})
        - 2 * occInd c {a, c'} {b, d} -
          2 * (spinInd true c {a, c'} {b, d} + spinInd false c {a, c'} {b, d}) := by
  simp only [wE, wO, wD, occInd, spinInd, mem_insert, mem_singleton, forall_eq_or_imp,
    forall_eq]
  generalize c a = A
  generalize c b = B
  generalize c c' = C
  generalize c d = D
  rcases A with _ | ⟨_ | _⟩ <;> rcases B with _ | ⟨_ | _⟩ <;> rcases C with _ | ⟨_ | _⟩ <;>
    rcases D with _ | ⟨_ | _⟩ <;> norm_num

variable (n : Bool → ℕ)

theorem sum_occInd (X Y : Finset V) (hXY : Disjoint X Y) :
    (∑ c ∈ basis V n, occInd c X Y) * (Fintype.card V).choose (n true + n false) =
      (basis V n).card * patternCount (Fintype.card V) (n true + n false) X.card Y.card := by
  have h := count_occ n X Y hXY
  rw [Fintype.sum_bool] at h
  simp only [occInd]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  exact h

theorem sum_spinInd_true (X Y : Finset V) (hXY : Disjoint X Y) :
    ∑ c ∈ basis V n, spinInd true c X Y =
      ((patternCount (Fintype.card V) (n true) X.card Y.card *
        patternCount (Fintype.card V) (n false) 0 (Y.card + n true) : ℕ) : ℂ) := by
  rw [← count_true n X Y hXY]
  simp only [spinInd]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

theorem sum_spinInd_false (X Y : Finset V) (hXY : Disjoint X Y) :
    ∑ c ∈ basis V n, spinInd false c X Y =
      ((patternCount (Fintype.card V) (n false) X.card Y.card *
        patternCount (Fintype.card V) (n true) 0 (Y.card + n false) : ℕ) : ℂ) := by
  rw [← count_false n X Y hXY]
  simp only [spinInd]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

end Local

/-! ### Counting identities in falling-factorial form -/

/-- Up sites first, then down sites: `C(N - y - a, b)` choices for the down sites. -/
theorem spin_count_mul (N a b x y : ℕ) :
    patternCount N a x y * patternCount N b 0 (y + a) * N.descFactorial (x + y) =
      N.choose a * (N - a).choose b * a.descFactorial x * (N - (a + b)).descFactorial y := by
  have e2 : patternCount N b 0 (y + a) = patternCount (N - a) b 0 y := by
    unfold patternCount
    simp only [zero_le, ↓reduceIte, Nat.sub_zero]
    congr 1
    omega
  have E1 := patternCount_mul_descFactorial N a x y
  have E3 := patternCount_mul_descFactorial (N - a) b 0 y
  simp only [zero_add, Nat.descFactorial_zero, mul_one] at E3
  rw [e2, show N - (a + b) = N - a - b by omega]
  calc patternCount N a x y * patternCount (N - a) b 0 y * N.descFactorial (x + y)
      = (patternCount N a x y * N.descFactorial (x + y)) * patternCount (N - a) b 0 y := by ring
    _ = N.choose a * a.descFactorial x * ((N - a).descFactorial y *
          patternCount (N - a) b 0 y) := by rw [E1]; ring
    _ = N.choose a * a.descFactorial x * ((N - a).choose b * (N - a - b).descFactorial y) := by
          rw [mul_comm ((N - a).descFactorial y), E3]
    _ = _ := by ring

theorem choose_mul_choose_comm (N a b : ℕ) :
    N.choose a * (N - a).choose b = N.choose b * (N - b).choose a := by
  have h1 := Nat.choose_mul (n := N) (k := a + b) (s := a) (by omega)
  have h2 := Nat.choose_mul (n := N) (k := a + b) (s := b) (by omega)
  rw [show a + b - a = b by omega] at h1
  rw [show a + b - b = a by omega] at h2
  rw [← h1, ← h2, Nat.choose_symm_add]

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (n : Bool → ℕ)

variable (V) in
/-- The occupation count `|B| p_xy`, in pattern form. -/
noncomputable def obV (x y : ℕ) : ℂ :=
  ((basis V n).card : ℂ) * patternCount (Fintype.card V) (n true + n false) x y /
    (Fintype.card V).choose (n true + n false)

variable (V) in
/-- The same-spin count: all up plus all down. -/
noncomputable def ssV (x y : ℕ) : ℂ :=
  ((patternCount (Fintype.card V) (n true) x y *
      patternCount (Fintype.card V) (n false) 0 (y + n true) : ℕ) : ℂ) +
    ((patternCount (Fintype.card V) (n false) x y *
      patternCount (Fintype.card V) (n true) 0 (y + n false) : ℕ) : ℂ)

/-- **`∑_c w(c, q)` is the same for every 4-cycle sequence.** -/
theorem sum_w {a b c' d : V} (hq : (a, b, c', d) ∈ fourCycleSeq G)
    (hnN : n true + n false ≤ Fintype.card V) :
    ∑ c ∈ basis V n, (wE c (a, b, c', d) + wO c (a, b, c', d) + wD c (a, b, c', d)) =
      -obV V n 2 2 - ssV V n 2 2 - obV V n 2 1 + ssV V n 3 1 - ssV V n 2 2 -
        2 * obV V n 2 2 - 2 * ssV V n 2 2 := by
  rw [fourCycleSeq, mem_filter] at hq
  obtain ⟨-, hab, hbc, hcd, hda, hac, hbd⟩ := hq
  simp only at hab hbc hcd hda hac hbd
  have hab' : a ≠ b := hab.ne
  have hbc' : b ≠ c' := hbc.ne
  have hcd' : c' ≠ d := hcd.ne
  have hda' : d ≠ a := hda.ne
  have hba : b ≠ a := hab'.symm
  have hcb : c' ≠ b := hbc'.symm
  have hdc : d ≠ c' := hcd'.symm
  have had : a ≠ d := hda'.symm
  have hca : c' ≠ a := hac.symm
  have hdb : d ≠ b := hbd.symm
  have d1 : Disjoint ({a, d} : Finset V) {b, c'} := by simp [*]
  have d2 : Disjoint ({a, b} : Finset V) {c'} := by simp [*]
  have d3 : Disjoint ({a, b, d} : Finset V) {c'} := by simp [*]
  have d4 : Disjoint ({a, b} : Finset V) {c', d} := by simp [*]
  have d5 : Disjoint ({a, c'} : Finset V) {b, d} := by simp [*]
  have hC : ((Fintype.card V).choose (n true + n false) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hnN).ne'
  have hOB : ∀ X Y : Finset V, Disjoint X Y →
      ∑ c ∈ basis V n, occInd c X Y = obV V n X.card Y.card := by
    intro X Y hXY
    rw [obV, eq_div_iff hC]
    exact sum_occInd n X Y hXY
  have hSS : ∀ X Y : Finset V, Disjoint X Y →
      ∑ c ∈ basis V n, spinInd true c X Y + ∑ c ∈ basis V n, spinInd false c X Y =
        ssV V n X.card Y.card := by
    intro X Y hXY
    rw [sum_spinInd_true n X Y hXY, sum_spinInd_false n X Y hXY, ssV]
  have k1 : ({a, d} : Finset V).card = 2 := card_pair hda'.symm
  have k2 : ({b, c'} : Finset V).card = 2 := card_pair hbc'
  have k3 : ({a, b} : Finset V).card = 2 := card_pair hab'
  have k4 : ({c'} : Finset V).card = 1 := card_singleton _
  have k5 : ({a, b, d} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab', hda'.symm]), card_pair hbd]
  have k6 : ({c', d} : Finset V).card = 2 := card_pair hcd'
  have k7 : ({a, c'} : Finset V).card = 2 := card_pair hac
  have k8 : ({b, d} : Finset V).card = 2 := card_pair hbd
  rw [sum_congr rfl fun c _ => w_local c a b c' d]
  simp only [sum_add_distrib, sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  rw [hOB _ _ d1, hOB _ _ d2, hOB _ _ d5, hSS _ _ d1, hSS _ _ d3, hSS _ _ d4, hSS _ _ d5]
  rw [k1, k2, k3, k4, k7, k8, k5, k6]

end Main

/-! ### The theorem -/

section Final

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem complexDescFactorial_one (m : ℕ) : (m.descFactorial 1 : ℂ) = m := by
  rw [cast_descFactorial]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_zero, sub_zero]

theorem complexDescFactorial_two (m : ℕ) : (m.descFactorial 2 : ℂ) = m * (m - 1) := by
  rw [cast_descFactorial]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_zero, Nat.cast_one, sub_zero]

theorem complexDescFactorial_three (m : ℕ) :
    (m.descFactorial 3 : ℂ) = m * (m - 1) * (m - 2) := by
  rw [cast_descFactorial]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, sub_zero]

theorem complexDescFactorial_four (m : ℕ) :
    (m.descFactorial 4 : ℂ) = m * (m - 1) * (m - 2) * (m - 3) := by
  rw [cast_descFactorial]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, sub_zero]

/-- **The exact fourth moment of `H∞` with `t = 1`.** -/
theorem fourthMoment_hinf (ord : V × Bool ↪ ℕ) (n : Bool → ℕ) (hN : 4 ≤ Fintype.card V)
    (hnN : n true + n false ≤ Fintype.card V) :
    fourthMoment (basis V n) (hinf G ord) =
      ((fourthMomentIntercept G (n true + n false) + exchangeSlope G (n true + n false) *
        ((n true).choose 2 + (n false).choose 2 : ℕ) : ℝ) : ℂ) := by
  set N := Fintype.card V with hNdef
  set B := basis V n with hBdef
  have hBcard : B.card = N.choose (n true) * (N - n true).choose (n false) := by
    rw [hBdef, card_basis_bool]
    simp only [patternCount, Nat.zero_le, ↓reduceIte, zero_add, Nat.sub_zero]
    rfl
  have hB0 : (B.card : ℂ) ≠ 0 := by
    rw [hBcard]; push_cast
    exact mul_ne_zero (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
      (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
  have hC0 : (N.choose (n true + n false) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hnN).ne'
  -- the total over the basis
  have hX : fourthMoment B (hinf G ord) =
      (∑ c ∈ B, ∑ c'' ∈ B, Qf G ord c'' c ^ 2) / B.card := by
    rw [fourthMoment, block_sum_hinf]
  have hsplit : ∑ c ∈ B, ∑ c'' ∈ B, Qf G ord c'' c ^ 2 =
      ∑ c ∈ B, ((∑ T ∈ powersetCard (occ c).card (univ : Finset V),
        pathCount G T (occ c) ^ 2 : ℕ) : ℂ) +
      ∑ c ∈ B, ∑ q ∈ fourCycleSeq G, (wE c q + wO c q + wD c q) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun c hc => sum_Qf_sq_eq_boson_add hc
  -- the boson part
  have hbos : ∑ c ∈ B, ((∑ T ∈ powersetCard (occ c).card (univ : Finset V),
        pathCount G T (occ c) ^ 2 : ℕ) : ℂ) =
      B.card * (((2 * G.edgeFinset.card + 4 * wedgeCount G + 8 * fourCycleCount G) *
          patternCount N (n true + n false) 1 1 +
        (24 * disjointEdgePairs G + 16 * fourCycleCount G) *
          patternCount N (n true + n false) 2 2 : ℕ) : ℂ) / N.choose (n true + n false) := by
    rw [eq_div_iff hC0]
    have h := sum_basis_comp_occ n (fun S => ((∑ T ∈ powersetCard S.card (univ : Finset V),
      pathCount G T S ^ 2 : ℕ) : ℂ))
    rw [Fintype.sum_bool] at h
    rw [h, ← sum_sq_pathCount G (n true + n false) (by omega)]
    push_cast
    congr 1
    refine sum_congr rfl fun S hS => ?_
    rw [(mem_powersetCard.1 hS).2]
  -- the 4-cycle part
  have hcyc : ∑ c ∈ B, ∑ q ∈ fourCycleSeq G, (wE c q + wO c q + wD c q) =
      (8 * fourCycleCount G : ℕ) * (-obV V n 2 2 - ssV V n 2 2 - obV V n 2 1 + ssV V n 3 1 -
        ssV V n 2 2 - 2 * obV V n 2 2 - 2 * ssV V n 2 2) := by
    have hq' : ∀ q ∈ fourCycleSeq G, ∑ c ∈ B, (wE c q + wO c q + wD c q) =
        -obV V n 2 2 - ssV V n 2 2 - obV V n 2 1 + ssV V n 3 1 - ssV V n 2 2 -
          2 * obV V n 2 2 - 2 * ssV V n 2 2 := by
      intro q hq
      obtain ⟨a, b, c', d⟩ := q
      exact sum_w G n hq hnN
    rw [sum_comm, sum_congr rfl hq', sum_const, nsmul_eq_mul, ← eight_mul_fourCycleCount]
  -- closed forms of the counts
  set Nc : ℂ := (N : ℂ) with hNc
  set u : ℂ := (n true : ℂ) with hu
  set d : ℂ := (n false : ℂ) with hd
  have hK : ((N - (n true + n false) : ℕ) : ℂ) = Nc - (u + d) := by
    rw [Nat.cast_sub hnN]; push_cast; ring
  have hN0 : Nc ≠ 0 := by rw [hNc]; exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : Nc - 1 ≠ 0 := by
    rw [hNc, sub_ne_zero]; exact_mod_cast (show N ≠ 1 by omega)
  have hN2 : Nc - 2 ≠ 0 := by
    rw [hNc, sub_ne_zero]; exact_mod_cast (show N ≠ 2 by omega)
  have hN3 : Nc - 3 ≠ 0 := by
    rw [hNc, sub_ne_zero]; exact_mod_cast (show N ≠ 3 by omega)
  have L : ∀ x y : ℕ, (patternCount N (n true + n false) x y : ℂ) * (N.descFactorial (x + y) : ℂ) =
      N.choose (n true + n false) * (n true + n false).descFactorial x *
        (N - (n true + n false)).descFactorial y := by
    intro x y
    exact_mod_cast patternCount_mul_descFactorial N (n true + n false) x y
  have p11 : (patternCount N (n true + n false) 1 1 : ℂ) =
      N.choose (n true + n false) * ((u + d) * (Nc - (u + d))) / (Nc * (Nc - 1)) := by
    have h := L 1 1
    rw [complexDescFactorial_two, complexDescFactorial_one, complexDescFactorial_one, hK] at h
    rw [eq_div_iff (mul_ne_zero hN0 hN1)]
    push_cast at h
    linear_combination h
  have p22 : (patternCount N (n true + n false) 2 2 : ℂ) =
      N.choose (n true + n false) * ((u + d) * (u + d - 1) * (Nc - (u + d)) *
        (Nc - (u + d) - 1)) / (Nc * (Nc - 1) * (Nc - 2) * (Nc - 3)) := by
    have h := L 2 2
    rw [complexDescFactorial_four, complexDescFactorial_two, complexDescFactorial_two, hK] at h
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hN0 hN1) hN2) hN3)]
    push_cast at h
    linear_combination h
  have p21 : (patternCount N (n true + n false) 2 1 : ℂ) =
      N.choose (n true + n false) * ((u + d) * (u + d - 1) * (Nc - (u + d))) /
        (Nc * (Nc - 1) * (Nc - 2)) := by
    have h := L 2 1
    rw [complexDescFactorial_three, complexDescFactorial_two, complexDescFactorial_one, hK] at h
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hN0 hN1) hN2)]
    push_cast at h
    linear_combination h
  have hBB : N.choose (n false) * (N - n false).choose (n true) = B.card := by
    rw [hBcard, choose_mul_choose_comm]
  have S : ∀ x y : ℕ, ((patternCount N (n true) x y * patternCount N (n false) 0 (y + n true) : ℕ)
      : ℂ) * (N.descFactorial (x + y) : ℂ) =
        B.card * (n true).descFactorial x * (N - (n true + n false)).descFactorial y := by
    intro x y
    have h := spin_count_mul N (n true) (n false) x y
    rw [← hBcard] at h
    exact_mod_cast h
  have F : ∀ x y : ℕ, ((patternCount N (n false) x y * patternCount N (n true) 0 (y + n false) : ℕ)
      : ℂ) * (N.descFactorial (x + y) : ℂ) =
        B.card * (n false).descFactorial x * (N - (n true + n false)).descFactorial y := by
    intro x y
    have h := spin_count_mul N (n false) (n true) x y
    rw [hBB, show n false + n true = n true + n false by ring] at h
    exact_mod_cast h
  have s22 : ssV V n 2 2 = B.card * ((u * (u - 1) + d * (d - 1)) * (Nc - (u + d)) *
      (Nc - (u + d) - 1)) / (Nc * (Nc - 1) * (Nc - 2) * (Nc - 3)) := by
    have h1 := S 2 2
    have h2 := F 2 2
    rw [complexDescFactorial_four, complexDescFactorial_two, complexDescFactorial_two, hK] at h1 h2
    rw [ssV, eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hN0 hN1) hN2) hN3)]
    linear_combination h1 + h2
  have s31 : ssV V n 3 1 = B.card * ((u * (u - 1) * (u - 2) + d * (d - 1) * (d - 2)) *
      (Nc - (u + d))) / (Nc * (Nc - 1) * (Nc - 2) * (Nc - 3)) := by
    have h1 := S 3 1
    have h2 := F 3 1
    rw [complexDescFactorial_four, complexDescFactorial_three, complexDescFactorial_one, hK] at h1 h2
    rw [ssV, eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hN0 hN1) hN2) hN3)]
    linear_combination h1 + h2
  -- assemble
  rw [hX, hsplit, hbos, hcyc, s22, s31, obV, obV]
  push_cast
  rw [p11, p22, p21]
  -- the target
  simp only [fourthMomentIntercept, exchangeSlope, occProb]
  push_cast
  have hnN' : n true + n false ≤ Fintype.card V := hnN
  simp only [complexDescFactorial_one, complexDescFactorial_two, complexDescFactorial_three,
    complexDescFactorial_four, Nat.cast_choose_two ℂ, Nat.cast_add, Nat.cast_sub hnN']
  simp only [← hNdef, ← hBdef]
  simp only [← hNc, ← hu, ← hd]
  field_simp
  ring

/-- **The exact fourth moment of `H∞`** (`Spec.FourthMomentHubbard`). -/
theorem fourthMoment_projectedHubbard :
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ)
    (ord : V × Bool ↪ ℕ) (n : Bool → ℕ),
    4 ≤ Fintype.card V → n true + n false ≤ Fintype.card V →
      fourthMoment (basis V n) (projectedHubbard G t (fun _ _ => 0) ord) =
        ((t ^ 4 * (fourthMomentIntercept G (n true + n false) +
            exchangeSlope G (n true + n false) *
              ((n true).choose 2 + (n false).choose 2 : ℕ)) : ℝ) : ℂ) := by
  intro V _ _ G _ t ord n hN hnN
  rw [projectedHubbard_eq_smul, fourthMoment_smul, fourthMoment_hinf G ord n hN hnN]
  push_cast
  ring

end Final

end HubbardMoments
