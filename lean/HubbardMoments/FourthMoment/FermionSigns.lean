-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.HardCoreBosons
public import HubbardMoments.Hubbard

/-!
# Fermion signs of two-hop paths

Stage 4 of the fourth-moment plan. `H∞ = P₀ H_t P₀` built from fermion operators
(`projectedHubbard`), without Peierls phases, is `t` times the operator with `t = 1`
(`projectedHubbard_eq_smul`), here called `hinf`. Its matrix element for one hop
`i → j` of a particle of spin `s` is `-(-1)^(m + p)` (`hinf_apply_move`), with `(-1)^(m + p)`
the sign `hopSign` of `sortedTupleSignRule`, and it is symmetric (`hinf_symm`).

A two-hop path `π` out of a configuration `c` ends at `endC c π` with amplitude
`pathSign c π`, the product of the two matrix elements. The relations between the
amplitudes of the paths with a common end are the fermionic content of `μ₄`:

* a hop and its reverse: amplitude `1` (`pathSign_back`);
* a particle moving `x → y → z` through an empty site: the sign of the direct hop `x → z`
  (`pathSign_empty`);
* the particle at `y` moving to `z`, then the particle at `x` to `y`, both of the same spin:
  minus that sign (`pathSign_occupied`), an exchange;
* two particles moving in either order: the same amplitude (`pathSign_two_comm`);
* two particles of the same spin moving onto the same two sites crosswise: the opposite
  amplitude (`pathSign_two_cross`), an exchange.

Each sign relation is a parity count of the orbitals below the moving ones
(`hopSign_relay_empty`, `hopSign_relay_occupied`, `hopSign_two_comm`, `hopSign_two_cross`).

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset

/-! ### Parity -/

theorem neg_one_pow_eq_of_even_add {a b : ℕ} (h : (a + b) % 2 = 0) :
    (-1 : ℂ) ^ a = (-1) ^ b := by
  have e : (-1 : ℂ) ^ a = (-1) ^ (a + b) * (-1) ^ b := by
    rw [pow_add, mul_assoc, neg_one_pow_mul_self, mul_one]
  rw [e, (Nat.even_iff.2 h).neg_one_pow, one_mul]

theorem neg_one_pow_eq_neg_of_odd_add {a b : ℕ} (h : (a + b) % 2 = 1) :
    (-1 : ℂ) ^ a = -(-1) ^ b := by
  have e : (-1 : ℂ) ^ a = (-1) ^ (a + b) * (-1) ^ b := by
    rw [pow_add, mul_assoc, neg_one_pow_mul_self, mul_one]
  rw [e, (Nat.odd_iff.2 h).neg_one_pow, neg_one_mul]

/-! ### The sign of one hop -/

section HopSign

variable {O : Type*} [DecidableEq O] (ord : O ↪ ℕ)

/-- The sign `(-1)^(m + p)` of the hop `o → o'` out of the Fock state `S`
(`sortedTupleSignRule`): `m` orbitals of `S` come before `o`, and `p` orbitals of `S \ {o}`
before `o'`. -/
def hopSign (S : Finset O) (o o' : O) : ℂ :=
  (-1) ^ (countBelow ord S o + countBelow ord (S.erase o) o')

theorem hopSign_mul_self (S : Finset O) (o o' : O) :
    hopSign ord S o o' * hopSign ord S o o' = 1 :=
  neg_one_pow_mul_self _

/-- The hop back has the same sign. -/
theorem hopSign_back {S : Finset O} {o o' : O} (ho' : o' ∉ S) :
    hopSign ord (insert o' (S.erase o)) o' o = hopSign ord S o o' := by
  have h1 : o' ∉ S.erase o := fun h => ho' (mem_of_mem_erase h)
  unfold hopSign
  rw [countBelow_insert_self, erase_insert h1, countBelow_erase_self, add_comm]

/-- A particle hopping `o_x → o_y → o_z`, with `o_y` empty: the sign of the direct hop. -/
theorem hopSign_relay_empty {S : Finset O} {ox oy oz : O} (hy : oy ∉ S) :
    hopSign ord S ox oy * hopSign ord (insert oy (S.erase ox)) oy oz = hopSign ord S ox oz := by
  have h1 : oy ∉ S.erase ox := fun h => hy (mem_of_mem_erase h)
  unfold hopSign
  rw [countBelow_insert_self, erase_insert h1, ← pow_add]
  have e : countBelow ord S ox + countBelow ord (S.erase ox) oy +
      (countBelow ord (S.erase ox) oy + countBelow ord (S.erase ox) oz) =
      countBelow ord S ox + countBelow ord (S.erase ox) oz +
        2 * countBelow ord (S.erase ox) oy := by ring
  rw [e, pow_add, pow_mul]
  simp

/-- The particle at `o_y` hops to `o_z`, then the particle at `o_x` hops to `o_y`: minus the
sign of the direct hop `o_x → o_z` (an exchange of the two particles). -/
theorem hopSign_relay_occupied {S : Finset O} {ox oy oz : O} (hx : ox ∈ S) (hy : oy ∈ S)
    (hz : oz ∉ S) (hxy : ox ≠ oy) :
    hopSign ord S oy oz * hopSign ord (insert oz (S.erase oy)) ox oy =
      -hopSign ord S ox oz := by
  have hzx : oz ≠ ox := fun h => hz (h ▸ hx)
  have hzy : oz ≠ oy := fun h => hz (h ▸ hy)
  set T := (S.erase oy).erase ox with hT
  have hT' : (S.erase ox).erase oy = T := by rw [hT, erase_right_comm]
  have hx' : ox ∈ S.erase oy := mem_erase.2 ⟨hxy, hx⟩
  have hy' : oy ∈ S.erase ox := mem_erase.2 ⟨hxy.symm, hy⟩
  have hz' : oz ∉ S.erase oy := fun h => hz (mem_of_mem_erase h)
  have hzT : oz ∉ T := fun h => hz' (mem_of_mem_erase h)
  have e1 := countBelow_erase ord hx oy
  have e2 : countBelow ord (S.erase ox) oy = countBelow ord T oy := by
    rw [← hT', countBelow_erase_self]
  have e3 := countBelow_erase ord hx' oz
  have e4 := countBelow_insert ord hz' ox
  have e5 : countBelow ord (S.erase oy) ox = countBelow ord T ox := by
    rw [hT, countBelow_erase_self]
  have e6 : countBelow ord ((insert oz (S.erase oy)).erase ox) oy =
      countBelow ord T oy + if ord oz < ord oy then 1 else 0 := by
    rw [erase_insert_of_ne hzx, ← hT, countBelow_insert ord hzT]
  have e7 := countBelow_erase ord hy ox
  have e8 := countBelow_erase ord hy' oz
  rw [hT'] at e8
  rw [← hT] at e3
  have p1 := lt_add_lt_eq_one ord hxy
  have p2 := lt_add_lt_eq_one ord hzx
  have p3 := lt_add_lt_eq_one ord hzy
  unfold hopSign
  rw [← pow_add]
  apply neg_one_pow_eq_neg_of_odd_add
  omega

/-- Two particles hop `o₁ → p₁` and `o₂ → p₂`, in either order: the same sign. -/
theorem hopSign_two_comm {S : Finset O} {o₁ o₂ p₁ p₂ : O} (h₁ : o₁ ∈ S) (h₂ : o₂ ∈ S)
    (k₁ : p₁ ∉ S) (k₂ : p₂ ∉ S) (ho : o₁ ≠ o₂) (hp : p₁ ≠ p₂) :
    hopSign ord S o₁ p₁ * hopSign ord (insert p₁ (S.erase o₁)) o₂ p₂ =
      hopSign ord S o₂ p₂ * hopSign ord (insert p₂ (S.erase o₂)) o₁ p₁ := by
  have hp₁o₂ : p₁ ≠ o₂ := fun h => k₁ (h ▸ h₂)
  have hp₂o₁ : p₂ ≠ o₁ := fun h => k₂ (h ▸ h₁)
  have hp₁o₁ : p₁ ≠ o₁ := fun h => k₁ (h ▸ h₁)
  have hp₂o₂ : p₂ ≠ o₂ := fun h => k₂ (h ▸ h₂)
  have hT' : (S.erase o₂).erase o₁ = (S.erase o₁).erase o₂ := erase_right_comm
  have m₁ : o₁ ∈ S.erase o₂ := mem_erase.2 ⟨ho, h₁⟩
  have m₂ : o₂ ∈ S.erase o₁ := mem_erase.2 ⟨ho.symm, h₂⟩
  have n₁ : p₁ ∉ S.erase o₁ := fun h => k₁ (mem_of_mem_erase h)
  have n₂ : p₂ ∉ S.erase o₂ := fun h => k₂ (mem_of_mem_erase h)
  have n₁T : p₁ ∉ (S.erase o₁).erase o₂ := fun h => n₁ (mem_of_mem_erase h)
  have n₂T : p₂ ∉ (S.erase o₁).erase o₂ := fun h => k₂ (mem_of_mem_erase (mem_of_mem_erase h))
  -- left
  have a1 := countBelow_erase ord h₂ o₁
  have a1' : countBelow ord (S.erase o₂) o₁ = countBelow ord ((S.erase o₁).erase o₂) o₁ := by
    rw [← hT', countBelow_erase_self]
  have a2 := countBelow_erase ord m₂ p₁
  have a3 := countBelow_insert ord n₁ o₂
  have a3' : countBelow ord (S.erase o₁) o₂ = countBelow ord ((S.erase o₁).erase o₂) o₂ := by
    rw [countBelow_erase_self]
  have a4 : countBelow ord ((insert p₁ (S.erase o₁)).erase o₂) p₂ =
      countBelow ord ((S.erase o₁).erase o₂) p₂ + if ord p₁ < ord p₂ then 1 else 0 := by
    rw [erase_insert_of_ne hp₁o₂, countBelow_insert ord n₁T]
  -- right
  have b1 := countBelow_erase ord h₁ o₂
  have b2 := countBelow_erase ord m₁ p₂
  rw [hT'] at b2
  have b3 := countBelow_insert ord n₂ o₁
  have b4 : countBelow ord ((insert p₂ (S.erase o₂)).erase o₁) p₁ =
      countBelow ord ((S.erase o₁).erase o₂) p₁ + if ord p₂ < ord p₁ then 1 else 0 := by
    rw [erase_insert_of_ne hp₂o₁, hT', countBelow_insert ord n₂T]
  have q1 := lt_add_lt_eq_one ord ho
  have q2 := lt_add_lt_eq_one ord hp₁o₂
  have q3 := lt_add_lt_eq_one ord hp
  have q4 := lt_add_lt_eq_one ord hp₂o₁
  unfold hopSign
  rw [← pow_add, ← pow_add]
  apply neg_one_pow_eq_of_even_add
  omega

/-- Two particles of the same spin moving onto the same two sites crosswise: the opposite
sign (an exchange). -/
theorem hopSign_two_cross {S : Finset O} {o₁ o₂ p₁ p₂ : O} (h₂ : o₂ ∈ S)
    (k₁ : p₁ ∉ S) (k₂ : p₂ ∉ S) (ho : o₁ ≠ o₂) (hp : p₁ ≠ p₂) :
    hopSign ord S o₁ p₁ * hopSign ord (insert p₁ (S.erase o₁)) o₂ p₂ =
      -(hopSign ord S o₁ p₂ * hopSign ord (insert p₂ (S.erase o₁)) o₂ p₁) := by
  have hp₁o₂ : p₁ ≠ o₂ := fun h => k₁ (h ▸ h₂)
  have hp₂o₂ : p₂ ≠ o₂ := fun h => k₂ (h ▸ h₂)
  have m₂ : o₂ ∈ S.erase o₁ := mem_erase.2 ⟨ho.symm, h₂⟩
  have n₁ : p₁ ∉ S.erase o₁ := fun h => k₁ (mem_of_mem_erase h)
  have n₂ : p₂ ∉ S.erase o₁ := fun h => k₂ (mem_of_mem_erase h)
  have n₁T : p₁ ∉ (S.erase o₁).erase o₂ := fun h => n₁ (mem_of_mem_erase h)
  have n₂T : p₂ ∉ (S.erase o₁).erase o₂ := fun h => n₂ (mem_of_mem_erase h)
  have c1 := countBelow_erase ord m₂ p₁
  have c2 := countBelow_erase ord m₂ p₂
  have c3 := countBelow_insert ord n₁ o₂
  have c4 := countBelow_insert ord n₂ o₂
  have c5 : countBelow ord (S.erase o₁) o₂ = countBelow ord ((S.erase o₁).erase o₂) o₂ := by
    rw [countBelow_erase_self]
  have c6 : countBelow ord ((insert p₁ (S.erase o₁)).erase o₂) p₂ =
      countBelow ord ((S.erase o₁).erase o₂) p₂ + if ord p₁ < ord p₂ then 1 else 0 := by
    rw [erase_insert_of_ne hp₁o₂, countBelow_insert ord n₁T]
  have c7 : countBelow ord ((insert p₂ (S.erase o₁)).erase o₂) p₁ =
      countBelow ord ((S.erase o₁).erase o₂) p₁ + if ord p₂ < ord p₁ then 1 else 0 := by
    rw [erase_insert_of_ne hp₂o₂, countBelow_insert ord n₂T]
  have q1 := lt_add_lt_eq_one ord hp₁o₂
  have q2 := lt_add_lt_eq_one ord hp₂o₂
  have q3 := lt_add_lt_eq_one ord hp
  unfold hopSign
  rw [← pow_add, ← pow_add]
  apply neg_one_pow_eq_neg_of_odd_add
  omega

end HopSign

/-! ### `H∞` without phases -/

section Hinf

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
  (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V × σ ↪ ℕ)

/-- `H∞` is linear in the hopping modulus `t`. -/
theorem projectedHubbard_eq_smul (t : ℝ) (A : V → V → ℝ) :
    projectedHubbard G t A ord = (t : ℂ) • projectedHubbard G 1 A ord := by
  ext c b
  simp only [projectedHubbard, hubbardHopping_apply, Matrix.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun p _ => sum_congr rfl fun s _ => ?_
  push_cast
  ring

/-- `H∞` with `t = 1` and no Peierls phases. -/
noncomputable abbrev hinf : Matrix (Config V σ) (Config V σ) ℂ :=
  projectedHubbard G 1 (fun _ _ => 0) ord

theorem hinf_isProjectedHopping : IsProjectedHopping G 1 (hinf G ord) :=
  projectedHubbard_isProjectedHopping G 1 ord zero_le_one (by intro x y; simp)

variable {G ord}

/-- **One hop.** The matrix element of `H∞` (`t = 1`) for the hop `i → j` of a particle of spin
`s`. -/
theorem hinf_apply_move {c : Config V σ} {i j : V} {s : σ} (hadj : G.Adj i j)
    (hi : c i = some s) (hj : c j = none) :
    hinf G ord (move c i j) c = -hopSign ord (configState c) (i, s) (j, s) := by
  have hij : i ≠ j := G.ne_of_adj hadj
  have hmem : (i, s) ∈ configState c := mem_configState.2 hi
  have hnot : (j, s) ∉ configState c := by simp [mem_configState, hj]
  simp only [hinf, projectedHubbard, configState_move hi hj hij, hubbardHopping_apply]
  rw [sum_eq_single (i, j), sum_eq_single s]
  · have hnot' : (j, s) ∉ (configState c).erase (i, s) := fun h => hnot (mem_of_mem_erase h)
    simp only [hmem, hnot', not_false_eq_true, and_self, ↓reduceIte]
    simp [hopSign]
  · intro s' _ hs
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    exfalso
    exact hs (Prod.mk.inj (hop_unique h₁ h₂ (by simp [hij]) hmem h₃.symm).1).2
  · intro h
    exact absurd (mem_univ s) h
  · intro p hp hpij
    refine sum_eq_zero fun s' _ => ?_
    have hadj' : G.Adj p.1 p.2 := (mem_filter.1 hp).2
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    have hne : (p.1, s') ≠ (p.2, s') := fun h => G.ne_of_adj hadj' (congrArg Prod.fst h)
    obtain ⟨e₁, e₂⟩ := hop_unique h₁ h₂ hne hmem h₃.symm
    have e₁' : p.1 = i := congrArg Prod.fst e₁
    have e₂' : p.2 = j := congrArg Prod.fst e₂
    exact absurd (Prod.ext e₁' e₂') hpij
  · intro h
    exact absurd (by simp [arcs, hadj] : (i, j) ∈ arcs G) h

theorem hinf_apply_eq_zero {b c : Config V σ}
    (h : ∀ i j, G.Adj i j → c i ≠ none → c j = none → b ≠ move c i j) : hinf G ord b c = 0 :=
  (hinf_isProjectedHopping G ord).apply_eq_zero c b h

/-- `H∞` (real, Hermitian) is symmetric. -/
theorem hinf_symm (b c : Config V σ) : hinf G ord b c = hinf G ord c b := by
  have key : ∀ b c : Config V σ, (∃ i j s, G.Adj i j ∧ c i = some s ∧ c j = none ∧
      b = move c i j) → hinf G ord b c = hinf G ord c b := by
    rintro b c ⟨i, j, s, hadj, hi, hj, rfl⟩
    have hij : i ≠ j := G.ne_of_adj hadj
    have hb : move c i j j = some s := by rw [move_apply_right, hi]
    have hb' : move c i j i = none := move_apply_left c hij
    have e : hinf G ord c (move c i j) =
        hinf G ord (move (move c i j) j i) (move c i j) := by rw [move_move c hij hj]
    rw [e, hinf_apply_move hadj hi hj, hinf_apply_move hadj.symm hb hb',
      configState_move hi hj hij, hopSign_back ord (by simp [mem_configState, hj])]
  by_cases h : ∃ i j s, G.Adj i j ∧ c i = some s ∧ c j = none ∧ b = move c i j
  · exact key b c h
  · by_cases h' : ∃ i j s, G.Adj i j ∧ b i = some s ∧ b j = none ∧ c = move b i j
    · exact (key c b h').symm
    · rw [hinf_apply_eq_zero, hinf_apply_eq_zero]
      · intro i j hadj hi hj hc
        obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hi
        exact h' ⟨i, j, s, hadj, hs, hj, hc⟩
      · intro i j hadj hi hj hb
        obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hi
        exact h ⟨i, j, s, hadj, hs, hj, hb⟩

end Hinf

/-! ### Two-hop paths of configurations -/

section Paths

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
  (G : SimpleGraph V) [DecidableRel G.Adj] (ord : V × σ ↪ ℕ)

/-- The configuration after the first hop of the path `π`. -/
def midC (c : Config V σ) (π : (V × V) × (V × V)) : Config V σ := move c π.1.1 π.1.2

/-- The configuration at the end of the path `π`. -/
def endC (c : Config V σ) (π : (V × V) × (V × V)) : Config V σ :=
  move (move c π.1.1 π.1.2) π.2.1 π.2.2

/-- The amplitude of the path `π` out of `c`: the product of its two matrix elements. -/
noncomputable def pathSign (c : Config V σ) (π : (V × V) × (V × V)) : ℂ :=
  hinf G ord (endC c π) (midC c π) * hinf G ord (midC c π) c

omit [Fintype σ] [DecidableEq σ] in
theorem occ_move {c : Config V σ} {i j : V} (hi : c i ≠ none) (hj : c j = none) (hij : i ≠ j) :
    occ (move c i j) = hopTo (occ c) (i, j) := by
  ext v
  rw [mem_occ, mem_hopTo, mem_occ]
  by_cases h1 : v = j
  · subst h1; simp [move_apply_right, hi]
  · by_cases h2 : v = i
    · subst h2; simp [move_apply_left c hij, h1]
    · simp [move_apply_of_ne c h2 h1, h1, h2]

omit [Fintype σ] [DecidableEq σ] in
theorem occ_endC {c : Config V σ} {π : (V × V) × (V × V)} (hπ : π ∈ paths G (occ c)) :
    occ (endC c π) = pathEnd (occ c) π := by
  rw [mem_paths, mem_hops, mem_hops] at hπ
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hπ
  rw [mem_occ] at h2
  rw [mem_occ, not_not] at h3
  have hm := occ_move h2 h3 h1.ne
  rw [← hm, mem_occ] at h5
  rw [← hm, mem_occ, not_not] at h6
  rw [endC, occ_move h5 h6 h4.ne, hm, pathEnd]

/-- The paths out of `c` stay in the basis. -/
theorem endC_mem_basis {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n)
    {π : (V × V) × (V × V)} (hπ : π ∈ paths G (occ c)) : endC c π ∈ basis V n := by
  rw [mem_paths, mem_hops, mem_hops] at hπ
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hπ
  rw [mem_occ] at h2
  rw [mem_occ, not_not] at h3
  have hm := occ_move h2 h3 h1.ne
  rw [← hm, mem_occ] at h5
  rw [← hm, mem_occ, not_not] at h6
  exact move_mem_basis (move_mem_basis hc h2 h3) h5 h6

variable {G ord}

/-- **A hop and its reverse**: back at `c`, with amplitude `1`. -/
theorem pathSign_back {c : Config V σ} {p : V × V} (hp : p ∈ hops G (occ c)) :
    endC c (p, (p.2, p.1)) = c ∧ pathSign G ord c (p, (p.2, p.1)) = 1 := by
  rw [mem_hops, mem_occ, mem_occ, not_not] at hp
  obtain ⟨hadj, hi, hj⟩ := hp
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hi
  have hij : p.1 ≠ p.2 := hadj.ne
  have he : endC c (p, (p.2, p.1)) = c := move_move c hij hj
  refine ⟨he, ?_⟩
  rw [pathSign, he, midC, hinf_symm, ← sq]
  rw [hinf_apply_move hadj hs hj, neg_sq, sq, hopSign_mul_self]

omit [Fintype V] [Fintype σ] [DecidableEq σ] in
/-- A particle moving `x → y → z` through an empty site ends as the direct move `x → z`. -/
theorem move_move_empty {c : Config V σ} {x y z : V} (hy : c y = none) (hxy : x ≠ y)
    (hyz : y ≠ z) : move (move c x y) y z = move c x z := by
  funext v
  by_cases h1 : v = z
  · subst h1; rw [move_apply_right, move_apply_right, move_apply_right]
  · by_cases h2 : v = y
    · subst h2; rw [move_apply_left _ hyz, move_apply_of_ne c hxy.symm h1, hy]
    · by_cases h3 : v = x
      · subst h3; rw [move_apply_of_ne _ h2 h1, move_apply_left c hxy, move_apply_left c (by
          intro h; exact h1 h)]
      · rw [move_apply_of_ne _ h2 h1, move_apply_of_ne c h3 h2, move_apply_of_ne c h3 h1]

/-- **Through an empty site**: the path `x → y → z` ends at `move c x z`, with the sign of the
direct hop. -/
theorem pathSign_empty {c : Config V σ} {x y z : V} {s : σ} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : x ≠ z) (hx : c x = some s) (hy : c y = none) (hz : c z = none) :
    endC c ((x, y), (y, z)) = move c x z ∧
      pathSign G ord c ((x, y), (y, z)) = hopSign ord (configState c) (x, s) (z, s) := by
  have hne1 : x ≠ y := hxy.ne
  have hne2 : y ≠ z := hyz.ne
  refine ⟨move_move_empty hy hne1 hne2, ?_⟩
  have hm1 : move c x y y = some s := by rw [move_apply_right, hx]
  have hm2 : move c x y z = none := by rw [move_apply_of_ne c hxz.symm hne2.symm, hz]
  rw [pathSign, endC, midC]
  simp only
  rw [hinf_apply_move hyz hm1 hm2, hinf_apply_move hxy hx hy, configState_move hx hy hne1,
    neg_mul_neg, mul_comm, hopSign_relay_empty ord (by simp [mem_configState, hy])]

omit [Fintype V] [Fintype σ] [DecidableEq σ] in
theorem endC_occupied_apply {c : Config V σ} {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) (v : V) :
    endC c ((y, z), (x, y)) v =
      if v = x then none else if v = y then c x else if v = z then c y else c v := by
  simp only [endC]
  by_cases h1 : v = x
  · subst h1; rw [ite_eq_left rfl, move_apply_left _ hxy]
  · rw [ite_eq_right h1]
    by_cases h2 : v = y
    · subst h2; rw [ite_eq_left rfl, move_apply_right, move_apply_of_ne c hxy hxz]
    · rw [ite_eq_right h2, move_apply_of_ne _ h1 h2]
      by_cases h3 : v = z
      · subst h3; rw [ite_eq_left rfl, move_apply_right]
      · rw [ite_eq_right h3, move_apply_of_ne c h2 h3]

/-- **Through an occupied site of the same spin** (the particle at `y` moves to `z`, then the
particle at `x` to `y`): the path ends at `move c x z`, with minus the sign of the direct
hop. -/
theorem pathSign_occupied {c : Config V σ} {x y z : V} {s : σ} (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hxz : x ≠ z) (hx : c x = some s) (hy : c y = some s) (hz : c z = none) :
    endC c ((y, z), (x, y)) = move c x z ∧
      pathSign G ord c ((y, z), (x, y)) = -hopSign ord (configState c) (x, s) (z, s) := by
  have hne1 : x ≠ y := hxy.ne
  have hne2 : y ≠ z := hyz.ne
  refine ⟨?_, ?_⟩
  · funext v
    rw [endC_occupied_apply hne1 hne2 hxz]
    by_cases h1 : v = x
    · subst h1; rw [ite_eq_left rfl, move_apply_left c hxz]
    · rw [ite_eq_right h1]
      by_cases h2 : v = y
      · subst h2; rw [ite_eq_left rfl, move_apply_of_ne c h1 hne2, hx, hy]
      · rw [ite_eq_right h2]
        by_cases h3 : v = z
        · subst h3; rw [ite_eq_left rfl, move_apply_right, hx, hy]
        · rw [ite_eq_right h3, move_apply_of_ne c h1 h3]
  · have hm1 : move c y z x = some s := by rw [move_apply_of_ne c hne1 hxz, hx]
    have hm2 : move c y z y = none := move_apply_left c hne2
    rw [pathSign, endC, midC]
    simp only
    rw [hinf_apply_move hxy hm1 hm2, hinf_apply_move hyz hy hz, configState_move hy hz hne2,
      neg_mul_neg, mul_comm,
      hopSign_relay_occupied ord (mem_configState.2 hx) (mem_configState.2 hy)
        (by simp [mem_configState, hz]) (by simp [hne1])]

omit [Fintype V] [Fintype σ] [DecidableEq σ] in
theorem endC_two_apply {c : Config V σ} {u₁ w₁ u₂ w₂ : V} (hu : u₁ ≠ u₂) (hw : w₁ ≠ w₂)
    (h11 : u₁ ≠ w₁) (h12 : u₁ ≠ w₂) (h21 : u₂ ≠ w₁) (h22 : u₂ ≠ w₂) (v : V) :
    endC c ((u₁, w₁), (u₂, w₂)) v =
      if v = u₁ ∨ v = u₂ then none else if v = w₁ then c u₁ else if v = w₂ then c u₂ else c v := by
  simp only [endC]
  by_cases a1 : v = u₁
  · subst a1; rw [ite_eq_left (Or.inl rfl), move_apply_of_ne _ hu h12, move_apply_left c h11]
  · by_cases a2 : v = u₂
    · subst a2; rw [ite_eq_left (Or.inr rfl), move_apply_left _ h22]
    · rw [ite_eq_right (by tauto)]
      by_cases a3 : v = w₁
      · subst a3; rw [ite_eq_left rfl, move_apply_of_ne _ (Ne.symm h21) hw, move_apply_right]
      · rw [ite_eq_right a3]
        by_cases a4 : v = w₂
        · subst a4; rw [ite_eq_left rfl, move_apply_right, move_apply_of_ne c hu.symm h21]
        · rw [ite_eq_right a4, move_apply_of_ne _ a2 a4, move_apply_of_ne c a1 a3]

/-- **Two particles, either order**: same end, same amplitude. -/
theorem pathSign_two_comm {c : Config V σ} {u₁ w₁ u₂ w₂ : V}
    (hπ : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G (occ c)) :
    endC c ((u₂, w₂), (u₁, w₁)) = endC c ((u₁, w₁), (u₂, w₂)) ∧
      pathSign G ord c ((u₂, w₂), (u₁, w₁)) = pathSign G ord c ((u₁, w₁), (u₂, w₂)) := by
  rw [mem_twoMoves_iff, mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not] at hπ
  obtain ⟨a1, a2, hu1, hu2, hw1, hw2, hu, hw⟩ := hπ
  obtain ⟨s₁, hs₁⟩ := Option.ne_none_iff_exists'.1 hu1
  obtain ⟨s₂, hs₂⟩ := Option.ne_none_iff_exists'.1 hu2
  have h11 : u₁ ≠ w₁ := a1.ne
  have h22 : u₂ ≠ w₂ := a2.ne
  have h12 : u₁ ≠ w₂ := fun h => hu1 (h ▸ hw2)
  have h21 : u₂ ≠ w₁ := fun h => hu2 (h ▸ hw1)
  refine ⟨?_, ?_⟩
  · funext v
    rw [endC_two_apply hu.symm hw.symm h22 h21 h12 h11, endC_two_apply hu hw h11 h12 h21 h22]
    by_cases b1 : v = u₁ ∨ v = u₂
    · rw [ite_eq_left (by tauto), ite_eq_left b1]
    · rw [ite_eq_right (by tauto), ite_eq_right b1]
      by_cases b2 : v = w₁
      · subst b2; rw [ite_eq_right hw, ite_eq_left rfl, ite_eq_left rfl]
      · simp [b2]
  · have m1 : move c u₁ w₁ u₂ = some s₂ := by rw [move_apply_of_ne c hu.symm h21, hs₂]
    have m2 : move c u₁ w₁ w₂ = none := by rw [move_apply_of_ne c (Ne.symm h12) hw.symm, hw2]
    have m3 : move c u₂ w₂ u₁ = some s₁ := by rw [move_apply_of_ne c hu h12, hs₁]
    have m4 : move c u₂ w₂ w₁ = none := by rw [move_apply_of_ne c (Ne.symm h21) hw, hw1]
    simp only [pathSign, endC, midC]
    rw [hinf_apply_move a1 m3 m4, hinf_apply_move a2 hs₂ hw2, hinf_apply_move a2 m1 m2,
      hinf_apply_move a1 hs₁ hw1, configState_move hs₁ hw1 h11, configState_move hs₂ hw2 h22,
      neg_mul_neg, neg_mul_neg]
    have hne : (u₁, s₁) ≠ (u₂, s₂) := fun h => hu (congrArg Prod.fst h)
    have hne' : (w₁, s₁) ≠ (w₂, s₂) := fun h => hw (congrArg Prod.fst h)
    have h := hopSign_two_comm ord (mem_configState.2 hs₁) (mem_configState.2 hs₂)
      (by simp [mem_configState, hw1]) (by simp [mem_configState, hw2]) hne hne'
    linear_combination h.symm

/-- **Two particles of the same spin crosswise**: the same end, the opposite amplitude. -/
theorem pathSign_two_cross {c : Config V σ} {u₁ w₁ u₂ w₂ : V}
    (hπ : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G (occ c))
    (hπ' : ((u₁, w₂), (u₂, w₁)) ∈ twoMoves G (occ c)) (hs : c u₁ = c u₂) :
    endC c ((u₁, w₂), (u₂, w₁)) = endC c ((u₁, w₁), (u₂, w₂)) ∧
      pathSign G ord c ((u₁, w₂), (u₂, w₁)) = -pathSign G ord c ((u₁, w₁), (u₂, w₂)) := by
  rw [mem_twoMoves_iff, mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not] at hπ hπ'
  obtain ⟨a1, a2, hu1, hu2, hw1, hw2, hu, hw⟩ := hπ
  obtain ⟨b1, b2, -, -, -, -, -, -⟩ := hπ'
  obtain ⟨s, hs₁⟩ := Option.ne_none_iff_exists'.1 hu1
  have hs₂ : c u₂ = some s := hs ▸ hs₁
  have h11 : u₁ ≠ w₁ := a1.ne
  have h22 : u₂ ≠ w₂ := a2.ne
  have h12 : u₁ ≠ w₂ := fun h => hu1 (h ▸ hw2)
  have h21 : u₂ ≠ w₁ := fun h => hu2 (h ▸ hw1)
  refine ⟨?_, ?_⟩
  · funext v
    rw [endC_two_apply hu hw.symm h12 h11 h22 h21, endC_two_apply hu hw h11 h12 h21 h22]
    by_cases c1 : v = u₁ ∨ v = u₂
    · rw [ite_eq_left c1, ite_eq_left c1]
    · rw [ite_eq_right c1, ite_eq_right c1]
      by_cases c2 : v = w₂
      · subst c2; rw [ite_eq_left rfl, ite_eq_right hw.symm, ite_eq_left rfl, hs]
      · rw [ite_eq_right c2]
        by_cases c3 : v = w₁
        · subst c3; rw [ite_eq_left rfl, ite_eq_left rfl, hs]
        · rw [ite_eq_right c3, ite_eq_right c3, ite_eq_right c2]
  · have m1 : move c u₁ w₁ u₂ = some s := by rw [move_apply_of_ne c hu.symm h21, hs₂]
    have m2 : move c u₁ w₁ w₂ = none := by rw [move_apply_of_ne c (Ne.symm h12) hw.symm, hw2]
    have m3 : move c u₁ w₂ u₂ = some s := by rw [move_apply_of_ne c hu.symm h22, hs₂]
    have m4 : move c u₁ w₂ w₁ = none := by rw [move_apply_of_ne c (Ne.symm h11) hw, hw1]
    simp only [pathSign, endC, midC]
    rw [hinf_apply_move b2 m3 m4, hinf_apply_move b1 hs₁ hw2, hinf_apply_move a2 m1 m2,
      hinf_apply_move a1 hs₁ hw1, configState_move hs₁ hw2 h12, configState_move hs₁ hw1 h11,
      neg_mul_neg, neg_mul_neg, mul_comm, mul_comm (hopSign ord _ (u₂, s) (w₂, s))]
    have hne : (u₁, s) ≠ (u₂, s) := fun h => hu (congrArg Prod.fst h)
    have hne' : (w₁, s) ≠ (w₂, s) := fun h => hw (congrArg Prod.fst h)
    rw [hopSign_two_cross ord (mem_configState.2 hs₂)
      (by simp [mem_configState, hw1]) (by simp [mem_configState, hw2]) hne hne', neg_neg]

end Paths

end HubbardMoments
