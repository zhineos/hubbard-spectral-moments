-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.FermionPaths

/-!
# `(H²)_{c'' c}` at the ends of the two-hop paths

Stage 5 of the fourth-moment plan, second part: the fermionic counterpart of
`pathCount_oneMove` and `pathCount_twoMove`. With `S` the occupied sites of `c`:

* at `move c x z` (one particle moved), `(H²) = ε_{xz} (e - o)`, where `e` counts the empty
  common neighbours of `x` and `z` and `o` the common neighbours holding a particle of the
  same spin as `x` (`Qf_oneMove`): the relays through them are exchanges;
* at the end of a relay through a particle of the other spin, only that path arrives
  (`Qf_relay_diff`);
* at the end of a two-particle move, `(H²) = ε (2 - 2 [crosswise moves exist, same spins])`
  (`Qf_twoMove`).

Hence `∑_{c''} (H²)_{c'' c}²` in closed form (`sum_Qf_sq_eq`).

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset

section Values

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
  {G : SimpleGraph V} [DecidableRel G.Adj] {ord : V × σ ↪ ℕ}

variable (G) in
/-- The empty common neighbours of `x` and `z`. -/
def eCount (c : Config V σ) (x z : V) : ℕ :=
  (univ.filter fun y => G.Adj x y ∧ G.Adj y z ∧ c y = none).card

variable (G) in
/-- The common neighbours of `x` and `z` holding a particle of the same spin as `x`. -/
def oCount (c : Config V σ) (x z : V) : ℕ :=
  (univ.filter fun y => G.Adj x y ∧ G.Adj y z ∧ c y = c x).card

omit [Fintype σ] [DecidableEq σ] in
/-- The occupied sites at the end of a relay. -/
theorem occ_endC_relay {c : Config V σ} {x y z : V} (hx : c x ≠ none) (hy : c y ≠ none)
    (hz : c z = none) (hxy : x ≠ y) (hyz : y ≠ z) :
    occ (endC c ((y, z), (x, y))) = hopTo (occ c) (x, z) := by
  have h1 : move c y z x ≠ none := by
    rw [move_apply_of_ne c hxy (fun h => hx (h ▸ hz))]; exact hx
  have h2 : move c y z y = none := move_apply_left c hyz
  simp only [endC]
  rw [occ_move h1 h2 hxy, occ_move hy hz hyz]
  exact hopTo_hopTo_occupied ((mem_occ).2 hx) ((mem_occ).2 hy) (by rw [mem_occ, not_not]; exact hz)
    hxy

omit [Fintype σ] [DecidableEq σ] in
theorem mem_E {c : Config V σ} {t : V × V × V} :
    t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c) ↔
      c t.1 ≠ none ∧ c t.2.2 = none ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ c t.2.1 = none := by
  rw [mem_filter, mem_oneMoves, mem_occ, mem_occ, mem_occ, not_not, not_not]
  tauto

omit [Fintype σ] [DecidableEq σ] in
theorem mem_O {c : Config V σ} {t : V × V × V} :
    t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c) ↔
      c t.1 ≠ none ∧ c t.2.2 = none ∧ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ c t.2.1 ≠ none := by
  rw [mem_filter, mem_oneMoves, mem_occ, mem_occ, mem_occ, not_not, not_not]
  tauto

omit [Fintype σ] [DecidableEq σ] in
theorem twoMoves_subset_paths (S : Finset V) : twoMoves G S ⊆ paths G S := filter_subset _ _

omit [Fintype σ] [DecidableEq σ] in
/-- The end of a two-particle move is not a one-particle move. -/
theorem endC_two_ne_move {c : Config V σ} {π : (V × V) × (V × V)}
    (hπ : π ∈ twoMoves G (occ c)) {x z : V} (hx : c x ≠ none) (hz : c z = none) :
    move c x z ≠ endC c π := by
  intro h
  have hxz : x ≠ z := fun e => hx (e ▸ hz)
  have := congrArg occ h
  rw [occ_move hx hz hxz, occ_endC G (twoMoves_subset_paths _ hπ)] at this
  rcases π with ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩
  exact hopTo_ne_pathEnd G hπ this

/-- **`(H²)` at a one-particle move `x → z`.** -/
theorem Qf_oneMove {c : Config V σ} {x z : V} {s : σ} (hx : c x = some s) (hz : c z = none) :
    Qf G ord (move c x z) c =
      hopSign ord (configState c) (x, s) (z, s) * ((eCount G c x z : ℂ) - oCount G c x z) := by
  have hx' : c x ≠ none := by rw [hx]; simp
  have hxz : x ≠ z := fun e => hx' (e ▸ hz)
  set h := hopSign ord (configState c) (x, s) (z, s)
  rw [Qf, sum_paths_split]
  -- hop and back
  have T1 : ∑ p ∈ hops G (occ c), (if move c x z = endC c (p, (p.2, p.1)) then
      pathSign G ord c (p, (p.2, p.1)) else 0) = 0 := by
    refine sum_eq_zero fun p hp => ?_
    rw [(pathSign_back (ord := ord) hp).1, ite_eq_right (move_ne_self c hx' hz)]
  -- two particles
  have T4 : ∑ π ∈ twoMoves G (occ c), (if move c x z = endC c π then pathSign G ord c π
      else 0) = 0 :=
    sum_eq_zero fun π hπ => ite_eq_right (endC_two_ne_move hπ hx' hz)
  -- through an empty site
  have T2 : ∑ t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c),
      (if move c x z = endC c ((t.1, t.2.1), (t.2.1, t.2.2)) then
        pathSign G ord c ((t.1, t.2.1), (t.2.1, t.2.2)) else 0) = h * eCount G c x z := by
    have step : ∀ t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c),
        (if move c x z = endC c ((t.1, t.2.1), (t.2.1, t.2.2)) then
          pathSign G ord c ((t.1, t.2.1), (t.2.1, t.2.2)) else 0) =
        if t.1 = x ∧ t.2.2 = z then h else 0 := by
      rintro ⟨x', y', z'⟩ ht
      rw [mem_E] at ht
      obtain ⟨h1, h2, h3, h4, h5⟩ := ht
      obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.1 h1
      have hxz' : x' ≠ z' := fun e => h1 (e ▸ h2)
      obtain ⟨e1, e2⟩ := pathSign_empty (ord := ord) h3 h4 hxz' hs' h5 h2
      simp only at e1 e2 ⊢
      rw [e1, e2]
      by_cases hc : x' = x ∧ z' = z
      · obtain ⟨rfl, rfl⟩ := hc
        rw [hx] at hs'
        obtain rfl := Option.some_injective _ hs'
        rw [ite_eq_left rfl, ite_eq_left ⟨rfl, rfl⟩]
      · rw [ite_eq_right hc, ite_eq_right]
        intro he
        obtain ⟨a, b⟩ := move_inj c hx' hz h1 h2 he
        exact hc ⟨a.symm, b.symm⟩
    rw [sum_congr rfl step, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    unfold eCount
    refine card_nbij' (fun t => t.2.1) (fun y => (x, y, z)) ?_ ?_ ?_ ?_
    · rintro ⟨x', y', z'⟩ ht
      rw [mem_coe, mem_filter, mem_E] at ht
      obtain ⟨⟨_, _, h3, h4, h5⟩, rfl, rfl⟩ := ht
      simp [h3, h4, h5]
    · intro y hy
      rw [mem_coe, mem_filter] at hy
      rw [mem_coe, mem_filter, mem_E]
      exact ⟨⟨hx', hz, hy.2.1, hy.2.2.1, hy.2.2.2⟩, rfl, rfl⟩
    · rintro ⟨x', y', z'⟩ ht
      rw [mem_coe, mem_filter] at ht
      obtain ⟨_, rfl, rfl⟩ := ht
      rfl
    · intro y _; rfl
  -- by a relay
  have T3 : ∑ t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c),
      (if move c x z = endC c ((t.2.1, t.2.2), (t.1, t.2.1)) then
        pathSign G ord c ((t.2.1, t.2.2), (t.1, t.2.1)) else 0) = -h * oCount G c x z := by
    have step : ∀ t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c),
        (if move c x z = endC c ((t.2.1, t.2.2), (t.1, t.2.1)) then
          pathSign G ord c ((t.2.1, t.2.2), (t.1, t.2.1)) else 0) =
        if t.1 = x ∧ t.2.2 = z ∧ c t.2.1 = c x then -h else 0 := by
      rintro ⟨x', y', z'⟩ ht
      rw [mem_O] at ht
      obtain ⟨h1, h2, h3, h4, h5⟩ := ht
      simp only
      have hxy' : x' ≠ y' := h3.ne
      have hyz' : y' ≠ z' := h4.ne
      have hxz' : x' ≠ z' := fun e => h1 (e ▸ h2)
      by_cases hc : x' = x ∧ z' = z ∧ c y' = c x
      · obtain ⟨rfl, rfl, hy⟩ := hc
        obtain ⟨e1, e2⟩ := pathSign_occupied (ord := ord) h3 h4 hxz' hx (hy.trans hx) h2
        rw [e1, e2, ite_eq_left rfl, ite_eq_left ⟨rfl, rfl, hy⟩]
      · rw [ite_eq_right hc, ite_eq_right]
        intro he
        have ho := congrArg occ he
        rw [occ_move hx' hz hxz, occ_endC_relay h1 h5 h2 hxy' hyz'] at ho
        obtain ⟨rfl, rfl⟩ := (hopTo_inj ((mem_occ).2 hx') ((mem_occ).2 h1)
          (by rw [mem_occ, not_not]; exact hz) (by rw [mem_occ, not_not]; exact h2)).1 ho
        have hv := congrFun he y'
        rw [endC_occupied_apply hxy' hyz' hxz', ite_eq_right hxy'.symm, ite_eq_left rfl,
          move_apply_of_ne c hxy'.symm (fun e => h5 (e ▸ hz))] at hv
        exact hc ⟨rfl, rfl, hv⟩
    rw [sum_congr rfl step, ← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    unfold oCount
    refine card_nbij' (fun t => t.2.1) (fun y => (x, y, z)) ?_ ?_ ?_ ?_
    · rintro ⟨x', y', z'⟩ ht
      rw [mem_coe, mem_filter, mem_O] at ht
      obtain ⟨⟨_, _, h3, h4, _⟩, rfl, rfl, h6⟩ := ht
      simp [h3, h4, h6]
    · intro y hy
      rw [mem_coe, mem_filter] at hy
      rw [mem_coe, mem_filter, mem_O]
      refine ⟨⟨hx', hz, hy.2.1, hy.2.2.1, ?_⟩, rfl, rfl, hy.2.2.2⟩
      rw [hy.2.2.2]; exact hx'
    · rintro ⟨x', y', z'⟩ ht
      rw [mem_coe, mem_filter] at ht
      obtain ⟨_, rfl, rfl, _⟩ := ht
      rfl
    · intro y _; rfl
  rw [T1, T2, T3, T4]
  ring

/-- **`(H²)` at the end of a relay through the other spin**: only that path arrives. -/
theorem Qf_relay_diff {c : Config V σ} {x y z : V}
    (ht : (x, y, z) ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c))
    (hs : c y ≠ c x) :
    Qf G ord (endC c ((y, z), (x, y))) c = pathSign G ord c ((y, z), (x, y)) := by
  have ht' := ht
  rw [mem_O] at ht'
  obtain ⟨hx, hz, hxy, hyz, hy⟩ := ht'
  simp only at hx hz hxy hyz hy
  have hxy' : x ≠ y := hxy.ne
  have hyz' : y ≠ z := hyz.ne
  have hxz : x ≠ z := fun e => hx (e ▸ hz)
  have hocc := occ_endC_relay hx hy hz hxy' hyz'
  -- the value of the end at `y` is `c x`
  have hval : endC c ((y, z), (x, y)) y = c x := by
    rw [endC_occupied_apply hxy' hyz' hxz, ite_eq_right hxy'.symm, ite_eq_left rfl]
  rw [Qf, sum_paths_split]
  have T1 : ∑ p ∈ hops G (occ c), (if endC c ((y, z), (x, y)) = endC c (p, (p.2, p.1)) then
      pathSign G ord c (p, (p.2, p.1)) else 0) = 0 := by
    refine sum_eq_zero fun p hp => ?_
    rw [(pathSign_back (ord := ord) hp).1, ite_eq_right]
    intro he
    have := congrFun he x
    rw [endC_occupied_apply hxy' hyz' hxz, ite_eq_left rfl] at this
    exact hx this.symm
  have T4 : ∑ π ∈ twoMoves G (occ c), (if endC c ((y, z), (x, y)) = endC c π then
      pathSign G ord c π else 0) = 0 := by
    refine sum_eq_zero fun π hπ => ite_eq_right fun he => ?_
    have := congrArg occ he
    rw [hocc, occ_endC G (twoMoves_subset_paths _ hπ)] at this
    rcases π with ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩
    exact hopTo_ne_pathEnd G hπ this
  have T2 : ∑ t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c),
      (if endC c ((y, z), (x, y)) = endC c ((t.1, t.2.1), (t.2.1, t.2.2)) then
        pathSign G ord c ((t.1, t.2.1), (t.2.1, t.2.2)) else 0) = 0 := by
    refine sum_eq_zero fun t ht => ite_eq_right fun he => ?_
    obtain ⟨x', y', z'⟩ := t
    rw [mem_E] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht
    simp only at h1 h2 h3 h4 h5
    have hxz' : x' ≠ z' := fun e => h1 (e ▸ h2)
    have e1 : endC c ((x', y'), (y', z')) = move c x' z' := move_move_empty h5 h3.ne h4.ne
    rw [e1] at he
    have ho := congrArg occ he
    rw [hocc, occ_move h1 h2 hxz'] at ho
    obtain ⟨rfl, rfl⟩ := (hopTo_inj ((mem_occ).2 hx) ((mem_occ).2 h1)
      (by rw [mem_occ, not_not]; exact hz) (by rw [mem_occ, not_not]; exact h2)).1 ho
    have hv := congrFun he y
    rw [hval, move_apply_of_ne c hxy'.symm hyz'] at hv
    exact hs hv.symm
  have T3 : ∑ t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c),
      (if endC c ((y, z), (x, y)) = endC c ((t.2.1, t.2.2), (t.1, t.2.1)) then
        pathSign G ord c ((t.2.1, t.2.2), (t.1, t.2.1)) else 0) =
      pathSign G ord c ((y, z), (x, y)) := by
    rw [sum_eq_single (x, y, z)]
    · rw [ite_eq_left rfl]
    · rintro ⟨x', y', z'⟩ ht' hne
      rw [ite_eq_right]
      intro he
      rw [mem_O] at ht'
      obtain ⟨h1, h2, h3, h4, h5⟩ := ht'
      simp only at h1 h2 h3 h4 h5 he
      have ho := congrArg occ he
      rw [hocc, occ_endC_relay h1 h5 h2 h3.ne h4.ne] at ho
      obtain ⟨rfl, rfl⟩ := (hopTo_inj ((mem_occ).2 hx) ((mem_occ).2 h1)
        (by rw [mem_occ, not_not]; exact hz) (by rw [mem_occ, not_not]; exact h2)).1 ho
      have hyy : y ≠ y' := fun e => hne (by rw [e])
      have hv := congrFun he y
      rw [hval, endC_occupied_apply h3.ne h4.ne hxz, ite_eq_right hxy'.symm, ite_eq_right hyy,
        ite_eq_right hyz'] at hv
      exact hs hv.symm
    · intro h; exact absurd ht h
  rw [T1, T2, T3, T4]
  simp

/-- **`(H²)` at the end of a two-particle move** `u₁ → w₁, u₂ → w₂`. -/
theorem Qf_twoMove {c : Config V σ} {u₁ w₁ u₂ w₂ : V}
    (hπ : ((u₁, w₁), (u₂, w₂)) ∈ twoMoves G (occ c)) :
    Qf G ord (endC c ((u₁, w₁), (u₂, w₂))) c =
      pathSign G ord c ((u₁, w₁), (u₂, w₂)) *
        (2 - 2 * if G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ ∧ c u₁ = c u₂ then 1 else 0) := by
  have hπ' := hπ
  rw [mem_twoMoves_iff, mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not] at hπ'
  obtain ⟨a1, a2, hu1, hu2, hw1, hw2, hu, hw⟩ := hπ'
  have h11 : u₁ ≠ w₁ := a1.ne
  have h22 : u₂ ≠ w₂ := a2.ne
  have h12 : u₁ ≠ w₂ := fun h => hu1 (h ▸ hw2)
  have h21 : u₂ ≠ w₁ := fun h => hu2 (h ▸ hw1)
  set π₀ : (V × V) × (V × V) := ((u₁, w₁), (u₂, w₂))
  have hocc := occ_endC G (twoMoves_subset_paths _ hπ)
  rw [Qf, sum_paths_split]
  have T1 : ∑ p ∈ hops G (occ c), (if endC c π₀ = endC c (p, (p.2, p.1)) then
      pathSign G ord c (p, (p.2, p.1)) else 0) = 0 := by
    refine sum_eq_zero fun p hp => ?_
    rw [(pathSign_back (ord := ord) hp).1, ite_eq_right]
    intro he
    have := congrArg occ he
    rw [hocc] at this
    have hw : w₁ ∈ pathEnd (occ c) π₀ := (mem_pathEnd_two G hπ).2 (Or.inl rfl)
    rw [this, mem_occ] at hw
    exact hw hw1
  have T2 : ∑ t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c),
      (if endC c π₀ = endC c ((t.1, t.2.1), (t.2.1, t.2.2)) then
        pathSign G ord c ((t.1, t.2.1), (t.2.1, t.2.2)) else 0) = 0 := by
    refine sum_eq_zero fun t ht => ite_eq_right fun he => ?_
    obtain ⟨x', y', z'⟩ := t
    rw [mem_E] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht
    have e1 : endC c ((x', y'), (y', z')) = move c x' z' := move_move_empty h5 h3.ne h4.ne
    rw [e1] at he
    exact endC_two_ne_move hπ h1 h2 he.symm
  have T3 : ∑ t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c),
      (if endC c π₀ = endC c ((t.2.1, t.2.2), (t.1, t.2.1)) then
        pathSign G ord c ((t.2.1, t.2.2), (t.1, t.2.1)) else 0) = 0 := by
    refine sum_eq_zero fun t ht => ite_eq_right fun he => ?_
    obtain ⟨x', y', z'⟩ := t
    rw [mem_O] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht
    simp only at he
    have ho := congrArg occ he
    rw [hocc, occ_endC_relay h1 h5 h2 h3.ne h4.ne] at ho
    exact hopTo_ne_pathEnd G hπ ho.symm
  -- the two-particle paths with the same end
  set π₂ : (V × V) × (V × V) := ((u₂, w₂), (u₁, w₁))
  set π₃ : (V × V) × (V × V) := ((u₁, w₂), (u₂, w₁))
  set π₄ : (V × V) × (V × V) := ((u₂, w₁), (u₁, w₂))
  have m₂ : π₂ ∈ twoMoves G (occ c) := by
    rw [mem_twoMoves_iff, mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not]
    exact ⟨a2, a1, hu2, hu1, hw2, hw1, hu.symm, hw.symm⟩
  have m₃ : π₃ ∈ twoMoves G (occ c) ↔ G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ := by
    rw [mem_twoMoves_iff, mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · exact fun h => ⟨h.1, h.2, hu1, hu2, hw2, hw1, hu, hw.symm⟩
  have m₄ : π₄ ∈ twoMoves G (occ c) ↔ G.Adj u₁ w₂ ∧ G.Adj u₂ w₁ := by
    rw [mem_twoMoves_iff, mem_occ, mem_occ, mem_occ, mem_occ, not_not, not_not]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, hu2, hu1, hw1, hw2, hu.symm, hw⟩
  have hfilter : ∀ π ∈ twoMoves G (occ c), endC c π₀ = endC c π →
      π ∈ ({π₀, π₂, π₃, π₄} : Finset _) := by
    intro π hπ'' he
    have := congrArg occ he
    rw [hocc, occ_endC G (twoMoves_subset_paths _ hπ'')] at this
    rcases π with ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩
    exact (pathEnd_eq_iff G hπ hπ'').1 this
  have T4 : ∑ π ∈ twoMoves G (occ c), (if endC c π₀ = endC c π then pathSign G ord c π
      else 0) = ∑ π ∈ ({π₀, π₂, π₃, π₄} : Finset _).filter (· ∈ twoMoves G (occ c)),
        (if endC c π₀ = endC c π then pathSign G ord c π else 0) := by
    refine sum_subset_zero_on_sdiff ?_ ?_ ?_ |>.symm
    · intro π hπ''
      exact (mem_filter.1 hπ'').2
    · intro π hπ''
      rw [mem_sdiff, mem_filter] at hπ''
      rw [ite_eq_right]
      intro he
      exact hπ''.2 ⟨hfilter π hπ''.1 he, hπ''.1⟩
    · intro _ _; rfl
  have d12 : π₀ ≠ π₂ := by simp [π₀, π₂, hu]
  have d13 : π₀ ≠ π₃ := by simp [π₀, π₃, hw]
  have d14 : π₀ ≠ π₄ := by simp [π₀, π₄, hu]
  have d23 : π₂ ≠ π₃ := by simp [π₂, π₃, hu.symm]
  have d24 : π₂ ≠ π₄ := by simp [π₂, π₄, hw.symm]
  have d34 : π₃ ≠ π₄ := by simp [π₃, π₄, hu]
  obtain ⟨e₂, s₂⟩ := pathSign_two_comm (ord := ord) hπ
  rw [T1, T2, T3, T4, filter_insert, ite_eq_left hπ, filter_insert, ite_eq_left m₂,
    sum_insert (by simp [d12, d13, d14]), sum_insert (by simp [d23, d24]),
    ite_eq_left rfl, ite_eq_left e₂.symm, s₂]
  by_cases hc : G.Adj u₁ w₂ ∧ G.Adj u₂ w₁
  · have hm3 := m₃.2 hc
    have hm4 := m₄.2 hc
    rw [filter_insert, ite_eq_left hm3, filter_singleton, ite_eq_left hm4,
      sum_insert (by simp [d34]), sum_singleton]
    obtain ⟨e₄, s₄⟩ := pathSign_two_comm (ord := ord) hm3
    by_cases hs : c u₁ = c u₂
    · obtain ⟨e₃, s₃⟩ := pathSign_two_cross (ord := ord) hπ hm3 hs
      rw [ite_eq_left e₃.symm, e₄, ite_eq_left e₃.symm, s₄, s₃,
        ite_eq_left ⟨hc.1, hc.2, hs⟩]
      ring
    · have hne3 : endC c π₀ ≠ endC c π₃ := by
        intro he
        have := congrFun he w₁
        rw [endC_two_apply hu hw h11 h12 h21 h22, endC_two_apply hu hw.symm h12 h11 h22 h21,
          ite_eq_right (by tauto), ite_eq_left rfl, ite_eq_right (by tauto), ite_eq_right hw,
          ite_eq_left rfl] at this
        exact hs this
      rw [ite_eq_right hne3, e₄, ite_eq_right hne3, ite_eq_right (fun h => hs h.2.2)]
      ring
  · rw [filter_insert, ite_eq_right (fun h => hc (m₃.1 h)), filter_singleton,
      ite_eq_right (fun h => hc (m₄.1 h)), sum_empty, ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)]
    ring

/-- **`∑_{c''} (H²)_{c'' c}²` in closed form.** -/
theorem sum_Qf_sq_eq {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n) :
    ∑ c'' ∈ basis V n, Qf G ord c'' c ^ 2 =
      ((hops G (occ c)).card : ℂ) * (hops G (occ c)).card +
        ∑ t ∈ (oneMoves G (occ c)).filter (fun t => t.2.1 ∉ occ c),
          ((eCount G c t.1 t.2.2 : ℂ) - oCount G c t.1 t.2.2) +
        ∑ t ∈ (oneMoves G (occ c)).filter (fun t => ¬ t.2.1 ∉ occ c),
          (if c t.2.1 = c t.1 then -((eCount G c t.1 t.2.2 : ℂ) - oCount G c t.1 t.2.2)
            else 1) +
        ∑ π ∈ twoMoves G (occ c),
          (2 - 2 * if G.Adj π.1.1 π.2.2 ∧ G.Adj π.2.1 π.1.2 ∧ c π.1.1 = c π.2.1 then 1 else 0) := by
  rw [sum_Qf_sq hc, sum_paths_split]
  congr 1
  congr 1
  congr 1
  · rw [sum_congr rfl fun p hp => by rw [(pathSign_back (ord := ord) hp).2, (pathSign_back (ord := ord) hp).1, one_mul,
      Qf_self hc], sum_const, nsmul_eq_mul]
  · refine sum_congr rfl fun t ht => ?_
    obtain ⟨x, y, z⟩ := t
    rw [mem_E] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h1
    obtain ⟨e1, e2⟩ := pathSign_empty (ord := ord) h3 h4 (fun e => h1 (e ▸ h2)) hs h5 h2
    simp only at e1 e2 ⊢
    rw [e1, e2, Qf_oneMove hs h2, ← mul_assoc, hopSign_mul_self, one_mul]
  · refine sum_congr rfl fun t ht => ?_
    obtain ⟨x, y, z⟩ := t
    have ht' := ht
    rw [mem_O] at ht'
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht'
    simp only at h1 h2 h3 h4 h5 ⊢
    by_cases hs : c y = c x
    · obtain ⟨s, hsx⟩ := Option.ne_none_iff_exists'.1 h1
      obtain ⟨e1, e2⟩ := pathSign_occupied (ord := ord) h3 h4 (fun e => h1 (e ▸ h2)) hsx
        (hs.trans hsx) h2
      rw [e1, e2, Qf_oneMove hsx h2, ite_eq_left hs, neg_mul, ← mul_assoc, hopSign_mul_self,
        one_mul]
    · rw [Qf_relay_diff ht hs, ite_eq_right hs, pathSign_sq]
      rw [mem_paths_iff]
      refine ⟨h4, (mem_occ).2 h5, ?_, h3, Or.inr ⟨h3.ne, (mem_occ).2 h1⟩, h4.ne, Or.inl rfl⟩
      rw [mem_occ, not_not]; exact h2
  · refine sum_congr rfl fun π hπ => ?_
    rcases π with ⟨⟨u₁, w₁⟩, ⟨u₂, w₂⟩⟩
    rw [Qf_twoMove hπ, ← mul_assoc, pathSign_sq (twoMoves_subset_paths _ hπ), one_mul]

end Values

end HubbardMoments
