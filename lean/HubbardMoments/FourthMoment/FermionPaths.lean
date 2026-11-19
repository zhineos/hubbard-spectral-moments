-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.FermionSigns

/-!
# The fermion fourth moment as a sum over two-hop paths

Stage 5 of the fourth-moment plan, first part. For `H = hinf` (`H∞` with `t = 1`, no phases)
on the basis `B` of a spin composition:

* `(H²)_{c'' c}`, computed in the basis, is the sum of the amplitudes `pathSign c π` of the
  two-hop paths `π` out of `c` that end at `c''` (`sum_hinf_mul_hinf`, with `Qf`);
* `Tr(H_B⁴) = ∑_{c, c''} (H²)_{c'' c}²` (`block_sum_hinf`), and
  `∑_{c''} (H²)_{c'' c}² = ∑_π pathSign c π · (H²)_{endC c π, c}` (`sum_Qf_sq`);
* a sum over the two-hop paths splits by type: a hop and its reverse, a particle moving
  through an empty site, a relay through an occupied site, and two particles
  (`sum_paths_split`).

Not imported by the library root; nothing here changes the released statements.
-/

@[expose] public section

namespace HubbardMoments

open Finset

/-! ### Splitting the two-hop paths by type -/

section Split

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The paths by type**, for any function of the path: the hops followed by their reverse;
the one-particle moves `x → y → z` through an empty `y` (path `((x, y), (y, z))`); the relays
through an occupied `y` (path `((y, z), (x, y))`); and the two-particle moves. -/
theorem sum_paths_split {M : Type*} [AddCommMonoid M] (S : Finset V)
    (f : (V × V) × (V × V) → M) :
    ∑ π ∈ paths G S, f π =
      ∑ p ∈ hops G S, f (p, (p.2, p.1)) +
        ∑ t ∈ (oneMoves G S).filter (fun t => t.2.1 ∉ S), f ((t.1, t.2.1), (t.2.1, t.2.2)) +
        ∑ t ∈ (oneMoves G S).filter (fun t => ¬ t.2.1 ∉ S), f ((t.2.1, t.2.2), (t.1, t.2.1)) +
        ∑ π ∈ twoMoves G S, f π := by
  set P := paths G S
  rw [← sum_filter_add_sum_filter_not P (fun π => π.2.1 = π.1.2),
    ← sum_filter_add_sum_filter_not (P.filter fun π => π.2.1 = π.1.2) (fun π => π.2.2 = π.1.1),
    ← sum_filter_add_sum_filter_not (P.filter fun π => ¬ π.2.1 = π.1.2) (fun π => π.2.2 = π.1.1)]
  have hA : ∑ π ∈ (P.filter fun π => π.2.1 = π.1.2).filter (fun π => π.2.2 = π.1.1), f π =
      ∑ p ∈ hops G S, f (p, (p.2, p.1)) := by
    refine sum_nbij' (fun π => π.1) (fun p => (p, (p.2, p.1))) ?_ ?_ ?_ ?_ ?_
    · intro π hπ
      rw [mem_filter, mem_filter] at hπ
      exact ((mem_paths G).1 hπ.1.1).1
    · intro p hp
      rw [mem_filter, mem_filter]
      exact ⟨⟨(mem_paths G).2 ⟨hp, swap_mem_hops G hp⟩, rfl⟩, rfl⟩
    · intro π hπ
      rw [mem_filter, mem_filter] at hπ
      obtain ⟨⟨_, h1⟩, h2⟩ := hπ
      rcases π with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only at h1 h2 ⊢
      rw [h1, h2]
    · intro p _; rfl
    · intro π hπ
      rw [mem_filter, mem_filter] at hπ
      obtain ⟨⟨_, h1⟩, h2⟩ := hπ
      rcases π with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only at h1 h2 ⊢
      rw [h1, h2]
  have hB : ∑ π ∈ (P.filter fun π => π.2.1 = π.1.2).filter (fun π => ¬ π.2.2 = π.1.1), f π =
      ∑ t ∈ (oneMoves G S).filter (fun t => t.2.1 ∉ S), f ((t.1, t.2.1), (t.2.1, t.2.2)) := by
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
      simp only [mem_filter, P] at hπ
      obtain ⟨⟨_, h⟩, _⟩ := hπ
      simp only at h ⊢
      rw [h]
  have hC : ∑ π ∈ (P.filter fun π => ¬ π.2.1 = π.1.2).filter (fun π => π.2.2 = π.1.1), f π =
      ∑ t ∈ (oneMoves G S).filter (fun t => ¬ t.2.1 ∉ S), f ((t.2.1, t.2.2), (t.1, t.2.1)) := by
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
      simp only [mem_filter, P] at hπ
      obtain ⟨_, h⟩ := hπ
      simp only at h ⊢
      rw [h]
  have hD : (P.filter fun π => ¬ π.2.1 = π.1.2).filter (fun π => ¬ π.2.2 = π.1.1) =
      twoMoves G S := by
    rw [twoMoves, filter_filter]
  rw [hA, hB, hC, hD]
  abel

end Split

/-! ### `(H²)_{c'' c}` as a sum over paths -/

section Square

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
  {G : SimpleGraph V} [DecidableRel G.Adj] {ord : V × σ ↪ ℕ}

omit [Fintype σ] [DecidableEq σ] in
theorem hops_occ {c : Config V σ} {p : V × V} :
    p ∈ hops G (occ c) ↔ G.Adj p.1 p.2 ∧ c p.1 ≠ none ∧ c p.2 = none := by
  rw [mem_hops, mem_occ, mem_occ, not_not]

/-- A sum over the basis against `H b c` is a sum over the hops out of `c`. -/
theorem sum_basis_mul_hinf {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n)
    (f : Config V σ → ℂ) :
    ∑ b ∈ basis V n, f b * hinf G ord b c =
      ∑ p ∈ hops G (occ c), f (move c p.1 p.2) * hinf G ord (move c p.1 p.2) c := by
  have himage : (hops G (occ c)).image (fun p => move c p.1 p.2) ⊆ basis V n := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    rw [hops_occ] at hp
    exact move_mem_basis hc hp.2.1 hp.2.2
  rw [← sum_subset himage, sum_image]
  · intro p hp q hq hpq
    rw [mem_coe, hops_occ] at hp hq
    obtain ⟨h1, h2⟩ := move_inj c hp.2.1 hp.2.2 hq.2.1 hq.2.2 hpq
    exact Prod.ext h1 h2
  · intro b _ hb
    have hzero : hinf G ord b c = 0 := by
      refine hinf_apply_eq_zero fun i j hij hi hj hbm => hb ?_
      exact mem_image.mpr ⟨(i, j), hops_occ.2 ⟨hij, hi, hj⟩, hbm.symm⟩
    simp [hzero]

/-- A matrix element of `H` out of `m` as a sum over the hops out of `m`. -/
theorem hinf_apply_eq_sum (c'' m : Config V σ) :
    hinf G ord c'' m = ∑ q ∈ hops G (occ m),
      if c'' = move m q.1 q.2 then hinf G ord (move m q.1 q.2) m else 0 := by
  by_cases h : ∃ q ∈ hops G (occ m), c'' = move m q.1 q.2
  · obtain ⟨q, hq, rfl⟩ := h
    rw [sum_eq_single q]
    · rw [ite_eq_left rfl]
    · intro q' hq' hne
      rw [ite_eq_right]
      intro he
      rw [hops_occ] at hq hq'
      obtain ⟨h1, h2⟩ := move_inj m hq.2.1 hq.2.2 hq'.2.1 hq'.2.2 he
      exact hne (Prod.ext h1 h2).symm
    · intro h; exact absurd hq h
  · rw [hinf_apply_eq_zero, sum_eq_zero]
    · intro q hq
      rw [ite_eq_right]
      intro he
      exact h ⟨q, hq, he⟩
    · intro i j hij hi hj he
      exact h ⟨(i, j), hops_occ.2 ⟨hij, hi, hj⟩, he⟩

variable (G ord) in
/-- `(H²)_{c'' c}`: the sum of the amplitudes of the two-hop paths from `c` to `c''`. -/
noncomputable def Qf (c'' c : Config V σ) : ℂ :=
  ∑ π ∈ paths G (occ c), if c'' = endC c π then pathSign G ord c π else 0

/-- **`(H²)_{c'' c}` in the basis is the path sum.** -/
theorem sum_hinf_mul_hinf {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n)
    (c'' : Config V σ) :
    ∑ b ∈ basis V n, hinf G ord c'' b * hinf G ord b c = Qf G ord c'' c := by
  rw [sum_basis_mul_hinf hc (fun b => hinf G ord c'' b), Qf, sum_paths]
  refine sum_congr rfl fun p hp => ?_
  rw [hops_occ] at hp
  rw [hinf_apply_eq_sum c'' (move c p.1 p.2), occ_move hp.2.1 hp.2.2 hp.1.ne, sum_mul]
  refine sum_congr rfl fun q _ => ?_
  rw [ite_mul, zero_mul]
  rfl

/-- `(H²)_{c'' c} = (H²)_{c c''}` on the basis. -/
theorem Qf_symm {n : σ → ℕ} {c c'' : Config V σ} (hc : c ∈ basis V n) (hc'' : c'' ∈ basis V n) :
    Qf G ord c'' c = Qf G ord c c'' := by
  rw [← sum_hinf_mul_hinf hc, ← sum_hinf_mul_hinf hc'']
  refine sum_congr rfl fun b _ => ?_
  rw [hinf_symm c'' b, hinf_symm b c, mul_comm]

/-- **`Tr(H_B⁴) = ∑_{c, c''} (H²)_{c'' c}²`.** -/
theorem block_sum_hinf (n : σ → ℕ) :
    ∑ c ∈ basis V n, ∑ b₁ ∈ basis V n, ∑ b₂ ∈ basis V n, ∑ b₃ ∈ basis V n,
        hinf G ord c b₁ * hinf G ord b₁ b₂ * hinf G ord b₂ b₃ * hinf G ord b₃ c =
      ∑ c ∈ basis V n, ∑ c'' ∈ basis V n, Qf G ord c'' c ^ 2 := by
  set B := basis V n
  refine sum_congr rfl fun c hc => ?_
  calc _ = ∑ b₂ ∈ B, (∑ b₁ ∈ B, hinf G ord c b₁ * hinf G ord b₁ b₂) *
            (∑ b₃ ∈ B, hinf G ord b₂ b₃ * hinf G ord b₃ c) := by
        rw [sum_comm]
        refine sum_congr rfl fun b₂ _ => ?_
        rw [sum_mul_sum]
        refine sum_congr rfl fun b₁ _ => sum_congr rfl fun b₃ _ => ?_
        ring
    _ = ∑ b₂ ∈ B, Qf G ord b₂ c ^ 2 := by
        refine sum_congr rfl fun b₂ hb₂ => ?_
        rw [sum_hinf_mul_hinf hb₂, sum_hinf_mul_hinf hc, Qf_symm hc hb₂, sq]

/-- `∑_{c''} (H²)_{c'' c}² = ∑_π pathSign c π · (H²)_{endC c π, c}`. -/
theorem sum_Qf_sq {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n) :
    ∑ c'' ∈ basis V n, Qf G ord c'' c ^ 2 =
      ∑ π ∈ paths G (occ c), pathSign G ord c π * Qf G ord (endC c π) c := by
  have h : ∀ c'', Qf G ord c'' c ^ 2 =
      ∑ π ∈ paths G (occ c), if c'' = endC c π then pathSign G ord c π * Qf G ord c'' c
        else 0 := by
    intro c''
    rw [sq]
    nth_rewrite 1 [Qf]
    rw [sum_mul]
    refine sum_congr rfl fun π _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl fun c'' _ => h c'', sum_comm]
  refine sum_congr rfl fun π hπ => ?_
  rw [sum_ite_eq', ite_eq_left (endC_mem_basis G hc hπ)]

/-- `(H²)_{cc} = M(c)`, the number of hops out of `c`. -/
theorem Qf_self {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n) :
    Qf G ord c c = (hops G (occ c)).card := by
  rw [← sum_hinf_mul_hinf hc, sum_mul_apply_self (hinf_isProjectedHopping G ord) hc]
  simp

/-- A path amplitude squares to `1`. -/
theorem pathSign_sq {c : Config V σ} {π : (V × V) × (V × V)} (hπ : π ∈ paths G (occ c)) :
    pathSign G ord c π * pathSign G ord c π = 1 := by
  rw [mem_paths, hops_occ] at hπ
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hπ
  rw [← occ_move h2 h3 h1.ne, hops_occ] at h4
  obtain ⟨h4, h5, h6⟩ := h4
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h2
  obtain ⟨s', hs'⟩ := Option.ne_none_iff_exists'.1 h5
  simp only [pathSign, endC, midC]
  rw [hinf_apply_move h4 hs' h6, hinf_apply_move h1 hs h3]
  have e1 := hopSign_mul_self ord (configState c) (π.1.1, s) (π.1.2, s)
  have e2 := hopSign_mul_self ord (configState (move c π.1.1 π.1.2)) (π.2.1, s') (π.2.2, s')
  linear_combination (hopSign ord (configState (move c π.1.1 π.1.2)) (π.2.1, s') (π.2.2, s') *
    hopSign ord (configState (move c π.1.1 π.1.2)) (π.2.1, s') (π.2.2, s')) * e1 + e2

end Square

end HubbardMoments
