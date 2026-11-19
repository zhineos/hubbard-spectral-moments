-- SPDX-License-Identifier: Apache-2.0
module

public import HubbardMoments.FourthMoment.FermionMoment

/-!
# The exact fourth moment on the square lattice

Stage 7 of the fourth-moment plan: the square-lattice forms of `fourthMoment_projectedHubbard`.

* `fourthMoment_projectedHubbard_torus`: on the `L × L` torus with `L = 3` or `L ≥ 5`, where
  `m = 2N`, `W = 6N`, `C₄ = N` and `D = C(2N, 2) - 6N = 2N² - 7N` (`torus_graph_counts`,
  `disjointEdgePairs_eq`), the intercept is `36N p₁₁ + (48N² - 184N) p₂₂ - 12N p₃₁` and the
  slope `-8(N - n)(8N - 11n - 2)/((N - 1)(N - 2)(N - 3))`.
* `fourthMoment_projectedHubbard_torus_four_table`: on the `4 × 4` torus (`m = 32`, `W = 96`, `C₄ = 24`, `D = 400`), the
  seven values of Table `tab:mu4exact`, evaluated from the closed form by `norm_num`.
-/

@[expose] public section

namespace HubbardMoments

open Finset

section TorusMoment

/-- `D` on the torus, as a real number: `D = C(2N, 2) - 6N`, `N = L²`, `L ≥ 3`. -/
theorem torus_disjointEdgePairs_real (L : ℕ) (hL : 3 ≤ L) :
    (disjointEdgePairs (torus L) : ℝ) =
      (2 * (L * L : ℕ) : ℝ) * (2 * (L * L : ℕ) - 1) / 2 - 6 * (L * L : ℕ) := by
  have h := disjointEdgePairs_add_wedgeCount (torus L)
  rw [torus_card_edgeFinset L hL, torus_wedgeCount L hL] at h
  have h' : (disjointEdgePairs (torus L) : ℝ) + (6 * (L * L) : ℕ) = ((2 * (L * L)).choose 2 : ℕ) := by
    exact_mod_cast h
  rw [Nat.cast_choose_two] at h'
  push_cast at h' ⊢
  linarith

/-- **`Spec.FourthMomentHubbardTorus`.** -/
theorem fourthMoment_projectedHubbard_torus :
  ∀ (L : ℕ) (t : ℝ) (ord : (Fin L × Fin L) × Bool ↪ ℕ) (n : Bool → ℕ),
    (L = 3 ∨ 5 ≤ L) → n true + n false ≤ L * L →
      fourthMoment (basis (Fin L × Fin L) n) (projectedHubbard (torus L) t (fun _ _ => 0) ord) =
        ((t ^ 4 * (36 * (L * L : ℕ) * occProb (L * L) (n true + n false) 1 1 +
            (48 * ((L * L : ℕ) : ℝ) ^ 2 - 184 * (L * L : ℕ)) *
              occProb (L * L) (n true + n false) 2 2 -
            12 * (L * L : ℕ) * occProb (L * L) (n true + n false) 3 1 -
            8 * (((L * L : ℕ) : ℝ) - (n true + n false : ℕ)) *
                (8 * ((L * L : ℕ) : ℝ) - 11 * (n true + n false : ℕ) - 2) /
              ((((L * L : ℕ) : ℝ) - 1) * (((L * L : ℕ) : ℝ) - 2) * (((L * L : ℕ) : ℝ) - 3)) *
              ((n true).choose 2 + (n false).choose 2 : ℕ)) : ℝ) : ℂ) := by
  intro L t ord n hL hnN
  have hL3 : 3 ≤ L := by omega
  have hcard : Fintype.card (Fin L × Fin L) = L * L := by
    rw [Fintype.card_prod, Fintype.card_fin]
  have hN9 : (9 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
    have : 9 ≤ L * L := Nat.mul_le_mul hL3 hL3
    exact_mod_cast this
  rw [fourthMoment_projectedHubbard (Fin L × Fin L) (torus L) t ord n (by rw [hcard]; nlinarith)
    (by rw [hcard]; exact hnN)]
  congr 1
  simp only [fourthMomentIntercept, exchangeSlope, hcard]
  rw [torus_card_edgeFinset L hL3, torus_wedgeCount L hL3, torus_fourCycleCount L hL,
    torus_disjointEdgePairs_real L hL3]
  set x : ℝ := ((L * L : ℕ) : ℝ) with hx
  have h1 : x - 1 ≠ 0 := by linarith
  have h2 : x - 2 ≠ 0 := by linarith
  have h3 : x - 3 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  have hLx : (L : ℝ) * L = x := by rw [hx]; push_cast; ring
  push_cast
  rw [hLx]
  field_simp
  ring

/-- The fourth moment on the `4 × 4` torus from the closed form, for `n↑ = a`, `n↓ = b`. -/
theorem fourthMoment_torus_four (t : ℝ) (ord : (Fin 4 × Fin 4) × Bool ↪ ℕ) (a b : ℕ)
    (hnN : a + b ≤ 16) :
    fourthMoment (basis (Fin 4 × Fin 4) (fun s => if s then a else b))
        (projectedHubbard (torus 4) t (fun _ _ => 0) ord) =
      ((t ^ 4 * ((2 * 32 + 4 * 96 + 8 * 24 : ℕ) * occProb 16 (a + b) 1 1 +
          (24 * (400 : ℝ) - 16 * 24) * occProb 16 (a + b) 2 2 -
            12 * (24 : ℝ) * occProb 16 (a + b) 3 1 +
          -(8 * (24 : ℝ) * ((16 : ℝ) - (a + b : ℕ)) * (8 * 16 - 11 * (a + b : ℕ) - 2)) /
              (16 * (16 - 1) * (16 - 2) * (16 - 3)) *
            (a.choose 2 + b.choose 2 : ℕ)) : ℝ) : ℂ) := by
  have hcard : Fintype.card (Fin 4 × Fin 4) = 16 := by
    rw [Fintype.card_prod, Fintype.card_fin]
  have hD : (disjointEdgePairs (torus 4) : ℝ) = 400 := by
    rw [torus_disjointEdgePairs_real 4 (by norm_num)]; norm_num
  have h := fourthMoment_projectedHubbard (Fin 4 × Fin 4) (torus 4) t ord (fun s => if s then a else b)
    (by rw [hcard]; norm_num) (by rw [hcard]; simpa using hnN)
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  refine h.trans (congrArg (fun r : ℝ => (r : ℂ)) ?_)
  simp only [fourthMomentIntercept, exchangeSlope, hcard]
  rw [torus_card_edgeFinset 4 (by norm_num), torus_wedgeCount 4 (by norm_num),
    torus_four_fourCycleCount, hD]
  push_cast
  ring

/-- **`Spec.FourthMomentTableL4`.** -/
theorem fourthMoment_projectedHubbard_torus_four_table :
  ∀ (t : ℝ) (ord : (Fin 4 × Fin 4) × Bool ↪ ℕ),
    let μ₄ := fun a b : ℕ => fourthMoment (basis (Fin 4 × Fin 4) (fun s => if s then a else b))
      (projectedHubbard (torus 4) t (fun _ _ => 0) ord)
    μ₄ 2 0 = ((t ^ 4 * (2176 / 15) : ℝ) : ℂ) ∧ μ₄ 1 1 = ((t ^ 4 * (2272 / 15) : ℝ) : ℂ) ∧
    μ₄ 3 0 = ((t ^ 4 * (9976 / 35) : ℝ) : ℂ) ∧ μ₄ 2 1 = ((t ^ 4 * (10348 / 35) : ℝ) : ℂ) ∧
    μ₄ 4 0 = ((t ^ 4 * (197632 / 455) : ℝ) : ℂ) ∧ μ₄ 3 1 = ((t ^ 4 * (203536 / 455) : ℝ) : ℂ) ∧
    μ₄ 2 2 = ((t ^ 4 * (15808 / 35) : ℝ) : ℂ) := by
  intro t ord
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · refine (fourthMoment_torus_four t ord _ _ (by norm_num)).trans
      (congrArg (fun r : ℝ => (r : ℂ)) ?_)
    norm_num [occProb, Nat.descFactorial, Nat.choose]

end TorusMoment

end HubbardMoments
