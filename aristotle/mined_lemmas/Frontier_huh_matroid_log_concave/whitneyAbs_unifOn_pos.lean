import RequestProject.Main

/-!
# Log-concavity of the characteristic polynomial of a uniform matroid

This file constructs the uniform matroid `U_{r,E}` on a finite ground set `E` and proves that
the coefficients of its characteristic polynomial form a log-concave sequence, i.e. the
Adiprasito–Huh–Katz theorem for uniform matroids.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The uniform matroid `U_{r,E}`: the independent sets are the subsets of `E` of size at most
`r`. -/

theorem whitneyAbs_unifOn_pos (E : Finset α) (r i : ℕ) (hr : r ≤ E.card) (hi : 1 ≤ i) :
    whitneyAbs (unifOn E r) E i = if i ≤ r then E.card.choose (r - i) else 0 := by
  rw [whitneyAbs, coeff_charPoly_unifOn E r i hr]
  split_ifs with hir
  · rw [Finset.sum_eq_single (r - i)]
    · rw [if_pos (by omega), mul_one, natAbs_signed]
    · intro k _ hne
      rw [if_neg (by rcases le_total r k with h | h <;> simp [h] <;> omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [Finset.sum_eq_zero fun k _ => by rw [if_neg (by omega), mul_zero]]
    rfl

/-- The constant coefficient of the characteristic polynomial of `U_{r,E}`. -/
