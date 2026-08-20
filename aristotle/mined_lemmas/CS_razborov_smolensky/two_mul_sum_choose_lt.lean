import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem two_mul_sum_choose_lt (m : ℕ) :
    2 * (∑ j ∈ range m, (2 * m).choose j) + (2 * m).choose m = 4 ^ m := by
  have htot : ∑ j ∈ range (2 * m + 1), (2 * m).choose j = 4 ^ m := by
    rw [Nat.sum_range_choose]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hsplit : ∑ j ∈ range (2 * m + 1), (2 * m).choose j
      = (∑ j ∈ range m, (2 * m).choose j) + (2 * m).choose m
        + ∑ j ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose j := by
    rw [← Finset.sum_range_succ (fun j => (2 * m).choose j) m]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ 2 * m + 1)]
  have hIco : ∑ j ∈ Ico (m + 1) (2 * m + 1), (2 * m).choose j
      = ∑ j ∈ range m, (2 * m).choose (m + 1 + j) := by
    rw [Finset.sum_Ico_eq_sum_range, show 2 * m + 1 - (m + 1) = m from by omega]
  rw [hsplit, hIco, ← sum_choose_lt_eq] at htot
  omega

/-- The partial sum of binomial coefficients up to `m + D`. -/
