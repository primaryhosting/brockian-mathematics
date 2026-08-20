import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem sum_choose_lt_eq (m : ℕ) :
    ∑ j ∈ range m, (2 * m).choose j = ∑ j ∈ range m, (2 * m).choose (m + 1 + j) := by
  have h := Finset.sum_range_reflect (fun j => (2 * m).choose (m + 1 + j)) m
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.mp hj
  have : m + 1 + (m - 1 - j) = 2 * m - j := by omega
  rw [this, Nat.choose_symm (by omega)]

/-- `2 ∑_{i<m} C(2m,i) + C(2m,m) = 4^m`. -/
