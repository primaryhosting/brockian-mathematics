import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem buildList_leaves (w : α → ℝ) :
    ∀ (n : ℕ) (ts : List (HTree α)), ts.length = n →
      msLeaves (↑(buildList w ts)) = msLeaves (↑ts) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ts hlen
    by_cases hbig : 2 ≤ ts.length
    · rw [buildList_of_le w hbig,
        ih (combineStep w ts).length (by have := combineStep_length w ts hbig; omega)
          (combineStep w ts) rfl, combineStep_leaves w ts hbig]
    · rw [buildList_of_lt w (Nat.not_le.1 hbig)]

