import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem buildList_length_eq_one (w : α → ℝ) :
    ∀ (n : ℕ) (ts : List (HTree α)), ts.length = n → ts ≠ [] →
      (buildList w ts).length = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ts hlen hne
    by_cases hbig : 2 ≤ ts.length
    · obtain ⟨t1, t2, rest, hcs, _, _, _, _⟩ := combineStep_spec w ts hbig
      rw [buildList_of_le w hbig]
      exact ih (combineStep w ts).length (by have := combineStep_length w ts hbig; omega)
        (combineStep w ts) rfl (by rw [hcs]; simp)
    · rw [buildList_of_lt w (Nat.not_le.1 hbig)]
      have : ts.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
      omega

