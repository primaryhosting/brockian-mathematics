import Mathlib
open Finset
namespace MS2.Prob2

/-- AM–GM for three nonnegative reals. -/

theorem qm_am_general {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i)^2 ≤ n * ∑ i, (a i)^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := a)
  simpa using h

end MS2.Prob2

