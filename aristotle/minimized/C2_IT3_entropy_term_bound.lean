import Mathlib
open Finset
namespace C2.IT3

/-- Each entropy term `-p log p` is nonnegative on `[0,1]`. -/

theorem entropy_term_bound (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ -p*Real.log p := by
  rcases eq_or_lt_of_le h0 with h | h
  · simp [← h]
  · have : Real.log p ≤ 0 := Real.log_nonpos h0 h1
    nlinarith

/-- The binary entropy is strictly positive for `0 < p < 1`. -/
