import Mathlib
namespace Brockian.MsBinet


theorem binet (n : ℕ) :
    (Nat.fib n : ℝ)
      = (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) / Real.sqrt 5 := by
  rw [eq_div_iff (ne_of_gt sqrt5_pos)]
  exact (binet_aux n).1

end Brockian.MsBinet

