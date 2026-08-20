import Mathlib
open Finset
namespace MS2.IT2


theorem uniform_max_entropy (n : ℕ) (hn : 0 < n) : -(1:ℝ) * Real.log (1/n) = Real.log n := by
  rw [Real.log_div one_ne_zero (by exact_mod_cast hn.ne')]
  simp

