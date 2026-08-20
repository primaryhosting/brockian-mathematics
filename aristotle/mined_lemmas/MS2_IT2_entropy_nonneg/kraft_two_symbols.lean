import Mathlib
open Finset
namespace MS2.IT2


theorem kraft_two_symbols (l : ℕ) : (2:ℝ)^(-(l:ℤ)) ≤ 1 := by
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  simp

