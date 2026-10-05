import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem treeLe_trans (w : α → ℝ) (a b c : HTree α) :
    treeLe w a b = true → treeLe w b c = true → treeLe w a c = true := by
  simp only [treeLe, decide_eq_true_eq]
  exact le_trans

