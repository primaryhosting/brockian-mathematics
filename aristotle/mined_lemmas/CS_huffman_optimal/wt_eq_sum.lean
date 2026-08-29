import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem wt_eq_sum (w : α → ℝ) (t : HTree α) : t.wt w = (t.leaves.map w).sum := by
  induction t with
  | leaf a => simp
  | node l r ihl ihr => simp [ihl, ihr]

