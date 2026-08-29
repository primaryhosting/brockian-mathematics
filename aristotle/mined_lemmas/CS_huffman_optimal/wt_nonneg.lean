import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem wt_nonneg {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (t : HTree α) : 0 ≤ t.wt w := by
  induction t with
  | leaf a => simpa using hw a
  | node l r ihl ihr => simp only [wt_node]; linarith

