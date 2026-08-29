import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def treeLe (w : α → ℝ) (a b : HTree α) : Bool := decide (a.wt w ≤ b.wt w)

