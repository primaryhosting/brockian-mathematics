import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def wt (w : α → ℝ) : HTree α → ℝ
  | leaf a => w a
  | node l r => wt w l + wt w r

