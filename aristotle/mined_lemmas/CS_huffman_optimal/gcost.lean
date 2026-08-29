import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def gcost (C W : β → ℝ) (M : Multiset (β × ℕ)) : ℝ :=
  (M.map (fun p => C p.1 + W p.1 * p.2)).sum

