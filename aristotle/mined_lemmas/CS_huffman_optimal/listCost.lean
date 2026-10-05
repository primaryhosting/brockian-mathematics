import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def listCost (w : α → ℝ) (ts : List (HTree α)) : ℝ :=
  (ts.map (HTree.cost w)).sum

/-- Extract from a length assignment the entry attached to a given item. -/
