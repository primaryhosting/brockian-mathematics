import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def kraftL (L : Multiset ℕ) : ℝ := (L.map (fun k => (2:ℝ) ^ (-(k:ℤ)))).sum

