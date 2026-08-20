import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/

lemma sub_one_ne_add_one (i : Fin 12) : i - 1 ≠ i + 1 := by
  intro h
  rw [sub_eq_add_neg] at h
  exact absurd (add_left_cancel h) (by decide)

/-- The key intertwining relation `A · P = P · D`. -/
