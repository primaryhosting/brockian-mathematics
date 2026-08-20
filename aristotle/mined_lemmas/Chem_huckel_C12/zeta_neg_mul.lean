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

lemma zeta_neg_mul (k : Fin 12) : zeta k * zeta (-k) = 1 := by
  rw [← zeta_add]
  simp [zeta_zero]

/-- The eigenvalue: `ζ k + ζ (-k) = 2 cos (2πk/12)`. -/
