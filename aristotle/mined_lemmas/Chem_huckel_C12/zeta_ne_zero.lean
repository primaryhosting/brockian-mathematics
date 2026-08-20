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

lemma zeta_ne_zero (a : Fin 12) : zeta a ≠ 0 := by
  have : om ≠ 0 := by
    simp [om, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

/-- `ζ k` is the complex exponential `exp ((2πk/12) I)`. -/
