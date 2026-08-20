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

lemma om_pow_mod (m : ℕ) : om ^ (m % 12) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 12]
  rw [pow_add, pow_mul, om_pow_twelve, one_pow, one_mul]

/-- The character `Fin 12 → ℂ`, `a ↦ ω ^ a`. -/
