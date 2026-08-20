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

lemma P12_apply (i j : Fin 12) : P12 i j = zeta (i * j) := by
  simp only [P12, Matrix.vandermonde_apply, zeta, Fin.val_mul, om_pow_mod, pow_mul]

