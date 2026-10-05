/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma om_pow_mod (a : ℕ) : om ^ (a % 14) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 14]
  rw [pow_add, pow_mul, om_pow_14, one_pow, one_mul]

/-- The additive character `x ↦ ω ^ x` of `Fin 14`, where `ω = exp (2πi/14)`. -/
