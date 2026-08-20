/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with positive integers:
`x ^ n + y ^ n = z ^ n` has no solution with `x, y, z > 0`. -/

def FLTFor (n : ℕ) : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- Fermat's Last Theorem: for every exponent `n > 2`, the equation `x ^ n + y ^ n = z ^ n`
has no solution in positive integers. -/
