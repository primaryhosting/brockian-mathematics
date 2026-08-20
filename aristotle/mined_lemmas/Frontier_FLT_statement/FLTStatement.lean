/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The elementary statement of Fermat's Last Theorem: for every exponent `n ≥ 3`,
the equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers. -/

def FLTStatement : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The elementary formulation `Frontier.FLTStatement` agrees with Mathlib's
`FermatLastTheorem`. -/
