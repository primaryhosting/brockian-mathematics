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

def FLT : Prop := ∀ n : ℕ, 2 < n → FLTFor n

/-- The positivity form `FLTFor n` agrees with Mathlib's `FermatLastTheoremFor n`
(which is phrased with `≠ 0`). -/
