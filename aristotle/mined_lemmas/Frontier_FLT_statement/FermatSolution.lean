/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean does not allow a module
-- docstring to precede the `import` commands; the same text appears as the module
-- docstring immediately below the imports.)

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A *Fermat solution* with exponent `n`: positive naturals `x, y, z` with
`x ^ n + y ^ n = z ^ n`. -/

def FermatSolution (n x y z : ℕ) : Prop := 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ n + y ^ n = z ^ n

/-- Fermat's Last Theorem for the exponent `n`: the equation `x ^ n + y ^ n = z ^ n`
has no solution in positive integers. -/
