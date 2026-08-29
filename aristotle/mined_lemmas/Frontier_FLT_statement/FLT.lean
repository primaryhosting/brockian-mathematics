-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with *positive* integers:
there are no `x, y, z > 0` with `x ^ n + y ^ n = z ^ n`. -/

def FLT : Prop := ∀ n : ℕ, 2 < n → FLTFor n

/-- The positive-integer formulation for a fixed exponent agrees with Mathlib's
`FermatLastTheoremFor` (which phrases the same thing via nonvanishing). -/
