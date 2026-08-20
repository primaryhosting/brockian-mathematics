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

theorem FLTFor_iff_fermatLastTheoremFor (n : ℕ) : FLTFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h x y z hx hy hz
    exact h x y z (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- `FLT` agrees with Mathlib's `FermatLastTheorem`. -/
