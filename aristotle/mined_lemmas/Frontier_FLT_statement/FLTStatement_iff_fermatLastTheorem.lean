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

theorem FLTStatement_iff_fermatLastTheorem : FLTStatement ↔ FermatLastTheorem := by
  constructor
  · intro h n hn a b c ha hb hc
    exact h n hn a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
  · intro h n hn x y z hx hy hz
    exact h n hn x y z hx.ne' hy.ne' hz.ne'

/-- The elementary statement of Fermat's Last Theorem for a fixed exponent `n`. -/
