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

theorem FLTStatementFor_iff_fermatLastTheoremFor (n : ℕ) :
    FLTStatementFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h a b c ha hb hc
    exact h a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 3`: `x ³ + y ³ = z ³` has no positive-integer solution. -/
