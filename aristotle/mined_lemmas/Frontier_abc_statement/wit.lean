import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

private def wit (n : ℕ) : ℕ × ℕ × ℕ :=
  (1, 3 ^ (2 ^ (n + 1)) - 1, 3 ^ (2 ^ (n + 1)))

