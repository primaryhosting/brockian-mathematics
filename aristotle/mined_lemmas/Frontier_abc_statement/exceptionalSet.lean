/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/

def exceptionalSet (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {p | ABCTriple p.1 p.2.1 p.2.2 ∧
        ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) < (p.2.2 : ℝ)}

/-- **The abc conjecture**: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/
