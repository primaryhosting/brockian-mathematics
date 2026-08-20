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

theorem abc_statement : ABCConjecture ↔ ABCBounded :=
  ⟨abc_bounded_of_conjecture, abc_conjecture_of_bounded⟩

/-- The base case `1 + 8 = 9`: this triple already violates the inequality
`c ≤ rad (a * b * c)`, so the exponent `1 + ε` (with `ε > 0`) cannot be replaced by `1`. -/
