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

def ABCConjecture : Prop := ∀ ε : ℝ, 0 < ε → (exceptionalSet ε).Finite

/-- The "effective-constant" form of the abc conjecture: for every `ε > 0` there is a
constant `K` with `c ≤ K * rad (a * b * c) ^ (1 + ε)` for all abc-triples. -/
