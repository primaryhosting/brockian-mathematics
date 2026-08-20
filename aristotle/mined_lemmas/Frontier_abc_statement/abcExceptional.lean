/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`.
By convention `rad 0 = rad 1 = 1`. -/

def abcExceptional (eps : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
        ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + eps) < (t.2.2 : ℝ)}

/-- The `abc` conjecture: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/
