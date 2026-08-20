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

lemma rad_pow {k : ℕ} (n : ℕ) (hk : k ≠ 0) : rad (n ^ k) = rad n := by
  rw [rad, rad, Nat.primeFactors_pow n hk]

