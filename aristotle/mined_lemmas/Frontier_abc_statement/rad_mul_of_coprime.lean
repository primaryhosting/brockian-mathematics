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

lemma rad_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    rad (a * b) = rad a * rad b := by
  rw [rad, rad, rad, Nat.primeFactors_mul ha hb, Finset.prod_union h.disjoint_primeFactors]

