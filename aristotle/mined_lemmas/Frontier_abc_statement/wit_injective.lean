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

private lemma wit_injective : Function.Injective wit := by
  intro n m h
  have h3 : (3 : ℕ) ^ (2 ^ (n + 1)) = 3 ^ (2 ^ (m + 1)) := congrArg (fun t => t.2.2) h
  have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ (m + 1) := Nat.pow_right_injective (by norm_num) h3
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

