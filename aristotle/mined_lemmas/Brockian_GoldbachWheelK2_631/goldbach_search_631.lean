/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, in the standard trial-division form:
`p` is at least `2` and has no divisor `m` with `2 ≤ m < p`.

This file is deliberately kept free of imports so that the required module
header can be the very first item in the file (Lean forbids `import` after a
module docstring).  The companion file
`RequestProject/GoldbachWheelK2_631_Mathlib.lean` proves
`IsPrimeNat p ↔ Nat.Prime p`, so the statement below is exactly the usual
Goldbach statement phrased with Mathlib's `Nat.Prime`. -/

private theorem goldbach_search_631 :
    ∀ n, n < 632 → 4 ≤ n → n % 2 = 0 →
      ∃ p, p < n + 1 ∧ IsPrimeNat p ∧ IsPrimeNat (n - p) := by
  decide

/-- **Goldbach wheel, K = 2, modulus 631**: every even `n` with `4 ≤ n ≤ 631`
is a sum of two primes. -/
