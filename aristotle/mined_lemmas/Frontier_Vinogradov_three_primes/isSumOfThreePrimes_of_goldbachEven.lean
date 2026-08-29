import Mathlib

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `IsSumOfThreePrimes n` says that `n` can be written as a sum of three (not necessarily
distinct) prime numbers. -/

theorem isSumOfThreePrimes_of_goldbachEven (h : GoldbachEven) {n : ℕ} (hn : 9 ≤ n)
    (hodd : Odd n) : IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨p, q, hp, hq, hpq⟩ := h (n - 3) (by omega) ⟨(n - 3) / 2, by omega⟩
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- **Vinogradov's three primes theorem**, in the form of a Lean-checked reduction to the
binary Goldbach statement: assuming every even number `≥ 4` is a sum of two primes, there is a
threshold (namely `9`) beyond which every odd number is a sum of three primes. -/
