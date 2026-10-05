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
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- `IsSumOfThreePrimes n` means that `n` can be written as a sum of three
(not necessarily distinct) prime numbers. -/

theorem isSumOfThreePrimes_of_odd_of_lt_500 (n : ℕ) (h7 : 7 ≤ n) (hlt : n < 500)
    (hodd : Odd n) : IsSumOfThreePrimes n := by
  have key : ∀ m < 500, 7 ≤ m → Odd m →
      ∃ p < m, Nat.Prime p ∧ Nat.Prime (m - 3 - p) ∧ m = 3 + p + (m - 3 - p) := by decide
  obtain ⟨p, -, hp, hq, hsum⟩ := key n hlt h7 hodd
  exact ⟨3, p, n - 3 - p, Nat.prime_three, hp, hq, hsum⟩

/-- Unconditionally, there are arbitrarily large odd numbers which are sums of three
primes: `4 + p = 2 + 2 + p` for any odd prime `p`. -/
