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

theorem isSumOfThreePrimes_of_odd_le_502 {n : ℕ} (hn : 9 ≤ n) (hn' : n ≤ 502) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨p, hp, hp', hq'⟩ := goldbach_lt_500 (n - 3) (by omega) (by omega) (by omega)
  exact ⟨3, p, n - 3 - p, Nat.prime_three, hp', hq', by omega⟩

end Frontier

