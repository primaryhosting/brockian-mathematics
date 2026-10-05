/-
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- `n` is a sum of three (not necessarily distinct) primes. -/

theorem isSumOfThreePrimes_of_odd_of_le (n : ℕ) (h9 : 9 ≤ n) (hle : n ≤ 403) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨p, -, hp, hr⟩ :=
    goldbach_le_400 (n - 3) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) ⟨k - 1, by omega⟩
  have h2 : 2 ≤ n - 3 - p := hr.two_le
  exact ⟨3, p, n - 3 - p, Nat.prime_three, hp, hr, by omega⟩

end Frontier

