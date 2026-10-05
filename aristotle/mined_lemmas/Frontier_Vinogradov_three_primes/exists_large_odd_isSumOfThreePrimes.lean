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

theorem exists_large_odd_isSumOfThreePrimes (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Odd n ∧ IsSumOfThreePrimes n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 3)
  have hp3 : 3 ≤ p := le_trans (le_max_right N 3) hpN
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  refine ⟨2 + 2 + p, ?_, ?_, ⟨2, 2, p, Nat.prime_two, Nat.prime_two, hp, rfl⟩⟩
  · have := le_trans (le_max_left N 3) hpN
    omega
  · rcases hpodd with ⟨k, hk⟩
    exact ⟨k + 2, by omega⟩

end Frontier

