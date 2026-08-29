import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The "wheel" of primes for modulus `1327`: the list of all prime numbers `p ≤ 1327`.
Note that the modulus `1327` is itself prime, so it is the last entry. -/

theorem wheelPrimes1327_prime : ∀ p ∈ wheelPrimes1327, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

/-- Combinatorial core: for every even `n` with `4 ≤ n ≤ 1327` there is an entry `p` of the
wheel such that `n - p` is also an entry of the wheel.  Verified by kernel evaluation. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
