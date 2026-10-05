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

theorem wheel1327_core :
    ∀ n < 1328, 4 ≤ n → n % 2 = 0 → ∃ p ∈ wheelPrimes1327, (n - p) ∈ wheelPrimes1327 := by
  decide +kernel

/-- **Goldbach's conjecture, verified on the wheel of modulus 1327** (`K = 2` summands):
every even natural number `n` with `4 ≤ n ≤ 1327` is a sum of two primes. -/
