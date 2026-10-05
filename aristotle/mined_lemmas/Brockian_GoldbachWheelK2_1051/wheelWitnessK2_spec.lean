/-
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- `wheelWitnessK2` is a table of small "wheel" primes: entry `i` is the least prime `p`
such that both `p` and `2 * i - p` are prime (and `0` for `i < 2`). -/

theorem wheelWitnessK2_spec : ∀ i < 526, 2 ≤ i →
    Nat.Prime (wheelWitnessK2.getD i 0) ∧ Nat.Prime (2 * i - wheelWitnessK2.getD i 0) ∧
      wheelWitnessK2.getD i 0 ≤ 2 * i ∧ wheelWitnessK2.getD i 0 ≤ 73 := by decide

/-- **Goldbach wheel, `K = 2`, modulus `1051`.**
Every even number `n` with `4 ≤ n ≤ 1051` is a sum of two primes, and moreover the smaller
prime can always be taken from the wheel of primes below `74`. -/
