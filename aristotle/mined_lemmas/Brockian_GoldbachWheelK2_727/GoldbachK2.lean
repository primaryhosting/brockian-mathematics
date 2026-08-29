/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000

namespace Brockian

/-- `GoldbachK2 n` says that `n` is a sum of two primes (the `K = 2` Goldbach property). -/

def GoldbachK2 (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- **Goldbach wheel, K = 2, modulus 727.**
Every even natural number `n` with `4 ≤ n ≤ 727` is a sum of two primes.
(The odd endpoint 727 is the wheel modulus; the largest even number covered is 726.) -/
