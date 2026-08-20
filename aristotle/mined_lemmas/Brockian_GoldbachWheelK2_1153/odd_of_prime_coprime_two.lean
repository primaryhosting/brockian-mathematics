/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- Key intermediate lemma: the wheel partner `2293 = 2 * 1153 - 13` is prime. -/

lemma odd_of_prime_coprime_two {p : ℕ} (hp : p.Prime) (h : Nat.Coprime p 2) : Odd p := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    simp [Nat.Coprime] at h
  · exact hodd

/-- **Goldbach wheel, modulus `K = 2`, at `n = 2 * 1153 = 2306`.**

The even number `2 * 1153` is a sum of two primes, both of which are coprime to the
wheel modulus `2` (equivalently, both odd) -- the witnesses are `13` and `2293`. -/
