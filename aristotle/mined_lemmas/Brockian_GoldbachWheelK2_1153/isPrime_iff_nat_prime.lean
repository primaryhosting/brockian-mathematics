/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`n` is at least `2` and its only divisors are `1` and `n`. -/

theorem isPrime_iff_nat_prime {n : ℕ} : IsPrime n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hd⟩
    rw [Nat.prime_def]
    exact ⟨h2, fun d hdvd => (hd d hdvd).imp id id⟩
  · intro hp
    exact ⟨hp.two_le, fun d hdvd => (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd)⟩

/-- **Goldbach's conjecture below the wheel modulus 1153**, stated with Mathlib's
`Nat.Prime` and `Even`: every even natural number `n` with `4 ≤ n ≤ 1153` is a sum of
two primes. -/
