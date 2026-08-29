/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality, stated in the usual way: `p` is at least `2` and its only divisors are
`1` and `p`. (This file is self-contained, so the predicate is spelled out here.) -/

theorem gwPrime_iff_prime (p : Nat) : GwPrime p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨h2, hdiv⟩
    refine Nat.prime_def.mpr ⟨h2, ?_⟩
    intro m hm
    exact hdiv m hm
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- Every even `n` with `4 ≤ n ≤ 1051` is a sum of two primes, stated with `Nat.Prime`. -/
