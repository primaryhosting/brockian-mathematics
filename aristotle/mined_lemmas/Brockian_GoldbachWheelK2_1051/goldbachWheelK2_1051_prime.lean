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

theorem goldbachWheelK2_1051_prime :
    ∀ n : Nat, 4 ≤ n → n ≤ 1051 → Even n →
      ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n h4 hle hev
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_1051 n h4 hle (Nat.even_iff.mp hev)
  exact ⟨p, q, (gwPrime_iff_prime p).mp hp, (gwPrime_iff_prime q).mp hq, hpq⟩

end Brockian

