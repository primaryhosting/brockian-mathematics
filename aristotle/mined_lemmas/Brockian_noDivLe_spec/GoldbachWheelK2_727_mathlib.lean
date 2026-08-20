/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/

theorem GoldbachWheelK2_727_mathlib :
    ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 727 →
      ∃ p q : ℕ, p ∈ goldbachWheelK2 ∧ Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro n hn h4 hle
  obtain ⟨p, q, hp, hpp, hqp, hsum⟩ :=
    GoldbachWheelK2_727 n (Nat.even_iff.mp hn) h4 hle
  exact ⟨p, q, hp, (isPrime_iff_nat_prime p).mp hpp, (isPrime_iff_nat_prime q).mp hqp, hsum⟩

/-- Every entry of the wheel really is prime. -/
