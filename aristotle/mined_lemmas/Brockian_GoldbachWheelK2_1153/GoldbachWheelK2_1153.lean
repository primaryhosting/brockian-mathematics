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

theorem GoldbachWheelK2_1153 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Nat.Coprime p 2 ∧ Nat.Coprime q 2 ∧
      Odd p ∧ Odd q ∧ p + q = 2 * 1153 := by
  refine ⟨13, 2293, by norm_num, prime_2293, by decide, ?_, ?_, ?_, by norm_num⟩
  · decide
  · exact ⟨6, by norm_num⟩
  · exact odd_of_prime_coprime_two prime_2293 (by decide)

/-- Every Goldbach representation of `2 * 1153` is automatically a wheel representation:
both summands are coprime to the modulus `2`. -/
