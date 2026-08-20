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
lemma prime_2293 : Nat.Prime 2293 := by norm_num

/-- Auxiliary: an odd prime is exactly a prime that is coprime to the wheel modulus `2`. -/
lemma odd_of_prime_coprime_two {p : ℕ} (hp : p.Prime) (h : Nat.Coprime p 2) : Odd p := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    simp [Nat.Coprime] at h
  · exact hodd

/-- **Goldbach wheel, modulus `K = 2`, at `n = 2 * 1153 = 2306`.**

The even number `2 * 1153` is a sum of two primes, both of which are coprime to the
wheel modulus `2` (equivalently, both odd) -- the witnesses are `13` and `2293`. -/
theorem GoldbachWheelK2_1153 :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Nat.Coprime p 2 ∧ Nat.Coprime q 2 ∧
      Odd p ∧ Odd q ∧ p + q = 2 * 1153 := by
  refine ⟨13, 2293, by norm_num, prime_2293, by decide, ?_, ?_, ?_, by norm_num⟩
  · decide
  · exact ⟨6, by norm_num⟩
  · exact odd_of_prime_coprime_two prime_2293 (by decide)

/-- Every Goldbach representation of `2 * 1153` is automatically a wheel representation:
both summands are coprime to the modulus `2`. -/
lemma goldbach_2306_summands_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p + q = 2 * 1153) : Odd p ∧ Odd q := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : q = 2304 := by omega
    subst this
    exact absurd hq (by norm_num)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : p = 2304 := by omega
    subst this
    exact absurd hp (by norm_num)
  exact ⟨hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2⟩

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

