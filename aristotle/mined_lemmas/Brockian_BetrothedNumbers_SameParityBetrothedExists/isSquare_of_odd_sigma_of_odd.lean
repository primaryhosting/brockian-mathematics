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

/-
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` are *betrothed* (quasi-amicable) numbers: they are distinct and each one's
sum of divisors equals `m + n + 1`. -/

lemma isSquare_of_odd_sigma_of_odd {m : ℕ} (hm : Odd m) (h : Odd (σ 1 m)) : IsSquare m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  refine isSquare_of_factorization_even hm0 ?_
  intro p
  by_cases hp : p ∈ m.primeFactors
  · have hprod := sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hm0
    have hdvd : (∑ i ∈ range (m.factorization p + 1), p ^ (i * 1)) ∣ σ 1 m := by
      rw [hprod]; exact Finset.dvd_prod_of_mem _ hp
    have hodd : Odd (∑ i ∈ range (m.factorization p + 1), p ^ (i * 1)) := h.of_dvd_nat hdvd
    have hpodd : Odd p := by
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      rcases hpp.eq_two_or_odd' with h2 | h2
      · exact absurd (h2 ▸ hpm) (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using hm)
      · exact h2
    have hgs := geom_sum_mod_two_of_odd hpodd (m.factorization p + 1)
    simp only [mul_one] at hodd
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  · simp [Finsupp.notMem_support_iff.mp hp]

/-- If `σ n` is odd, then `n` is a square or twice a square. -/
