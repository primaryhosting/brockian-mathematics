import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

theorem coprime_pair_four_primeFactors {m n : ℕ} (h : IsBetrothedPair m n)
    (hcop : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  by_contra hcon
  push_neg at hcon
  have hcard : (m * n).primeFactors.card ≤ 3 := by omega
  have hsigma : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  have hgt : 4 * (m * n) < (m + n + 1) * (m + n + 1) := by
    zify
    nlinarith [sq_nonneg ((m : ℤ) - (n : ℤ))]
  have hmn1 : 1 < m * n := by
    have hpos : 0 < m * n := Nat.mul_pos hm hn
    have hne : m * n ≠ 1 := by
      intro he
      have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right he
      have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_left he
      subst hm1; subst hn1
      rw [ArithmeticFunction.sigma_one] at hsm
      omega
    omega
  have := sigma_lt_four_mul hmn1 hcard
  omega

end BetrothedNumbers

end Brockian

