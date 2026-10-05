import Mathlib

/-!
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
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

namespace Chebyshev

open ArithmeticFunction

/-- The second Chebyshev function at 4: `ψ(4) = Λ(1)+Λ(2)+Λ(3)+Λ(4) = log 2 + log 3 + log 2
= log 12`. -/
theorem psi_two_le :
    (∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n) = Real.log 12 := by
  have h2 : Λ 2 = Real.log 2 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h3 : Λ 3 = Real.log 3 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have h4 : Λ 4 = Real.log 2 := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
  have h12 : (12 : ℝ) = 2 * 2 * 3 := by norm_num
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num)]
  simp only [Finset.Icc_self, Finset.sum_singleton, ArithmeticFunction.vonMangoldt_apply_one,
    h2, h3, h4, h12]
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  ring

end Chebyshev

