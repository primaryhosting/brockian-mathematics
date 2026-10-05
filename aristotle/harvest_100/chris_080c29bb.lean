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

/-- The second Chebyshev function at `4`: the sum of the von Mangoldt function `Λ` over
`n ∈ {1, 2, 3, 4}` equals `log 12`, since `Λ 1 = 0`, `Λ 2 = log 2`, `Λ 3 = log 3`,
`Λ 4 = log 2`. -/
theorem psi_two_le :
    (∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n) = Real.log 12 := by
  have e1 : Λ 1 = 0 := vonMangoldt_apply_one
  have e2 : Λ 2 = Real.log 2 := by
    simpa using vonMangoldt_apply_prime (p := 2) Nat.prime_two
  have e3 : Λ 3 = Real.log 3 := by
    simpa using vonMangoldt_apply_prime (p := 3) Nat.prime_three
  have e4 : Λ 4 = Real.log 2 := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h, vonMangoldt_apply_pow (by norm_num), e2]
  have hlog : Real.log 12 = Real.log 2 + Real.log 3 + Real.log 2 := by
    rw [show (12 : ℝ) = 2 * 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.sum_Icc_succ_top (by norm_num),
    Finset.sum_Icc_succ_top (by norm_num), hlog]
  simp [e1, e2, e3, e4]

end Chebyshev

