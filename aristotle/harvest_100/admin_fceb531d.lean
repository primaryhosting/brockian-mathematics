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

/-- The second Chebyshev function at `4`: `ψ(4) = Λ(1)+Λ(2)+Λ(3)+Λ(4) = log 12`. -/
theorem psi_two_le :
    ∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n = Real.log 12 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have hΛ1 : ArithmeticFunction.vonMangoldt 1 = 0 := vonMangoldt_apply_one
  have hΛ2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    simpa using vonMangoldt_apply_prime Nat.prime_two
  have hΛ3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    simpa using vonMangoldt_apply_prime Nat.prime_three
  have hΛ4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [h4, vonMangoldt_apply_pow (two_ne_zero)]
    simpa using vonMangoldt_apply_prime Nat.prime_two
  have hsum : ∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n
      = ArithmeticFunction.vonMangoldt 1 + ArithmeticFunction.vonMangoldt 2
        + ArithmeticFunction.vonMangoldt 3 + ArithmeticFunction.vonMangoldt 4 := by
    rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
    simp [Finset.sum_insert, Finset.mem_insert]
    ring
  rw [hsum, hΛ1, hΛ2, hΛ3, hΛ4]
  have h12 : (12 : ℝ) = 2 * 3 * 2 := by norm_num
  rw [h12, Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by norm_num)]
  ring

end Chebyshev

