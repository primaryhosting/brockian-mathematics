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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chebyshev

open ArithmeticFunction

/-- Λ(4) = log 2, since 4 = 2². -/

theorem psi_two_le :
    ∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n = Real.log 12 := by
  rw [sum_vonMangoldt_Icc_four]
  have h12 : (12 : ℝ) = 2 ^ 2 * 3 := by norm_num
  rw [h12, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  push_cast
  ring

end Chebyshev

