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

/-- The von Mangoldt function at `4` equals `log 2`, since `4 = 2 ^ 2`. -/

lemma log_two_add_log_three_add_log_two :
    Real.log 2 + Real.log 3 + Real.log 2 = Real.log 12 := by
  have h : (12 : ℝ) = 2 * 3 * 2 := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/-- The second Chebyshev function at `4`:
`ψ(4) = ∑_{n ≤ 4} Λ(n) = log 2 + log 3 + log 2 = log 12`. -/
