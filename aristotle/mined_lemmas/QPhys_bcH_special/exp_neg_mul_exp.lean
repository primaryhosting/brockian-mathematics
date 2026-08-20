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

namespace QPhys

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- In a Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  simpa using exp_mul_exp_neg (-x)

/-- If the commutator `C = AB - BA` is central, then `e^{tA} B e^{-tA} = B + t C`. -/
