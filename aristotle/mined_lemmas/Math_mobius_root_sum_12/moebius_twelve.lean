import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
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

set_option grind.warning false

namespace Math

/-- The Möbius function vanishes at `12`, since `12 = 2 ^ 2 * 3` is not squarefree. -/

lemma moebius_twelve : ArithmeticFunction.moebius 12 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  decide

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/
