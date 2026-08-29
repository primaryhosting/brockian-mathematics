import Mathlib

/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
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


namespace Riemann.Method

/-- **Simple zero shadow.** For every natural number `m` with `1 ≤ m` we have
`2 * m ≤ m ^ 2 + 1`, with equality if and only if `m = 1`.
This is Montgomery's `(m - 1) ^ 2 ≥ 0` integrality step.

The hypothesis `1 ≤ m` is kept as requested; it turns out not to be needed
(both parts also hold for `m = 0`). -/
theorem simple_zero_shadow (m : ℕ) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  constructor
  · nlinarith [Nat.sub_add_cancel hm, sq_nonneg (m - 1 : ℤ)]
  · constructor
    · intro h
      nlinarith [sq_nonneg (m - 1 : ℤ), h]
    · rintro rfl
      norm_num

end Riemann.Method
#print axioms Riemann.Method.simple_zero_shadow

