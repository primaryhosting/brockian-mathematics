/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- **Simple Zero Shadow.**
For every natural number `m` with `1 ≤ m` we have `2 * m ≤ m ^ 2 + 1`, with equality
if and only if `m = 1`.  This is Montgomery's `(m - 1) ^ 2 ≥ 0` integrality step that
separates *simple* zeros in the two-thirds argument. -/
theorem simple_zero_shadow (m : Nat) (hm : 1 ≤ m) :
    2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  match m with
  | 0 => omega
  | 1 => exact ⟨by decide, by decide⟩
  | (k + 2) =>
    have h : (k + 2) ^ 2 = k * k + 4 * k + 4 := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.succ_mul, Nat.mul_succ]
      omega
    omega

end Riemann.Method

#print axioms Riemann.Method.simple_zero_shadow

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

