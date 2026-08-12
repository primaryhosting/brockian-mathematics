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

/-!
# Integrality Three Halves
Category: Riemann Program
Target: Riemann.Method.integrality_three_halves
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- For every natural number `m`, `3 * m ≤ m ^ 2 + 2`; equivalently `m ^ 2 ≥ 3 * m - 2`,
i.e. `(m - 1) * (m - 2) ≥ 0`. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  have hsq : m ^ 2 = m * m := by simp [Nat.pow_succ]
  rw [hsq]
  match m with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (k + 3) =>
      have h : (k + 3) * (k + 3) = k * k + 6 * k + 9 := by
        simp [Nat.mul_add, Nat.add_mul]
        omega
      rw [h]
      omega

#print axioms Riemann.Method.integrality_three_halves

end Riemann.Method

