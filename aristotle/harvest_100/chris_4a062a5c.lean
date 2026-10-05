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

/-- **Integrality step.** For every natural number `m`, `3 * m ≤ m ^ 2 + 2`.

Equivalently `m ^ 2 ≥ 3 * m - 2`, i.e. `(m - 1) * (m - 2) ≥ 0` over the integers.
The proof splits on `m = 0`, `m = 1`, and `m = k + 2`; in the last case
`(k + 2) ^ 2 + 2 = k * k + 4 * k + 6 ≥ 3 * k + 6 = 3 * (k + 2)`. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  match m with
  | 0 => decide
  | 1 => decide
  | (k + 2) =>
    have hsq : (k + 2) ^ 2 = k * k + 4 * k + 4 := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.succ_mul, Nat.mul_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hsq]
    have h : 4 * k ≤ k * k + 4 * k := Nat.le_add_left _ _
    omega

end Riemann.Method

