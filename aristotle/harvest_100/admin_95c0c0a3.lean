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

/--
For every natural number `m`, `3 * m ≤ m ^ 2 + 2`.

Equivalently `m ^ 2 ≥ 3 * m - 2`, i.e. `(m - 1) * (m - 2) ≥ 0` over the integers.
This is the integrality step behind Theorem C (the 5/6-distinct route) of the
zeta-two-thirds program, the next level above `m ^ 2 ≥ 2 * m - 1`.

The proof splits on `m < 3` (three finite checks) versus `m ≥ 3`, where
`3 * m ≤ m * m = m ^ 2 ≤ m ^ 2 + 2`.
-/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  cases Nat.lt_or_ge m 3 with
  | inl h =>
      match m, h with
      | 0, _ => decide
      | 1, _ => decide
      | 2, _ => decide
  | inr h =>
      calc 3 * m ≤ m * m := Nat.mul_le_mul h (Nat.le_refl m)
        _ ≤ m ^ 2 + 2 := by rw [Nat.pow_two]; exact Nat.le_add_right _ _

end Riemann.Method

