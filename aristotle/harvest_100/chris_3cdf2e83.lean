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

/-- For every natural number `m`, `3 * m ≤ m ^ 2 + 2`.

Equivalently `m ^ 2 ≥ 3 * m - 2`, i.e. `(m - 1) * (m - 2) ≥ 0` over the integers.

The proof splits on `m = 0`, `m = 1`, and `m = k + 2`; in the last case
`(k + 2) ^ 2 + 2 = k * k + (4 * k + 4) + 2` dominates `3 * (k + 2) = 3 * k + 6`.

Note: the file cannot carry an `import` line, since the required header is a module
docstring, which must follow all imports. The proof therefore uses only core `Nat`
lemmas together with `omega`; with Mathlib available, `nlinarith [sq_nonneg m]` or
`nlinarith [Nat.sub_one_mul, Nat.le_of_lt_succ]` closes the goal in one step. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  match m with
  | 0 => decide
  | 1 => decide
  | (k + 2) =>
    have h : (k + 2) ^ 2 = k * k + (4 * k + 4) := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.mul_comm]
      omega
    rw [h]
    calc 3 * (k + 2) = (4 * k + 4) + 2 - k := by omega
      _ ≤ (4 * k + 4) + 2 := Nat.sub_le _ _
      _ ≤ k * k + (4 * k + 4) + 2 := Nat.add_le_add_right (Nat.le_add_left _ _) 2

end Riemann.Method

