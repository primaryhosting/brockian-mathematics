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

Over the integers this is equivalent to `(m - 1) * (m - 2) ≥ 0`: the product of the two
factors is nonnegative because for `m = 1, 2` one factor vanishes, for `m = 0` both are
negative, and for `m ≥ 3` both are positive.

The proof splits on `m = 0`, `m = 1` and `m = k + 2`; in the last case
`(k + 2) ^ 2 + 2 = k * k + 4 * k + 6 ≥ 3 * k + 6 = 3 * (k + 2)`.

Note: the required file header is a module docstring, which must precede any `import`
command, so this file uses only Lean core (`omega`, `simp`, `decide`) and no Mathlib
lemmas. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  obtain _ | _ | k := m
  · decide
  · decide
  · have h : (k + 1 + 1) ^ 2 = k * k + 4 * k + 4 := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul]
      omega
    omega

end Riemann.Method

