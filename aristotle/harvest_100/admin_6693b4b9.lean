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

Since the required file header must be the very first thing in the file, no `import`
command may appear, so this is proved using only Lean core. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  match m with
  | 0 => decide
  | 1 => decide
  | (k + 2) =>
    have h : (k + 2) ^ 2 = k * k + 4 * k + 4 := by
      simp [Nat.pow_succ, Nat.pow_zero, Nat.succ_mul, Nat.mul_succ]
      omega
    omega

end Riemann.Method

