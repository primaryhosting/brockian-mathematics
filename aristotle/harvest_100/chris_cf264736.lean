/-
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the header above uses `/- ... -/` rather than `/-! ... -/`, since Lean 4 rejects a
-- module doc comment placed before the `import` line ("invalid 'import' command").

import Mathlib

namespace Math

/-- **Cassini's identity at `n = 3`**: `F 2 * F 4 - F 3 ^ 2 = (-1) ^ 3`.

Derived from Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`
(Cassini's identity: `fib (n + 1) * fib (n - 1) - fib n ^ 2 = (-1) ^ |n|`) at `n = 3`. -/
theorem cassini_3 :
    (Nat.fib 2 : ℤ) * (Nat.fib 4 : ℤ) - (Nat.fib 3 : ℤ) ^ 2 = (-1 : ℤ) ^ 3 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 3
  rw [show ((3 : ℤ) + 1) = ((4 : ℕ) : ℤ) by norm_num,
    show ((3 : ℤ) - 1) = ((2 : ℕ) : ℤ) by norm_num,
    show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, Int.fib_natCast, Int.fib_natCast,
    Int.fib_natCast] at h
  simpa using h

end Math

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

