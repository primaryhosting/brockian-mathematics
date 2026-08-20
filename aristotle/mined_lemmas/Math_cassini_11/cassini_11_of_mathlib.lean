/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in
`RequestProject/Cassini11Mathlib.lean`). It is defined here so that this file,
which must begin with the header comment above, needs no `import` line. -/

theorem cassini_11_of_mathlib :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1 : ℤ) ^ 11 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq ((11 : ℕ) : ℤ)
  rw [show ((11:ℕ):ℤ) + 1 = ((12:ℕ):ℤ) by norm_num,
      show ((11:ℕ):ℤ) - 1 = ((10:ℕ):ℤ) by norm_num,
      Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.natAbs_natCast] at h
  linarith [h]

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

