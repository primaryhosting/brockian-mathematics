import Mathlib
/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 2`**: `F 1 * F 3 - F 2 ^ 2 = (-1) ^ 2`,
where `F = Nat.fib` is the Fibonacci sequence and the computation takes place in `ℤ`.

The proof specializes Mathlib's `Int.fib_succ_mul_fib_pred_sub_fib_sq`
(Cassini's identity, `Mathlib/Data/Int/Fib/Lemmas.lean`) at `n = 2`. -/
theorem cassini_2 :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1) ^ 2 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 2
  rw [show ((2 : ℤ) + 1) = ((3 : ℕ) : ℤ) by norm_num,
      show ((2 : ℤ) - 1) = ((1 : ℕ) : ℤ) by norm_num,
      show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num,
      Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  rw [mul_comm]
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

