/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `RequestProject/CassiniMathlib.lean`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 9`: `F(8) · F(10) − F(9)² = (−1)^9`. -/
theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
  decide

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

import Mathlib
import RequestProject.Math

/-!
# Cassini 9 — Mathlib version

The same statement as `Math.cassini_9`, but phrased with Mathlib's `Nat.fib`,
together with a derivation from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`, and a proof that the local `Math.fib`
agrees with `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity at `n = 9`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_9_nat_fib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  norm_num [Nat.fib]

/-- Cassini's identity at `n = 9`, obtained from Mathlib's general Cassini identity. -/
theorem cassini_9_via_mathlib :
    Int.fib (9 + 1) * Int.fib (9 - 1) - Int.fib 9 ^ 2 = (-1) ^ (9 : ℤ).natAbs :=
  Int.fib_succ_mul_fib_pred_sub_fib_sq 9

end Math

