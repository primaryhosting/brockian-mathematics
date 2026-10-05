/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci numbers, valued in `ℤ`: `fibZ 0 = 0`, `fibZ 1 = 1`,
`fibZ (n+2) = fibZ n + fibZ (n+1)`. -/
def fibZ : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibZ n + fibZ (n + 1)

/-- Cassini's identity at `n = 15`: `F(14) * F(16) - F(15)^2 = (-1)^15`. -/
theorem cassini_15 : fibZ 14 * fibZ 16 - fibZ 15 ^ 2 = (-1) ^ 15 := by rfl

end Math

import Mathlib
import RequestProject.Cassini15

/-!
# Cassini 15, phrased with Mathlib's `Nat.fib`

This file connects the self-contained Fibonacci function `Math.fibZ` used in
`RequestProject/Cassini15.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 15` in those terms.
-/

namespace Math

/-- `fibZ` agrees with Mathlib's `Nat.fib`. -/
theorem fibZ_eq_fib (n : Nat) : fibZ n = (Nat.fib n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (m + 2) =>
      rw [fibZ, ih m (by omega), ih (m + 1) (by omega), Nat.fib_add_two]
      push_cast
      ring

/-- Cassini's identity at `n = 15`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_15_fib :
    (Nat.fib 14 : ℤ) * (Nat.fib 16 : ℤ) - (Nat.fib 15 : ℤ) ^ 2 = (-1) ^ 15 := by
  simpa [fibZ_eq_fib] using cassini_15

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

