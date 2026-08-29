/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

@[simp] theorem fib_zero : fib 0 = 0 := rfl

@[simp] theorem fib_one : fib 1 = 1 := rfl

@[simp] theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- Cassini's identity at `n = 11`: `F(10) · F(12) − F(11)² = (−1)^11`. -/
theorem cassini_11 :
    (fib 10 : Int) * (fib 12 : Int) - (fib 11 : Int) ^ 2 = (-1) ^ 11 := by
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
import RequestProject.Cassini11

/-!
# Cassini 11, phrased with Mathlib's `Nat.fib`

The target theorem `Math.cassini_11` lives in `RequestProject/Cassini11.lean`, whose required
header comment must be the very first thing in the file (so that file carries no imports and
uses its own copy `Math.fib` of the Fibonacci sequence).  Here we check that `Math.fib` agrees
with Mathlib's `Nat.fib` and restate Cassini's identity accordingly.
-/

namespace Math

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 => rw [fib_add_two, Nat.fib_add_two, ih1, ih2, Nat.add_comm]

/-- Cassini's identity at `n = 11`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_11_nat_fib :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1) ^ 11 := by
  simpa only [fib_eq_nat_fib] using cassini_11

end Math

