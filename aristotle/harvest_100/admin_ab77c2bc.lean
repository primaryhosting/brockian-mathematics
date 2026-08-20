import Mathlib
import RequestProject.Cassini13

/-!
# Cassini 13, stated with Mathlib's `Nat.fib`

The target theorem `Math.cassini_13` lives in `RequestProject/Cassini13.lean`, which is
import-free (a module docstring must be the first thing in that file, and Lean requires
`import` lines to come before any command).  Here we check that the local `Math.fib`
agrees with Mathlib's `Nat.fib` and restate Cassini's identity accordingly.
-/

namespace Math

theorem fib_eq_nat_fib (n : Nat) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega), Nat.add_comm]

/-- Cassini's identity at `n = 13`, phrased with Mathlib's `Nat.fib`. -/
theorem cassini_13_natFib :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  simpa [fib_eq_nat_fib] using cassini_13

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

/-!
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 13`: `F(12) * F(14) - F(13)^2 = (-1)^13`. -/
theorem cassini_13 :
    (fib 12 : Int) * (fib 14 : Int) - (fib 13 : Int) ^ 2 = (-1) ^ 13 := by
  decide

end Math

