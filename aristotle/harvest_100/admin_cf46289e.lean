/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 5`: `F(4) * F(6) - F(5)^2 = (-1)^5`. -/
theorem cassini_5 :
    (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1 : Int) ^ 5 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini5

/-!
# Cassini 5 (Mathlib version)

The header of `RequestProject/Cassini5.lean` is required to be the very first thing in that
file, which prevents an `import` line there; so the statement in terms of Mathlib's `Nat.fib`
is recorded here, together with the agreement `Math.fib = Nat.fib`.
-/

namespace Math

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-- Cassini's identity at `n = 5`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_5_nat_fib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1 : ℤ) ^ 5 := by
  simpa [fib_eq_nat_fib] using cassini_5

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

