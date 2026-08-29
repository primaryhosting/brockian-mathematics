/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, and Lean requires all
`import` commands to precede any command (including a module docstring). The file is therefore
kept self-contained: the Fibonacci numbers are defined here and everything is proved from
first principles, with no imports.
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- The algebraic core of the induction step of Cassini's identity. -/
private theorem cassini_step (x y c : Int) (h : x * (x + y) - y ^ 2 = c) :
    y * (y + (x + y)) - (x + y) ^ 2 = c * (-1) := by grind

/-- Cassini's identity: `F n * F (n+2) - F (n+1) ^ 2 = (-1) ^ (n+1)` (over `ℤ`). -/
theorem cassini (n : Nat) :
    (fib n : Int) * (fib (n + 2) : Int) - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h1 : (fib (k + 3) : Int) = (fib (k + 1) : Int) + (fib (k + 2) : Int) := by
      have : fib (k + 3) = fib (k + 1) + fib (k + 2) := rfl
      omega
    have h2 : (fib (k + 2) : Int) = (fib k : Int) + (fib (k + 1) : Int) := by
      have : fib (k + 2) = fib k + fib (k + 1) := rfl
      omega
    have hp : ((-1 : Int)) ^ (k + 1 + 1) = ((-1 : Int)) ^ (k + 1) * (-1) :=
      Int.pow_succ (-1) (k + 1)
    rw [h2] at ih
    show (fib (k + 1) : Int) * (fib (k + 3) : Int) - (fib (k + 2) : Int) ^ 2 = (-1) ^ (k + 1 + 1)
    rw [hp, h1, h2]
    exact cassini_step _ _ _ ih

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
theorem cassini_14 :
    (fib 13 : Int) * (fib 15 : Int) - (fib 14 : Int) ^ 2 = (-1) ^ 14 :=
  cassini 13

/-- Sanity check on the Fibonacci values involved: `F 13 = 233`, `F 14 = 377`, `F 15 = 610`. -/
theorem fib_values : fib 13 = 233 ∧ fib 14 = 377 ∧ fib 15 = 610 := by decide

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

