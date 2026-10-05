import Mathlib
import RequestProject.Cassini14

/-!
# Cassini 14, phrased with Mathlib's `Nat.fib`

The target theorem `Math.cassini_14` lives in `Cassini14.lean`, whose required header comment
must be the very first thing in that file; a module docstring may not precede `import`
commands, so that file is written against core Lean with its own `Math.fib`.  Here we check
that `Math.fib` agrees with Mathlib's `Nat.fib` and restate Cassini's identity accordingly.
-/

namespace Math

theorem fib_eq_natFib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (m + 2) =>
      rw [show fib (m + 2) = fib m + fib (m + 1) from rfl, Nat.fib_add_two,
        ih m (by omega), ih (m + 1) (by omega)]

/-- Cassini's identity at `n = 14` for Mathlib's `Nat.fib`. -/
theorem cassini_14_natFib :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1) ^ 14 := by
  have h := cassini_14
  simp only [fib_eq_natFib] at h
  rw [sq]
  exact h

end Math

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(This agrees with Mathlib's `Nat.fib`; see `Math.fib_eq_natFib` in `Cassini14Mathlib.lean`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity: `F(n) * F(n+2) - F(n+1)^2 = (-1)^(n+1)`, by induction on `n`. -/
theorem cassini_general (n : Nat) :
    (fib n : Int) * (fib (n + 2) : Int) - (fib (n + 1) : Int) * (fib (n + 1) : Int)
      = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
      have h3 : fib (k + 1 + 2) = fib (k + 1) + (fib k + fib (k + 1)) := rfl
      have h2 : fib (k + 1 + 1) = fib k + fib (k + 1) := rfl
      have hi : fib (k + 2) = fib k + fib (k + 1) := rfl
      have hp : ((-1 : Int)) ^ (k + 1 + 1) = (-1) ^ (k + 1) * (-1) := Int.pow_succ _ _
      rw [h3, h2, hp]
      rw [hi] at ih
      simp only [Int.natCast_add, Int.mul_add, Int.mul_comm] at ih ⊢
      omega

/-- Cassini's identity at `n = 14`: `F(13) · F(15) − F(14)² = (−1)^14`. -/
theorem cassini_14 :
    (fib 13 : Int) * (fib 15 : Int) - (fib 14 : Int) * (fib 14 : Int) = (-1) ^ 14 :=
  cassini_general 13

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

