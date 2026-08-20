/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math

theorem fib_eq_natFib (n : Nat) : fib n = (Nat.fib n : Int) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (k + 2) =>
        rw [fib_add_two, Nat.fib_add_two, ih k (by omega), ih (k + 1) (by omega)]
        push_cast
        ring

/-- Cassini's identity at `n = 14`, stated with Mathlib's `Nat.fib`:
`F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
theorem cassini_14_natFib :
    (Nat.fib 13 : Int) * (Nat.fib 15 : Int) - (Nat.fib 14 : Int) ^ 2 = (-1 : Int) ^ 14 := by
  simpa [fib_eq_natFib] using cassini_14

end Math

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, valued in `ℤ`: `F 0 = 0`, `F 1 = 1`,
`F (n + 2) = F n + F (n + 1)`. -/
def fib : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

@[simp] theorem fib_zero : fib 0 = 0 := rfl

@[simp] theorem fib_one : fib 1 = 1 := rfl

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- Key intermediate lemma (Cassini's identity in product form):
`F (n + 1) * F (n + 3) - F (n + 2) * F (n + 2) = (-1) ^ (n + 2)` for every `n`. -/
theorem cassini_mul (n : Nat) :
    fib (n + 1) * fib (n + 3) - fib (n + 2) * fib (n + 2) = (-1 : Int) ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
      have h3 : fib (k + 3) = fib (k + 1) + fib (k + 2) := fib_add_two (k + 1)
      have h4 : fib (k + 4) = fib (k + 2) + fib (k + 3) := fib_add_two (k + 2)
      have hp : ((-1 : Int)) ^ (k + 3) = -((-1 : Int)) ^ (k + 2) := by
        simp [Int.pow_succ]
      rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl,
        show k + 1 + 3 = k + 4 from rfl, hp, h4, h3]
      rw [h3] at ih
      generalize ((-1 : Int)) ^ (k + 2) = c at ih
      generalize fib (k + 1) = a at ih ⊢
      generalize fib (k + 2) = b at ih ⊢
      grind

/-- Cassini's identity: `F (n + 1) * F (n + 3) - F (n + 2) ^ 2 = (-1) ^ (n + 2)`. -/
theorem cassini (n : Nat) :
    fib (n + 1) * fib (n + 3) - fib (n + 2) ^ 2 = (-1 : Int) ^ (n + 2) := by
  simpa [Int.pow_succ] using cassini_mul n

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
theorem cassini_14 : fib 13 * fib 15 - fib 14 ^ 2 = (-1 : Int) ^ 14 :=
  cassini 12

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

