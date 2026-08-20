/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

This file is required to begin with the header comment above, which Lean only accepts as a
module docstring when the file has no `import` commands; hence the sequence is defined here
from scratch. The file `RequestProject/Cassini10Mathlib.lean` proves that this definition
agrees with Mathlib's `Nat.fib`, and derives the same identity for `Nat.fib` from Mathlib's
Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity** at `n = 10`: `F(9) * F(11) - F(10)^2 = (-1)^10`. -/
theorem cassini_10 : (fib 9 : Int) * (fib 11 : Int) - (fib 10 : Int) ^ 2 = (-1) ^ 10 := by
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
import RequestProject.Cassini10

/-!
# Cassini 10, via Mathlib's Fibonacci numbers

We check that the Fibonacci sequence `Math.fib` used in `RequestProject/Cassini10.lean`
agrees with Mathlib's `Nat.fib`, and we re-derive the identity
`F 9 * F 11 - F 10 ^ 2 = (-1) ^ 10` for `Nat.fib` from Mathlib's Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

theorem fib_eq_nat_fib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, ih n (by omega), ih (n + 1) (by omega), Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity at `n = 10`, stated for Mathlib's `Nat.fib`, deduced from Mathlib's
general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_10_nat_fib :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 10
  have e9 : Int.fib ((10 : ℤ) - 1) = (Nat.fib 9 : ℤ) := by
    rw [show (10 : ℤ) - 1 = ((9 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e10 : Int.fib (10 : ℤ) = (Nat.fib 10 : ℤ) := by
    rw [show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e11 : Int.fib ((10 : ℤ) + 1) = (Nat.fib 11 : ℤ) := by
    rw [show (10 : ℤ) + 1 = ((11 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [e9, e10, e11] at h
  rw [mul_comm]
  simpa using h

end Math

