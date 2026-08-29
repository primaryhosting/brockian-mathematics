/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file's required header comment must be the very first thing in the file, which
prevents an `import` line, so the sequence is defined here from scratch rather than
taken from Mathlib; it agrees with `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 8`: `F 7 * F 9 - F 8 ^ 2 = (-1) ^ 8`. -/
theorem cassini_8 :
    (fib 7 : Int) * (fib 9 : Int) - (fib 8 : Int) ^ 2 = (-1) ^ 8 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini8

/-!
# Cassini's identity, Mathlib companion file

`RequestProject/Cassini8.lean` must begin with a fixed header comment, which prevents it
from containing an `import` line, so it defines `Math.fib` from scratch.  Here we identify
`Math.fib` with `Nat.fib`, prove the general Cassini identity, and restate the `n = 8`
instance in terms of `Nat.fib`.
-/

namespace Math

@[simp] theorem fib_eq_natFib (n : ℕ) : fib n = Nat.fib n := by
  induction n using fib.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 => rw [fib, ih1, ih2, Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity: `F n * F (n + 2) - F (n + 1) ^ 2 = (-1) ^ (n + 1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]
        push_cast
        ring
      have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        rw [Nat.fib_add_two]
        push_cast
        ring
      rw [show k + 1 + 2 = k + 3 from rfl, h, h2, pow_succ]
      rw [h2] at ih
      linear_combination -ih

/-- Cassini's identity at `n = 8`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_8' :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 :=
  cassini 7

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

