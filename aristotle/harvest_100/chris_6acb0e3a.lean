/-
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Key intermediate lemma: the general Cassini identity for Fibonacci numbers,
`F(n+2) * F(n) - F(n+1)^2 = (-1)^(n+1)` over the integers. -/
theorem cassini_general (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have h2 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
      rw [show k + 1 + 2 = k + 3 from rfl, h2]
      linear_combination (-1 : ℤ) * ih - (Nat.fib (k + 2) : ℤ) * h1

/-- Cassini's identity at `n = 14`: `F(13) * F(15) - F(14)^2 = (-1)^14`. -/
theorem cassini_14 :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1) ^ 14 := by
  have h := cassini_general 13
  linear_combination h

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

