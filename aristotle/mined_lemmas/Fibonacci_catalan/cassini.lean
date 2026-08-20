/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Fibonacci

/-- Cassini's identity: `fib (m+1)^2 - fib m * fib (m+2) = (-1)^m`. -/

theorem cassini (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) = (-1) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have h1 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      have h2 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h1' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h1
      have h2' : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h2
      have hidx1 : (k + 1) + 1 = k + 2 := rfl
      have hidx2 : (k + 1) + 2 = k + 3 := rfl
      rw [hidx1, hidx2, h2', h1']
      have hpow : ((-1 : ℤ)) ^ (k + 1) = -((-1 : ℤ) ^ k) := by rw [pow_succ]; ring
      have ih' : (Nat.fib (k + 1) : ℤ) ^ 2
          - (Nat.fib k : ℤ) * ((Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ)) = (-1) ^ k := by
        rw [← h1']; exact ih
      rw [hpow]
      linear_combination -ih'

/-- Catalan's identity, in addition form (no natural subtraction):
`fib (m+r)^2 - fib m * fib (m+2r) = (-1)^m * fib r ^ 2`. -/
