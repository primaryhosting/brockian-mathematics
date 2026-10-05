/-
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Catalan
Category: Fibonacci
Target: Fibonacci.catalan
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- Cassini's identity, in the form `F(m+1)² - F(m+1)F(m) - F(m)² = (-1)ᵐ` over `ℤ`. -/

theorem fib_two_mul_int (r : ℕ) :
    (Nat.fib (2 * r) : ℤ) = Nat.fib r * (2 * (Nat.fib (r + 1) : ℤ) - Nat.fib r) := by
  have hle : Nat.fib r ≤ 2 * Nat.fib (r + 1) := by
    have := Nat.fib_le_fib_succ (n := r)
    omega
  have h := Nat.fib_two_mul r
  have : (Nat.fib (2 * r) : ℤ) = (Nat.fib r : ℤ) * ((2 * Nat.fib (r + 1) - Nat.fib r : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) h
  rw [this]
  push_cast [Nat.cast_sub hle]
  ring

