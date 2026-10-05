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

theorem fib_add_int (m r : ℕ) :
    (Nat.fib (m + r) : ℤ)
      = Nat.fib m * ((Nat.fib (r + 1) : ℤ) - Nat.fib r) + Nat.fib (m + 1) * Nat.fib r := by
  cases r with
  | zero => simp
  | succ s =>
      have h : Nat.fib (m + s + 1) = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) :=
        Nat.fib_add m s
      have h2 : (Nat.fib (s + 2) : ℤ) = Nat.fib s + Nat.fib (s + 1) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (Nat.fib_add_two (n := s))
      have h1 : (Nat.fib (m + (s + 1)) : ℤ)
          = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
        have : m + (s + 1) = m + s + 1 := by omega
        rw [this]
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) h
      rw [h1, show s + 1 + 1 = s + 2 from rfl, h2]
      ring

/-- Doubling formula over `ℤ` (no truncated subtraction). -/
