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

theorem cassini_aux (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib (m + 1) * Nat.fib m - (Nat.fib m : ℤ) ^ 2 = (-1) ^ m := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      have h : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (Nat.fib_add_two (n := k))
      rw [h, pow_succ]
      linear_combination (-1 : ℤ) * ih

/-- Addition formula for Fibonacci numbers over `ℤ`, valid for all `r` (including `r = 0`). -/
