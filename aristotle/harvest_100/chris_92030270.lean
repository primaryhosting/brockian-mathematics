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
/-!
# Divides
Category: Fibonacci
Target: Fibonacci.divides
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- **Divisibility of Fibonacci numbers.**
For all `m n : ℕ`, `Nat.fib m` divides `Nat.fib (m * n)`.

Proved by induction on `n`, using the addition formula
`fib (m + k) = fib m * fib (k + 1) + fib (m - 1) * fib k` (in the form `Nat.fib_add`). -/
theorem divides (m n : ℕ) : Nat.fib m ∣ Nat.fib (m * n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    cases m with
    | zero => simp
    | succ p =>
      have h : (p + 1) * (k + 1) = (p + 1) * k + p + 1 := by ring
      rw [h, Nat.fib_add]
      exact Nat.dvd_add (Dvd.dvd.mul_right ih _) (Dvd.dvd.mul_left dvd_rfl _)

end Fibonacci

