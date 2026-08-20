/-
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cassini
Category: Fibonacci
Target: Fibonacci.cassini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- **Cassini's identity** for the Fibonacci numbers, stated over `ℤ` to avoid
truncated subtraction:  `F(n+2) * F(n) - F(n+1)^2 = (-1)^(n+1)`.
Proved by induction on `n` using the recurrence `F(n+3) = F(n+2) + F(n+1)`.

(Mathlib contains a related statement for the integer-indexed Fibonacci function,
`Int.fib_succ_mul_fib_pred_sub_fib_sq`; the proof below is self-contained for `Nat.fib`.) -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 2) : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]
      push_cast
      ring
    have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib k : ℤ) := by
      rw [Nat.fib_add_two]
      push_cast
      ring
    have hpow : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by
      rw [pow_succ]
      ring
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, h1, hpow, ← ih, h2]
    ring

end Fibonacci

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

