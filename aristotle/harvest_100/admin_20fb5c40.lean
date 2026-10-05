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

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the header block above appears immediately after the
-- single `import Mathlib` line.

namespace Fibonacci

/-- Auxiliary step: `Nat.fib m` divides `Nat.fib (k + m)` whenever it divides `Nat.fib k`.
This follows from the addition formula
`fib (a + b + 1) = fib a * fib b + fib (a + 1) * fib (b + 1)`. -/
theorem dvd_fib_add (m k : ℕ) (h : Nat.fib m ∣ Nat.fib k) :
    Nat.fib m ∣ Nat.fib (k + m) := by
  match m with
  | 0 => simpa using h
  | (m + 1) =>
    have : k + (m + 1) = k + m + 1 := by ring
    rw [this, Nat.fib_add]
    exact Nat.dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_left dvd_rfl _)

/-- **Divisibility for Fibonacci numbers**: for all `m n : ℕ`,
`Nat.fib m` divides `Nat.fib (m * n)`. -/
theorem divides (m n : ℕ) : Nat.fib m ∣ Nat.fib (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : m * (n + 1) = m * n + m := by ring
    rw [this]
    exact dvd_fib_add m (m * n) ih

end Fibonacci

