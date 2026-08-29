/-
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced verbatim above as a plain block comment: Lean 4
-- requires `import` lines to precede every command, and `/-! ... -/` is a module
-- docstring command, so it cannot appear before `import Mathlib`.)

import Mathlib

namespace Math

/-- **Cassini's identity** for the Fibonacci numbers, stated over the integers:
`F n * F (n + 2) - F (n + 1) ^ 2 = (-1) ^ (n + 1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (Nat.fib (n + 3) : ℤ) = (Nat.fib (n + 1) : ℤ) + (Nat.fib (n + 2) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := n + 1))
    have h2 : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := n))
    have hpow : ((-1 : ℤ)) ^ (n + 2) = -((-1 : ℤ) ^ (n + 1)) := by ring
    simp only [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl]
    rw [h, hpow, ← ih, h2]
    ring

/-- **Cassini's identity at `n = 8`**: `F 7 * F 9 - F 8 ^ 2 = (-1) ^ 8`,
stated over the integers.  Numerically `F 7 = 13`, `F 8 = 21`, `F 9 = 34`,
so the left-hand side is `442 - 441 = 1`. -/
theorem cassini_8 :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  simpa using cassini 7

#print axioms Math.cassini
#print axioms Math.cassini_8

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

