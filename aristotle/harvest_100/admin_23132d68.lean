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

/-
# Cassini 6
Category: Pure Mathematics
Target: Math.cassini_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- Cassini's identity at `n = 6`, over the integers:
`F 5 * F 7 - (F 6)^2 = (-1)^6`, where `F` is `Nat.fib`.

Mathlib does not contain a general Cassini identity for `Nat.fib`; the values
`F 5 = 5`, `F 6 = 8`, `F 7 = 13` are computed from `Nat.fib` (see
`Nat.fib_add_two`), giving `5 * 13 - 8 ^ 2 = 1 = (-1) ^ 6`. -/
theorem cassini_6 :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1 : ℤ) ^ 6 := by
  norm_num [Nat.fib]

/-- The general Cassini identity, over the integers:
`F (n+1) * F (n+3) - F (n+2) ^ 2 = (-1) ^ n`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) * (Nat.fib (n + 3) : ℤ) - (Nat.fib (n + 2) : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [Nat.fib]
  | succ k ih =>
    have h : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
    have h' : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    push_cast [h, h']
    push_cast [h'] at ih
    ring_nf
    ring_nf at ih
    linarith [ih, pow_succ (-1 : ℤ) k]

/-- `cassini_6` follows from the general identity at `n = 6`. -/
example : (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1 : ℤ) ^ 6 := by simpa using cassini 4

end Math

