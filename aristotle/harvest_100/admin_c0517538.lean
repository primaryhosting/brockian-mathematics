import Mathlib
import RequestProject.Cassini14

/-!
# Cassini 14, stated with Mathlib's `Nat.fib`

This companion file links the self-contained `Math.fib` of `RequestProject/Cassini14.lean`
with Mathlib's `Nat.fib`, proves Cassini's identity in general, and restates it at `n = 14`.
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity: `F n * F (n + 2) - F (n + 1) ^ 2 = (-1) ^ (n + 1)`. -/
theorem cassini : ∀ n : ℕ,
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1)
  | 0 => by norm_num
  | n + 1 => by
      have ih := cassini n
      have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h3 : Nat.fib (n + 1 + 2) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
      rw [h2] at ih
      rw [h3, h2]
      push_cast at ih ⊢
      have hp : ((-1 : ℤ)) ^ (n + 1 + 1) = -(-1) ^ (n + 1) := by ring
      rw [hp]
      linear_combination -ih

/-- Cassini's identity at `n = 14`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_14_natFib :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1) ^ 14 :=
  cassini 13

end Math

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(Defined here rather than imported, since this file must begin with the header
comment above and hence cannot contain `import` commands; the file
`RequestProject/Cassini14Mathlib.lean` proves this agrees with `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
theorem cassini_14 : (fib 13 : Int) * (fib 15 : Int) - (fib 14 : Int) ^ 2 = (-1) ^ 14 := by
  decide

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

