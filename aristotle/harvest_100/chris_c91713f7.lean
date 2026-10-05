/-
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header above is a
-- block comment and is repeated as a module docstring below.)

import Mathlib

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
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

namespace Math

/-- **Cassini's identity** for the Fibonacci numbers, proved by induction on `n`:
`F n * F (n+2) - F (n+1) ^ 2 = (-1) ^ (n+1)` over the integers. -/
theorem cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1' : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℤ))
          (Nat.fib_add_two (n := k + 1))
      have h2' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast (R := ℤ)) (Nat.fib_add_two (n := k))
      have hpow : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by
        rw [pow_succ]; ring
      show (Nat.fib (k + 1) : ℤ) * (Nat.fib (k + 3) : ℤ) - (Nat.fib (k + 2) : ℤ) ^ 2
          = (-1) ^ (k + 1 + 1)
      rw [h1', hpow, ← ih]
      nlinarith [h2', sq_nonneg ((Nat.fib (k + 1) : ℤ))]

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`. -/
theorem cassini_14 :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1 : ℤ) ^ 14 :=
  cassini 13

end Math

