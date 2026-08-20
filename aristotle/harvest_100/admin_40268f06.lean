import Mathlib
import RequestProject.Cassini13

/-!
# Cassini 13, stated for Mathlib's `Nat.fib`

Companion to `RequestProject/Cassini13.lean`.  We check that the locally defined
`Math.fib` agrees with Mathlib's `Nat.fib`, restate Cassini's identity at `n = 13`
for `Nat.fib`, and prove the general Cassini identity
`F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)` by induction.
-/

namespace Math

theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- **Cassini's identity** in general: `F (n+2) * F n - F (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k + 1))
      have h3 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.fib_add_two (n := k))
      rw [h3] at ih
      rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl, h, h3, pow_succ]
      linear_combination -ih

/-- Cassini's identity at `n = 13`, for Mathlib's `Nat.fib`. -/
theorem cassini_13_nat_fib :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  simpa using cassini 12

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

/-!
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

This file is required to begin with the header comment above; since Lean 4 does not
permit an `import` command to follow a module doc comment, this file is kept
import-free and therefore carries its own copy of the Fibonacci sequence.  The
companion file `RequestProject/Cassini13Mathlib.lean` imports Mathlib, proves
`Math.fib = Nat.fib`, and restates the result for Mathlib's `Nat.fib`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 13`**: `F 12 * F 14 - F 13 ^ 2 = (-1) ^ 13`,
computed in `ℤ`.  Numerically, `F 12 = 144`, `F 13 = 233`, `F 14 = 377`, and
`144 * 377 - 233 ^ 2 = 54288 - 54289 = -1`. -/
theorem cassini_13 :
    (fib 12 : Int) * (fib 14 : Int) - (fib 13 : Int) ^ 2 = (-1) ^ 13 := by
  decide

end Math

