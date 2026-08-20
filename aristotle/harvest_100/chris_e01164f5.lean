import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, in Mathlib terms

This file links the self-contained Fibonacci function `Math.fib` of
`RequestProject.Cassini12` with Mathlib's `Nat.fib`, and restates Cassini's identity
at `n = 12` for `Nat.fib`. It also proves the general Cassini identity.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 12`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_12_nat_fib :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1 : ℤ) ^ 12 := by
  norm_num [Nat.fib]

/-- The general Cassini identity: `F(n) * F(n+2) - F(n+1)^2 = (-1)^(n+1)`. -/
theorem cassini_general (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      push_cast [h, h2] at *
      ring_nf
      ring_nf at ih
      linarith [ih]

end Math

/-!
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean requires `import` commands to appear before any other command, and a
-- module docstring `/-! ... -/` counts as a command. Since the header comment above must
-- literally begin the file, this module carries no imports and is self-contained.
-- The file `RequestProject/Cassini12Mathlib.lean` links `Math.fib` below to Mathlib's
-- `Nat.fib` and restates the result in Mathlib terms.

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 12`: `F(11) * F(13) - F(12)^2 = (-1)^12`. -/
theorem cassini_12 :
    (fib 11 : Int) * (fib 13 : Int) - (fib 12 : Int) ^ 2 = (-1 : Int) ^ 12 := by
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

