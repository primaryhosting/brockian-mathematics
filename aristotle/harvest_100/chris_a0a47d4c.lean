import Mathlib
import RequestProject.Cassini14

/-!
# Cassini 14 (Mathlib restatement)

This file identifies the self-contained Fibonacci sequence `Math.F` of
`RequestProject/Cassini14.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 14` in terms of `Nat.fib`.
-/

namespace Math

theorem F_eq_fib (n : ℕ) : F n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [F, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-- Cassini's identity at `n = 14`, phrased with Mathlib's `Nat.fib`. -/
theorem cassini_14_fib :
    (Nat.fib 13 : ℤ) * (Nat.fib 15 : ℤ) - (Nat.fib 14 : ℤ) ^ 2 = (-1) ^ 14 := by
  simpa [F_eq_fib] using cassini_14

end Math

/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 does not permit any comment (including this header) to precede an
-- `import` line, so this file is deliberately import-free and self-contained.
-- The companion file `RequestProject/Cassini14Mathlib.lean` connects the Fibonacci
-- numbers defined here with Mathlib's `Nat.fib` and restates the result.

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/
def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

/-- Cassini's identity at `n = 14`: `F 13 * F 15 - F 14 ^ 2 = (-1) ^ 14`,
with the arithmetic carried out in `ℤ`. -/
theorem cassini_14 : (F 13 : Int) * (F 15 : Int) - (F 14 : Int) ^ 2 = (-1) ^ 14 := by
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

