/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to precede every other command, including
-- module docstrings, so this module is kept dependency-free (the header above must be
-- the first thing in the file). The Fibonacci sequence is therefore defined here, and
-- `RequestProject/Main.lean` (which does import Mathlib) proves that it agrees with
-- `Nat.fib` and re-derives the statement from Mathlib's Cassini identity
-- `Int.fib_succ_mul_fib_pred_sub_fib_sq`.

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n + 2) = F n + F (n + 1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity** at `n = 4`: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`. -/
theorem cassini_4 :
    (fib 3 : Int) * (fib 5 : Int) - (fib 4 : Int) ^ 2 = (-1 : Int) ^ 4 := by
  decide

end Math

import Mathlib
import Math

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

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini at `n = 4`, stated with `Nat.fib` and derived from Mathlib's Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_4_nat_fib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 4
  rw [show ((4 : ℤ) + 1) = ((5 : ℕ) : ℤ) by norm_num,
    show ((4 : ℤ) - 1) = ((3 : ℕ) : ℤ) by norm_num,
    show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, Int.fib_natCast, Int.fib_natCast,
    Int.fib_natCast] at h
  simpa using h

/-- The target statement `Math.cassini_4` restated via `Nat.fib`. -/
theorem cassini_4' :
    (Math.fib 3 : ℤ) * (Math.fib 5 : ℤ) - (Math.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [fib_eq_nat_fib] using cassini_4_nat_fib

end Math

