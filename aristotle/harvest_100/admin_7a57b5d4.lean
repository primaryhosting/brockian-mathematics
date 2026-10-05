/-
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the header above is written as a plain block comment.)

import Mathlib

/-!
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cassini's identity at `n = 12`**: `F(11) * F(13) - F(12)^2 = (-1)^12`,
where `F` is the Fibonacci sequence (`Nat.fib`), the computation taking place in `ℤ`.

The proof specializes Mathlib's Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq : ∀ n : ℤ, Int.fib (n + 1) * Int.fib (n - 1)
  - Int.fib n ^ 2 = (-1) ^ n.natAbs`
to `n = 12`, transporting along `Int.fib_natCast`.
(The identity can also be checked directly by `norm_num [Nat.fib]`.) -/
theorem cassini_12 :
    (Nat.fib 11 : ℤ) * (Nat.fib 13 : ℤ) - (Nat.fib 12 : ℤ) ^ 2 = (-1 : ℤ) ^ 12 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 12
  have h11 : Int.fib (12 - 1) = (Nat.fib 11 : ℤ) := by
    rw [show (12 - 1 : ℤ) = ((11 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h13 : Int.fib (12 + 1) = (Nat.fib 13 : ℤ) := by
    rw [show (12 + 1 : ℤ) = ((13 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h12 : Int.fib 12 = (Nat.fib 12 : ℤ) := by
    rw [show (12 : ℤ) = ((12 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  rw [h11, h13, h12] at h
  simpa [mul_comm] using h

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

