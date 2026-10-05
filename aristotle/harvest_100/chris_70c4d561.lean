import Mathlib
import RequestProject.Math

/-!
# Cassini 5 — Mathlib companion file

This file connects the self-contained development in `RequestProject/Math.lean` with
Mathlib: it shows `Math.fib = Nat.fib`, restates `Math.cassini_5` in terms of `Nat.fib`,
and re-derives it from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 5`, phrased with Mathlib's `Nat.fib`. -/
theorem cassini_5_nat_fib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1) ^ 5 := by
  simpa [fib_eq_nat_fib] using cassini_5

/-- Cassini's identity at `n = 5`, derived from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq : ∀ n : ℤ,
  Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs`. -/
theorem cassini_5_of_mathlib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1) ^ 5 := by
  have e6 : Int.fib 6 = (Nat.fib 6 : ℤ) := by
    rw [show ((6 : ℤ)) = ((6 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e5 : Int.fib 5 = (Nat.fib 5 : ℤ) := by
    rw [show ((5 : ℤ)) = ((5 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have e4 : Int.fib 4 = (Nat.fib 4 : ℤ) := by
    rw [show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by norm_num, Int.fib_natCast]
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 5
  rw [show ((5 : ℤ) + 1) = 6 by norm_num, show ((5 : ℤ) - 1) = 4 by norm_num,
    show ((5 : ℤ)).natAbs = 5 from rfl, e6, e5, e4] at h
  linarith [h]

end Math

/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

(This file must begin with the required header comment, which Lean parses as a module
docstring and therefore forbids any `import` afterwards; so the sequence is defined here
from scratch.  The file `RequestProject/MathCassini.lean` proves that this is exactly
Mathlib's `Nat.fib`, and re-derives the statement below from Mathlib's general form of
Cassini's identity.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 5`**: `F 4 * F 6 - F 5 ^ 2 = (-1) ^ 5`, over the integers. -/
theorem cassini_5 :
    (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1) ^ 5 := by
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

