/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in
`RequestProject/Cassini11Mathlib.lean`). It is defined here so that this file,
which must begin with the header comment above, needs no `import` line. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 11`**: `F 10 * F 12 - F 11 ^ 2 = (-1) ^ 11`.

Numerically: `55 * 144 - 89 ^ 2 = 7920 - 7921 = -1`.

This is the `n = 11` instance of Cassini's identity, which is available in Mathlib as
`Int.fib_succ_mul_fib_pred_sub_fib_sq`; that derivation is carried out in
`RequestProject/Cassini11Mathlib.lean` as `Math.cassini_11_of_mathlib`. -/
theorem cassini_11 :
    (fib 10 : Int) * (fib 12 : Int) - (fib 11 : Int) ^ 2 = (-1 : Int) ^ 11 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini11

/-!
# Cassini 11, via Mathlib

Companion file to `RequestProject/Cassini11.lean`: here we check that the locally
defined `Math.fib` agrees with Mathlib's `Nat.fib`, and we rederive the `n = 11`
instance of Cassini's identity from Mathlib's general version
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 11`, stated with Mathlib's `Nat.fib` and derived from
Mathlib's general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_11_of_mathlib :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1 : ℤ) ^ 11 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq ((11 : ℕ) : ℤ)
  rw [show ((11:ℕ):ℤ) + 1 = ((12:ℕ):ℤ) by norm_num,
      show ((11:ℕ):ℤ) - 1 = ((10:ℕ):ℤ) by norm_num,
      Int.fib_natCast, Int.fib_natCast, Int.fib_natCast, Int.natAbs_natCast] at h
  linarith [h]

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

