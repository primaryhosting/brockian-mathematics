import Mathlib
import RequestProject.Math

/-!
# Cassini 6 (Mathlib version)
Category: Pure Mathematics
Target: Math.cassini_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The same statement as `Math.cassini_6`, but phrased with Mathlib's `Nat.fib` and derived from
Mathlib's Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`
(`Mathlib/Data/Int/Fib/Lemmas.lean`).
-/

namespace Math

/-- **Cassini's identity at `n = 6`** for Mathlib's `Nat.fib`:
`F 5 * F 7 - F 6 ^ 2 = (-1) ^ 6`.

Derived from `Int.fib_succ_mul_fib_pred_sub_fib_sq`, which states
`Int.fib (n + 1) * Int.fib (n - 1) - Int.fib n ^ 2 = (-1) ^ n.natAbs` for all `n : ℤ`. -/
theorem cassini_6_nat_fib :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1 : ℤ) ^ 6 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 6
  rw [show ((6 : ℤ) + 1) = ((7 : ℕ) : ℤ) by norm_num,
    show ((6 : ℤ) - 1) = ((5 : ℕ) : ℤ) by norm_num,
    show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num,
    Int.fib_natCast, Int.fib_natCast, Int.fib_natCast] at h
  simp only [Int.natAbs_natCast] at h
  linarith [h]

/-- The Fibonacci numbers defined in `RequestProject/Math.lean` agree with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

end Math

/-!
# Cassini 6
Category: Pure Mathematics
Target: Math.cassini_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(Defined here rather than taken from Mathlib because the required header comment above is a
module docstring, which Lean does not allow to precede an `import` command; the same statement
is proved from Mathlib's Cassini identity in `RequestProject/MathViaMathlib.lean`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 6`**: `F 5 * F 7 - F 6 ^ 2 = (-1) ^ 6`, i.e. `5 * 13 - 8 ^ 2 = 1`,
stated over `ℤ`. -/
theorem cassini_6 :
    (fib 5 : Int) * (fib 7 : Int) - (fib 6 : Int) ^ 2 = (-1 : Int) ^ 6 := by
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

