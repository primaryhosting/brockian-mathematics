import Mathlib
import RequestProject.Cassini6

/-!
# Cassini 6, Mathlib version

Companion file to `RequestProject/Cassini6.lean`.  We check that the Fibonacci
sequence `Math.fib` used there agrees with Mathlib's `Nat.fib`, restate
Cassini's identity at `n = 6` for `Nat.fib`, and derive it once more from
Mathlib's general Cassini identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.fib_add_two]

/-- Cassini's identity at `n = 6`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_6_nat_fib :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1) ^ 6 := by
  simpa [fib_eq_nat_fib] using Math.cassini_6

/-- Cassini's identity at `n = 6`, obtained from Mathlib's general Cassini
identity `Int.fib_succ_mul_fib_pred_sub_fib_sq`. -/
theorem cassini_6_of_mathlib :
    Int.fib 7 * Int.fib 5 - Int.fib 6 ^ 2 = (-1) ^ 6 := by
  have h := Int.fib_succ_mul_fib_pred_sub_fib_sq 6
  norm_num at h
  exact h

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
# Cassini 6
Category: Pure Mathematics
Target: Math.cassini_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file carries the required header comment as its very first token, so it
cannot contain an `import`; `Math.fib` is shown to agree with Mathlib's
`Nat.fib` in `RequestProject/Cassini6Mathlib.lean`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 6`: `F 5 · F 7 − F 6 ^ 2 = (−1) ^ 6`,
i.e. `5 · 13 − 8 ^ 2 = 1`.  The computation is carried out in `ℤ`, so that the
subtraction and the sign `(−1) ^ 6` make sense. -/
theorem cassini_6 :
    (fib 5 : Int) * (fib 7 : Int) - (fib 6 : Int) ^ 2 = (-1) ^ 6 := by
  decide

end Math

