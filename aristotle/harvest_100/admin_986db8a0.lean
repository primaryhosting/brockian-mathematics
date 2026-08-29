import Mathlib
import RequestProject.Cassini6

/-!
# Cassini 6, Mathlib form

`Math.fib` agrees with Mathlib's `Nat.fib`, so Cassini's identity at `n = 6` also holds
in the form `Nat.fib 5 * Nat.fib 7 - Nat.fib 6 ^ 2 = (-1) ^ 6`.
-/

namespace Math

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 6`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_6_natFib :
    (Nat.fib 5 : ℤ) * (Nat.fib 7 : ℤ) - (Nat.fib 6 : ℤ) ^ 2 = (-1) ^ 6 := by
  simpa [fib_eq_natFib] using cassini_6

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

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 6`: `F(5) * F(7) - F(6)^2 = (-1)^6`. -/
theorem cassini_6 :
    (fib 5 : Int) * (fib 7 : Int) - (fib 6 : Int) ^ 2 = (-1) ^ 6 := by
  decide

end Math

