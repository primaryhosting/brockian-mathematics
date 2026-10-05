/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, with `fib 0 = 0` and `fib 1 = 1`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 3`: `F(2) * F(4) - F(3)^2 = (-1)^3`. -/
theorem cassini_3 :
    (fib 2 : Int) * (fib 4 : Int) - (fib 3 : Int) ^ 2 = (-1) ^ 3 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini3

/-!
# Cassini 3, stated with Mathlib's `Nat.fib`

Supplementary file: identifies the local `Math.fib` with Mathlib's `Nat.fib`
and restates Cassini's identity at `n = 3` in those terms.
-/

namespace Math

/-- The local Fibonacci function agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 3`, phrased with `Nat.fib`. -/
theorem cassini_3_natFib :
    (Nat.fib 2 : ℤ) * (Nat.fib 4 : ℤ) - (Nat.fib 3 : ℤ) ^ 2 = (-1) ^ 3 := by
  simpa [fib_eq_natFib] using cassini_3

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

