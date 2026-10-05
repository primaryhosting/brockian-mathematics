import Mathlib
import RequestProject.Math

/-!
# Cassini 3, stated with Mathlib's `Nat.fib`

This file links the self-contained `Math.fib` used in `RequestProject.Math` with
Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 3` for `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 3` for Mathlib's `Nat.fib`. -/
theorem cassini_3_nat_fib :
    (Nat.fib 2 : Int) * (Nat.fib 4 : Int) - (Nat.fib 3 : Int) ^ 2 = (-1) ^ 3 := by
  simp only [← fib_eq_nat_fib]
  exact cassini_3

end Math

/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in `RequestProject.MathFib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 3`: `F(2) · F(4) − F(3)² = (−1)³`,
i.e. `1 · 3 − 2² = −1`. -/
theorem cassini_3 :
    (fib 2 : Int) * (fib 4 : Int) - (fib 3 : Int) ^ 2 = (-1) ^ 3 := by
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

