import Mathlib
import RequestProject.Cassini7

/-!
# Cassini 7, stated with Mathlib's `Nat.fib`

This companion file links the self-contained `Math.fib` of `RequestProject.Cassini7`
with Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 7` in those terms.
-/

namespace Math

theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity at `n = 7`, with Mathlib's `Nat.fib`. -/
theorem cassini_7_nat_fib :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  simpa [fib_eq_nat_fib] using cassini_7

end Math

/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(This file carries the required header comment at its very top, so it cannot contain
`import` commands; `Math.fib` is proved equal to Mathlib's `Nat.fib` in
`RequestProject.Cassini7Mathlib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 7`: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`. -/
theorem cassini_7 :
    (fib 6 : Int) * (fib 8 : Int) - (fib 7 : Int) ^ 2 = (-1) ^ 7 := by
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

