/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(Defined here rather than imported, since this file must start with the header comment
above and hence cannot carry an `import` line; `Math.fib_eq_natFib` in
`RequestProject.Cassini9Mathlib` identifies it with Mathlib's `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 9`: `F(8) * F(10) - F(9)^2 = (-1)^9`. -/
theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
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

import Mathlib
import RequestProject.Cassini9

/-!
# Cassini 9, stated with Mathlib's `Nat.fib`

This file connects the self-contained `Math.fib` of `RequestProject.Cassini9`
with Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 9` in those terms.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 9`, with Mathlib's `Nat.fib`:
`F(8) * F(10) - F(9)^2 = (-1)^9`. -/
theorem cassini_9_natFib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simpa [fib_eq_natFib] using cassini_9

end Math

